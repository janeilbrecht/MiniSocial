import os
import time
import uuid
from flask import Flask, render_template, request, redirect, url_for, session, flash, g, abort, jsonify
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from cryptography.fernet import Fernet
import collections
import json
import sqlite3
import hashlib
import re
import csv
import unicodedata
from datetime import datetime

app = Flask(__name__)
app.secret_key = '123456789' 
DATABASE = 'database.sqlite'

UPLOAD_FOLDER = os.path.join(app.root_path, 'static', 'uploads')
ALLOWED_EXTENSIONS = {'png', 'jpg', 'jpeg', 'gif', 'webp'}
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['MAX_CONTENT_LENGTH'] = 5 * 1024 * 1024  # 5MB max upload
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def save_uploaded_image(file, prefix, user_id):
    if not file or file.filename == '':
        return None
    if allowed_file(file.filename):
        ext = file.filename.rsplit('.', 1)[1].lower()
        unique_name = f"{prefix}_{user_id}_{int(time.time())}_{uuid.uuid4().hex[:8]}.{ext}"
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], unique_name)
        file.save(filepath)
        return unique_name
    return False

def delete_upload(filename):
    """Removes a previously uploaded image from the uploads folder (ignores missing files)."""
    if not filename:
        return
    path = os.path.join(app.config['UPLOAD_FOLDER'], filename)
    if os.path.exists(path):
        try:
            os.remove(path)
        except OSError:
            pass

def can_comment_on_post(user_id, group_id):
    """Posts outside groups can be commented on by anyone logged in (login is enforced
    separately). Posts inside a group can only be commented on by members of that group."""
    if not group_id:
        return True
    if not user_id:
        return False
    member = query_db('SELECT 1 FROM group_members WHERE group_id = ? AND user_id = ?',
                      (group_id, user_id), one=True)
    return member is not None

def normalize_place_text(value):
    """Normalize place names for accent-insensitive matching."""
    value = (value or '').translate(str.maketrans({
        'ø': 'o', 'Ø': 'O', 'ł': 'l', 'Ł': 'L', 'đ': 'd', 'Đ': 'D',
        'ð': 'd', 'Ð': 'D', 'þ': 'th', 'Þ': 'Th', 'æ': 'ae', 'Æ': 'AE',
        'œ': 'oe', 'Œ': 'OE', 'ß': 'ss', 'ı': 'i'
    }))
    value = unicodedata.normalize('NFKD', value)
    value = ''.join(char for char in value if not unicodedata.combining(char))
    return re.sub(r'[^a-z0-9]+', '', value.casefold())


def selected_city(city_id):
    """Return a city only when the submitted ID exists in the local place catalogue."""
    if not city_id:
        return None
    try:
        city_id = int(city_id)
    except (TypeError, ValueError):
        return None
    return query_db(
        'SELECT id, city_name, country_code, country_name FROM cities WHERE id = ?',
        (city_id,), one=True
    )


def user_country(user_id):
    """Return the verified country for a user, or None if no city is selected."""
    if not user_id:
        return None
    return query_db(
        "SELECT c.country_code, c.country_name FROM users u "
        "JOIN cities c ON c.id = u.city_id WHERE u.id = ?",
        (user_id,), one=True
    )


def country_flag(country_code):
    """Convert a two-letter ISO country code to its Unicode flag emoji."""
    code = (country_code or '').strip().upper()
    if len(code) != 2 or not code.isalpha() or not code.isascii():
        return ''
    return ''.join(chr(127397 + ord(char)) for char in code)


app.jinja_env.globals['country_flag'] = country_flag


def can_access_town_hall_post(user_id, country_code):
    """Town Hall content is available only to users currently assigned to that country."""
    if not country_code:
        return True
    country = user_country(user_id)
    return bool(country and country['country_code'] == country_code)


def city_catalogue_file():
    """Return the path of the bundled city catalogue (data/worldwide_cities.csv)."""
    path = os.path.join(app.root_path, 'data', 'worldwide_cities.csv')
    if not os.path.exists(path):
        raise RuntimeError(f'Bundled city catalogue not found: {path}')
    return path


def init_db_schema():
    try:
        with sqlite3.connect(DATABASE) as conn:
            cursor = conn.cursor()
            cursor.execute("PRAGMA table_info(users)")
            columns = [row[1] for row in cursor.fetchall()]
            if 'bg_color' not in columns:
                cursor.execute("ALTER TABLE users ADD COLUMN bg_color TEXT DEFAULT '#f2f2f2'")
            if 'profile_picture' not in columns:
                cursor.execute("ALTER TABLE users ADD COLUMN profile_picture TEXT DEFAULT NULL")
            if 'banner_picture' not in columns:
                cursor.execute("ALTER TABLE users ADD COLUMN banner_picture TEXT DEFAULT NULL")
            if 'city_id' not in columns:
                cursor.execute("ALTER TABLE users ADD COLUMN city_id INTEGER DEFAULT NULL REFERENCES cities(id)")
            if 'legacy_location' not in columns:
                cursor.execute("ALTER TABLE users ADD COLUMN legacy_location TEXT DEFAULT NULL")

            cursor.execute("""
                CREATE TABLE IF NOT EXISTS cities (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    city_name TEXT NOT NULL,
                    country_code TEXT NOT NULL,
                    country_name TEXT NOT NULL,
                    UNIQUE(city_name, country_code)
                )
            """)

            # Load the bundled city catalogue (data/worldwide_cities.csv). It is
            # only re-imported when the file changes, and no network access or
            # live geocoding service is needed.
            cities_file = city_catalogue_file()
            catalogue_source = f'bundled:{os.path.getsize(cities_file)}:{os.path.getmtime(cities_file)}'
            cursor.execute("CREATE TABLE IF NOT EXISTS city_catalogue_meta (id INTEGER PRIMARY KEY CHECK (id = 1), source TEXT NOT NULL)")
            loaded_meta = cursor.execute("SELECT source FROM city_catalogue_meta WHERE id = 1").fetchone()
            if not loaded_meta or loaded_meta[0] != catalogue_source:
                with open(cities_file, 'r', encoding='utf-8', newline='') as place_file:
                    places = [(place['city_name'], place['country_code'], place['country_name'])
                              for place in csv.DictReader(place_file)]
                cursor.executemany(
                    "INSERT OR IGNORE INTO cities (city_name, country_code, country_name) VALUES (?, ?, ?)",
                    places
                )
                # Keep the table in sync with the CSV: remove places that are no
                # longer in the file (e.g. from an older, larger catalogue), but
                # never a place that a user has selected as their city.
                cursor.execute("CREATE TEMP TABLE catalogue_keep (city_name TEXT, country_code TEXT)")
                cursor.executemany("INSERT INTO catalogue_keep VALUES (?, ?)", ((p[0], p[1]) for p in places))
                cursor.execute("""
                    DELETE FROM cities
                    WHERE id NOT IN (
                        SELECT ci.id FROM cities ci
                        JOIN catalogue_keep k ON k.city_name = ci.city_name AND k.country_code = ci.country_code
                    )
                    AND id NOT IN (SELECT city_id FROM users WHERE city_id IS NOT NULL)
                """)
                cursor.execute("DROP TABLE catalogue_keep")
                cursor.execute(
                    "INSERT INTO city_catalogue_meta (id, source) VALUES (1, ?) ON CONFLICT(id) DO UPDATE SET source = excluded.source",
                    (catalogue_source,)
                )
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_cities_name ON cities(city_name)")
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_cities_country ON cities(country_code)")

            # Migrate old free-text locations only when they can be mapped
            # unambiguously to a place in the local city catalogue.
            city_rows = cursor.execute(
                "SELECT id, city_name, country_code, country_name FROM cities"
            ).fetchall()
            by_name = collections.defaultdict(list)
            by_name_country = {}
            for city_row in city_rows:
                city_id, city_name, country_code, country_name = city_row
                by_name[normalize_place_text(city_name)].append(city_row)
                by_name_country[(normalize_place_text(city_name), country_code)] = city_row
            country_aliases = {
                'uk': 'GB', 'greatbritain': 'GB', 'britain': 'GB', 'england': 'GB',
                'scotland': 'GB', 'wales': 'GB', 'northernireland': 'GB',
                'theuk': 'GB', 'czechrepublic': 'CZ', 'turkey': 'TR',
                'thenetherlands': 'NL', 'holland': 'NL', 'republicofireland': 'IE',
                'moldova': 'MD', 'macedonia': 'MK', 'russia': 'RU',
                'bosnia': 'BA', 'bosniaandherzegovina': 'BA', 'vatican': 'VA',
            }
            legacy_rows = cursor.execute(
                "SELECT id, location, city_id, legacy_location FROM users WHERE location IS NOT NULL AND TRIM(location) != ''"
            ).fetchall()
            for user_row in legacy_rows:
                user_id, old_location, existing_city_id, old_legacy = user_row
                if existing_city_id:
                    continue
                parts = [part.strip() for part in (old_location or '').split(',') if part.strip()]
                match = None
                if len(parts) >= 2:
                    city_key = normalize_place_text(parts[0])
                    country_key = normalize_place_text(parts[-1])
                    country_code = country_aliases.get(country_key)
                    if not country_code:
                        for candidate in city_rows:
                            if normalize_place_text(candidate[3]) == country_key:
                                country_code = candidate[2]
                                break
                    if country_code:
                        match = by_name_country.get((city_key, country_code))
                elif len(parts) == 1:
                    candidates = by_name.get(normalize_place_text(parts[0]), [])
                    if len(candidates) == 1:
                        match = candidates[0]
                if match:
                    city_id, city_name, country_code, country_name = match
                    cursor.execute(
                        "UPDATE users SET city_id = ?, location = ? WHERE id = ?",
                        (city_id, f"{city_name}, {country_name}", user_id)
                    )
                else:
                    cursor.execute(
                        "UPDATE users SET legacy_location = COALESCE(legacy_location, location), location = NULL, city_id = NULL WHERE id = ?",
                        (user_id,)
                    )

            # Create groups table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS groups (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT UNIQUE NOT NULL,
                    description TEXT DEFAULT '',
                    admin_id INTEGER NOT NULL,
                    bg_color TEXT DEFAULT '#f2f2f2',
                    banner_picture TEXT DEFAULT NULL,
                    hide_members INTEGER DEFAULT 0,
                    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP NOT NULL
                )
            """)

            cursor.execute("PRAGMA table_info(groups)")
            group_columns = [row[1] for row in cursor.fetchall()]
            if 'hide_members' not in group_columns:
                cursor.execute("ALTER TABLE groups ADD COLUMN hide_members INTEGER DEFAULT 0")

            # Create group_members table
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS group_members (
                    group_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    joined_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP NOT NULL,
                    PRIMARY KEY (group_id, user_id)
                )
            """)

            # Add group_id to posts table if missing
            cursor.execute("PRAGMA table_info(posts)")
            post_columns = [row[1] for row in cursor.fetchall()]
            if 'group_id' not in post_columns:
                cursor.execute("ALTER TABLE posts ADD COLUMN group_id INTEGER DEFAULT NULL")
            if 'town_hall_country_code' not in post_columns:
                cursor.execute("ALTER TABLE posts ADD COLUMN town_hall_country_code TEXT DEFAULT NULL")
            cursor.execute(
                "CREATE INDEX IF NOT EXISTS idx_posts_town_hall_country "
                "ON posts(town_hall_country_code)"
            )

            conn.commit()
    except sqlite3.Error as e:
        print(f"Database schema init error: {e}")

init_db_schema()

# Load censorship data
# WARNING! The censorship.dat file contains disturbing language when decrypted. 
# If you want to test whether moderation works, 
# you can trigger censorship using these words: 
# tier1badword, tier2badword, tier3badword
ENCRYPTED_FILE_PATH = 'censorship.dat'
fernet = Fernet('xpplx11wZUibz0E8tV8Z9mf-wwggzSrc21uQ17Qq2gg=')
with open(ENCRYPTED_FILE_PATH, 'rb') as encrypted_file:
    encrypted_data = encrypted_file.read()
decrypted_data = fernet.decrypt(encrypted_data)
MODERATION_CONFIG = json.loads(decrypted_data)
TIER1_WORDS = MODERATION_CONFIG['categories']['tier1_severe_violations']['words']
TIER2_PHRASES = MODERATION_CONFIG['categories']['tier2_spam_scams']['phrases']
TIER3_WORDS = MODERATION_CONFIG['categories']['tier3_mild_profanity']['words']

def get_db():
    """
    Connect to the application's configured database. The connection
    is unique for each request and will be reused if this is called
    again.
    """
    if 'db' not in g:
        g.db = sqlite3.connect(
            DATABASE,
            detect_types=sqlite3.PARSE_DECLTYPES
        )
        g.db.row_factory = sqlite3.Row

    return g.db


@app.teardown_appcontext
def close_connection(exception):
    """Closes the database again at the end of the request."""
    db = g.pop('db', None)

    if db is not None:
        db.close()


def query_db(query, args=(), one=False, commit=False):
    """
    Queries the database and returns a list of dictionaries, a single
    dictionary, or None. Also handles write operations.
    """
    db = get_db()
    
    # Using 'with' on a connection object implicitly handles transactions.
    # The 'with' statement will automatically commit if successful, 
    # or rollback if an exception occurs. This is safer.
    try:
        with db:
            cur = db.execute(query, args)
        
        # For SELECT statements, fetch the results after the transaction block
        if not commit:
            rv = cur.fetchall()
            return (rv[0] if rv else None) if one else rv
        
        # For write operations, we might want the cursor to get info like lastrowid
        return cur

    except sqlite3.Error as e:
        print(f"Database error: {e}")
        return None

@app.template_filter('datetimeformat')
def datetimeformat(value):
    if isinstance(value, datetime):
        dt = value
    elif isinstance(value, str):
        dt = datetime.strptime(value, '%Y-%m-%d %H:%M:%S')
    else:
        return "N/A"
    return dt.strftime('%b %d, %Y %H:%M')

def is_dark_color(hex_color):
    """Determine if a hex color is dark, returning True if dark (needs light text), False if light (needs dark text)."""
    if not hex_color or not isinstance(hex_color, str):
        return False
    hex_str = hex_color.strip().lstrip('#')
    if len(hex_str) == 3:
        hex_str = ''.join(c * 2 for c in hex_str)
    if len(hex_str) != 6:
        return False
    try:
        r = int(hex_str[0:2], 16)
        g = int(hex_str[2:4], 16)
        b = int(hex_str[4:6], 16)
        # Perceived brightness formula (standard ITU-R BT.601)
        brightness = (r * 299 + g * 587 + b * 114) / 1000
        return brightness < 150
    except ValueError:
        return False

@app.template_filter('is_dark_color')
def is_dark_color_filter(hex_color):
    return is_dark_color(hex_color)

@app.template_global('is_dark_color')
def is_dark_color_global(hex_color):
    return is_dark_color(hex_color)

REACTION_EMOJIS = {
    'like': '❤️', 'love': '😍', 'laugh': '😂',
    'wow': '😮', 'sad': '😢', 'angry': '😠',
}
REACTION_TYPES = list(REACTION_EMOJIS.keys())


@app.route('/')
def feed():
    #  1. Get Pagination and Filter Parameters 
    try:
        page = int(request.args.get('page', 1))
    except ValueError:
        page = 1
    sort = request.args.get('sort', 'new').lower()
    show = request.args.get('show', 'all').lower()
    
    # Define how many posts to show per page
    POSTS_PER_PAGE = 10
    offset = (page - 1) * POSTS_PER_PAGE

    current_user_id = session.get('user_id')
    params = []

    #  2. Build the Query 
    if current_user_id:
        if show == 'following':
            where_clause = "WHERE p.town_hall_country_code IS NULL AND p.user_id IN (SELECT followed_id FROM follows WHERE follower_id = ?) AND (p.group_id IS NULL OR p.group_id IN (SELECT group_id FROM group_members WHERE user_id = ?))"
            params.extend([current_user_id, current_user_id])
        else:
            where_clause = "WHERE p.town_hall_country_code IS NULL AND (p.group_id IS NULL OR p.group_id IN (SELECT group_id FROM group_members WHERE user_id = ?))"
            params.append(current_user_id)
    else:
        where_clause = "WHERE p.group_id IS NULL AND p.town_hall_country_code IS NULL"

    # Add the pagination parameters to the query arguments
    pagination_params = (POSTS_PER_PAGE, offset)

    if sort == 'popular':
        query = f"""
            SELECT p.id, p.content, p.created_at, p.group_id, g.name as group_name, u.username, u.id as user_id, u.profile_picture,
                   IFNULL(r.total_reactions, 0) as total_reactions
            FROM posts p
            JOIN users u ON p.user_id = u.id
            LEFT JOIN groups g ON p.group_id = g.id
            LEFT JOIN (
                SELECT post_id, COUNT(*) as total_reactions FROM reactions GROUP BY post_id
            ) r ON p.id = r.post_id
            {where_clause}
            ORDER BY total_reactions DESC, p.created_at DESC
            LIMIT ? OFFSET ?
        """
        final_params = params + list(pagination_params)
        posts = query_db(query, final_params)
    elif sort == 'recommended':
        posts = recommend(current_user_id, show == 'following' and current_user_id)
    else:  # Default sort is 'new'
        query = f"""
            SELECT p.id, p.content, p.created_at, p.group_id, g.name as group_name, u.username, u.id as user_id, u.profile_picture
            FROM posts p
            JOIN users u ON p.user_id = u.id
            LEFT JOIN groups g ON p.group_id = g.id
            {where_clause}
            ORDER BY p.created_at DESC
            LIMIT ? OFFSET ?
        """
        final_params = params + list(pagination_params)
        posts = query_db(query, final_params)

    posts_data = []
    for post in posts:
        # Determine if the current user follows the poster
        followed_poster = False
        if current_user_id and post['user_id'] != current_user_id:
            follow_check = query_db(
                'SELECT 1 FROM follows WHERE follower_id = ? AND followed_id = ?',
                (current_user_id, post['user_id']),
                one=True
            )
            if follow_check:
                followed_poster = True

        # Determine if the current user reacted to this post and with what reaction
        user_reaction = None
        if current_user_id:
            reaction_check = query_db(
                'SELECT reaction_type FROM reactions WHERE user_id = ? AND post_id = ?',
                (current_user_id, post['id']),
                one=True
            )
            if reaction_check:
                user_reaction = reaction_check['reaction_type']

        reactions = query_db('SELECT reaction_type, COUNT(*) as count FROM reactions WHERE post_id = ? GROUP BY reaction_type', (post['id'],))
        comments_raw = query_db('SELECT c.id, c.content, c.created_at, u.username, u.id as user_id, u.profile_picture FROM comments c JOIN users u ON c.user_id = u.id WHERE c.post_id = ? ORDER BY c.created_at ASC', (post['id'],))
        post_dict = dict(post)
        post_dict['content'], _ = moderate_content(post_dict['content'])
        comments_moderated = []
        for comment in comments_raw:
            comment_dict = dict(comment)
            comment_dict['content'], _ = moderate_content(comment_dict['content'])
            comments_moderated.append(comment_dict)
        posts_data.append({
            'post': post_dict,
            'reactions': reactions,
            'user_reaction': user_reaction,
            'followed_poster': followed_poster,
            'comments': comments_moderated
        })

    #  4. Render Template with Pagination Info 
    return render_template('feed.html.j2', 
                           posts=posts_data, 
                           current_sort=sort,
                           current_show=show,
                           page=page, # Pass current page number
                           per_page=POSTS_PER_PAGE, # Pass items per page
                           reaction_emojis=REACTION_EMOJIS,
                           reaction_types=REACTION_TYPES,
                           town_hall_country=user_country(current_user_id))

@app.route('/town-hall')
def town_hall():
    """Show the Town Hall for the logged-in user's verified country."""
    user_id = session.get('user_id')
    if not user_id:
        flash('Please log in to access your country’s Town Hall.', 'info')
        return redirect(url_for('login'))

    country = user_country(user_id)
    if not country:
        flash('Select a verified city in your profile before using Town Hall.', 'warning')
        return redirect(url_for('edit_profile'))

    try:
        page = max(1, int(request.args.get('page', 1)))
    except (TypeError, ValueError):
        page = 1
    per_page = 10
    offset = (page - 1) * per_page

    raw_posts = query_db('''
        SELECT p.id, p.content, p.created_at, p.group_id, p.town_hall_country_code,
               u.username, u.id AS user_id, u.profile_picture
        FROM posts p
        JOIN users u ON u.id = p.user_id
        WHERE p.town_hall_country_code = ?
        ORDER BY p.created_at DESC
        LIMIT ? OFFSET ?
    ''', (country['country_code'], per_page, offset))

    posts_data = []
    for raw_post in raw_posts:
        post = dict(raw_post)
        post['content'], _ = moderate_content(post['content'])
        user_reaction = None
        reaction = query_db(
            'SELECT reaction_type FROM reactions WHERE user_id = ? AND post_id = ?',
            (user_id, post['id']), one=True
        )
        if reaction:
            user_reaction = reaction['reaction_type']
        reactions = query_db(
            'SELECT reaction_type, COUNT(*) AS count FROM reactions WHERE post_id = ? GROUP BY reaction_type',
            (post['id'],)
        )
        comments_raw = query_db('''
            SELECT c.id, c.content, c.created_at, u.username, u.id AS user_id, u.profile_picture
            FROM comments c JOIN users u ON u.id = c.user_id
            WHERE c.post_id = ? ORDER BY c.created_at ASC
        ''', (post['id'],))
        comments = []
        for raw_comment in comments_raw:
            comment = dict(raw_comment)
            comment['content'], _ = moderate_content(comment['content'])
            comments.append(comment)
        posts_data.append({
            'post': post,
            'reactions': reactions,
            'user_reaction': user_reaction,
            'followed_poster': False,
            'comments': comments
        })

    return render_template(
        'town_hall.html.j2',
        posts=posts_data,
        country=country,
        page=page,
        per_page=per_page,
        reaction_emojis=REACTION_EMOJIS,
        reaction_types=REACTION_TYPES
    )


@app.route('/posts/new', methods=['POST'])
def add_post():
    """Handles creating a new post from the feed or from a group."""
    user_id = session.get('user_id')

    # Block access if user is not logged in
    if not user_id:
        flash('You must be logged in to create a post.', 'danger')
        return redirect(url_for('login'))

    # A post can belong to a group, a country's Town Hall, or the public feed.
    content = request.form.get('content')
    group_id = request.form.get('group_id')
    group_name = request.form.get('group_name')
    town_hall_country_code = (request.form.get('town_hall_country_code') or '').strip().upper() or None

    if town_hall_country_code:
        country = user_country(user_id)
        if group_id or group_name or not country or town_hall_country_code != country['country_code']:
            flash('You can only post to the Town Hall for your verified country.', 'danger')
            return redirect(url_for('town_hall') if country else url_for('edit_profile'))

    if group_name and not group_id:
        grp = query_db('SELECT id FROM groups WHERE LOWER(name) = LOWER(?)', (group_name.strip(),), one=True)
        if grp:
            group_id = grp['id']

    if group_id:
        try:
            group_id = int(group_id)
        except (ValueError, TypeError):
            group_id = None

    if group_id:
        grp = query_db('SELECT id, name FROM groups WHERE id = ?', (group_id,), one=True)
        if grp:
            is_member = query_db('SELECT 1 FROM group_members WHERE group_id = ? AND user_id = ?',
                                 (group_id, user_id), one=True)
            if not is_member:
                flash(f'You must be a member of g/{grp["name"]} to post in this group.', 'danger')
                return redirect(request.referrer or url_for('group_page', name=grp['name']))

    # Pass the user's content through the moderation function
    moderated_content = content

    # Basic validation to ensure post is not empty
    if moderated_content and moderated_content.strip():
        db = get_db()
        db.execute(
            'INSERT INTO posts (user_id, content, group_id, town_hall_country_code) VALUES (?, ?, ?, ?)',
            (user_id, moderated_content, group_id, town_hall_country_code)
        )
        db.commit()
        flash('Your post was successfully created!', 'success')
    else:
        # This will catch empty posts or posts that were fully censored
        flash('Post cannot be empty or was fully censored.', 'warning')

    if town_hall_country_code:
        return redirect(url_for('town_hall'))
    if group_name:
        return redirect(url_for('group_page', name=group_name))
    elif group_id:
        grp = query_db('SELECT name FROM groups WHERE id = ?', (group_id,), one=True)
        if grp:
            return redirect(url_for('group_page', name=grp['name']))

    # Redirect back to the referrer or main feed
    return redirect(request.referrer or url_for('feed'))
    
    
@app.route('/posts/<int:post_id>/delete', methods=['POST'])
def delete_post(post_id):
    """Handles deleting a post."""
    user_id = session.get('user_id')

    # Block access if user is not logged in
    if not user_id:
        flash('You must be logged in to delete a post.', 'danger')
        return redirect(url_for('login'))

    # Find the post in the database
    post = query_db('SELECT id, user_id, group_id, town_hall_country_code FROM posts WHERE id = ?', (post_id,), one=True)

    # Check if the post exists
    if not post:
        flash('Post not found.', 'danger')
        return redirect(url_for('feed'))
    if not can_access_town_hall_post(user_id, post['town_hall_country_code']):
        abort(404)

    is_author = (post['user_id'] == user_id)
    is_site_admin = (session.get('username') == 'admin')
    is_group_admin = False
    if post['group_id']:
        grp = query_db('SELECT admin_id FROM groups WHERE id = ?', (post['group_id'],), one=True)
        if grp and grp['admin_id'] == user_id:
            is_group_admin = True

    if not (is_author or is_site_admin or is_group_admin):
        # Security check: prevent unauthorized users from deleting posts
        flash('You do not have permission to delete this post.', 'danger')
        return redirect(request.referrer or url_for('feed'))

    # If all checks pass, proceed with deletion
    db = get_db()
    # To maintain database integrity, delete associated records first
    db.execute('DELETE FROM comments WHERE post_id = ?', (post_id,))
    db.execute('DELETE FROM reactions WHERE post_id = ?', (post_id,))
    # Finally, delete the post itself
    db.execute('DELETE FROM posts WHERE id = ?', (post_id,))
    db.commit()

    flash('Your post was successfully deleted.', 'success')
    # Redirect back to the page the user came from, or the feed as a fallback
    return redirect(request.referrer or url_for('feed'))

@app.route('/u/<username>')
def user_profile(username):
    """Displays a user's profile page with moderated bio, posts, and latest comments."""
    
    user_raw = query_db("""SELECT u.*, c.city_name || ', ' || c.country_name AS verified_location
        FROM users u LEFT JOIN cities c ON c.id = u.city_id WHERE u.username = ?""", (username,), one=True)
    if not user_raw:
        abort(404)

    user = dict(user_raw)
    user['location'] = user.get('verified_location')
    moderated_bio, _ = moderate_content(user.get('profile', ''))
    user['profile'] = moderated_bio

    posts_raw = query_db('''
        SELECT p.id, p.content, p.user_id, p.created_at, p.group_id, g.name as group_name
        FROM posts p
        LEFT JOIN groups g ON p.group_id = g.id
        WHERE p.user_id = ? AND p.town_hall_country_code IS NULL
        ORDER BY p.created_at DESC
    ''', (user['id'],))
    posts = []
    for post_raw in posts_raw:
        post = dict(post_raw)
        moderated_post_content, _ = moderate_content(post['content'])
        post['content'] = moderated_post_content
        posts.append(post)

    comments_raw = query_db('''
        SELECT c.id, c.content, c.user_id, c.post_id, c.created_at
        FROM comments c JOIN posts p ON p.id = c.post_id
        WHERE c.user_id = ? AND p.town_hall_country_code IS NULL
        ORDER BY c.created_at DESC LIMIT 100
    ''', (user['id'],))
    comments = []
    for comment_raw in comments_raw:
        comment = dict(comment_raw)
        moderated_comment_content, _ = moderate_content(comment['content'])
        comment['content'] = moderated_comment_content
        comments.append(comment)

    followers_count = query_db('SELECT COUNT(*) as cnt FROM follows WHERE followed_id = ?', (user['id'],), one=True)['cnt']
    following_count = query_db('SELECT COUNT(*) as cnt FROM follows WHERE follower_id = ?', (user['id'],), one=True)['cnt']

    #  NEW: CHECK FOLLOW STATUS 
    is_currently_following = False # Default to False
    current_user_id = session.get('user_id')
    
    # We only need to check if a user is logged in
    if current_user_id:
        follow_relation = query_db(
            'SELECT 1 FROM follows WHERE follower_id = ? AND followed_id = ?',
            (current_user_id, user['id']),
            one=True
        )
        if follow_relation:
            is_currently_following = True
    # --

    return render_template('user_profile.html.j2', 
                           user=user, 
                           posts=posts, 
                           comments=comments, 
                           followers_count=followers_count, 
                           following_count=following_count,
                           is_following=is_currently_following)
    

@app.route('/edit_profile', methods=['GET', 'POST'])
def edit_profile():
    """Allows logged-in users to customize their profile (bio, location, birthdate, bg color, avatar, banner)."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to edit your profile.', 'danger')
        return redirect(url_for('login'))

    user = query_db("""SELECT u.*, c.city_name AS selected_city_name, c.country_name AS selected_country_name,
        c.city_name || ', ' || c.country_name AS verified_location
        FROM users u LEFT JOIN cities c ON c.id = u.city_id WHERE u.id = ?""", (user_id,), one=True)
    if not user:
        flash('User not found.', 'danger')
        return redirect(url_for('feed'))

    user = dict(user)
    user['location'] = user.get('verified_location') or ''

    if request.method == 'POST':
        location_input = request.form.get('location', '').strip()
        city_id_input = request.form.get('city_id', '').strip()
        city = selected_city(city_id_input) if city_id_input else None
        if city_id_input and not city:
            flash('Please select a city from the suggestions.', 'danger')
            user['location'] = location_input
            user['city_id'] = None
            return render_template('edit_profile.html.j2', user=user)
        if location_input and not city:
            flash('Please choose a valid city from the suggestions, or clear the location field.', 'danger')
            user['location'] = location_input
            user['city_id'] = None
            return render_template('edit_profile.html.j2', user=user)
        location = f"{city['city_name']}, {city['country_name']}" if city else None
        city_id = city['id'] if city else None
        user['location'] = location or ''
        user['city_id'] = city_id
        birthdate = request.form.get('birthdate', '').strip()
        profile = request.form.get('profile', '').strip()
        bg_color = request.form.get('bg_color', '').strip()

        # Validate bg_color (allow standard hex color codes)
        if bg_color and not re.match(r'^#(?:[0-9a-fA-F]{3}){1,2}$', bg_color):
            bg_color = user.get('bg_color') or '#f2f2f2'

        profile_picture_name = user.get('profile_picture')
        banner_picture_name = user.get('banner_picture')

        # Handle explicit picture removals
        if request.form.get('remove_profile_picture'):
            if profile_picture_name:
                old_path = os.path.join(app.config['UPLOAD_FOLDER'], profile_picture_name)
                if os.path.exists(old_path):
                    try:
                        os.remove(old_path)
                    except OSError:
                        pass
            profile_picture_name = None

        if request.form.get('remove_banner_picture'):
            if banner_picture_name:
                old_path = os.path.join(app.config['UPLOAD_FOLDER'], banner_picture_name)
                if os.path.exists(old_path):
                    try:
                        os.remove(old_path)
                    except OSError:
                        pass
            banner_picture_name = None

        # Handle Profile Picture Upload
        if 'profile_picture' in request.files:
            file = request.files['profile_picture']
            if file and file.filename != '':
                saved_name = save_uploaded_image(file, 'avatar', user_id)
                if saved_name is False:
                    flash('Invalid image format for profile picture. Allowed formats: png, jpg, jpeg, gif, webp.', 'danger')
                    return render_template('edit_profile.html.j2', user=user)
                elif saved_name:
                    if profile_picture_name:
                        old_path = os.path.join(app.config['UPLOAD_FOLDER'], profile_picture_name)
                        if os.path.exists(old_path):
                            try:
                                os.remove(old_path)
                            except OSError:
                                pass
                    profile_picture_name = saved_name

        # Handle Banner Picture Upload
        if 'banner_picture' in request.files:
            file = request.files['banner_picture']
            if file and file.filename != '':
                saved_name = save_uploaded_image(file, 'banner', user_id)
                if saved_name is False:
                    flash('Invalid image format for banner picture. Allowed formats: png, jpg, jpeg, gif, webp.', 'danger')
                    return render_template('edit_profile.html.j2', user=user)
                elif saved_name:
                    if banner_picture_name:
                        old_path = os.path.join(app.config['UPLOAD_FOLDER'], banner_picture_name)
                        if os.path.exists(old_path):
                            try:
                                os.remove(old_path)
                            except OSError:
                                pass
                    banner_picture_name = saved_name

        db = get_db()
        db.execute('''
            UPDATE users
            SET location = ?, city_id = ?, birthdate = ?, profile = ?, bg_color = ?, profile_picture = ?, banner_picture = ?
            WHERE id = ?
        ''', (location, city_id, birthdate, profile, bg_color, profile_picture_name, banner_picture_name, user_id))
        db.commit()

        flash('Your profile has been successfully updated!', 'success')
        return redirect(url_for('user_profile', username=user['username']))

    return render_template('edit_profile.html.j2', user=user)
    

@app.route('/u/<username>/followers')
def user_followers(username):
    user = query_db('SELECT * FROM users WHERE username = ?', (username,), one=True)
    if not user:
        abort(404)
    followers = query_db('''
        SELECT u.username, u.profile_picture
        FROM follows f
        JOIN users u ON f.follower_id = u.id
        WHERE f.followed_id = ?
    ''', (user['id'],))
    return render_template('user_list.html.j2', user=user, users=followers, title="Followers of")

@app.route('/u/<username>/following')
def user_following(username):
    user = query_db('SELECT * FROM users WHERE username = ?', (username,), one=True)
    if not user:
        abort(404)
    following = query_db('''
        SELECT u.username, u.profile_picture
        FROM follows f
        JOIN users u ON f.followed_id = u.id
        WHERE f.follower_id = ?
    ''', (user['id'],))
    return render_template('user_list.html.j2', user=user, users=following, title="Users followed by")

@app.route('/posts/<int:post_id>')
def post_detail(post_id):
    """Displays a single post and its comments, with content moderation applied."""
    
    post_raw = query_db('''
        SELECT p.id, p.content, p.created_at, p.group_id, p.town_hall_country_code, g.name as group_name,
               u.username, u.id as user_id, u.profile_picture
        FROM posts p
        JOIN users u ON p.user_id = u.id
        LEFT JOIN groups g ON p.group_id = g.id
        WHERE p.id = ?
    ''', (post_id,), one=True)

    if not post_raw:
        abort(404)

    # Town Hall posts are only accessible through the matching country's Town Hall.
    if post_raw['town_hall_country_code']:
        country = user_country(session.get('user_id'))
        if not country or country['country_code'] != post_raw['town_hall_country_code']:
            abort(404)
        return redirect(url_for('town_hall'))

    #  Moderation for the Main Post 
    # Convert the raw database row to a mutable dictionary
    post = dict(post_raw)
    # Unpack the tuple from moderate_content, we only need the moderated content string here
    moderated_post_content, _ = moderate_content(post['content'])
    post['content'] = moderated_post_content

    #  Fetch Reactions (No moderation needed) 
    reactions = query_db('''
        SELECT reaction_type, COUNT(*) as count
        FROM reactions
        WHERE post_id = ?
        GROUP BY reaction_type
    ''', (post_id,))

    #  Fetch and Moderate Comments 
    comments_raw = query_db('SELECT c.id, c.content, c.created_at, u.username, u.id as user_id, u.profile_picture FROM comments c JOIN users u ON c.user_id = u.id WHERE c.post_id = ? ORDER BY c.created_at ASC', (post_id,))
    
    comments = [] # Create a new list for the moderated comments
    for comment_raw in comments_raw:
        comment = dict(comment_raw) # Convert to a dictionary
        # Moderate the content of each comment
        print(comment['content'])
        moderated_comment_content, _ = moderate_content(comment['content'])
        comment['content'] = moderated_comment_content
        comments.append(comment)

    # Pass the moderated data to the template
    return render_template('post_detail.html.j2',
                           post=post,
                           reactions=reactions,
                           comments=comments,
                           can_comment=can_comment_on_post(session.get('user_id'), post['group_id']),
                           reaction_emojis=REACTION_EMOJIS,
                           reaction_types=REACTION_TYPES)

# ----------------- Group Routes -----------------

@app.route('/groups')
def groups_list():
    """Displays the groups overview page with joined groups and all groups."""
    current_user_id = session.get('user_id')
    my_groups = []

    if current_user_id:
        my_groups = query_db('''
            SELECT g.id, g.name, g.description, g.admin_id, g.created_at, g.bg_color,
                   u.username as admin_username, u.profile_picture as admin_profile_picture,
                   (SELECT COUNT(*) FROM group_members WHERE group_id = g.id) as member_count,
                   (SELECT COUNT(*) FROM posts WHERE group_id = g.id) as post_count,
                   1 as is_member
            FROM groups g
            JOIN users u ON g.admin_id = u.id
            JOIN group_members gm ON g.id = gm.group_id
            WHERE gm.user_id = ?
            ORDER BY g.name ASC
        ''', (current_user_id,))

    all_groups = query_db('''
        SELECT g.id, g.name, g.description, g.admin_id, g.created_at, g.bg_color,
               u.username as admin_username, u.profile_picture as admin_profile_picture,
               (SELECT COUNT(*) FROM group_members WHERE group_id = g.id) as member_count,
               (SELECT COUNT(*) FROM posts WHERE group_id = g.id) as post_count,
               CASE WHEN gm.user_id IS NOT NULL THEN 1 ELSE 0 END as is_member
        FROM groups g
        JOIN users u ON g.admin_id = u.id
        LEFT JOIN group_members gm ON g.id = gm.group_id AND gm.user_id = ?
        ORDER BY g.name ASC
    ''', (current_user_id or -1,))

    return render_template('groups.html.j2', my_groups=my_groups, all_groups=all_groups)


@app.route('/groups/create', methods=['POST'])
def create_group():
    """Handles creating a new group."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to create a group.', 'danger')
        return redirect(url_for('login'))

    name = request.form.get('name', '').strip()
    description = request.form.get('description', '').strip()
    bg_color = request.form.get('bg_color', '#f2f2f2').strip()
    hide_members = 1 if request.form.get('hide_members') in ('1', 'on', 'true', 'True') else 0

    if not name:
        flash('Group name cannot be empty.', 'danger')
        return redirect(url_for('groups_list'))

    # Check valid characters (alphanumeric, underscore, hyphen)
    if not re.match(r'^[a-zA-Z0-9_-]{2,50}$', name):
        flash('Group name must be between 2 and 50 characters and contain only letters, numbers, underscores, and hyphens.', 'danger')
        return redirect(url_for('groups_list'))

    # Check if group already exists (case-insensitive)
    existing = query_db('SELECT 1 FROM groups WHERE LOWER(name) = LOWER(?)', (name,), one=True)
    if existing:
        flash(f'A group with the name "{name}" already exists.', 'danger')
        return redirect(url_for('groups_list'))

    if bg_color and not re.match(r'^#(?:[0-9a-fA-F]{3}){1,2}$', bg_color):
        bg_color = '#f2f2f2'

    db = get_db()
    cur = db.execute(
        'INSERT INTO groups (name, description, admin_id, bg_color, hide_members) VALUES (?, ?, ?, ?, ?)',
        (name, description, user_id, bg_color, hide_members)
    )
    group_id = cur.lastrowid
    # Automatically add admin as a member
    db.execute('INSERT INTO group_members (group_id, user_id) VALUES (?, ?)', (group_id, user_id))
    db.commit()

    flash(f'Group "g/{name}" was successfully created!', 'success')
    return redirect(url_for('group_page', name=name))


@app.route('/groups/<name>')
@app.route('/g/<name>')
def group_page(name):
    """Displays a group page with all posts made to that group."""
    group_raw = query_db('''
        SELECT g.*, u.username as admin_username, u.profile_picture as admin_profile_picture
        FROM groups g
        JOIN users u ON g.admin_id = u.id
        WHERE LOWER(g.name) = LOWER(?)
    ''', (name.strip(),), one=True)

    if not group_raw:
        abort(404)

    group = dict(group_raw)
    current_user_id = session.get('user_id')

    # Get member count & post count
    member_count = query_db('SELECT COUNT(*) as count FROM group_members WHERE group_id = ?', (group['id'],), one=True)['count']
    post_count = query_db('SELECT COUNT(*) as count FROM posts WHERE group_id = ?', (group['id'],), one=True)['count']

    # Membership check
    is_member = False
    if current_user_id:
        member_check = query_db('SELECT 1 FROM group_members WHERE group_id = ? AND user_id = ?', (group['id'], current_user_id), one=True)
        if member_check:
            is_member = True

    is_admin = (current_user_id == group['admin_id'])

    # Fetch posts made to this group
    posts_raw = query_db('''
        SELECT p.id, p.content, p.created_at, p.group_id, g.name as group_name,
               u.username, u.id as user_id, u.profile_picture
        FROM posts p
        JOIN users u ON p.user_id = u.id
        JOIN groups g ON p.group_id = g.id
        WHERE p.group_id = ?
        ORDER BY p.created_at DESC
    ''', (group['id'],))

    posts_data = []
    for post in posts_raw:
        followed_poster = False
        if current_user_id and post['user_id'] != current_user_id:
            follow_check = query_db('SELECT 1 FROM follows WHERE follower_id = ? AND followed_id = ?', (current_user_id, post['user_id']), one=True)
            if follow_check:
                followed_poster = True

        user_reaction = None
        if current_user_id:
            reaction_check = query_db('SELECT reaction_type FROM reactions WHERE user_id = ? AND post_id = ?', (current_user_id, post['id']), one=True)
            if reaction_check:
                user_reaction = reaction_check['reaction_type']

        reactions = query_db('SELECT reaction_type, COUNT(*) as count FROM reactions WHERE post_id = ? GROUP BY reaction_type', (post['id'],))
        comments_raw = query_db('SELECT c.id, c.content, c.created_at, u.username, u.id as user_id, u.profile_picture FROM comments c JOIN users u ON c.user_id = u.id WHERE c.post_id = ? ORDER BY c.created_at ASC', (post['id'],))
        post_dict = dict(post)
        post_dict['content'], _ = moderate_content(post_dict['content'])
        comments_moderated = []
        for comment in comments_raw:
            comment_dict = dict(comment)
            comment_dict['content'], _ = moderate_content(comment_dict['content'])
            comments_moderated.append(comment_dict)
        posts_data.append({
            'post': post_dict,
            'reactions': reactions,
            'user_reaction': user_reaction,
            'followed_poster': followed_poster,
            'comments': comments_moderated
        })

    return render_template(
        'group_page.html.j2',
        group=group,
        member_count=member_count,
        post_count=post_count,
        is_member=is_member,
        is_admin=is_admin,
        posts=posts_data,
        reaction_emojis=REACTION_EMOJIS,
        reaction_types=REACTION_TYPES
    )


@app.route('/groups/<name>/edit', methods=['GET', 'POST'])
@app.route('/g/<name>/edit', methods=['GET', 'POST'])
def edit_group(name):
    """Allows the group admin to customize the group (description, color, banner, member list visibility)."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to edit a group.', 'danger')
        return redirect(url_for('login'))

    group_raw = query_db('SELECT * FROM groups WHERE LOWER(name) = LOWER(?)', (name.strip(),), one=True)
    if not group_raw:
        abort(404)
    group = dict(group_raw)

    is_site_admin = (session.get('username') == 'admin')
    if group['admin_id'] != user_id and not is_site_admin:
        flash('Only the group admin can edit this group.', 'danger')
        return redirect(url_for('group_page', name=group['name']))

    if request.method == 'POST':
        description = request.form.get('description', '').strip()
        bg_color = request.form.get('bg_color', '').strip()
        hide_members = 1 if request.form.get('hide_members') in ('1', 'on', 'true', 'True') else 0

        # Validate bg_color (allow standard hex color codes)
        if not re.match(r'^#(?:[0-9a-fA-F]{3}){1,2}$', bg_color):
            bg_color = group.get('bg_color') or '#f2f2f2'

        old_banner = group.get('banner_picture')
        banner_name = old_banner

        if request.form.get('remove_banner_picture'):
            banner_name = None

        file = request.files.get('banner_picture')
        if file and file.filename != '':
            saved_name = save_uploaded_image(file, 'groupbanner', group['id'])
            if saved_name is False:
                flash('Invalid image format for banner picture. Allowed formats: png, jpg, jpeg, gif, webp.', 'danger')
                return render_template('edit_group.html.j2', group=group)
            banner_name = saved_name

        db = get_db()
        db.execute('''
            UPDATE groups
            SET description = ?, bg_color = ?, banner_picture = ?, hide_members = ?
            WHERE id = ?
        ''', (description, bg_color, banner_name, hide_members, group['id']))
        db.commit()

        # Clean up the replaced / removed banner file only after the DB update succeeded
        if old_banner and old_banner != banner_name:
            delete_upload(old_banner)

        flash('Group was successfully updated!', 'success')
        return redirect(url_for('group_page', name=group['name']))

    return render_template('edit_group.html.j2', group=group)


@app.route('/groups/<name>/join', methods=['POST'])
@app.route('/g/<name>/join', methods=['POST'])
def join_group(name):
    """Joins a group."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to join a group.', 'danger')
        return redirect(url_for('login'))

    group = query_db('SELECT id, name FROM groups WHERE LOWER(name) = LOWER(?)', (name.strip(),), one=True)
    if not group:
        abort(404)

    db = get_db()
    db.execute('INSERT OR IGNORE INTO group_members (group_id, user_id) VALUES (?, ?)', (group['id'], user_id))
    db.commit()

    flash(f'You have joined g/{group["name"]}!', 'success')
    return redirect(request.referrer or url_for('group_page', name=group['name']))


@app.route('/groups/<name>/leave', methods=['POST'])
@app.route('/g/<name>/leave', methods=['POST'])
def leave_group(name):
    """Leaves a group."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to leave a group.', 'danger')
        return redirect(url_for('login'))

    group = query_db('SELECT id, name, admin_id FROM groups WHERE LOWER(name) = LOWER(?)', (name.strip(),), one=True)
    if not group:
        abort(404)

    db = get_db()
    db.execute('DELETE FROM group_members WHERE group_id = ? AND user_id = ?', (group['id'], user_id))
    db.commit()

    flash(f'You have left g/{group["name"]}.', 'info')
    return redirect(request.referrer or url_for('group_page', name=group['name']))


@app.route('/groups/<name>/posts/new', methods=['POST'])
@app.route('/g/<name>/posts/new', methods=['POST'])
def add_group_post(name):
    """Creates a new post in a group."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in to create a post.', 'danger')
        return redirect(url_for('login'))

    group = query_db('SELECT id, name FROM groups WHERE LOWER(name) = LOWER(?)', (name.strip(),), one=True)
    if not group:
        abort(404)

    is_member = query_db('SELECT 1 FROM group_members WHERE group_id = ? AND user_id = ?',
                         (group['id'], user_id), one=True)
    if not is_member:
        flash(f'You must be a member of g/{group["name"]} to post in this group.', 'danger')
        return redirect(url_for('group_page', name=group['name']))

    content = request.form.get('content')
    moderated_content = content

    if moderated_content and moderated_content.strip():
        db = get_db()
        db.execute('INSERT INTO posts (user_id, content, group_id) VALUES (?, ?, ?)',
                   (user_id, moderated_content, group['id']))
        db.commit()
        flash(f'Your post was successfully created in g/{group["name"]}!', 'success')
    else:
        flash('Post cannot be empty or was fully censored.', 'warning')

    return redirect(url_for('group_page', name=group['name']))


@app.route('/groups/<name>/members')
@app.route('/g/<name>/members')
def group_members_list(name):
    """Displays the list of members for a group."""
    group_raw = query_db('''
        SELECT g.*, u.username as admin_username, u.profile_picture as admin_profile_picture
        FROM groups g
        JOIN users u ON g.admin_id = u.id
        WHERE LOWER(g.name) = LOWER(?)
    ''', (name.strip(),), one=True)

    if not group_raw:
        abort(404)

    group = dict(group_raw)
    current_user_id = session.get('user_id')
    is_admin = (current_user_id == group['admin_id'] or session.get('username') == 'admin')

    if group.get('hide_members') and not is_admin:
        flash('The member list for this group is hidden by the group administrator.', 'warning')
        return redirect(url_for('group_page', name=group['name']))

    members = query_db('''
        SELECT u.id, u.username, u.profile_picture, gm.joined_at
        FROM group_members gm
        JOIN users u ON gm.user_id = u.id
        WHERE gm.group_id = ?
        ORDER BY (u.id = ?) DESC, gm.joined_at ASC
    ''', (group['id'], group['admin_id']))

    return render_template(
        'group_members.html.j2',
        group=group,
        members=members,
        is_admin=is_admin
    )


@app.route('/groups/<name>/toggle_member_visibility', methods=['POST'])
@app.route('/groups/<name>/toggle_members_visibility', methods=['POST'])
@app.route('/g/<name>/toggle_members_visibility', methods=['POST'])
@app.route('/g/<name>/toggle_member_visibility', methods=['POST'])
def toggle_group_members_visibility(name):
    """Allows group admin to toggle whether member list is visible to non-admins."""
    user_id = session.get('user_id')
    if not user_id:
        flash('You must be logged in as group admin to perform this action.', 'danger')
        return redirect(url_for('login'))

    group = query_db('SELECT id, name, admin_id, hide_members FROM groups WHERE LOWER(name) = LOWER(?)', (name.strip(),), one=True)
    if not group:
        abort(404)

    is_site_admin = (session.get('username') == 'admin')
    if group['admin_id'] != user_id and not is_site_admin:
        flash('Only the group admin can change member list visibility.', 'danger')
        return redirect(url_for('group_page', name=group['name']))

    new_visibility = 0 if group['hide_members'] else 1
    db = get_db()
    db.execute('UPDATE groups SET hide_members = ? WHERE id = ?', (new_visibility, group['id']))
    db.commit()

    if new_visibility:
        flash('Group member list is now hidden from non-admin users.', 'info')
    else:
        flash('Group member list is now visible to everyone.', 'success')

    return redirect(request.referrer or url_for('group_page', name=group['name']))


@app.route('/about')
def about():
    return render_template('about.html.j2')

@app.route('/privacy')
def privacy():
    return render_template('privacy.html.j2')


@app.route('/api/cities')
def search_cities():
    """Search the local city catalogue for the profile selector."""
    query = request.args.get('q', '').strip()
    normalized_query = normalize_place_text(query)
    if len(normalized_query) < 2:
        return jsonify([])

    # Keep matching and limiting in SQLite so only a handful of rows are returned.
    like_query = f"%{query}%"
    prefix_query = f"{query}%"
    rows = query_db("""
        SELECT id, city_name, country_code, country_name
        FROM cities
        WHERE city_name LIKE ? COLLATE NOCASE OR country_name LIKE ? COLLATE NOCASE
        ORDER BY CASE WHEN city_name LIKE ? COLLATE NOCASE THEN 0 ELSE 1 END,
                 city_name COLLATE NOCASE, country_name COLLATE NOCASE
        LIMIT 12
    """, (like_query, like_query, prefix_query))
    return jsonify([{
        'id': row['id'],
        'city_name': row['city_name'],
        'country_code': row['country_code'],
        'country_name': row['country_name'],
        'label': f"{row['city_name']}, {row['country_name']}"
    } for row in rows])


@app.route('/signup', methods=['GET', 'POST'])
def signup():
    if request.method == 'POST':
        username = request.form['username']
        password = request.form['password']
        location_input = request.form.get('location', '').strip()
        city_id_input = request.form.get('city_id', '').strip()
        city = selected_city(city_id_input) if city_id_input else None
        if (city_id_input and not city) or (location_input and not city):
            flash('Please choose a valid city from the suggestions, or clear the location field.', 'danger')
            return render_template('signup.html.j2', location_input=location_input, form_username=username, form_birthdate=request.form.get('birthdate', ''), form_profile=request.form.get('profile', ''))
        location = f"{city['city_name']}, {city['country_name']}" if city else None
        city_id = city['id'] if city else None
        birthdate = request.form.get('birthdate', '')
        profile = request.form.get('profile', '')

        hashed_password = generate_password_hash(password)

        db = get_db()
        cur = db.cursor()
        try:
            cur.execute(
                'INSERT INTO users (username, password, location, city_id, birthdate, profile) VALUES (?, ?, ?, ?, ?, ?)',
                (username, hashed_password, location, city_id, birthdate, profile)
            )
            db.commit()

            # 1. Get the ID of the user we just created.
            new_user_id = cur.lastrowid

            # 2. Add user info to the session cookie.
            session.clear() # Clear any old session data
            session['user_id'] = new_user_id
            session['username'] = username

            # 3. Flash a welcome message and redirect to the feed.
            flash(f'Welcome, {username}! Your account has been created.', 'success')
            return redirect(url_for('feed')) # Redirect to the main feed/dashboard

        except sqlite3.IntegrityError:
            flash('Username already taken. Please choose another one.', 'danger')
        finally:
            cur.close()
            db.close()
            
    return render_template('signup.html.j2')

@app.route('/login', methods=['GET', 'POST'])
def login():
    if request.method == 'POST':
        username = request.form['username']
        password = request.form['password']

        db = get_db()
        user = db.execute('SELECT * FROM users WHERE username = ?', (username,)).fetchone()
        db.close()

        # 1. Check if the user exists.
        # 2. If user exists, use check_password_hash to securely compare the password.
        #    This function handles the salt and prevents timing attacks.
        if user and check_password_hash(user['password'], password):
            # Password is correct!
            session['user_id'] = user['id']
            session['username'] = user['username']
            flash('Logged in successfully.', 'success')
            return redirect(url_for('feed'))
        else:
            # User does not exist or password was incorrect.
            flash('Invalid username or password.', 'danger')
            
    return render_template('login.html.j2')

@app.route('/logout')
def logout():
    session.clear()
    flash('Logged out.', 'info')
    return redirect(url_for('login'))

@app.route('/posts/<int:post_id>/comment', methods=['POST'])
def add_comment(post_id):
    """Handles adding a new comment to a specific post."""
    user_id = session.get('user_id')

    # Block access if user is not logged in
    if not user_id:
        flash('You must be logged in to comment.', 'danger')
        return redirect(url_for('login'))

    # Make sure the post exists and check whether it belongs to a group
    post = query_db('SELECT id, group_id, town_hall_country_code FROM posts WHERE id = ?', (post_id,), one=True)
    if not post:
        abort(404)
    if not can_access_town_hall_post(user_id, post['town_hall_country_code']):
        abort(404)

    # Comments on group posts are restricted to members of that group
    if not can_comment_on_post(user_id, post['group_id']):
        grp = query_db('SELECT name FROM groups WHERE id = ?', (post['group_id'],), one=True)
        flash(f'You must be a member of g/{grp["name"]} to comment on its posts.', 'danger')
        return redirect(url_for('group_page', name=grp['name']))

    # Get content from the submitted form
    content = request.form.get('content')

    # Basic validation to ensure comment is not empty
    if content and content.strip():
        db = get_db()
        db.execute('INSERT INTO comments (post_id, user_id, content) VALUES (?, ?, ?)',
                   (post_id, user_id, content))
        db.commit()
        flash('Your comment was added.', 'success')
    else:
        flash('Comment cannot be empty.', 'warning')

    # Redirect back to the page the user came from (likely the post detail page)
    return redirect(request.referrer or url_for('post_detail', post_id=post_id))

@app.route('/comments/<int:comment_id>/delete', methods=['POST'])
def delete_comment(comment_id):
    """Handles deleting a comment."""
    user_id = session.get('user_id')

    # Block access if user is not logged in
    if not user_id:
        flash('You must be logged in to delete a comment.', 'danger')
        return redirect(url_for('login'))

    # Find the comment and the original post's author ID
    comment = query_db('''
        SELECT c.id, c.user_id, p.user_id as post_author_id, p.town_hall_country_code
        FROM comments c
        JOIN posts p ON c.post_id = p.id
        WHERE c.id = ?
    ''', (comment_id,), one=True)

    # Check if the comment exists
    if not comment:
        flash('Comment not found.', 'danger')
        return redirect(request.referrer or url_for('feed'))
    if not can_access_town_hall_post(user_id, comment['town_hall_country_code']):
        abort(404)

    # Security Check: Allow deletion if the user is the comment's author OR the post's author
    if user_id != comment['user_id'] and user_id != comment['post_author_id']:
        flash('You do not have permission to delete this comment.', 'danger')
        return redirect(request.referrer or url_for('feed'))

    # If all checks pass, proceed with deletion
    db = get_db()
    db.execute('DELETE FROM comments WHERE id = ?', (comment_id,))
    db.commit()

    flash('Comment successfully deleted.', 'success')
    # Redirect back to the page the user came from
    return redirect(request.referrer or url_for('feed'))

@app.route('/react', methods=['POST'])
def add_reaction():
    """Handles adding a new reaction or updating an existing one."""
    user_id = session.get('user_id')

    if not user_id:
        flash("You must be logged in to react.", "danger")
        return redirect(url_for('login'))

    post_id = request.form.get('post_id')
    new_reaction_type = request.form.get('reaction')

    if not post_id or new_reaction_type not in REACTION_TYPES:
        flash("Invalid reaction request.", "warning")
        return redirect(request.referrer or url_for('feed'))

    post = query_db(
        'SELECT town_hall_country_code FROM posts WHERE id = ?',
        (post_id,), one=True
    )
    if not post:
        abort(404)
    if not can_access_town_hall_post(user_id, post['town_hall_country_code']):
        abort(404)

    db = get_db()

    # Step 1: Check if a reaction from this user already exists on this post.
    existing_reaction = query_db('SELECT id FROM reactions WHERE post_id = ? AND user_id = ?',
                                 (post_id, user_id), one=True)

    if existing_reaction:
        # Step 2: If it exists, UPDATE the reaction_type.
        db.execute('UPDATE reactions SET reaction_type = ? WHERE id = ?',
                   (new_reaction_type, existing_reaction['id']))
    else:
        # Step 3: If it does not exist, INSERT a new reaction.
        db.execute('INSERT INTO reactions (post_id, user_id, reaction_type) VALUES (?, ?, ?)',
                   (post_id, user_id, new_reaction_type))

    db.commit()

    return redirect(request.referrer or url_for('feed'))

@app.route('/unreact', methods=['POST'])
def unreact():
    """Handles removing a user's reaction from a post."""
    user_id = session.get('user_id')

    if not user_id:
        flash("You must be logged in to unreact.", "danger")
        return redirect(url_for('login'))

    post_id = request.form.get('post_id')

    if not post_id:
        flash("Invalid unreact request.", "warning")
        return redirect(request.referrer or url_for('feed'))

    post = query_db(
        'SELECT town_hall_country_code FROM posts WHERE id = ?',
        (post_id,), one=True
    )
    if not post:
        abort(404)
    if not can_access_town_hall_post(user_id, post['town_hall_country_code']):
        abort(404)

    db = get_db()

    # Remove the reaction if it exists
    existing_reaction = query_db(
        'SELECT id FROM reactions WHERE post_id = ? AND user_id = ?',
        (post_id, user_id),
        one=True
    )

    if existing_reaction:
        db.execute('DELETE FROM reactions WHERE id = ?', (existing_reaction['id'],))
        db.commit()
        flash("Reaction removed.", "success")
    else:
        flash("No reaction to remove.", "info")

    return redirect(request.referrer or url_for('feed'))


@app.route('/u/<int:user_id>/follow', methods=['POST'])
def follow_user(user_id):
    """Handles the logic for the current user to follow another user."""
    follower_id = session.get('user_id')

    # Security: Ensure user is logged in
    if not follower_id:
        flash("You must be logged in to follow users.", "danger")
        return redirect(url_for('login'))

    # Security: Prevent users from following themselves
    if follower_id == user_id:
        flash("You cannot follow yourself.", "warning")
        return redirect(request.referrer or url_for('feed'))

    # Check if the user to be followed actually exists
    user_to_follow = query_db('SELECT id FROM users WHERE id = ?', (user_id,), one=True)
    if not user_to_follow:
        flash("The user you are trying to follow does not exist.", "danger")
        return redirect(request.referrer or url_for('feed'))
        
    db = get_db()
    try:
        # Insert the follow relationship. The PRIMARY KEY constraint will prevent duplicates if you've set one.
        db.execute('INSERT INTO follows (follower_id, followed_id) VALUES (?, ?)',
                   (follower_id, user_id))
        db.commit()
        username_to_follow = query_db('SELECT username FROM users WHERE id = ?', (user_id,), one=True)['username']
        flash(f"You are now following {username_to_follow}.", "success")
    except sqlite3.IntegrityError:
        flash("You are already following this user.", "info")

    return redirect(request.referrer or url_for('feed'))


@app.route('/u/<int:user_id>/unfollow', methods=['POST'])
def unfollow_user(user_id):
    """Handles the logic for the current user to unfollow another user."""
    follower_id = session.get('user_id')

    # Security: Ensure user is logged in
    if not follower_id:
        flash("You must be logged in to unfollow users.", "danger")
        return redirect(url_for('login'))

    db = get_db()
    cur = db.execute('DELETE FROM follows WHERE follower_id = ? AND followed_id = ?',
               (follower_id, user_id))
    db.commit()

    if cur.rowcount > 0:
        # cur.rowcount tells us if a row was actually deleted
        username_unfollowed = query_db('SELECT username FROM users WHERE id = ?', (user_id,), one=True)['username']
        flash(f"You have unfollowed {username_unfollowed}.", "success")
    else:
        # This case handles if someone tries to unfollow a user they weren't following
        flash("You were not following this user.", "info")

    # Redirect back to the page the user came from
    return redirect(request.referrer or url_for('feed'))

@app.route('/admin')
def admin_dashboard():
    """Displays the admin dashboard with users, posts, and comments, sorted by risk."""

    if session.get('username') != 'admin':
        flash("You do not have permission to access this page.", "danger")
        return redirect(url_for('feed'))

    RISK_LEVELS = { "HIGH": 5, "MEDIUM": 3, "LOW": 1 }
    PAGE_SIZE = 50

    def get_risk_profile(score):
        if score >= RISK_LEVELS["HIGH"]:
            return "HIGH", 3
        elif score >= RISK_LEVELS["MEDIUM"]:
            return "MEDIUM", 2
        elif score >= RISK_LEVELS["LOW"]:
            return "LOW", 1
        return "NONE", 0

    # Get pagination and current tab parameters
    try:
        users_page = int(request.args.get('users_page', 1))
        posts_page = int(request.args.get('posts_page', 1))
        comments_page = int(request.args.get('comments_page', 1))
    except ValueError:
        users_page = 1
        posts_page = 1
        comments_page = 1
    
    current_tab = request.args.get('tab', 'users') # Default to 'users' tab

    users_offset = (users_page - 1) * PAGE_SIZE
    
    # First, get all users to calculate risk, then apply pagination in Python
    # It's more complex to do this efficiently in SQL if risk calc is Python-side
    all_users_raw = query_db('SELECT id, username, profile, created_at FROM users')
    all_users = []
    for user in all_users_raw:
        user_dict = dict(user)
        user_risk_score = user_risk_analysis(user_dict['id'])
        risk_label, risk_sort_key = get_risk_profile(user_risk_score)
        user_dict['risk_label'] = risk_label
        user_dict['risk_sort_key'] = risk_sort_key
        user_dict['risk_score'] = min(5.0, round(user_risk_score, 2))
        all_users.append(user_dict)

    all_users.sort(key=lambda x: x['risk_score'], reverse=True)
    total_users = len(all_users)
    users = all_users[users_offset : users_offset + PAGE_SIZE]
    total_users_pages = (total_users + PAGE_SIZE - 1) // PAGE_SIZE

    # --- Posts Tab Data ---
    posts_offset = (posts_page - 1) * PAGE_SIZE
    total_posts_count = query_db('SELECT COUNT(*) as count FROM posts', one=True)['count']
    total_posts_pages = (total_posts_count + PAGE_SIZE - 1) // PAGE_SIZE

    posts_raw = query_db(f'''
        SELECT p.id, p.content, p.created_at, u.username, u.created_at as user_created_at
        FROM posts p JOIN users u ON p.user_id = u.id
        ORDER BY p.id DESC -- Order by ID for consistent pagination before risk sort
        LIMIT ? OFFSET ?
    ''', (PAGE_SIZE, posts_offset))
    posts = []
    for post in posts_raw:
        post_dict = dict(post)
        _, base_score = moderate_content(post_dict['content'])
        final_score = base_score 
        author_created_dt = post_dict['user_created_at']
        author_age_days = (datetime.utcnow() - author_created_dt).days
        if author_age_days < 7:
            final_score *= 1.5
        risk_label, risk_sort_key = get_risk_profile(final_score)
        post_dict['risk_label'] = risk_label
        post_dict['risk_sort_key'] = risk_sort_key
        post_dict['risk_score'] = round(final_score, 2)
        posts.append(post_dict)

    posts.sort(key=lambda x: x['risk_score'], reverse=True) # Sort after fetching and scoring

    # --- Comments Tab Data ---
    comments_offset = (comments_page - 1) * PAGE_SIZE
    total_comments_count = query_db('SELECT COUNT(*) as count FROM comments', one=True)['count']
    total_comments_pages = (total_comments_count + PAGE_SIZE - 1) // PAGE_SIZE

    comments_raw = query_db(f'''
        SELECT c.id, c.content, c.created_at, u.username, u.created_at as user_created_at
        FROM comments c JOIN users u ON c.user_id = u.id
        ORDER BY c.id DESC -- Order by ID for consistent pagination before risk sort
        LIMIT ? OFFSET ?
    ''', (PAGE_SIZE, comments_offset))
    comments = []
    for comment in comments_raw:
        comment_dict = dict(comment)
        _, score = moderate_content(comment_dict['content'])
        author_created_dt = comment_dict['user_created_at']
        author_age_days = (datetime.utcnow() - author_created_dt).days
        if author_age_days < 7:
            score *= 1.5
        risk_label, risk_sort_key = get_risk_profile(score)
        comment_dict['risk_label'] = risk_label
        comment_dict['risk_sort_key'] = risk_sort_key
        comment_dict['risk_score'] = round(score, 2)
        comments.append(comment_dict)

    comments.sort(key=lambda x: x['risk_score'], reverse=True) # Sort after fetching and scoring


    return render_template('admin.html.j2', 
                           users=users, 
                           posts=posts, 
                           comments=comments,
                           
                           # Pagination for Users
                           users_page=users_page,
                           total_users_pages=total_users_pages,
                           users_has_next=(users_page < total_users_pages),
                           users_has_prev=(users_page > 1),

                           # Pagination for Posts
                           posts_page=posts_page,
                           total_posts_pages=total_posts_pages,
                           posts_has_next=(posts_page < total_posts_pages),
                           posts_has_prev=(posts_page > 1),

                           # Pagination for Comments
                           comments_page=comments_page,
                           total_comments_pages=total_comments_pages,
                           comments_has_next=(comments_page < total_comments_pages),
                           comments_has_prev=(comments_page > 1),

                           current_tab=current_tab,
                           PAGE_SIZE=PAGE_SIZE)



@app.route('/admin/delete/user/<int:user_id>', methods=['POST'])
def admin_delete_user(user_id):
    if session.get('username') != 'admin':
        flash("You do not have permission to perform this action.", "danger")
        return redirect(url_for('feed'))
        
    if user_id == session.get('user_id'):
        flash('You cannot delete your own account from the admin panel.', 'danger')
        return redirect(url_for('admin_dashboard'))
    
    db = get_db()
    db.execute('DELETE FROM users WHERE id = ?', (user_id,))
    db.commit()
    flash(f'User {user_id} and all their content has been deleted.', 'success')
    return redirect(url_for('admin_dashboard'))


@app.route('/admin/delete/post/<int:post_id>', methods=['POST'])
def admin_delete_post(post_id):
    if session.get('username') != 'admin':
        flash("You do not have permission to perform this action.", "danger")
        return redirect(url_for('feed'))

    db = get_db()
    db.execute('DELETE FROM comments WHERE post_id = ?', (post_id,))
    db.execute('DELETE FROM reactions WHERE post_id = ?', (post_id,))
    db.execute('DELETE FROM posts WHERE id = ?', (post_id,))
    db.commit()
    flash(f'Post {post_id} has been deleted.', 'success')
    return redirect(url_for('admin_dashboard'))


@app.route('/admin/delete/comment/<int:comment_id>', methods=['POST'])
def admin_delete_comment(comment_id):
    if session.get('username') != 'admin':
        flash("You do not have permission to perform this action.", "danger")
        return redirect(url_for('feed'))

    db = get_db()
    db.execute('DELETE FROM comments WHERE id = ?', (comment_id,))
    db.commit()
    flash(f'Comment {comment_id} has been deleted.', 'success')
    return redirect(url_for('admin_dashboard'))

@app.route('/rules')
def rules():
    return render_template('rules.html.j2')

@app.template_global()
def loop_color(user_id):
    # Generate a pastel color based on user_id hash
    h = hashlib.md5(str(user_id).encode()).hexdigest()
    r = int(h[0:2], 16)
    g = int(h[2:4], 16)
    b = int(h[4:6], 16)
    return f'rgb({r % 128 + 80}, {g % 128 + 80}, {b % 128 + 80})'


# ----- Functions to be implemented are below
# Coding Assignment #2

# Assignment 2.2
def user_risk_analysis(user_id):
    """
    Args:
        user_id: The ID of the user on which we perform risk analysis.

    Returns:
        A float number score showing the risk associated with this user. There are no strict rules or bounds to this score, other than that a score of less than 1.0 means no risk, 1.0 to 3.0 is low risk, 3.0 to 5.0 is medium risk and above 5.0 is high risk. (An upper bound of 5.0 is applied to this score elsewhere in the codebase) 
        
        You will be able to check the scores by logging in with the administrator account:
            username: admin
            password: admin
        Then, navigate to the /admin endpoint. (http://localhost:8080/admin)
    """
    
    score = 0

    return score;

    
# Assignment 2.1
def moderate_content(content):
    """
    Args
        content: the text content of a post or comment to be moderated.
        
    Returns: 
        A tuple containing the moderated content (string) and a severity score (float). There are no strict rules or bounds to the severity score, other than that a score of less than 1.0 means no risk, 1.0 to 3.0 is low risk, 3.0 to 5.0 is medium risk and above 5.0 is high risk.
    
    This function moderates a string of content and calculates a severity score based on
    rules loaded from the 'censorship.dat' file. These are already loaded as TIER1_WORDS, TIER2_PHRASES and TIER3_WORDS. Tier 1 corresponds to strong profanity, Tier 2 to scam/spam phrases and Tier 3 to mild profanity.
    
    You will be able to check the scores by logging in with the administrator account:
            username: admin
            password: admin
    Then, navigate to the /admin endpoint. (http://localhost:8080/admin)
    """

    moderated_content = content
    score = 0
    
    return moderated_content, score

# Coding Assignment #3
# Assignment 3.1
def recommend(user_id, filter_following):
    """
    Args:
        user_id: The ID of the current user.
        filter_following: Boolean, True if we only want to see recommendations from followed users.

    Returns:
        A list of 5 recommended posts, in reverse-chronological order.

    To test whether your recommendation algorithm works, let's pretend we like the DIY topic. Here are some users that often post DIY comment and a few example posts. Make sure your account did not engage with anything else. You should test your algorithm with these and see if your recommendation algorithm picks up on your interest in DIY and starts showing related content.
    
    Users: @starboy99, @DancingDolphin, @blogger_bob
    Posts: 1810, 1875, 1880, 2113
    
    Materials: 
    - https://www.nvidia.com/en-us/glossary/recommendation-system/
    - http://www.configworks.com/mz/handout_recsys_sac2010.pdf
    - https://www.researchgate.net/publication/227268858_Recommender_Systems_Handbook
    """

    recommended_posts = {} 

    return recommended_posts;

if __name__ == '__main__':
    app.run(debug=True, port=8080)


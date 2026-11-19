#!/usr/bin/env python3
import glob
import hashlib
import json
import math
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

GAP_MAX = 30 * 60_000
KEEP_FULL = 7 * 86_400_000
LAUNCH_MAX = 8 * 86_400
ANCHOR_MAX = 1_800
MIN_GAP = 300
VH_MAX = 1_500
VH_RETIRED = 80
VH_VIDEOS = 300
BACKFILL_MAX = 86_400_000


def env(name, default=''):
    return (os.environ.get(name) or default).strip()


API = env('YT_API_BASE', 'https://www.googleapis.com/youtube/v3/')
KEY = env('YT_API_KEY')
CHANNELS = env('CHANNELS') or env('CHANNEL')
NOW = int(env('RECORDER_NOW_MS') or time.time() * 1000)
STUDIO_DIR = env('STUDIO_DIR', 'studio')
SEED_DIR = env('SEED_DIR', '.')
try:
    TZ = ZoneInfo(env('TZ_NAME', 'America/New_York'))
except (ZoneInfoNotFoundError, ValueError):
    sys.exit(f"TZ_NAME {env('TZ_NAME')!r} isn't a time zone name like America/New_York.")


class ApiError(Exception):
    def __init__(self, code, body):
        super().__init__(f'{code}: {body[:400]}')
        self.code = code


class NotFound(Exception):
    pass


def api(path, **params):
    params['key'] = KEY
    url = API + path + '?' + urllib.parse.urlencode(params)
    try:
        with urllib.request.urlopen(url, timeout=30) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        raise ApiError(e.code, e.read().decode('utf-8', 'replace')) from None


def num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and math.isfinite(x)


def norm(x):
    return re.sub(r'[^a-z0-9]', '', (x or '').lower())


def reading(x, loose=False):
    if isinstance(x, list) and len(x) == 2 and num(x[0]) and (num(x[1]) or (loose and x[1] is None)):
        return [int(x[0]), x[1]]
    return None


def channel_query(raw):
    m = re.search(r'(?:^|/channel/)(UC[\w-]{22})(?=$|[/?#])', raw)
    if m:
        return {'id': m.group(1)}
    m = re.search(r'youtube\.com/@([^/?#\s]+)', raw, re.I)
    handle = urllib.parse.unquote(m.group(1)) if m else raw.lstrip('@')
    return {'forHandle': '@' + handle}


def seconds(iso):
    m = re.fullmatch(r'P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?', iso or '')
    if not m:
        return None
    d, h, mi, s = (int(x or 0) for x in m.groups())
    return d * 86_400 + h * 3_600 + mi * 60 + s


def iso_ms(text):
    return int(datetime.fromisoformat(text.replace('Z', '+00:00')).timestamp() * 1000)


def hour_floor(ms):
    dt = datetime.fromtimestamp(ms / 1000, TZ).replace(minute=0, second=0, microsecond=0)
    return int(dt.timestamp() * 1000)


def spread(buckets, t0, v0, t1, v1):
    dt, dv = t1 - t0, v1 - v0
    if dt <= 0 or dv == 0:
        return
    slot = 2 if dt > GAP_MAX else 1
    a = t0
    while a < t1:
        hs = hour_floor(a)
        b = min(t1, hs + 3_600_000)
        bucket = buckets.setdefault(hs, [hs, 0.0, 0.0])
        bucket[slot] += dv * (b - a) / dt
        a = b


def share(b):
    return abs(b[1]) / ((abs(b[1]) + abs(b[2])) or 1)


def record_video(pts, age, views):
    if not pts and age <= ANCHOR_MAX:
        pts.append([0, 0])
    if pts and age <= pts[-1][0]:
        if age == pts[-1][0]:
            pts[-1] = [age, views]
        return pts
    if len(pts) >= 2 and age - pts[-2][0] < max(MIN_GAP, age / 40):
        pts[-1] = [age, views]
    else:
        pts.append([age, views])
    if len(pts) > VH_MAX:
        half = len(pts) // 2
        pts = [p for i, p in enumerate(pts[:half]) if i == 0 or i % 2 == 0] + pts[half:]
    return pts


def prepend(H, pts):
    first = H['first']
    pts = sorted(p for p in pts if first is None or p[0] < first[0])
    if not pts:
        return
    if first is not None:
        pts.append(first)
    for a, b in zip(pts, pts[1:]):
        spread(H['b'], a[0], a[1], b[0], b[1])
    H['first'] = list(pts[0])
    if H['last'] is None:
        H['last'] = list(pts[-1])


def track_hours(H, pts, views, pub):
    if H['first'] is None and pub and pub < min([p[0] for p in pts] + [NOW]) <= pub + BACKFILL_MAX:
        pts = [[pub, 0]] + pts
    prepend(H, pts)
    last = H['last']
    if last is None or NOW > last[0]:
        if last is not None:
            spread(H['b'], last[0], last[1], NOW, views)
        H['last'] = [NOW, views]
    if H['first'] is None:
        H['first'] = [NOW, views]


def retire(pts):
    if len(pts) <= VH_RETIRED:
        return pts
    out = [pts[0]]
    for p in pts[1:-1]:
        if p[0] >= max(out[-1][0] * 1.08, out[-1][0] + MIN_GAP):
            out.append(p)
    out.append(pts[-1])
    return out


def thin(samples):
    cutoff = NOW - KEEP_FULL
    by_hour = {}
    for s in samples:
        if s[0] < cutoff:
            by_hour[hour_floor(s[0])] = s
    return sorted(by_hour.values()) + [s for s in samples if s[0] >= cutoff]


def load(path):
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return {}
    with open(path, encoding='utf-8') as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError(f'{path} is not a JSON object; refusing to overwrite it.')
    return data


def write(path, data):
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(data, f, separators=(',', ':'))
    os.replace(tmp, path)


def load_state(data):
    hourly = {}
    for key in ('views', 'subs'):
        src = (data.get('hourly') or {}).get(key) or {}
        buckets = {}
        for b in src.get('buckets') or []:
            if isinstance(b, list) and len(b) >= 3 and all(num(x) for x in b[:3]):
                buckets[int(b[0])] = [int(b[0]), float(b[1]), float(b[2])]
        hourly[key] = {'first': reading(src.get('first'), True), 'last': reading(src.get('last')), 'buckets': buckets}
    samples = []
    for s in data.get('samples') or []:
        if isinstance(s, list) and len(s) >= 2 and num(s[0]) and num(s[1]):
            rest = (list(s[2:5]) + [None, None, None])[:3]
            samples.append([int(s[0]), s[1]] + [x if num(x) else None for x in rest])
    vhour = {}
    src_all = data.get('vhour')
    for vid, src in (src_all if isinstance(src_all, dict) else {}).items():
        if not isinstance(src, dict):
            continue
        first, last = reading(src.get('first')), reading(src.get('last'))
        if not first or not last:
            continue
        b = {}
        for x in src.get('b') or []:
            if isinstance(x, list) and len(x) >= 3 and all(num(y) for y in x[:3]):
                b[int(x[0])] = [int(x[0]), float(x[1]), float(x[2])]
        vhour[vid] = {'first': first, 'last': last, 'b': b}
    return {
        'samples': samples,
        'hourly': hourly,
        'vhour': vhour,
        'vh': {k: v for k, v in (data.get('vh') or {}).items() if isinstance(v, list)},
        'seeds': [x for x in data.get('seeds') or [] if isinstance(x, str)],
        'seed_studio': {int(x[0]): x[1] for x in data.get('seedStudio') or [] if isinstance(x, list) and len(x) == 2 and num(x[0]) and num(x[1])},
    }


def studio_hours(names):
    out = {}
    current = hour_floor(NOW)
    if not os.path.isdir(STUDIO_DIR):
        return out
    for folder in sorted(os.listdir(STUDIO_DIR)):
        full = os.path.join(STUDIO_DIR, folder)
        if not os.path.isdir(full) or norm(folder) not in names:
            continue
        for path in sorted(glob.glob(os.path.join(full, '**', '*.csv'), recursive=True)):
            with open(path, encoding='utf-8-sig') as f:
                for line in f:
                    m = re.match(r'\s*(\d{4})-(\d{1,2})-(\d{1,2})[ T](\d{1,2})(?::\d{2})?\s*[,;\t]\s*([\d,]+)\s*$', line)
                    if not m:
                        continue
                    y, mo, d, h = (int(x) for x in m.groups()[:4])
                    hs = int(datetime(y, mo, d, h, tzinfo=TZ).timestamp() * 1000)
                    if hs < current:
                        out[hs] = int(m.group(5).replace(',', ''))
    return out


def load_seeds():
    out = {}
    paths = glob.glob(os.path.join(SEED_DIR, 'seed*.json')) + glob.glob(os.path.join(SEED_DIR, 'seeds', '**', '*.json'), recursive=True)
    for path in sorted(set(paths)):
        with open(path, 'rb') as f:
            raw = f.read()
        try:
            seed = json.loads(raw.decode('utf-8-sig'))
        except ValueError:
            print(f'Skipping {path}: it is not valid JSON.')
            continue
        if not isinstance(seed, dict) or not isinstance(seed.get('channelId'), str):
            print(f'Skipping {path}: it is not a history export from the page.')
            continue
        out.setdefault(seed['channelId'], []).append((hashlib.sha256(raw).hexdigest()[:16], seed, path))
    return out


def merge_hourly(H, sh, studio):
    sb = {}
    for b in sh.get('buckets') or []:
        if not (isinstance(b, list) and len(b) >= 3 and all(num(x) for x in b[:3])):
            continue
        hs = hour_floor(int(b[0]))
        cur = sb.setdefault(hs, [hs, 0.0, 0.0])
        cur[1] += float(b[1])
        cur[2] += float(b[2])
        if studio is not None and len(b) > 3 and num(b[3]):
            studio[hs] = b[3]
    s_last = reading(sh.get('last'))
    active = [hs for hs, b in sb.items() if b[1] or b[2]]
    if not active and not s_last:
        return
    s_first = min(active) if active else hour_floor(s_last[0])
    mine, first, last = H['buckets'], H['first'], H['last']
    if last is None:
        mine.update({hs: list(b) for hs, b in sb.items()})
        H['last'] = s_last
    elif s_last and first and first[1] is not None and s_last[0] <= first[0]:
        for hs, b in sb.items():
            cur = mine.setdefault(hs, [hs, 0.0, 0.0])
            cur[1] += b[1]
            cur[2] += b[2]
        spread(mine, s_last[0], s_last[1], first[0], first[1])
    else:
        edges = {s_first} | {hour_floor(r[0]) for r in (first, last, s_last) if r}
        for hs, b in sb.items():
            a = mine.get(hs)
            if a is None or (abs(b[1] + b[2]) > abs(a[1] + a[2]) if hs in edges else share(b) > share(a)):
                mine[hs] = list(b)
        if s_last and s_last[0] > last[0]:
            H['last'] = s_last
    if first is None or s_first < first[0]:
        H['first'] = [s_first, None]


def merge_seed(state, mark, seed, path):
    if mark in state['seeds']:
        return
    state['seeds'].append(mark)
    have = {s[0] for s in state['samples']}
    for p in seed.get('hist') or []:
        if isinstance(p, list) and len(p) >= 2 and num(p[0]) and num(p[1]) and int(p[0]) not in have:
            state['samples'].append([int(p[0]), p[1], None, None, None])
    state['samples'].sort(key=lambda s: s[0])
    for key in ('views', 'subs'):
        merge_hourly(state['hourly'][key], (seed.get('hourly') or {}).get(key) or {}, state['seed_studio'] if key == 'views' else None)
    for vid, pts in (seed.get('vh') or {}).items():
        if not isinstance(pts, list):
            continue
        merged = {p[0]: p for p in state['vh'].get(vid, [])}
        for p in pts:
            if isinstance(p, list) and len(p) == 2 and num(p[0]) and num(p[1]):
                merged.setdefault(p[0], [p[0], p[1]])
        state['vh'][vid] = sorted(merged.values())
    print(f'Merged {path} into the history.')


def fetch_channel(query):
    r = api('channels', part='snippet,contentDetails,statistics', **channel_query(query))
    items = r.get('items') or []
    if not items:
        raise NotFound('no channel with that @handle or ID')
    return items[0]


def fetch_uploads(playlist):
    ids, token = [], None
    while True:
        params = {'part': 'contentDetails', 'playlistId': playlist, 'maxResults': 50}
        if token:
            params['pageToken'] = token
        try:
            page = api('playlistItems', **params)
        except ApiError as e:
            if e.code == 404:
                return []
            raise
        ids += [it['contentDetails']['videoId'] for it in page.get('items', []) if (it.get('contentDetails') or {}).get('videoId')]
        token = page.get('nextPageToken')
        if not token:
            return list(dict.fromkeys(ids))


def record_channel(query, store, seeds):
    c = fetch_channel(query)
    sn, st = c.get('snippet') or {}, c.get('statistics') or {}
    uploads = ((c.get('contentDetails') or {}).get('relatedPlaylists') or {}).get('uploads') or 'UU' + c['id'][2:]
    ids = fetch_uploads(uploads)
    videos = []
    for i in range(0, len(ids), 50):
        videos += api('videos', part='snippet,statistics,contentDetails', id=','.join(ids[i:i + 50])).get('items', [])

    path = os.path.join(store, 'data', c['id'] + '.json')
    state = load_state(load(path))
    for mark, seed, seed_path in seeds.get(c['id'], []):
        merge_seed(state, mark, seed, seed_path)

    rows, total, likes, comments = [], 0, 0, 0
    published = {}
    for it in videos:
        s, vs = it.get('statistics') or {}, it.get('snippet') or {}
        views = int(s.get('viewCount', 0))
        pub = iso_ms(vs['publishedAt']) if vs.get('publishedAt') else 0
        dur = seconds((it.get('contentDetails') or {}).get('duration'))
        th = vs.get('thumbnails') or {}
        thumb = (th.get('medium') or th.get('default') or th.get('high') or {}).get('url', '')
        like = int(s['likeCount']) if 'likeCount' in s else None
        comment = int(s['commentCount']) if 'commentCount' in s else None
        rows.append([it['id'], vs.get('title') or it['id'], thumb, pub, int(dur is not None and dur <= 180), views, like, comment])
        total += views
        likes += like or 0
        comments += comment or 0
        published[it['id']] = pub
        if pub:
            age = max(0, round((NOW - pub) / 1000))
            if age <= LAUNCH_MAX:
                state['vh'][it['id']] = record_video(state['vh'].get(it['id'], []), age, views)
        H = state['vhour'].setdefault(it['id'], {'first': None, 'last': None, 'b': {}})
        pts = state['vh'].get(it['id']) if pub else None
        track_hours(H, [[pub + int(p[0]) * 1000, p[1]] for p in pts or [] if isinstance(p, list) and len(p) >= 2 and num(p[0]) and num(p[1])], views, pub)
    subs = None if st.get('hiddenSubscriberCount') else (int(st['subscriberCount']) if 'subscriberCount' in st else None)

    for key, value in (('views', total), ('subs', subs)):
        H = state['hourly'][key]
        if value is None:
            continue
        if H['last'] and NOW > H['last'][0]:
            spread(H['buckets'], H['last'][0], H['last'][1], NOW, value)
        if not H['last'] or NOW > H['last'][0]:
            H['last'] = [NOW, value]
        if H['first'] is None:
            H['first'] = [NOW, value]

    samples = state['samples']
    if not samples or NOW > samples[-1][0]:
        samples.append([NOW, total, subs, likes, comments])
    samples = thin(samples)

    vh = {}
    keep = sorted(state['vh'], key=lambda v: published.get(v, 0), reverse=True)[:VH_VIDEOS]
    for vid in keep:
        pts = state['vh'][vid]
        age = (NOW - published[vid]) / 1000 if published.get(vid) else LAUNCH_MAX + 1
        vh[vid] = retire(pts) if age > LAUNCH_MAX else pts

    vhour = {}
    for vid in sorted(published, key=lambda v: published[v], reverse=True)[:VH_VIDEOS]:
        H = state['vhour'].get(vid)
        if H and H['last']:
            b = [[hs, round(x[1], 2), round(x[2], 2)] for hs, x in sorted(H['b'].items())]
            vhour[vid] = {'first': H['first'], 'last': H['last'], 'b': [x for x in b if x[1] or x[2]]}

    handle = sn.get('customUrl') or ''
    names ={norm(x) for x in (c['id'], sn.get('title'), handle, channel_query(query).get('forHandle'))} - {''}
    studio = dict(state['seed_studio'])
    studio.update(studio_hours(names))
    round2 = lambda x: round(x, 2)
    title = sn.get('title') or c['id']
    avatar = ((sn.get('thumbnails') or {}).get('default') or {}).get('url', '')
    write(path, {
        'v': 1,
        'tz': str(TZ),
        'updated': NOW,
        'channel': {'id': c['id'], 'title': title, 'avatar': avatar, 'handle': handle, 'uploads': uploads},
        'latest': {'t': NOW, 'total': total, 'subs': subs, 'hiddenSubs': bool(st.get('hiddenSubscriberCount')),
                   'statTotal': int(st.get('viewCount', 0)), 'likes': likes, 'comments': comments, 'videos': rows},
        'samples': samples,
        'hourly': {k: {'first': H['first'], 'last': H['last'],
                       'buckets': [[b[0], round2(b[1]), round2(b[2])] for _, b in sorted(H['buckets'].items())]}
                   for k, H in state['hourly'].items()},
        'studio': sorted([hs, v] for hs, v in studio.items()),
        'seedStudio': sorted([hs, v] for hs, v in state['seed_studio'].items()),
        'seeds': state['seeds'],
        'vh': vh,
        'vhour': vhour,
    })
    print(f'{title}: {total:,} views, {subs if subs is not None else "hidden"} subscribers, {len(rows)} uploads.')
    return {'id': c['id'], 'title': title, 'avatar': avatar, 'handle': handle, 'q': query, 'updated': NOW}


def main():
    if len(sys.argv) != 2:
        sys.exit('usage: record.py path/to/store')
    queries = list(dict.fromkeys(q for q in re.split(r'[\s,]+', CHANNELS) if q))
    if not KEY or not queries:
        sys.exit('Add the YT_API_KEY secret and the CHANNELS variable in the repo settings.')
    store = sys.argv[1]
    index_path = os.path.join(store, 'channels.json')
    try:
        previous = {c.get('q'): c for c in (load(index_path).get('channels') or []) if isinstance(c, dict) and isinstance(c.get('id'), str)}
    except (ValueError, OSError) as e:
        sys.exit(f"Couldn't read {index_path}: {e}")
    seeds = load_seeds()
    entries, failed = [], 0
    for q in queries:
        try:
            entries.append(record_channel(q, store, seeds))
        except (ApiError, NotFound, ValueError, OSError) as e:
            failed += 1
            print(f'::error::{q}: {e}')
            if q in previous:
                entries.append(previous[q])
    if failed == len(queries):
        sys.exit('No channel could be recorded this run, so nothing was changed.')
    seen, channels = set(), []
    for e in entries:
        if e['id'] not in seen:
            seen.add(e['id'])
            channels.append(e)
    write(index_path, {'v': 1, 'updated': NOW, 'channels': channels})


if __name__ == '__main__':
    main()

import sys
import os
import json
import secrets
import base64
import fnmatch
import tempfile
import shutil
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives import hashes

_M = bytes([0xA7, 0x3C, 0x91, 0xF2, 0x08, 0xDE, 0x55, 0x1B])
_META_INFO = b'\x9f\x1aVAF-META\x00\x01'
_FILE_INFO = b'\xa3\x7eVAF-FILE\x00\x02'
_HDR_AAD = bytes([0x11, 0x9C, 0x4B, 0xE7, 0x02, 0x88, 0xAF, 0x3D])
_SCRYPT_N = 1 << 17
_SCRYPT_R = 8
_SCRYPT_P = 1
_MIN_BUCKET = 256
_META_BLOCK = 512
_CHUNK = 65536
_TAG = 16
_MAX_META = 64 * 1024 * 1024
_MAX_FILE = 1 << 40
_MAX_ENTRIES = 1 << 20


def _mk(pw, salt):
    return Scrypt(salt, 32, _SCRYPT_N, _SCRYPT_R, _SCRYPT_P).derive(pw)


def _sk(mk, info):
    return HKDF(hashes.SHA512(), 32, None, info).derive(mk)


def _newpassword():
    return base64.urlsafe_b64encode(secrets.token_bytes(32)).decode().rstrip('=')


def _bucket(n, base=_MIN_BUCKET):
    if n <= base:
        return base
    b = base
    while b < n:
        b <<= 1
    return b


def _ct_len(padded_len):
    if padded_len <= _CHUNK:
        return padded_len + _TAG
    return padded_len + _TAG * (padded_len // _CHUNK)


def _chunk_plan(padded_len):
    if padded_len <= _CHUNK:
        return 1, padded_len
    return padded_len // _CHUNK, _CHUNK


def _file_key(mk, name, sec, salt):
    info = _FILE_INFO + json.dumps([sec, name], separators=(',', ':')).encode('utf-8') + b'\x00' + salt
    return _sk(mk, info)


def _padmeta(data):
    n = len(data) + 4
    min_target = max(n + _TAG, _META_BLOCK)
    target = _bucket(min_target, _META_BLOCK)
    padded_pt_len = target - _TAG
    return len(data).to_bytes(4, 'big') + data + secrets.token_bytes(padded_pt_len - n)


def _check_part(p):
    if not isinstance(p, str) or p in ('', '.', '..'):
        raise SystemExit('unsafe path component: %r' % (p,))
    for c in '/\\\0':
        if c in p:
            raise SystemExit('unsafe path component: %r' % (p,))
    if os.name == 'nt' and ':' in p:
        raise SystemExit('unsafe path component: %r' % (p,))
    return p


def _entry_path(sec, name):
    if sec:
        return '/'.join(sec) + '/' + name
    return name


def _parse_path(s):
    parts = [p for p in s.replace('\\', '/').split('/') if p]
    if not parts:
        raise SystemExit('empty path')
    for p in parts:
        _check_part(p)
    return parts[:-1], parts[-1]


def _safe_target(outdir, sec, name):
    base = os.path.realpath(outdir)
    parts = [_check_part(p) for p in sec] + [_check_part(name)]
    target = os.path.realpath(os.path.join(base, *parts))
    try:
        if os.path.commonpath([base, target]) != base:
            raise SystemExit('path escapes output dir')
    except ValueError:
        raise SystemExit('path escapes output dir')
    return target


def _padded_chunks(plaintext_iter, real_size, padded_len):
    n, sz = _chunk_plan(padded_len)
    it = iter(plaintext_iter)
    buf = bytearray()
    got = 0
    for _ in range(n):
        while len(buf) < sz and got < real_size:
            piece = next(it, None)
            if piece is None:
                raise SystemExit('file shrank while packing')
            got += len(piece)
            if got > real_size:
                raise SystemExit('file grew while packing')
            buf += piece
        if len(buf) < sz:
            buf += secrets.token_bytes(sz - len(buf))
        yield bytes(buf[:sz])
        del buf[:sz]
    if next(it, None) is not None:
        raise SystemExit('file grew while packing')


def _iter_file_plain(path):
    with open(path, 'rb') as f:
        while True:
            b = f.read(_CHUNK)
            if not b:
                return
            yield b


def _write_file_stream(out_f, key, salt, prefix, plaintext_iter, real_size):
    padded_len = _bucket(real_size)
    aes = AESGCM(key)
    for idx, pt in enumerate(_padded_chunks(plaintext_iter, real_size, padded_len)):
        idx_b = idx.to_bytes(8, 'big')
        nonce = prefix + idx_b
        aad = _HDR_AAD + salt + prefix + idx_b
        out_f.write(aes.encrypt(nonce, pt, aad))


def _iter_vaf_plain(vaf_path, blob_start, old_salt, mk, entry):
    key = _file_key(mk, entry['n'], entry.get('sec', []), old_salt)
    prefix = bytes.fromhex(entry['p'])
    real_size = entry['s']
    padded_len = _bucket(real_size)
    n, sz = _chunk_plan(padded_len)
    aes = AESGCM(key)
    with open(vaf_path, 'rb') as f:
        f.seek(blob_start + entry['o'])
        real_remaining = real_size
        for idx in range(n):
            enc_len = sz + _TAG
            buf = f.read(enc_len)
            if len(buf) != enc_len:
                raise SystemExit('truncated vaf')
            idx_b = idx.to_bytes(8, 'big')
            nonce = prefix + idx_b
            aad = _HDR_AAD + old_salt + prefix + idx_b
            try:
                pt = aes.decrypt(nonce, buf, aad)
            except Exception:
                raise SystemExit('authentication failed')
            if real_remaining <= 0:
                continue
            take = min(len(pt), real_remaining)
            yield pt[:take]
            real_remaining -= take


def _read_header_and_meta(path, pw):
    try:
        total = os.path.getsize(path)
    except OSError:
        raise SystemExit('cannot stat vaf file')
    with open(path, 'rb') as f:
        magic = f.read(8)
        if len(magic) != 8 or magic != _M:
            raise SystemExit('invalid vaf file')
        salt = f.read(32)
        if len(salt) != 32:
            raise SystemExit('invalid vaf file')
        mlb = f.read(4)
        if len(mlb) != 4:
            raise SystemExit('invalid vaf file')
        ml = int.from_bytes(mlb, 'big')
        if ml > _MAX_META or ml > total - 56:
            raise SystemExit('invalid vaf file')
        mn = f.read(12)
        if len(mn) != 12:
            raise SystemExit('invalid vaf file')
        mct = f.read(ml)
        if len(mct) != ml:
            raise SystemExit('invalid vaf file')
        blob_start = f.tell()
    mk = _mk(pw.encode('utf-8'), salt)
    fmk = _sk(mk, _META_INFO)
    try:
        mp = AESGCM(fmk).decrypt(mn, mct, _HDR_AAD + _M + salt)
    except Exception:
        raise SystemExit('authentication failed')
    if len(mp) < 4:
        raise SystemExit('corrupted meta')
    plen = int.from_bytes(mp[:4], 'big')
    if plen > len(mp) - 4:
        raise SystemExit('corrupted meta')
    try:
        meta = json.loads(mp[4:4 + plen])
    except Exception:
        raise SystemExit('corrupted meta')
    if not isinstance(meta, dict) or not isinstance(meta.get('files'), list):
        raise SystemExit('corrupted meta')
    if len(meta['files']) > _MAX_ENTRIES:
        raise SystemExit('too many entries')
    for e in meta['files']:
        if not isinstance(e, dict):
            raise SystemExit('corrupted entry')
        name = e.get('n')
        sec = e.get('sec', [])
        size = e.get('s')
        off = e.get('o')
        ln = e.get('l')
        pr = e.get('p')
        if not isinstance(name, str) or not name or not isinstance(sec, list):
            raise SystemExit('corrupted entry')
        for p in sec:
            if not isinstance(p, str) or not p:
                raise SystemExit('corrupted entry')
        if not isinstance(size, int) or not isinstance(off, int) or not isinstance(ln, int):
            raise SystemExit('corrupted entry')
        if size < 0 or size > _MAX_FILE or off < 0 or ln < 0:
            raise SystemExit('corrupted entry')
        if not isinstance(pr, str):
            raise SystemExit('corrupted entry')
        try:
            if len(bytes.fromhex(pr)) != 4:
                raise ValueError
        except ValueError:
            raise SystemExit('corrupted entry')
        if ln != _ct_len(_bucket(size)):
            raise SystemExit('corrupted entry')
    blob_size = total - blob_start
    by_off = sorted(meta['files'], key=lambda e: e['o'])
    last_end = 0
    for e in by_off:
        if e['o'] < last_end:
            raise SystemExit('overlapping entries')
        last_end = e['o'] + e['l']
    for e in by_off:
        if e['o'] + e['l'] > blob_size:
            raise SystemExit('corrupted entry offsets')
    return salt, mk, meta, blob_start


def _validate_entries(entries):
    if len(entries) > _MAX_ENTRIES:
        raise SystemExit('too many entries')
    if len(entries) > (1 << 32):
        raise SystemExit('too many entries for prefix space')
    paths = set()
    dirs = set()
    for name, sec, _, _ in entries:
        _check_part(name)
        for p in sec:
            _check_part(p)
        ep = _entry_path(sec, name)
        if ep in paths:
            raise SystemExit('duplicate entry: ' + ep)
        paths.add(ep)
        for k in range(1, len(sec) + 1):
            dirs.add('/'.join(sec[:k]))
    clash = paths & dirs
    if clash:
        raise SystemExit('file/dir conflict: ' + sorted(clash)[0])


def _write_vaf_from_entries(path, pw, entries):
    _validate_entries(entries)
    salt = secrets.token_bytes(32)
    mk = _mk(pw.encode('utf-8'), salt)
    fmk = _sk(mk, _META_INFO)
    file_metas = []
    offset = 0
    for i, (name, sec, real_size, _) in enumerate(entries):
        if not isinstance(real_size, int) or real_size < 0 or real_size > _MAX_FILE:
            raise SystemExit('invalid size for: ' + name)
        padded_len = _bucket(real_size)
        ct_len = _ct_len(padded_len)
        prefix = i.to_bytes(4, 'big')
        file_metas.append({'n': name, 'sec': list(sec), 's': real_size, 'p': prefix.hex(), 'o': offset, 'l': ct_len})
        offset += ct_len
    meta = {'v': 3, 'files': file_metas}
    mb = json.dumps(meta, separators=(',', ':')).encode('utf-8')
    mp = _padmeta(mb)
    mn = secrets.token_bytes(12)
    mct = AESGCM(fmk).encrypt(mn, mp, _HDR_AAD + _M + salt)
    d = os.path.dirname(os.path.abspath(path)) or '.'
    fd, tmp = tempfile.mkstemp(dir=d, prefix='.vaf_tmp_')
    try:
        with os.fdopen(fd, 'wb') as f:
            f.write(_M)
            f.write(salt)
            f.write(len(mct).to_bytes(4, 'big'))
            f.write(mn)
            f.write(mct)
            for (name, sec, real_size, factory), info in zip(entries, file_metas):
                key = _file_key(mk, name, sec, salt)
                prefix = bytes.fromhex(info['p'])
                _write_file_stream(f, key, salt, prefix, factory(), real_size)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def _split_opts(args, need_pw=True):
    items = []
    pw = None
    force = False
    skip_existing = False
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--PASSWORD':
            if i + 1 >= len(args):
                raise SystemExit('--PASSWORD requires a value')
            pw = args[i + 1]
            i += 2
        elif a.startswith('--PASSWORD='):
            pw = a.split('=', 1)[1]
            i += 1
        elif a == '--force':
            force = True
            i += 1
        elif a == '--skip-existing':
            skip_existing = True
            i += 1
        else:
            items.append(a)
            i += 1
    if need_pw and pw is None:
        raise SystemExit('missing --PASSWORD')
    return items, pw, force, skip_existing


def _split_vaf_and_inputs(items):
    for i, a in enumerate(items):
        if a.endswith('.vaf') and not a.startswith('--'):
            return a, items[:i] + items[i+1:]
    raise SystemExit('no .vaf path found in arguments')


def _existing_entries(vaf, blob_start, salt, mk, meta):
    out = []
    for e in meta['files']:
        sec = list(e.get('sec', []))
        out.append((e['n'], sec, e['s'], (lambda e=e: _iter_vaf_plain(vaf, blob_start, salt, mk, e))))
    return out


def _walk_sections(root):
    base_parent = os.path.dirname(os.path.abspath(root))
    for dirpath, dirnames, filenames in os.walk(root):
        rel = os.path.relpath(os.path.abspath(dirpath), base_parent)
        parts = [] if rel == '.' else rel.split(os.sep)
        for part in parts:
            _check_part(part)
        for fn in filenames:
            _check_part(fn)
            yield parts, fn, os.path.join(dirpath, fn)


def _collect_inputs(inputs, base_entries, vaf_abs=None, skip_existing=False):
    existing = set(_entry_path(sec, name) for name, sec, _, _ in base_entries)
    entries = list(base_entries)
    added = []
    skipped = []
    for it in inputs:
        if os.path.isdir(it):
            for sec, name, fp in _walk_sections(it):
                if vaf_abs and os.path.abspath(fp) == vaf_abs:
                    continue
                p = _entry_path(sec, name)
                if skip_existing and p in existing:
                    skipped.append(p)
                    continue
                entries.append((name, list(sec), os.path.getsize(fp), (lambda p=fp: _iter_file_plain(p))))
                added.append(p)
                existing.add(p)
        elif os.path.isfile(it):
            if vaf_abs and os.path.abspath(it) == vaf_abs:
                raise SystemExit('cannot add target .vaf into itself')
            nm = os.path.basename(it)
            _check_part(nm)
            p = _entry_path([], nm)
            if skip_existing and p in existing:
                skipped.append(p)
                continue
            entries.append((nm, [], os.path.getsize(it), (lambda p=it: _iter_file_plain(p))))
            added.append(p)
            existing.add(p)
        else:
            raise SystemExit('no such file or directory: ' + it)
    return entries, added, skipped


def cmd_create(path, force):
    if os.path.exists(path) and not force:
        raise SystemExit('target exists, use --force to overwrite: ' + path)
    pw = _newpassword()
    _write_vaf_from_entries(path, pw, [])
    print('VAF created:', path)
    print('PASSWORD (shown once, save it):', pw)


def cmd_caaf(path, inputs, force):
    if not inputs:
        raise SystemExit('no inputs')
    if os.path.exists(path) and not force:
        raise SystemExit('target exists, use --force to overwrite: ' + path)
    entries, _, _ = _collect_inputs(inputs, [], os.path.abspath(path))
    pw = _newpassword()
    _write_vaf_from_entries(path, pw, entries)
    print('VAF created:', path, '| entries:', len(entries))
    print('PASSWORD (shown once, save it):', pw)


def cmd_af(args):
    items, pw, _, skip_existing = _split_opts(args)
    vaf, inputs = _split_vaf_and_inputs(items)
    if not inputs:
        raise SystemExit('no inputs')
    salt, mk, meta, blob_start = _read_header_and_meta(vaf, pw)
    base = _existing_entries(vaf, blob_start, salt, mk, meta)
    entries, added, skipped = _collect_inputs(inputs, base, os.path.abspath(vaf), skip_existing)
    _write_vaf_from_entries(vaf, pw, entries)
    print('Added:', len(added), 'entries' + (', skipped: %d' % len(skipped) if skipped else ''))


def cmd_aaf(args):
    items, pw, _, skip_existing = _split_opts(args)
    vaf, exclusions = _split_vaf_and_inputs(items)
    salt, mk, meta, blob_start = _read_header_and_meta(vaf, pw)
    base = _existing_entries(vaf, blob_start, salt, mk, meta)
    existing = set(_entry_path(sec, name) for name, sec, _, _ in base)
    vaf_abs = os.path.abspath(vaf)
    entries = list(base)
    added = []
    skipped = []
    for name in sorted(os.listdir('.')):
        p = os.path.abspath(name)
        if p == vaf_abs:
            continue
        if not os.path.isfile(name):
            continue
        if any(fnmatch.fnmatch(name, pat) for pat in exclusions):
            continue
        _check_part(name)
        if skip_existing and name in existing:
            skipped.append(name)
            continue
        entries.append((name, [], os.path.getsize(name), (lambda p=name: _iter_file_plain(p))))
        added.append(name)
        existing.add(name)
    _write_vaf_from_entries(vaf, pw, entries)
    print('Added:', len(added), 'files' + (', skipped: %d' % len(skipped) if skipped else ''))


def cmd_unpack(args):
    items, pw, _, _ = _split_opts(args)
    vaf, extra = _split_vaf_and_inputs(items)
    if extra:
        raise SystemExit('unexpected arguments')
    salt, mk, meta, blob_start = _read_header_and_meta(vaf, pw)
    target_dir = os.path.abspath(os.path.splitext(os.path.basename(vaf))[0] + '_extracted')
    parent = os.path.dirname(target_dir) or '.'
    os.makedirs(parent, exist_ok=True)
    tmp_dir = tempfile.mkdtemp(dir=parent, prefix='.vaf_extract_')
    try:
        for e in meta['files']:
            sec = list(e.get('sec', []))
            target = _safe_target(tmp_dir, sec, e['n'])
            os.makedirs(os.path.dirname(target), exist_ok=True)
            try:
                out = open(target, 'xb')
            except FileExistsError:
                raise SystemExit('duplicate entry during unpack: ' + _entry_path(sec, e['n']))
            try:
                with out:
                    for chunk in _iter_vaf_plain(vaf, blob_start, salt, mk, e):
                        out.write(chunk)
            except BaseException:
                try:
                    os.unlink(target)
                except OSError:
                    pass
                raise
        final = target_dir
        if os.path.exists(final):
            base_name, ext = os.path.splitext(final)
            i = 1
            while os.path.exists('%s_%d%s' % (base_name, i, ext)):
                i += 1
            final = '%s_%d%s' % (base_name, i, ext)
        os.rename(tmp_dir, final)
    except BaseException:
        shutil.rmtree(tmp_dir, ignore_errors=True)
        raise
    print('Extracted', len(meta['files']), 'files to', final)


def cmd_del(args):
    items, pw, _, _ = _split_opts(args)
    vaf, targets = _split_vaf_and_inputs(items)
    if not targets:
        raise SystemExit('no file specified')
    salt, mk, meta, blob_start = _read_header_and_meta(vaf, pw)
    by_path = {_entry_path(e.get('sec', []), e['n']): e for e in meta['files']}
    for t in targets:
        if t not in by_path:
            raise SystemExit('not found: ' + t)
    remove = set(targets)
    entries = []
    for e in meta['files']:
        p = _entry_path(e.get('sec', []), e['n'])
        if p in remove:
            continue
        entries.append((e['n'], list(e.get('sec', [])), e['s'], (lambda e=e: _iter_vaf_plain(vaf, blob_start, salt, mk, e))))
    _write_vaf_from_entries(vaf, pw, entries)
    print('Deleted:', ', '.join(targets))


def cmd_rename(args):
    items, pw, _, _ = _split_opts(args)
    vaf, rest = _split_vaf_and_inputs(items)
    if not rest or len(rest) % 2 != 0:
        raise SystemExit('rename needs old/new pairs')
    salt, mk, meta, blob_start = _read_header_and_meta(vaf, pw)
    by_path = {_entry_path(e.get('sec', []), e['n']): e for e in meta['files']}
    renames = {}
    for i in range(0, len(rest), 2):
        old, new = rest[i], rest[i + 1]
        if old not in by_path:
            raise SystemExit('not found: ' + old)
        _parse_path(new)
        renames[old] = new
    entries = []
    for e in meta['files']:
        p = _entry_path(e.get('sec', []), e['n'])
        if p in renames:
            nsec, nname = _parse_path(renames[p])
            entries.append((nname, nsec, e['s'], (lambda e=e: _iter_vaf_plain(vaf, blob_start, salt, mk, e))))
        else:
            entries.append((e['n'], list(e.get('sec', [])), e['s'], (lambda e=e: _iter_vaf_plain(vaf, blob_start, salt, mk, e))))
    _write_vaf_from_entries(vaf, pw, entries)
    print('Renamed.')


def cmd_ls(args):
    items, pw, _, _ = _split_opts(args)
    vaf, extra = _split_vaf_and_inputs(items)
    if extra:
        raise SystemExit('unexpected arguments')
    _, _, meta, _ = _read_header_and_meta(vaf, pw)
    rows = sorted((_entry_path(e.get('sec', []), e['n']), e['s']) for e in meta['files'])
    width = max([len(str(size)) for _, size in rows] + [1])
    for path, size in rows:
        print(str(size).rjust(width), path)
    print('Total:', len(rows), 'files,', sum(size for _, size in rows), 'bytes')


def main():
    a = sys.argv[1:]
    if not a:
        print('Varazd Advanced Asset Pack Engine')
        print('  -c    main.vaf [--force]')
        print('  -caaf main.vaf f1 dir1 dir2 ... [--force]')
        print('  -af   main.vaf f1 dir1 ... --PASSWORD pwd [--skip-existing]')
        print('  -aaf  main.vaf --PASSWORD pwd [--skip-existing] [exclude_glob ...]')
        print('  -u    main.vaf --PASSWORD pwd')
        print('  -df   main.vaf path1 path2 ... --PASSWORD pwd')
        print('  --rf  main.vaf old1 new1 old2 new2 ... --PASSWORD pwd')
        print('  ls    main.vaf --PASSWORD pwd')
        return
    c = a[0]
    if c == '-c':
        items, _, force, _ = _split_opts(a[1:], need_pw=False)
        if len(items) != 1:
            raise SystemExit('-c takes exactly one path')
        cmd_create(items[0], force)
    elif c == '-caaf':
        items, _, force, _ = _split_opts(a[1:], need_pw=False)
        if len(items) < 2:
            raise SystemExit('-caaf needs target and inputs')
        cmd_caaf(items[0], items[1:], force)
    elif c == '-af':
        cmd_af(a[1:])
    elif c == '-aaf':
        cmd_aaf(a[1:])
    elif c == '-u':
        cmd_unpack(a[1:])
    elif c == '-df':
        cmd_del(a[1:])
    elif c == '--rf':
        cmd_rename(a[1:])
    elif c == 'ls':
        cmd_ls(a[1:])
    else:
        raise SystemExit('unknown command: ' + c)


if __name__ == '__main__':
    main()
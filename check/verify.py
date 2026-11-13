#!/usr/bin/env python3
"""A180207 package audit and bounded known-term smoke; never starts a campaign.
Copyright (c) 2026 Carlo Corti. Python 3.12+, standard library only.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(text):
    p = PurePosixPath(text)
    require(bool(text) and not p.is_absolute() and '..' not in p.parts
            and '\\' not in text and p.as_posix() == text and text != '.',
            'unsafe relative path: ' + text)
    return p


def inventory():
    expected = {}
    for line in (ROOT/'checks.sha256').read_text().splitlines():
        digest, sep, name = line.partition('  ')
        require(sep and len(digest) == 64 and all(c in '0123456789abcdef' for c in digest),
                'malformed checksum line')
        relative(name)
        require(name not in expected and name != 'checks.sha256', 'duplicate/self checksum')
        expected[name] = digest
    found = set()
    expected_dirs = {str(p) for name in expected
                     for p in Path(name).parents if str(p) != '.'}
    for directory, dirs, files in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        require(not (base/'.git').is_symlink(), 'metadata symlink')
        if base == ROOT:
            dirs[:] = [d for d in dirs if d != '.git']
            files = [f for f in files if f != '.git']
        for name in dirs + files:
            p = base/name
            require(not p.is_symlink(), 'payload symlink: ' + str(p))
        for name in dirs:
            require((base/name).relative_to(ROOT).as_posix() in expected_dirs,
                    'unexpected payload directory: ' + str(base/name))
        for name in files:
            found.add((base/name).relative_to(ROOT).as_posix())
    require(found == set(expected) | {'checks.sha256'},
            'missing/unexpected payload: ' + repr(sorted(found ^ (set(expected) | {'checks.sha256'}))))
    for name, digest in expected.items():
        require(sha((ROOT/name).read_bytes()) == digest, 'changed payload: ' + name)


def load_originals():
    index = json.loads((ROOT/'proof/index.json').read_text())
    require(index['schema'] == 1 and index['sequence'] == 'A180207', 'bad evidence index')
    records = index['originals']
    result, archives = {}, {}
    for row in records:
        relative(row['original'])
        require(row['original'] not in result, 'duplicate original path')
        if 'public' in row:
            relative(row['public'])
            raw = (ROOT/row['public']).read_bytes()
        else:
            relative(row['archive']); relative(row['member'])
            archives.setdefault(row['archive'], []).append(row)
            raw = None
        result[row['original']] = (row, raw)
    for name, rows in archives.items():
        required = {r['member']: r for r in rows}
        require(len(required) == len(rows), 'duplicate indexed archive member')
        expanded = sum(r['bytes'] for r in rows)
        require(0 <= expanded <= 128*1024**2, 'archive expansion outside declared scope')
        seen = set()
        with tarfile.open(ROOT/name, 'r:gz') as archive:
            for member in archive:
                relative(member.name)
                require(member.isfile() and member.name in required and member.name not in seen,
                        'unexpected/link/duplicate archive member: ' + member.name)
                row = required[member.name]
                require(member.size == row['bytes'] and (member.mode & 0o777) == row['mode'],
                        'archive size/mode mismatch: ' + member.name)
                stream = archive.extractfile(member)
                require(stream is not None, 'unreadable archive member')
                raw = stream.read()
                result[row['original']] = (row, raw)
                seen.add(member.name)
        require(seen == set(required), 'missing archive member')
    for original, (row, raw) in result.items():
        require(raw is not None and len(raw) == row['bytes'] and sha(raw) == row['sha256'],
                'original identity mismatch: ' + original)
    return {name: raw for name, (_, raw) in result.items()}, index


def evidence(raw):
    def obj(name):
        return json.loads(raw[name])

    def rows(data):
        return [tuple(map(int, line.split())) for line in data.splitlines() if line.strip()]

    native = rows(raw['runs/m22/res.tsv'])
    require([n for n, _ in native] == list(range(1, 23)), 'native coverage')
    canonical = (ROOT/'data/b180207.txt').read_bytes()
    require(rows(canonical) == native, 'canonical/native mismatch')
    regenerated = (''.join(f'{n} {v}\n' for n, v in native) + '\n').encode('ascii')
    require(regenerated == canonical, 'b-file framing or regeneration mismatch')
    known = raw['outputs/valid22/known16.txt']
    require(canonical.splitlines(keepends=True)[:16] == known.splitlines(keepends=True)[:16],
            'historical prefix changed')
    values = dict(native)
    admit = obj('outputs/valid22/admit.json')
    def references(value):
        if isinstance(value, dict):
            if 'path' in value and 'sha256' in value:
                require(value['path'] in raw and sha(raw[value['path']]) == value['sha256'],
                        'missing/changed admitted dependency: ' + value['path'])
            for child in value.values():
                references(child)
        elif isinstance(value, list):
            for child in value:
                references(child)
    references(admit)
    require(admit['status'] == 'VALIDATED_LOCAL_THROUGH22' and admit['first_unresolved'] == 23,
            'scientific admission')
    config = obj('runs/m22/run.json')
    for field, path in [('source', 'src/a180207.c'), ('makefile', 'src/Makefile'),
                        ('binary', 'src/a180207')]:
        require(sha(raw[path]) == config[field], 'original native identity: ' + field)
    require((config['M'], config['workers'], config['depth']) == (22, 1, 1), 'native configuration')
    done = obj('runs/ops22/s01/done.json')
    require(done['native_exit'] == 0 and done['check_exit'] == 0
            and done['results']['rows'] == 22, 'native completion receipt')
    require(done['call_sha256'] == sha(raw['runs/ops22/s01/call.json']), 'native call binding')
    for line in raw['runs/m22/sha.txt'].decode().splitlines():
        digest, name = line.split('  ', 1)
        require(sha(raw['runs/m22/' + name]) == digest, 'native job member: ' + name)
    ie = obj('outputs/valid22/qualify.json')['ie_rows']
    require([r['n'] for r in ie] == list(range(1, 17)), 'IE historical coverage')
    for n in range(17, 23):
        row = obj(f'outputs/valid22/ie{n}.out')
        receipt = obj(f'outputs/valid22/ie{n}.done')
        require(receipt['status'] == 'EXITED' and receipt['exit_code'] == 0, 'IE incomplete')
        ie.append(row)
    for row in ie:
        n = row['n']; N = n-1
        require(row['status'] == 'COMPLETE' and int(row['count']) == values[n], 'IE count')
        require(row['subsets'] == row['expected_subsets'] == 1 << N, 'IE subset coverage')
        require(row['states'] == math.comb(N+3, 3), 'IE state geometry')
        require(int(row['absolute_sum_bound']) == (1 << N)*(N+1)*N**N < 1 << 127, 'IE bound')
    build = obj('outputs/valid22/build.json')
    require(sha(raw['validation/iecheck.cpp']) == build['source_sha256']
            and sha(raw['outputs/valid22/iecheck']) == build['binary_sha256'], 'IE identity')
    probe = obj('outputs/probe.json')
    require(probe['status'] == 'PASS', 'probe incomplete')
    require([r['n'] for r in probe['permutation_replay']] == list(range(1, 10)), 'brute domain')
    for row in probe['permutation_replay']:
        require(row['permutations_examined'] == math.factorial(row['n'])
                and row['count'] == values[row['n']] == sum(row['by_zero_position']), 'brute row')
    require([r['n'] for r in probe['dp_replay']] == list(range(1, 13)), 'Python inline domain')
    for row in probe['dp_replay']:
        require(row['count'] == values[row['n']], 'Python inline row')
    require(obj('outputs/full16.json')['status'] == 'PASS'
            and obj('outputs/full16.json')['count'] == values[16], 'Python16')
    require(obj('outputs/valid22/win17.json')['status'] == 'COMPLETE'
            and obj('outputs/valid22/win17.json')['count'] == values[17], 'Python17')
    require(obj('outputs/valid22/win17.done')['exit_code'] == 0, 'Python17 receipt')
    side = obj('outputs/sidechk.json')
    for row in side['rows']:
        for count in row['counts']:
            require(count['count'] == values[count['n']], 'side coefficient count')
    part = obj('outputs/partchk.json')['rows']
    require([r['prefix_depth'] for r in part] == list(range(5))
            and len({r['F_sha256_decimal_lines'] for r in part}) == 1, 'partition coefficient equality')
    for row in part:
        require(row['a16'] == values[16] and row['units'] == math.comb(15, row['prefix_depth']),
                'partition coverage')
    require(all(v % 2 == 0 for n, v in native if n > 1)
            and all(b >= 2*a for (_, a), (_, b) in zip(native, native[1:])), 'proved invariants')
    return values


def restore(raw, index, destination):
    target = destination.resolve()
    require(not target.exists() and not target.is_relative_to(ROOT),
            'restore destination must be new and outside the package')
    target.mkdir(parents=True)
    for row in index['originals']:
        p = target.joinpath(*relative(row['original']).parts)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(raw[row['original']]); p.chmod(row['mode'])
    print('RESTORED_FROZEN_INPUTS', target)


def run(args, cwd, seconds):
    result = subprocess.run([str(x) for x in args], cwd=cwd, capture_output=True,
                            text=True, timeout=seconds,
                            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'MAKEFLAGS': ''})
    require(result.returncode == 0, 'command failed: ' + repr(args)
            + '\n' + result.stdout[-3000:] + result.stderr[-3000:])
    return result


def smoke(raw, index, values):
    with tempfile.TemporaryDirectory(prefix='a180207-') as folder:
        work = Path(folder)
        # Only a private copy of the old job and old executable is inspected.
        for original in ['src/a180207'] + [p for p in raw if p.startswith('runs/m22/')]:
            p = work/original
            p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(raw[original])
        exe = work/'src/a180207'; exe.chmod(0o755)
        before = {p: sha(v) for p, v in raw.items() if p.startswith('runs/m22/')}
        run([exe, 'check', '--root', work/'runs/m22'], work, 30)
        for original, digest in before.items():
            require(sha((work/original).read_bytes()) == digest, 'native check mutated job')
        # New builds never replace or masquerade as the historical executable.
        build = work/'build'; build.mkdir()
        for name in ['a180207.c', 'Makefile']:
            shutil.copyfile(ROOT/'src'/name, build/name)
        run(['make', '--no-print-directory'], build, 60)
        fresh = build/'a180207'
        run([fresh, '--help'], work, 10)
        run([fresh, 'next', '--root', work/'small', '--max', '6', '--workers', '1',
             '--depth', '1', '--seconds', '2'], work, 15)
        small = [tuple(map(int, s.split())) for s in (work/'small/res.tsv').read_text().splitlines()]
        require(small == [(n, values[n]) for n in range(1, 7)], 'new public build smoke6')
        checker = work/'iecheck'
        run(['g++-13', '-std=c++17', '-O3', '-march=znver4', '-mtune=znver4',
             '-Wall', '-Wextra', '-Wpedantic', '-Wshadow', '-Wconversion', '-Wformat=2',
             ROOT/'check/iecheck.cpp', '-o', checker], work, 60)
        for n in [1, 2, 6]:
            row = json.loads(run([checker, n], work, 10).stdout)
            require(row['status'] == 'COMPLETE' and int(row['count']) == values[n], 'IE smoke')
        run([sys.executable, '-B', ROOT/'check/window_check.py', '--n', '6',
             '--out', work/'win.json', '--memory-gib', '1'], work, 15)
        require(json.loads((work/'win.json').read_text())['count'] == values[6], 'Python smoke')
        print('SMOKE_PASS original-native-read-only; new-C1..6; new-IE1,2,6; Python6')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--records', action='store_true', help='integrity/retained records only; no build/execution')
    parser.add_argument('--restore', type=Path, help='restore original evidence layout to a new outside directory')
    args = parser.parse_args()
    try:
        inventory(); raw, index = load_originals(); values = evidence(raw)
        if args.restore is not None:
            restore(raw, index, args.restore)
        elif not args.records:
            smoke(raw, index, values)
        print('PUBLIC_VALIDATION_PASS contiguous=1..22 first_unresolved=23 no_new_term')
        return 0
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError,
            subprocess.SubprocessError) as exc:
        print('PUBLIC_VALIDATION_FAIL:', exc, file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())

#!/usr/bin/env python3
"""Verify every dependency checkout against the pinned local Lake manifest."""
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
formal = root / 'formalization'
manifest = json.loads((formal / 'lake-manifest.json').read_text())

def check(package):
    if package.get('type') != 'git' or not package.get('rev'):
        raise ValueError(f"Unpinned dependency: {package['name']}")
    directory = formal / manifest['packagesDir'] / package['name'].strip('«»')
    def git(*args):
        return subprocess.run(['git', '-C', str(directory), *args], check=True,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()
    actual = git('rev-parse', 'HEAD')
    changes = git('status', '--porcelain', '--untracked-files=no')
    return {'name': package['name'], 'expected': package['rev'], 'actual': actual,
        'tracked_changes': changes, 'pass': actual == package['rev'] and not changes}

with ThreadPoolExecutor(max_workers=8) as pool:
    results = list(pool.map(check, manifest['packages']))
(root / 'validation' / 'dependencies.json').write_text(json.dumps(results, indent=2) + '\n')
if not all(result['pass'] for result in results):
    raise SystemExit('FAIL: dependency revision mismatch or tracked changes; see validation/dependencies.json')
print(f'PASS: {len(results)} pinned dependency revisions; no tracked dependency changes.')

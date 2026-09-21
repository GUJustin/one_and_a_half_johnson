#!/usr/bin/env python3
"""Build locally and audit every explicitly named project declaration.

This inventory supports the simple declaration/namespace syntax used here.
Unsupported declaration commands fail closed; no remote CI is contacted.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def validate_axiom_output(output, names):
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    found = {name: sorted(a.strip() for a in axioms.split(',') if a.strip()) for name, axioms in reports}
    if set(found) != set(names):
        raise ValueError(f'Incomplete axiom output: missing={set(names)-set(found)}, unexpected={set(found)-set(names)}')
    for name, axioms in found.items():
        if not set(axioms) <= ALLOWED:
            raise ValueError(f'Forbidden axioms: {name}: {axioms}')
    return found


def main():
    ROOT = Path(__file__).resolve().parents[1]
    FORMAL = ROOT / 'formalization'
    LEANROOT = FORMAL / 'OneAndAHalfJohnson'
    subprocess.run([sys.executable, str(ROOT / 'scripts' / 'check_dependencies.py')], check=True)
    DECL = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_.]*)\b')
    namespace = []
    names = []
    files = sorted(LEANROOT.rglob('*.lean'))
    source_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    for path in files:
        namespace = []
        for line in path.read_text().splitlines():
            line = line.lstrip()
            if re.match(r'^namespace\s+', line):
                namespace.append(line.split()[1])
            elif re.match(r'^end\s+', line):
                closed = line.split()[1]
                if namespace and closed == namespace[-1]:
                    namespace.pop()
            elif (match := DECL.match(line)):
                names.append('.'.join(namespace + [match[1]]))
            elif re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev|instance|axiom|opaque|structure|class|inductive)\b', line):
                raise SystemExit(f'Unsupported declaration inventory syntax: {path}: {line}')
    if len(set(names)) != len(names):
        raise SystemExit('Duplicate declaration names in inventory')
    modules = ['.'.join(p.relative_to(FORMAL).with_suffix('').parts) for p in files]
    check = '\n'.join('import ' + m for m in modules) + '\n\n'
    check += '\n'.join('#print axioms ' + n for n in names) + '\n'
    (FORMAL / 'Checks' / 'Axioms.lean').write_text(check)
    lake = shutil.which('lake') or str(Path.home() / '.elan' / 'bin' / 'lake')
    env = dict(os.environ, LAKE_ARTIFACT_CACHE='false', LAKE_NO_CACHE='true')
    commands = [[lake, 'build', 'OneAndAHalfJohnson', *modules], [lake, 'env', 'lean', 'Checks/Axioms.lean']]
    logs = []
    for command in commands:
        result = subprocess.run(command, cwd=FORMAL, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logs.append(result.stdout)
        print(result.stdout, end='')
        if result.returncode:
            raise SystemExit(result.returncode)
    found = validate_axiom_output(logs[-1], names)
    final_files = sorted(LEANROOT.rglob('*.lean'))
    final_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in final_files}
    if final_hashes != source_hashes:
        raise SystemExit('Source files changed during validation; rerun on a stable snapshot.')
    manifest = json.loads((FORMAL / 'lake-manifest.json').read_text())
    receipt = {
        'status': 'PASS',
        'scope': 'Every explicitly named local declaration; target propositions are definitions, not proofs of their truth.',
        'toolchain': (FORMAL / 'lean-toolchain').read_text().strip(),
        'dependency_pins': {p['name']: p.get('rev') for p in manifest['packages']},
        'source_sha256': source_hashes,
        'declarations': found,
    }
    (ROOT / 'validation' / 'axioms.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'validation' / 'lean.log').write_text('\n'.join(logs))
    print(f'PASS: {len(names)} declarations, standard axioms only.')


if __name__ == '__main__':
    main()

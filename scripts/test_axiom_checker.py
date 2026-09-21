#!/usr/bin/env python3
"""Check the trust gate against actual kernel axiom output, including an admission."""
from pathlib import Path
import shutil
import subprocess
import tempfile
from check_axioms import validate_axiom_output

root = Path(__file__).resolve().parents[1]
lake = shutil.which('lake') or str(Path.home() / '.elan' / 'bin' / 'lake')
for proof, should_pass in [('by trivial', True), ('by sorry', False)]:
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean') as source:
        source.write('theorem trustControl : True := ' + proof + '\n#print axioms trustControl\n')
        source.flush()
        result = subprocess.run([lake, 'env', 'lean', source.name], cwd=root / 'formalization',
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
    try:
        validate_axiom_output(result.stdout, ['trustControl'])
        accepted = True
    except ValueError:
        accepted = False
    assert accepted == should_pass, result.stdout
try:
    validate_axiom_output('', ['missing'])
except ValueError:
    pass
else:
    raise AssertionError('Missing axiom output was accepted')
print('PASS: proved control accepted; sorryAx rejected; missing output rejected.')

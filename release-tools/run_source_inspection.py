from pathlib import Path
import os,subprocess
src=Path('/Volumes/Sheridan/sandbox/Math Musings/FableForward/riemann/A4-12-lean-boundaries/lean')
paths=[src/'.lake/build/lib/lean']+list((src/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
Path('build').mkdir(exist_ok=True)
Path('build/InspectSource.lean').write_text(Path('release-tools/InspectSource.lean.in').read_text())
with open('build/source-deps.jsonl','w') as f:
 p=subprocess.run(['/Users/agenthome/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean','build/InspectSource.lean'],env=env,stdout=f,stderr=subprocess.STDOUT)
print('exit',p.returncode)

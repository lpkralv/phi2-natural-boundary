"""Audit release-owned Lean sources, pins, import coverage and statement definitions."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent.parent
V11=Path('/Volumes/Sheridan/sandbox/_Scratch/math-musings-phi2-bundle-v3/repo/phi2-natural-boundary')
SRC=Path('/Volumes/Sheridan/sandbox/Math Musings/FableForward/riemann/A4-12-lean-boundaries/lean/GoldbachBoundaries')
def code(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-': depth+=1; i+=2
            elif s[i:i+2]=='-/': depth-=1; i+=2
            else: i+=1
        elif string:
            if s[i]=='\\': i+=2
            elif s[i]=='"': string=False; i+=1
            else: i+=1
        elif s[i:i+2]=='/-': out.append(' '); depth=1; i+=2
        elif s[i:i+2]=='--':
            j=s.find('\n',i); i=len(s) if j<0 else j
        elif s[i]=='"': out.append(' '); string=True; i+=1
        else: out.append(s[i]); i+=1
    return ''.join(out)
files=[ROOT/'Phi2NB.lean']+sorted((ROOT/'Phi2NB').rglob('*.lean'))
for p in files+sorted(ROOT.glob('Check*.lean')):
    hits=re.findall(r'\b(?:sorry|axiom|admit|native_decide|implemented_by|extern)\b',code(p.read_text()))
    assert not hits,(p,hits)
print('PASS: no prohibited constructs in release-owned Lean sources or axiom-check scripts.')
for name in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
    assert (ROOT/name).read_bytes()==(V11/name).read_bytes(),name
    print('UNCHANGED',name,hashlib.sha256((ROOT/name).read_bytes()).hexdigest())
legacy=list((V11/'Phi2NB').rglob('*.lean'))
for p in legacy:
    q=ROOT/p.relative_to(V11)
    if p.relative_to(V11).as_posix()=='Phi2NB/Paper2/Defs.lean':
        assert code(p.read_text())==code(q.read_text()),p
    else: assert p.read_bytes()==q.read_bytes(),p
print(f'PASS: all {len(legacy)} v1.1 library modules retained; only the Hinf docstring changed.')
allmods={p.relative_to(ROOT).with_suffix('').as_posix().replace('/','.') for p in files}
seen=set()
def visit(n):
    if n in seen:return
    seen.add(n)
    p=ROOT/(n.replace('.','/')+'.lean')
    for dep in re.findall(r'^import (Phi2NB(?:\.[^\s]+)?)',p.read_text(),re.M):visit(dep)
visit('Phi2NB')
assert allmods==seen,(allmods-seen,seen-allmods)
print(f'PASS: single root Phi2NB imports all {len(files)} library files.')
def definition(path,name):
    s=code(path.read_text())
    m=re.search(r'^(?:noncomputable )?(?:def|abbrev) '+re.escape(name)+r'\b[^\n]*(?:\n(?!\n).*)*',s,re.M)
    assert m,(path,name)
    return ' '.join(m.group().split())
for name,source,release in [
 ('Hinf','Paper2/Defs.lean','Paper2/Defs.lean'),
 *[(n,'Paper2/Defs.lean','HInfSupport/Paper2/Defs.lean') for n in ['Z1','Z2','Z3','ZLittlewood']],
 ('StirlingStrip','Phi2HInf/Defs.lean','Phi2HInf/Defs.lean'),
 ('Nzero','Paper2/Defs.lean','Paper2/Defs.lean'),
 ('Phi2','Phi2/Defs.lean','Phi2/Defs.lean'),
 ('PhiR','PhiR/Defs.lean','PhiR/Defs.lean'),
 *[(n,'Defs.lean','Defs.lean') for n in ['NontrivialZeros','zetaMult','HH','halfPlane','lineOne','NoMeromorphicExtensionAt','IsNaturalBoundary']],
 ('lineAt','PhiR/Defs.lean','PhiR/Defs.lean')]:
    assert definition(SRC/source,name)==definition(ROOT/'Phi2NB'/release,name),(name,'definition mismatch')
print('PASS: 17 definitions underlying the four H∞ statements match the in-repo bodies.')
counts={}
for group,ps in [('HInf',list((ROOT/'Phi2NB/Phi2HInf').rglob('*.lean'))),
                 ('HInfSupport',list((ROOT/'Phi2NB/HInfSupport').rglob('*.lean'))),
                 ('Library',files),('LibraryAndChecks',files+list(ROOT.glob('Check*.lean')))]:
    counts[group]={'files':len(ps),'lines':sum(len(p.read_text().splitlines()) for p in ps)}
    print(group,counts[group])
(ROOT/'release-tools/counts.json').write_text(json.dumps(counts,indent=2)+'\n')

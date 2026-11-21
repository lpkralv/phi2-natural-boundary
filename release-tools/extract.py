"""Extract H-infinity declarations from source metadata, sharing the v1.1 library.
Inputs are read-only; output is confined to this release workspace.
"""
from pathlib import Path
from collections import defaultdict
import json, re, sys
ROOT=Path(__file__).resolve().parent.parent
SRC=Path('/Volumes/Sheridan/sandbox/Math Musings/FableForward/riemann/A4-12-lean-boundaries/lean')
V11=Path('/Volumes/Sheridan/sandbox/_Scratch/math-musings-phi2-bundle-v3/repo/phi2-natural-boundary')
def load_index(root,prefix):
    mods={}; decls={}
    for p in (root/'.lake/build/lib/lean'/prefix).rglob('*.ilean'):
        a=json.loads(p.read_text()); mods[a['module']]=a
        for n,span in a['decls'].items(): decls[n]=(a['module'],span)
    return mods,decls
mods,decls=load_index(SRC,'GoldbachBoundaries')
vmods,vdecls=load_index(V11,'Phi2NB')
graph={}; types={}
for line in (ROOT/(sys.argv[1] if len(sys.argv)>1 else 'build/source-deps.jsonl')).read_text().splitlines():
    row=json.loads(line)
    if len(row)==2: n,(m,(ds,ts))=row
    else: n,m,ds,ts=row
    graph[n]=ds; types[n]=ts
# Reuse definitions and proof declarations unless their source type takes full Z2.
clashes={n for n in vdecls if 'GoldbachBoundaries.Paper2.Z2' in types.get(n,[])}
renames={n:n+'_fullZ2' for n in clashes}
shared=set(vdecls)-clashes
roots=['GoldbachBoundaries.Phi2HInf.'+n for n in ['phi2_hinf_natural_boundary','phiR_hinf_natural_boundary','phi2_hinf_natural_boundary_classical','phiR_hinf_natural_boundary_classical']]
# Pole at 2B and RH criterion (Phi2HInf.PoleTwoBsup and its fills): every declaration the 2026-11-20 report names.
roots+=['GoldbachBoundaries.Phi2HInf.'+n for n in ['ZetaNoZeroIoo','zetaNoZeroIoo',
 'analyticAt_M0_of_not_mem_phi2Poles','ofReal_not_mem_phi2Poles','hasResidue_Phi2cHInf_of_not_mem_phi2Poles',
 'exists_rightZero_of_offLine','Bsup_attained_of_offLine','collision_twoBsup_iff','collisionTwoBsupEquiv',
 'zeroCoef_mul_zeroCoef_conj','collisionAtom_twoBsup','collisionAtom_twoBsup_pos','hasResidue_Phi2cHInf_twoBsup',
 'not_analyticAt_Phi2cHInf_twoBsup','analyticAt_cauchy_of_gap','analyticAt_C_of_not_pairSum',
 'analyticAt_Phi2cHInf_of_not_pole','exists_trivial_of_riemannZeta_eq_zero_of_re_nonpos',
 'riemannHypothesis_iff_nontrivialZeros','analyticAt_Phi2cHInf_real_of_RH','riemannHypothesis_iff_analyticAt_Phi2cHInf_real',
 'phi2_hinf_pole_twoBsup',"phi2_hinf_pole_twoBsup'",'phi2_hinf_pole_twoBsup_of_continuation',
 'phi2_hinf_rh_iff_no_real_pole',"phi2_hinf_rh_iff_no_real_pole'",'phi2_hinf_rh_iff_no_real_pole_of_continuation']]
selected=set(); seen=set()
def visit(n):
    if n in seen or n in shared: return
    seen.add(n)
    if n in decls: selected.add(n)
    for d in graph.get(n,[]): visit(d)
for n in roots: visit(n)
# Source spellings may reference helper lemmas erased from the proof term.
refs=defaultdict(set)
for m,a in mods.items():
    for k,v in a['references'].items():
        k=json.loads(k)
        if 'c' not in k: continue
        d=k['c']['n']
        for u in v['usages']:
            if len(u)>4 and u[4]: refs[u[4]].add(d)
while True:
    before=len(selected)
    for n in list(selected):
        for d in refs[n]: visit(d)
    if len(selected)==before: break
by_mod=defaultdict(set)
for n in selected: by_mod[decls[n][0]].add(n)
def outmod(m):
    return m.replace('GoldbachBoundaries.Phi2HInf','Phi2NB.Phi2HInf',1) if m.startswith('GoldbachBoundaries.Phi2HInf') else m.replace('GoldbachBoundaries','Phi2NB.HInfSupport',1)
def offset(text,l,c):
    # .ilean uses zero-based lines and UTF-16 columns.
    ls=text.splitlines(keepends=True)
    s=ls[l].encode('utf-16-le')[:c*2].decode('utf-16-le')
    return sum(len(x) for x in ls[:l])+len(s)
def strip_comments(s):
    out=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s[i:i+2]=='/-': depth+=1; i+=2
            elif s[i:i+2]=='-/': depth-=1; i+=2
            else:
                if s[i]=='\n': out.append('\n')
                i+=1
        elif not string and s[i:i+2]=='/-': depth=1; i+=2
        elif not string and s[i:i+2]=='--':
            j=s.find('\n',i); i=len(s) if j<0 else j
        else:
            out.append(s[i])
            if s[i]=='"' and (i==0 or s[i-1]!='\\'): string=not string
            i+=1
    return ''.join(out)
for m,names in by_mod.items():
    a=mods[m]; text=(SRC/(m.replace('.','/')+'.lean')).read_text()
    edits=[]; kept=[]
    all_ranges=defaultdict(set)
    for n,sp in a['decls'].items():
        start,end=offset(text,*sp[:2]),offset(text,*sp[2:4])
        all_ranges[start,end].add(n)
    for (s,e),ns in all_ranges.items():
        if ns & names: kept.append((s,e))
        else: edits.append((s,e,''))
    # Only rename references inside retained declarations, using compiler-resolved names.
    def in_kept(s,e): return any(l<=s and e<=r for l,r in kept)
    for n in names & clashes:
        sp=a['decls'][n]; s,e=offset(text,*sp[4:6]),offset(text,*sp[6:8])
        old=text[s:e]; edits.append((s,e,old+'_fullZ2'))
    for k,v in a['references'].items():
        k=json.loads(k)
        if 'c' not in k or k['c']['n'] not in renames: continue
        for u in v['usages']:
            s,e=offset(text,*u[:2]),offset(text,*u[2:4])
            if in_kept(s,e): edits.append((s,e,'_root_.'+renames[k['c']['n']]))
    # Remove contained edits when a whole declaration is dropped.
    drops=[(s,e) for s,e,v in edits if v=='']
    edits=[(s,e,v) for s,e,v in edits if not any(l<=s and e<=r and (l,r)!=(s,e) for l,r in drops)]
    for s,e,v in sorted(set(edits),reverse=True): text=text[:s]+v+text[e:]
    text=strip_comments(text)
    text=re.sub(r'^import .*\n','',text,flags=re.M)
    text=re.sub(r'\n\s*\n\s*\n','\n\n',text).strip()+'\n'
    needed=set()
    for n in names:
        for d in set(graph.get(n,[]))|refs[n]:
            if d in selected and decls[d][0]!=m: needed.add(outmod(decls[d][0]))
    imports=['Phi2NB.PhiR.Statement']+sorted(needed)
    header=''.join('import '+i+'\n' for i in imports)
    header+='\n/-! Extracted for v1.2 from `'+m+'`.\nShared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/\n\n'
    p=ROOT/(outmod(m).replace('.','/')+'.lean'); p.parent.mkdir(parents=True,exist_ok=True); p.write_text(header+text)
report={'roots':roots,'selected':sorted(selected),'renamed':{n:renames[n] for n in selected & clashes},'modules':{m:outmod(m) for m in sorted(by_mod)}}
(ROOT/'build/extraction.json').write_text(json.dumps(report,indent=2)+'\n')
import hashlib
report['source_sha256']={m:hashlib.sha256((SRC/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in sorted(by_mod)}
(ROOT/'release-tools/extraction.json').write_text(json.dumps(report,indent=2)+'\n')
print(len(selected),'declarations in',len(by_mod),'files;',len(selected & clashes),'renamed helpers')
print('\n'.join(sorted(by_mod)))

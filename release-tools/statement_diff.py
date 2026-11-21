"""Record source theorem headers and require exact public-statement preservation."""
from pathlib import Path
import re, json
ROOT=Path(__file__).resolve().parent.parent
V11=Path('/Volumes/Sheridan/sandbox/_Scratch/math-musings-phi2-bundle-v3/repo/phi2-natural-boundary')
SRC=Path('/Volumes/Sheridan/sandbox/Math Musings/FableForward/riemann/A4-12-lean-boundaries/lean')
entries=[
 ('phi2_natural_boundary','Phi2/Statement.lean'),
 ('phi2_natural_boundary_classical','Phi2/Statement.lean'),
 ('Phi2Proof.phi2_continuation','Phi2/Proof/M1Continuation.lean'),
 ('Phi2Proof.tendsto_eta_Hphi2','Phi2/Proof/M3Radial.lean'),
 ('phiR_natural_boundary','PhiR/Statement.lean'),
 ('phiR_natural_boundary_classical','PhiR/Statement.lean'),
 ('phiR_natural_boundary_two','PhiR/Statement.lean'),
 ('phiR_singular_iff','PhiR/Statement.lean'),
 ('phiR_reduction','PhiR/Statement.lean'),
 ('phiR_radial_limit','PhiR/Statement.lean'),
 ('PhiRProof.phiR_continuation','PhiR/Proof/M2Continuation.lean'),
 ('PhiRProof.tendsto_eta_Phi2c','PhiR/Proof/M5Radial.lean'),
]+[('Phi2HInf.'+n,'Phi2HInf/'+f) for n,f in [
 ('phi2_hinf_natural_boundary','Statements.lean'),('phiR_hinf_natural_boundary','Statements.lean'),
 ('phi2_hinf_natural_boundary_classical','Classical.lean'),('phiR_hinf_natural_boundary_classical','Classical.lean'),
 # Added in v1.2 (pole at 2B and RH criterion under H-infinity, gated 2026-11-20).
 ('phi2_hinf_pole_twoBsup','PoleTwoBsup.lean'),("phi2_hinf_pole_twoBsup'",'PoleTwoBsup.lean'),
 ('phi2_hinf_pole_twoBsup_of_continuation','PoleTwoBsup.lean'),
 ('phi2_hinf_rh_iff_no_real_pole','PoleTwoBsup.lean'),("phi2_hinf_rh_iff_no_real_pole'",'PoleTwoBsup.lean'),
 ('phi2_hinf_rh_iff_no_real_pole_of_continuation','PoleTwoBsup.lean'),
 ('hasResidue_Phi2cHInf_of_not_mem_phi2Poles','Fill/pole_twoBsup.lean')]]
def header(path,name):
    s=path.read_text(); m=re.search(r'^theorem '+re.escape(name.rsplit('.',1)[-1])+r"(?![\w'])" ,s,re.M)
    if m is None: return None
    e=s.index(':=',m.start())
    return s[m.start():e].rstrip()
lines=['# Statement comparison for v1.2','',
'All names below have the prefix `GoldbachBoundaries.`. Each block contains the source bytes from `theorem` through the type, with the proof and final `:=` omitted. Line breaks inside the statement are preserved. The comparison covers the public boundary theorems, their classical corollaries, and the continuation, reduction, transfer and radial-limit results named in the README.','',
'The v1.1 reference is the published release source. The in-repo reference is `FableForward/riemann/A4-12-lean-boundaries/lean/GoldbachBoundaries/`. The comparison script fails if any v1.1 statement changes or any H∞ statement changes. The seven statements of the pole at 2B and the RH criterion (the last seven blocks) are new in v1.2 and have no v1.1 counterpart.','',
'The four H∞ statements and their premise identifiers are unchanged. The H∞ premise `Z2` retains both the asymptotic and the local count. Shared definitions have the same bodies; `Hinf`, `Phi2`, `PhiR`, `HH`, `halfPlane`, `lineOne`, `lineAt` and the natural-boundary predicates use the release definitions. The extracted `Z1`, `Z3` and `ZLittlewood` have the source definition bodies. They are definitionally equal to `ZeroSymmetry`, `LogDerivZetaLocal` and `LittlewoodGap`, respectively.','',
'The RH statements retain v1.1\'s weaker counting premise. In the in-repo RH tree, `Z2` includes the Riemann–von Mangoldt asymptotic as well as the local bound. In v1.1 and v1.2, `RiemannVonMangoldt` is only the local bound. This difference predates v1.2; no release theorem is strengthened. `Z3`/`LogDerivZetaLocal` and `ZLittlewood`/`LittlewoodGap` have identical definition bodies. Binder spellings and line breaks also differ between those two RH trees.','',
'The H∞ classical corollaries require agreement only where the continuation is analytic. The retained RH classical corollaries require agreement everywhere in the half-disc. The codiscrete RH boundary clauses also exclude analytic-point agreement, as explained in the paper’s §9. The H∞ conclusions have no exact pole/residue catalogue; the RH conclusions retain theirs. These differences are present in the input statements.','']
for name,rel in entries:
    release=header(ROOT/'Phi2NB'/rel,name); source=header(SRC/'GoldbachBoundaries'/rel,name)
    is_hinf=rel.startswith('Phi2HInf/')
    previous=None if is_hinf else header(V11/'Phi2NB'/rel,name)
    assert release==(source if is_hinf else previous),(name,'statement changed')
    if not is_hinf and source is not None:
        mapped=source
        for old,new in {'Z2':'RiemannVonMangoldt','Z3':'LogDerivZetaLocal','ZLittlewood':'LittlewoodGap','hZ2':'hRvM','hZ3':'hLD'}.items():
            mapped=re.sub(r'\b'+old+r'\b',new,mapped)
        assert ' '.join(mapped.split())==' '.join(release.split()),(name,'undocumented in-repo difference')
    lines+=['## `'+name+'`','','Release file: `Phi2NB/'+rel+'`. In-repo file: `GoldbachBoundaries/'+rel+'`.','',
        '### v1.2','','```lean',release,'```','','### In-repo','', *(['```lean',source,'```'] if source is not None else ['Not present in the in-repo file; retained from v1.1.']), '', '### v1.1','']
    if previous is None: lines+=['Not present in v1.1.','','Difference: none from the in-repo statement.','']
    else:
        lines+=['```lean',previous,'```','','Difference: none from v1.1. '+('No counterpart in the in-repo file.' if source is None else 'None from the in-repo statement.' if source==release else 'The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.'),'']
(ROOT/'STATEMENT-DIFF.md').write_text('\n'.join(lines))
print('PASS: 12 retained statements, four H∞ statements and seven pole-at-2B/RH-criterion statements are byte-identical to their release/source references.')
print('PASS: every in-repo RH counterpart matches after the documented premise/binder mapping and whitespace normalization.')

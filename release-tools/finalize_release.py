"""Fill observed build/check evidence into README and assemble a source-only archive."""
from pathlib import Path
import datetime,hashlib,json,tarfile
root=Path(__file__).resolve().parent.parent
record=json.loads((root/'release-tools/build-record.json').read_text())
assert len(record['commands'])==3 and all(c['exit_code']==0 for c in record['commands'])
assert record['jobs']>0
summary=(root/'AxiomAudit.out').read_text()
assert 'CheckAxioms.lean: 16 results; each exactly [propext, Classical.choice, Quot.sound].' in summary
assert 'CheckPhiRAxioms.lean: 6 results; each exactly [propext, Classical.choice, Quot.sound].' in summary
assert 'CheckPoleAxioms.lean: 26 results; each exactly [propext, Classical.choice, Quot.sound].' in summary
build=record['commands'][-1]
seconds=(datetime.datetime.fromisoformat(build['finished_utc'])-datetime.datetime.fromisoformat(build['started_utc'])).total_seconds()
jobs=record['jobs']
date=datetime.datetime.fromisoformat(build['finished_utc']).astimezone().strftime('%Y-%m-%d')
build_text=f'''The complete release was checked on {date} on macOS, Apple silicon, with `lake clean`,
`lake exe cache get`, then plain `lake build`. All three commands exited successfully. The build ended with

    Build completed successfully ({jobs} jobs).

The `lake build` step took {seconds/60:.1f} minutes. [BuildV12Clean.out](BuildV12Clean.out) is the full output;
[BuildV12Clean.tail.out](BuildV12Clean.tail.out) contains its final 35 lines. `CleanV12.out`, `CacheGet.out` and
`release-tools/build-record.json` record the clean/cache steps, exit codes and times. `Toolchain.out` records the
compiler version. Lake used its default scheduling; the job count above is Lake's total, not a CPU count.

The cache command restored the matching local Mathlib cache, with no downloads in the final run. PrimeNumberTheoremAnd and all release modules then compiled
from source after `lake clean`; no compiled artifacts from either input library were used.'''
axioms_text='''`CheckAxioms.lean` imports the complete `Phi2NB` library and prints the axioms and types of 16 results: the four
H∞ theorems and 12 retained results, including every main theorem in Appendix A. `CheckPoleAxioms.lean` does the same
for the 26 declarations of Theorem C (the pole at 2B and the RH criterion) that are listed in the section on intermediate
results, among them its six main statements `phi2_hinf_pole_twoBsup`, `phi2_hinf_pole_twoBsup'`,
`phi2_hinf_pole_twoBsup_of_continuation`, `phi2_hinf_rh_iff_no_real_pole`, `phi2_hinf_rh_iff_no_real_pole'` and
`phi2_hinf_rh_iff_no_real_pole_of_continuation`. Every axiom list is exactly

    [propext, Classical.choice, Quot.sound]

The captured outputs are [CheckAxioms.out](CheckAxioms.out) and [CheckPoleAxioms.out](CheckPoleAxioms.out). The original `CheckPhiRAxioms.lean` also gives those
same three axioms for each of its six results; its fresh output is [CheckPhiRAxioms.out](CheckPhiRAxioms.out).
`AxiomAudit.out` records the exact-list checks. `StatementAudit.out` records the statement comparison, and
`SourceAudit.out` records the source scan, definition comparisons, pins and file counts.

The release-owned Lean files contain no `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `extern`
construct. These are the three standard axioms of Lean's logic. The pinned PrimeNumberTheoremAnd dependency
prints two existing `declaration uses 'sorry'` warnings in `Wiener.lean`; the axiom outputs show that neither is
in the dependency closure of the audited results. The release's warnings are linter and deprecation notices.

The extraction and audit tools in `release-tools/` use the original read-only input paths recorded for this
build. They are not needed to build or use the library.'''
p=root/'README.md';text=p.read_text()
assert '<!-- BUILD -->' in text and '<!-- AXIOMS -->' in text
text=text.replace('<!-- BUILD -->',build_text).replace('<!-- AXIOMS -->',axioms_text)
p.write_text(text)
# Preserve the exact author block from v1.1.
v11=Path('/Volumes/Sheridan/sandbox/_Scratch/math-musings-phi2-bundle-v3/repo/phi2-natural-boundary/README.md')
assert p.read_text().splitlines()[2:4]==v11.read_text().splitlines()[2:4]
base='phi2-natural-boundary-v1.2'
fixed=['.gitignore','lean-toolchain','lakefile.toml','lake-manifest.json','LICENSE','README.md',
       'STATEMENT-DIFF.md','Phi2NB.lean','CheckAxioms.lean','CheckPhiRAxioms.lean',
       'CheckPoleAxioms.lean','CheckPoleAxioms.out','CheckAxioms.out','CheckPhiRAxioms.out','AxiomAudit.out','SourceAudit.out','StatementAudit.out',
       'BuildV12Clean.out','BuildV12Clean.tail.out','CleanV12.out','CacheGet.out','Toolchain.out']
files=[root/n for n in fixed]+sorted((root/'Phi2NB').rglob('*.lean'))
files+=sorted(p for p in (root/'release-tools').iterdir() if p.suffix in {'.py','.in','.json'})
archive=root/(base+'.tar.gz')
with tarfile.open(archive,'w:gz') as tar:
    for p in files:tar.add(p,arcname=base+'/'+p.relative_to(root).as_posix(),recursive=False)
sha=hashlib.sha256(archive.read_bytes()).hexdigest()
(root/(archive.name+'.sha256')).write_text(sha+'  '+archive.name+'\n')
with tarfile.open(archive) as tar:
    names=tar.getnames()
    assert not any('/.lake/' in n or '/.git/' in n or '/build/' in n for n in names)
    assert all(base+'/'+p.relative_to(root).as_posix() in names for p in (root/'Phi2NB').rglob('*.lean'))
print('Archive:',archive.name,'files:',len(files),'bytes:',archive.stat().st_size)
print('SHA256:',sha)
print('Build jobs:',jobs,'build minutes:',round(seconds/60,1))

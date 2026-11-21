"""Capture fresh axiom outputs and check the exact axiom list for every audited result."""
from pathlib import Path
import re,subprocess,sys
root=Path(__file__).resolve().parent.parent
expected_axioms=['propext','Classical.choice','Quot.sound']
summary=[]
for source in ['CheckAxioms.lean','CheckPhiRAxioms.lean','CheckPoleAxioms.lean']:
    output=root/Path(source).with_suffix('.out')
    expected=re.findall(r'^#print axioms (\S+)',(root/source).read_text(),re.M)
    with output.open('w') as f:
        result=subprocess.run(['lake','env','lean',source],cwd=root,stdout=f,stderr=subprocess.STDOUT)
    if result.returncode:
        print(source,'failed:',result.returncode,flush=True);sys.exit(result.returncode)
    rows=re.findall(r"^'(\S+)' depends on axioms:\s*\[([^\]]*)\]",output.read_text(),re.M)
    assert len(rows)==len(expected),(source,'axiom row count',len(rows),len(expected))
    assert set(n for n,_ in rows)==set(expected),(source,'axiom names')
    for name,axioms in rows:
        actual=[a.strip() for a in axioms.split(',')]
        assert actual==expected_axioms,(name,actual)
    line=f'{source}: {len(rows)} results; each exactly [propext, Classical.choice, Quot.sound].'
    summary.append(line);print(line,flush=True)
(root/'AxiomAudit.out').write_text('\n'.join(summary)+'\n')
for script,output in [('statement_diff.py','StatementAudit.out'),('audit_release.py','SourceAudit.out')]:
    with (root/output).open('w') as f:
        result=subprocess.run([sys.executable,'release-tools/'+script],cwd=root,stdout=f,stderr=subprocess.STDOUT)
    if result.returncode:sys.exit(result.returncode)
    print(script,'passed',flush=True)

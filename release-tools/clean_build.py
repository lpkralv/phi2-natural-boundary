"""Run the final source-clean release build, restoring only the Mathlib cache."""
from pathlib import Path
import datetime,json,os,re,subprocess,sys
root=Path(__file__).resolve().parent.parent
os.chdir(root)
env=dict(os.environ,MATHLIB_CACHE_DIR=str(root/'build/mathlib-cache'))
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commands':[]}
for command,output in [(['lake','clean'],'CleanV12.out'),(['lake','exe','cache','get'],'CacheGet.out'),(['lake','build'],'BuildV12Clean.out')]:
    start=datetime.datetime.now(datetime.timezone.utc)
    with open(output,'w') as log:
        p=subprocess.run(command,env=env,stdout=log,stderr=subprocess.STDOUT)
    entry={'command':command,'output':output,'exit_code':p.returncode,'started_utc':start.isoformat(),'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    record['commands'].append(entry)
    if command==['lake','build']:
        text=(root/output).read_text()
        tail='\n'.join(text.splitlines()[-35:])+'\n'
        (root/'BuildV12Clean.tail.out').write_text(tail)
        m=re.search(r'Build completed successfully \((\d+) jobs\)',text)
        if m:record['jobs']=int(m.group(1))
    (root/'release-tools/build-record.json').write_text(json.dumps(record,indent=2)+'\n')
    print(' '.join(command),'exit',p.returncode,flush=True)
    if p.returncode:sys.exit(p.returncode)

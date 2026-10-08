"""Pin already completed direct checks and exact blueprint sources to a Git commit."""
from pathlib import Path
import hashlib,json,subprocess,time
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-gaussian')
b=Path('/private/tmp/tnlean-source-gaussian');bp=Path((b/'blueprint-dir').read_text().strip())
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();qrev='b2521d2a2843d824ce85a4d94bf4b60d322d6c6f'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def committed(p):return subprocess.check_output(['git','-C',str(root),'show',rev+':'+p])
build=read(b/'strict-checks/build-commands.json');audit=read(b/'imported-audit/audit-command.json')
for row in build['builds']:
 assert hashlib.sha256(committed(row['source_path'])).hexdigest()==row['source_sha256']==sha(root/row['source_path'])
 assert sha(Path(row['artifact']))==row['artifact_sha256']
 assert row['returncode']==0 and not (b/'strict-checks'/(row['module']+'.log')).read_bytes()
assert len(build['builds'])==17
for r in read(b/'source-freeze.json')['files']:assert sha(root/r['path'])==r['sha256']
start=time.monotonic();deps=read(b/'imported-audit/imported-dependencies.json')
for r in deps:assert sha(Path(r['artifact']))==r['sha256'],r['module']
save(b/'artifact-pin-check.json',{'source_revision':rev,'artifact_count':len(deps),'all_hashes_unchanged':True,'seconds':round(time.monotonic()-start,3),'dependency_manifest_sha256':sha(b/'imported-audit/imported-dependencies.json')})
for p,r in [(b/'strict-checks/build-commands.json',build),(b/'imported-audit/audit-command.json',audit)]:
 r['source_revision']=rev;r['all_source_bytes_match_git_commit']=True;save(p,r)
# Check the copied sources against the immutable Git tree in one batch.
paths=read(bp/'TNLean-source-sha256.json')
paths.update({p:s for p,s in read(bp/'blueprint-source-sha256.json').items() if Path(p).name not in ['focused.tex','content-focused.tex','web.tex']})
paths.update({p:sha(root/p) for p in ['blueprint/src/content.tex','lakefile.toml','lake-manifest.json','lean-toolchain','tenkz.toml']})
proc=subprocess.Popen(['git','-C',str(root),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for p,expected in paths.items():
 proc.stdin.write((rev+':'+p+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();assert len(header)==3,(p,header)
 data=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n';assert hashlib.sha256(data).hexdigest()==expected,p
proc.stdin.close();assert proc.wait()==0
save(bp/'snapshot-commit-check.json',{'source_revision':rev,'qic_revision':qrev,'checked_files':len(paths),'all_hashes_match':True,'source_sha256':paths})
save(bp/'source-revision.json',{'base_revision':build['base_revision'],'source_revision':rev,'qic_revision':qrev,'scope':'Already rendered exact source bytes checked against the committed tree; source-only snapshot and focused rendering, no Lake build.'})
save(bp/'visual-review.json',{'source_revision':rev,'pdf_pages_reviewed':[33,34,35,36,37],'result':'pass','notes':'Every page of the new chapter inspected. Equations, quantifiers, tags and proof text are readable; no new chapter overflow. One inherited 0.99057pt heading overfull box remains in the common-source chapter.'})
print('PIN_PASS',rev,len(deps),len(paths))

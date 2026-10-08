#!/usr/bin/env python3
"""Record completed exact-source checks; do not compile Lean or change proof files."""
import argparse,gzip,hashlib,json,shlex,shutil,subprocess
from pathlib import Path
SLUG='8769-message-resource-bounds'

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def require(x,msg):
 if not x:raise RuntimeError(msg)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--records',type=Path,required=True);ap.add_argument('--revision',required=True);a=ap.parse_args()
 root,b=a.root.resolve(),a.records.resolve();rev=a.revision;bp=Path((b/'blueprint-dir').read_text().strip());out=root/'docs/provenance/evidence'/SLUG
 builds=read(b/'strict-checks/build-commands.json');audit=read(b/'imported-audit/audit-command.json');axioms=read(b/'imported-audit/axiom-dependencies.json');rows=read(b/'declarations.json');old=read(b/'inherited-provenance-refresh.json')
 require(builds['source_revision']==audit['source_revision']==rev,'Source pin differs')
 require(len(rows)==65 and len(old)==0 and len(axioms)==65,'Declaration counts differ')
 require(set(axioms)=={r['declaration'] for r in rows+old},'Incomplete imported audit')
 require(all(set(x)<={'propext','Classical.choice','Quot.sound'} for x in axioms.values()),'Unexpected axioms')
 require(sha(b/'imported-audit/axioms.log')==audit['log_sha256'],'Audit log changed')
 require(read(b/'artifact-pin-check.json')['all_hashes_unchanged'],'Artifacts were not pinned')
 require(len(builds['builds'])==14,'Expected complete 14-module affected closure')
 for r in builds['builds']:
  data=subprocess.check_output(['git','-C',str(root),'show',rev+':'+r['source_path']])
  require(hashlib.sha256(data).hexdigest()==r['source_sha256']==sha(root/r['source_path']),'Compiled bytes differ: '+r['source_path'])
  require(r['returncode']==0 and '-DwarningAsError=true' in r['command'],'Strict compilation missing')
  require(sha(b/'strict-checks'/(r['module']+'.log'))==r['log_sha256'],'Build log changed')
 require(read(b/'declaration-check/command.json')['returncode']==0,'Full declaration presence check failed')
 require(read(bp/'source-revision.json')['source_revision']==rev,'Blueprint not pinned')
 require(read(bp/'sync.json')['sync_ok'],'Source synchronization failed')
 require(set(read(bp/'tag-coverage.json').values())=={1},'New tags not exact-once')
 require(read(bp/'visual-review.json')['result']=='pass','Visual review absent')
 out.mkdir(parents=True,exist_ok=True);compressed={}
 def cp(p,rel=None,compress=False):
  rel=rel or p.name;dest=out/rel;dest.parent.mkdir(parents=True,exist_ok=True);data=p.read_bytes();dest.write_bytes(gzip.compress(data,mtime=0) if compress else data)
  if compress:compressed[rel]={'uncompressed_sha256':hashlib.sha256(data).hexdigest(),'uncompressed_bytes':len(data)}
 for name in ['env.json','build-plan.json','source-freeze.json','source-preservation.json','declarations.json','inherited-provenance-refresh.json','artifact-pin-check.json','format-command.json','environment-preparation.json','notice-integrity-check.json','handoff.json']:
  cp(b/name)
 for p in (b/'original-sources').rglob('*.lean'):cp(p,'original-sources/'+str(p.relative_to(b/'original-sources'))+'.gz',True)
 for p in (b/'strict-checks').glob('*.log'):cp(p,'strict-checks/'+p.name+'.gz',True)
 cp(b/'strict-checks/build-commands.json','strict-checks/build-commands.json')
 for p in (b/'imported-audit').iterdir():
  if p.name in ['imported-dependencies.json','imported-modules.json','Axioms.lean']:cp(p,'imported-audit/'+p.name+'.gz',True)
  else:cp(p,'imported-audit/'+p.name)
 for p in (b/'declaration-check').iterdir():
  zipped=p.name=='lean_declarations.txt';cp(p,'declaration-check/'+p.name+('.gz' if zipped else ''),zipped)
 cp(b/'tactic-pattern-scan.log','tactic-pattern-scan.log.gz',True)
 for folder in ['initial-checks']:
  for p in (b/folder).rglob('*'):
   if p.is_file():cp(p,'initial-checks/'+folder+'/'+str(p.relative_to(b/folder))+'.gz',True)
 for name in ['check-message-resource-bounds.py','audit-message-resource-bounds.py','check-message-resource-declarations.py','pin-message-resource-bounds.py','prepare-message-resource-bounds.py','check-message-resource-notices.py','format-message-resource-bounds.py']:
  cp(Path('/tmp')/name,'verification-scripts/'+name)
 for name in ['commands.json','source-revision.json','tag-coverage.json','visual-review.json','scoped_web_check.py']:
  cp(bp/name,'blueprint/'+name)
 for name in ['TNLean-source-sha256.json','QICLean-source-sha256.json','blueprint-source-sha256.json','snapshot-commit-check.json','qic-snapshot-check.json','dependency-graph.json','sync.json','full-lean-decls.txt']:
  cp(bp/name,'blueprint/'+name+'.gz',True)
 for p in bp.glob('*.log'):cp(p,'blueprint/'+p.name+'.gz',True)
 cp(bp/'blueprint/src/focused.log','blueprint/final-tex.log.gz',True)
 cp(bp/'blueprint/src/focused.pdf','blueprint/focused.pdf')
 for p in bp.glob('final-page-*.png'):cp(p,'blueprint/'+p.name)
 for name in ['focused.tex','content-focused.tex','web.tex']:cp(bp/'blueprint/src'/name,'blueprint/render-inputs/'+name+'.gz',True)
 for name in ['texra-blueprint.toml','texra-blueprint.full.toml']:cp(bp/name,'blueprint/render-inputs/'+name)
 cp(Path('/tmp/verify-message-resource-blueprint.py'),'blueprint/verify-blueprint.py')
 # The canonical checker and schema are versioned at the source revision.
 cp(root/'scripts/check_openai_provenance.py','canonical/check_openai_provenance.py')
 cp(root/'docs/provenance/openai-math.schema.json','canonical/openai-math.schema.json')
 lines=['Direct Lean checks with the package options and warnings as errors.',f'Source revision: {rev}','Scope: complete affected 14-module TNLean import closure; no local Lake build.',f'LEAN_PATH={builds["LEAN_PATH"]}','']
 for r in builds['builds']:
  lines += [f'Source: {r["source_path"]}',f'Source SHA256: {r["source_sha256"]}',f'Working directory: {r["cwd"]}',f'Command: {shlex.join(r["command"])}',f'Exit code: {r["returncode"]}',f'Elapsed seconds: {r["seconds"]}',f'Artifact SHA256: {r["artifact_sha256"]}','Diagnostics: none.','']
 (out/'direct-build.log').write_text('\n'.join(lines))
 (out/'axioms.log').write_text(f'Source revision: {rev}\nWorking directory: {audit["cwd"]}\nCommand: {shlex.join(audit["command"])}\nExit code: {audit["returncode"]}\n\n'+(b/'imported-audit/axioms.log').read_text())
 def verification(row):
  build=next(x for x in builds['builds'] if x['source_path']==row['path'])
  cmds=[]
  for kind,cmd,log in [('build',build['command'],'direct-build.log'),('axioms',audit['command'],'axioms.log')]:
   cmds.append({'kind':kind,'command':shlex.join(cmd),'exit_code':0,'log':str((out/log).relative_to(root)),'sha256':sha(out/log)})
  return {'result':'passed','repository':'LionSR/TNLean','revision':rev,'commands':cmds}
 paper={'version':'September 24, 2026','path':'preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex','labels':['eq:compression-subset-expansion']}
 scope=('Constructs the exact finite expansion of messages into the existing local monomials, including weighted gates and their original-circuit realization. Proves the product-of-dimensions count and coefficient formulas, polynomial branch and sample bounds after the physical output exchange, and actual link alphabet, locality and degree bounds. Private input dimensions are finite but have no numerical bound. A contraction-of-local-tensors identity for the sampled physical operator remains separate.')
 entries=[{'id':r['id'],'status':'ported','reuse_kind':'original','upstream':None,'downstream':{'repository':'LionSR/TNLean','path':r['path'],'declaration':r['declaration'],'name_status':'declared'},'paper_sources':[{**paper,'labels':[r['paper_label']]}],'license':'Apache-2.0','notices':[],'changes':['Independently formalized from the manuscript; no upstream Lean proof text reused.',scope],'verification':verification(r),'no_upstream_proof_text_reused':True} for r in rows]
 save(root/'docs/provenance/openai-math.d'/(SLUG+'.json'),{'schema_version':1,'source':{'repository':'openai/math','commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a'},'entries':entries})
 previous=[]
 for shard in sorted({r['shard'] for r in old}):
  p=root/shard;data=read(p);prior=subprocess.check_output(['git','-C',str(root),'show',rev+':'+shard]);arch=out/'historical-shards'/(p.name+'.gz');arch.parent.mkdir(exist_ok=True);arch.write_bytes(gzip.compress(prior,mtime=0))
  targets={r['id']:r for r in old if r['shard']==shard}
  original=json.loads(prior);original_by_id={e['id']:e for e in original['entries']}
  for e in data['entries']:
   if e['id'] not in targets:continue
   original_e=original_by_id[e['id']];require({k:v for k,v in e.items() if k!='verification'}=={k:v for k,v in original_e.items() if k!='verification'},'Inherited entry changed outside verification')
   previous.append({'shard':shard,'id':e['id'],'previous_verification':original_e['verification']});e['verification']=verification(targets[e['id']])
  save(p,data)
 save(out/'inherited-verification-history.json',previous)
 # Preserve the independently checked incoming sources and their historical records.
 for folder in sorted({row['original_evidence'] for row in read(b/'handoff.json')['sources']}):
  folder=Path(folder);name=folder.parent.name+'-'+folder.name
  for p in folder.rglob('*'):
   if not p.is_file() or p.suffix in ['.olean','.ilean','.c','.o'] or '__pycache__' in p.parts:continue
   zipped=p.suffix!='.gz';cp(p,'historical-evidence/'+name+'/'+str(p.relative_to(folder))+('.gz' if zipped else ''),zipped)
 cp(Path(__file__),'record-evidence.py');cp(Path('/tmp/validate-message-resource-bounds-evidence.py'),'validate-evidence.py')
 save(out/'source-revision.json',{'source_revision':rev,'base_revision':builds['base_revision'],'qic_revision':'caac4b549c1b5c14fcedbee647567f51e27b296d'})
 save(out/'compression.json',compressed)
 require((out/'README.md').is_file(),'Write the mathematical and verification summary first')
 save(out/'manifest.json',{'sha256':{str(p.relative_to(out)):sha(p) for p in sorted(out.rglob('*')) if p.is_file() and p.name!='manifest.json' and '__pycache__' not in p.parts}})
 print('RECORDED',len(entries),'NEW',len(previous),'REFRESHED',len(list(out.rglob('*'))),'FILES')
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Validate the recorded deterministic correction evidence without compiling Lean."""
import argparse,gzip,hashlib,json,re,subprocess
from pathlib import Path

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(x,msg):
 if not x:raise RuntimeError(msg)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=Path(__file__).resolve().parent
 manifest=read(out/'manifest.json')['sha256']
 for p,h in manifest.items():require(sha(out/p)==h,'Evidence bytes differ: '+p)
 pin=read(out/'source-revision.json');rev=pin['source_revision'];rows=read(out/'declarations.json');old=read(out/'inherited-provenance-refresh.json')
 builds=read(out/'strict-checks/build-commands.json');axioms=read(out/'imported-audit/axiom-dependencies.json');audit=read(out/'imported-audit/audit-command.json')
 require(len(rows)==67 and len(old)==24 and set(axioms)=={r['declaration'] for r in rows+old},'Declaration audit is incomplete')
 require(all(set(xs)<={'propext','Classical.choice','Quot.sound'} for xs in axioms.values()),'Unexpected axiom dependency')
 require(builds['source_revision']==audit['source_revision']==rev,'Source revisions differ')
 require(sha(out/'imported-audit/axioms.log')==audit['log_sha256'],'Imported audit log differs')
 for r in builds['builds']:
  data=subprocess.check_output(['git','-C',str(root),'show',rev+':'+r['source_path']])
  require(hashlib.sha256(data).hexdigest()==r['source_sha256']==sha(root/r['source_path']),'Compiled source differs: '+r['source_path'])
  log=gzip.decompress((out/'strict-checks'/(r['module']+'.log.gz')).read_bytes())
  require(not log and r['returncode']==0 and '-DwarningAsError=true' in r['command'],'Strict check failed')
 require(len(builds['builds'])==35,'Incomplete affected closure')
 depbytes=gzip.decompress((out/'imported-audit/imported-dependencies.json.gz').read_bytes());deps=json.loads(depbytes)
 require(len(deps)==14632 and hashlib.sha256(depbytes).hexdigest()==audit['imported_dependencies_sha256'],'Imported dependency manifest differs')
 require(read(out/'artifact-pin-check.json')['all_hashes_unchanged'],'Artifact pin check missing')
 require(read(out/'declaration-check/command.json')['checked_count']==20877,'Full declaration count differs')
 newshard=read(root/'docs/provenance/openai-math.d/8769-source-corrections.json')
 require({e['id'] for e in newshard['entries']}=={r['id'] for r in rows},'New provenance set differs')
 for p in {r['shard'] for r in old}:
  before=json.loads(gzip.decompress((out/'historical-shards'/(Path(p).name+'.gz')).read_bytes()));after=read(root/p)
  targets={r['id'] for r in old if r['shard']==p}
  require(before.keys()==after.keys(),'Inherited shard structure differs')
  require(len(before['entries'])==len(after['entries']),'Inherited entry count differs')
  for x,y in zip(before['entries'],after['entries']):
   require(x['id']==y['id'],'Inherited entry order differs')
   if x['id'] in targets:
    require({k:v for k,v in x.items() if k!='verification'}=={k:v for k,v in y.items() if k!='verification'},'Inherited non-verification content differs')
    require(y['verification']['revision']==rev,'Inherited verification not refreshed')
   else:require(x==y,'Unrelated inherited entry differs')
 tags=read(out/'blueprint/tag-coverage.json');require(set(tags)=={r['declaration'] for r in rows} and set(tags.values())=={1},'Blueprint tag coverage differs')
 graph=json.loads(gzip.decompress((out/'blueprint/dependency-graph.json.gz').read_bytes()));require(not graph['cycles'] and not graph['duplicate_labels'],'Dependency graph failed')
 require(read(out/'blueprint/visual-review.json')['result']=='pass','Visual review absent')
 require(read(out/'blueprint/source-revision.json')['source_revision']==rev,'Blueprint revision differs')
 for p in ['scripts/check_openai_provenance.py','docs/provenance/openai-math.schema.json']:
  require((root/p).read_bytes()==(out/'canonical'/Path(p).name).read_bytes(),'Canonical validator changed')
 print(f'Evidence valid: {len(manifest)} files, 35 strict module checks, 91 standard-axiom declarations, 14,632 imported artifacts, 20,877 compiled blueprint names.')
 print('This validates recorded checks; it does not run Lean or replace the full canonical provenance check.')
if __name__=='__main__':main()

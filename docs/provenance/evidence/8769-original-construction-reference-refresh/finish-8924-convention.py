"""Deferred exact-byte refresh after the registered paper-gap name correction."""
from pathlib import Path
import argparse, gzip, hashlib, json, os, re, shlex, shutil, subprocess, time

ROOT = Path('/private/tmp/tnlean-convention-reference-refresh')
REPO = Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-original-compression-sampling')
REV = '98d16bce7908740fa90676f850ce7d399dda1230'
SOURCE = 'TNLean/PEPS/Approximation/DistributedConstruction.lean'
SLUG = '8769-original-construction-reference-refresh'
def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x): p.write_text(json.dumps(x,indent=2)+'\n')

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--clearance',type=Path,required=True)
args=parser.parse_args()
clear=read(args.clearance)
assert clear.get('verification_released') is True and clear.get('scope')==SLUG
cfg=read(ROOT/'env.json'); summary=read(ROOT/'summary.json')
assert summary['source_revision']==REV
assert sha(REPO/SOURCE)==summary['source_sha256']==sha(ROOT/'src'/SOURCE)
assert subprocess.check_output(['git','-C',str(REPO),'rev-parse','HEAD'],text=True).strip()==REV
for name in ['strict','axioms']:
 row=read(ROOT/(name+'-command.json'))
 assert row['returncode']==0 and row['log_sha256']==sha(ROOT/(name+'.log'))
 assert '-j1' in row['command']

# Preserve the already successful audit, then record its exact imported closure.
previous=ROOT/'clean-audit-before-import-list'
assert not previous.exists();previous.mkdir()
for name in ['axioms.log','axioms-command.json','axiom-dependencies.json']:
 shutil.copy2(ROOT/name,previous/name)
shutil.copy2(ROOT/'src/Audit.lean',previous/'Audit.lean')
p=ROOT/'src/Audit.lean'
p.write_text(p.read_text()+ '\nrun_cmd do\n  let e ← Lean.getEnv\n  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)\n  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))\n')
cmd=[cfg['lean'],'-j1',*cfg['options'],'-DwarningAsError=true','Audit.lean']
env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];env['LEAN_NUM_THREADS']='1'
t=time.monotonic();result=subprocess.run(cmd,cwd=ROOT/'src',env=env,capture_output=True,text=True)
(ROOT/'axioms.log').write_text(result.stdout+result.stderr)
audit={'command':cmd,'cwd':str(ROOT/'src'),'returncode':result.returncode,'seconds':time.monotonic()-t,
 'source_revision':REV,'source_path':SOURCE,'source_sha256':summary['source_sha256'],
 'audit_source_sha256':sha(p),'log_sha256':sha(ROOT/'axioms.log')}
save(ROOT/'axioms-command.json',audit)
assert result.returncode==0,result.stdout+result.stderr
found={a:[v.strip() for v in b.split(',') if v.strip()] for a,b in
 re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",result.stdout+result.stderr,re.S)}
assert set(found)==set(summary['public_names'])
assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in found.values())
save(ROOT/'axiom-dependencies.json',found)

old={r['module']:r for r in read(Path('/private/tmp/tnlean-original-compression-sampling/imported-audit/imported-dependencies.json'))}
paths=[Path(p) for p in cfg['LEAN_PATH'].split(':')]
rows=[]
for mod in read(ROOT/'src/imported-modules.json'):
 rel=Path(mod.replace('.','/')+'.olean')
 path=next(p/rel for p in paths if (p/rel).is_file())
 digest=sha(path)
 if mod!='TNLean.PEPS.Approximation.DistributedConstruction':
  assert digest==old[mod]['sha256'],mod
 rows.append({'module':mod,'artifact':str(path),'resolved_artifact':str(path.resolve()),
              'sha256':digest,'bytes':path.stat().st_size})
save(ROOT/'imported-dependencies.json',rows)
save(ROOT/'artifact-pin-check.json',{'all_hashes_unchanged':True,
 'exception':'DistributedConstruction was freshly compiled from the recorded source revision.',
 'imported_artifacts':len(rows),'imported_dependencies_sha256':sha(ROOT/'imported-dependencies.json')})
summary.update({'checks':[read(ROOT/'strict-command.json'),audit],
 'artifact_snapshots_deferred':False,'imported_artifacts':len(rows),
 'scope':'One comment-only source-path correction; all mathematical tokens unchanged.'})
save(ROOT/'summary.json',summary)

out=REPO/'docs/provenance/evidence'/SLUG
assert not out.exists();out.mkdir(parents=True)
for name in ['summary.json','strict-command.json','axioms-command.json','axiom-dependencies.json',
             'artifact-pin-check.json','env.json','strict.log','axioms.log']:
 shutil.copy2(ROOT/name,out/name)
shutil.copy2(p,out/'Audit.lean')
shutil.copy2(ROOT/'src'/SOURCE,out/'DistributedConstruction.lean')
for folder in ['initial-hash-command-notices','clean-audit-before-import-list']:
 shutil.copytree(ROOT/folder,out/folder)
for name in ['imported-dependencies.json','initial-ci-provenance-failure.log']:
 (out/(name+'.gz')).write_bytes(gzip.compress((ROOT/name).read_bytes(),mtime=0))
save(out/'compressed-evidence.json',[{'path':name+'.gz','uncompressed_sha256':sha(ROOT/name),
 'sha256':sha(out/(name+'.gz'))} for name in ['imported-dependencies.json','initial-ci-provenance-failure.log']])
(out/'README.md').write_text('''# Registered paper-gap reference correction

The source revision corrects only the path of the nonempty-party convention
note. The exact revised Lean source passes strict direct compilation with the
package options, one worker, and warnings as errors. Its five declarations have
only the standard Lean axioms. The imported artifacts match the earlier frozen
verification except for this freshly compiled module.

The earlier successful evidence remains unchanged. This supplement retains the
CI provenance rejection caused by the changed comment bytes, the initial audit
with hash-command notices, and both subsequent successful imported audits. It
does not claim a new local Lake build or a repeat of the complete provenance check.
''')
shard=REPO/'docs/provenance/openai-math.d/8769-original-compression-sampling.json'
ledger=read(shard); changed=0
for e in ledger['entries']:
 if e['downstream']['path']!=SOURCE:continue
 changed+=1;e['verification']['revision']=REV;e['verification']['commands']=[]
 for kind,name in [('build','strict'),('axioms','axioms')]:
  row=read(ROOT/(name+'-command.json'));log=out/(name+'.log')
  e['verification']['commands'].append({'kind':kind,'command':shlex.join(row['command']),
    'exit_code':0,'log':str(log.relative_to(REPO)),'sha256':sha(log)})
 e['changes'].append('Refreshed exact-byte evidence after correcting the registered paper-gap filename in the module comment; mathematical tokens are unchanged.')
assert changed==5
save(shard,ledger)
save(out/'manifest.json',[{'path':str(p.relative_to(out)),'sha256':sha(p),'bytes':p.stat().st_size}
 for p in sorted(out.rglob('*')) if p.is_file()])
print('PASS: five exact-source entries refreshed; imported artifacts',len(rows),flush=True)

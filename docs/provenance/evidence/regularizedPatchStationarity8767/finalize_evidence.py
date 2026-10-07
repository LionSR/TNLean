"""Bind unchanged actual compiler evidence to the published immutable source tree.
No compiler invocation and no external-service mutation are performed.
"""
from pathlib import Path
import json,hashlib,subprocess,shlex
B=Path('/workspace/scratch/7637e06d0fc2');D=B/'patch-coordinate-validation';R=B/'TNLean-patch-coordinate-stationarity'
PUB='ac1fdd4c8a17b9811d15b8f2e9f05798a427c6fd';LOCAL='0580e6c660f20c30f2faf4bbfa385be84cc0936b';BASE='e9311cbbaf55517308f416b008df5ddafcc047c9';CURRENT='a5ae1ba4f0238984e0e81eb81312ebdf6b6f9d27'
E=R/'docs/provenance/evidence/regularizedPatchStationarity8767'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
man=json.loads((D/'source-publication-manifest.json').read_text())
assert man['source_commit']==LOCAL and man['base']==BASE and len(man['files'])==68
assert git('rev-parse','HEAD').decode().strip()==PUB
assert git('show','-s','--format=%P',PUB).decode().strip()==BASE
assert git('rev-parse',PUB+'^{tree}').decode().strip()==man['source_tree']=='5e001153aa873e85e713ba36c6931f62e1b40ae2'
assert git('rev-parse',PUB+'^{tree}')==git('rev-parse',LOCAL+'^{tree}')
assert not git('status','--porcelain')
for row in man['files']:
 p=R/row['path'];assert sha(p)==row['sha256'];data=git('show',PUB+':'+row['path']);assert p.read_bytes()==data
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['blob_sha']
runs=json.loads((D/'final-runs.json').read_text());by_module={r['module']:r for r in runs}
for r in runs:
 assert r['exit_code']==0 and r['source_closure_unchanged']
 assert r['source_closure_sha256_before']==r['source_closure_sha256_after']
 assert all(sha(Path(p))==h for p,h in r['source_closure_sha256_before'].items())
 assert sha(Path(r['source']))==r['source_sha256']
 p=Path(r['source'])
 if p.is_relative_to(R):assert p.read_bytes()==git('show',PUB+':'+p.relative_to(R).as_posix())
 assert (E/'lean/logs'/(r['module']+'.log')).read_bytes()==Path(r['log']).read_bytes()
attestation={'published_source_revision':PUB,'locally_checked_source_revision':LOCAL,'identical_git_tree':man['source_tree'],'checked_parent':BASE,'checked_parent_status':'published unmerged TNLean#8822 head when these compiler checks ran','newer_published_parent':CURRENT,'newer_parent_relation':'reported and locally resolved only; this leaf has not integrated or compiled against the later current-parent/cache-only refresh','accepted_qic_pin':man['accepted_qic_revision'],'source_files':man['files'],'published_changed_files_verified':68,'native_source_artifact_pairs':85,'public_declarations_and_stock_axiom_reports':18,'strict_final_records':8,'new_compiler_invocations':0,'raw_logs_rewritten':False,'full_local_lake_build':False,'remote_mutations_by_leaf_worker':False}
dump(E/'source-tree-attestation.json',attestation)
ledger_path=R/'docs/provenance/openai-math.d/regularizedPatchStationarity8767.json';ledger=json.loads(ledger_path.read_text())
assert len(ledger['entries'])==18
for e in ledger['entries']:
 assert e['status']=='planned' and e['downstream']['name_status']=='proposed' and e['verification']=={'result':'pending'}
 module=e['downstream']['path'][:-5].replace('/','.')
 e['status']='ported';e['downstream']['name_status']='declared'
 e['verification']={'result':'passed','repository':'LionSR/TNLean','revision':PUB,'commands':[]}
 for kind,r in [('build',by_module[module]),('axioms',by_module['PatchCoordinateAxioms'])]:
  log=E/'lean/logs'/(r['module']+'.log')
  e['verification']['commands'].append({'kind':kind,'command':shlex.join(r['command']),'exit_code':0,'log':log.relative_to(R).as_posix(),'sha256':sha(log)})
dump(ledger_path,ledger)
p=R/'docs/formalization/peps-regularized-patch-stationarity.md';s=p.read_text()
s=s.replace('The integration base is published but unmerged','The exact source parent used for the preserved compiler checks is published but unmerged')
s=s.replace('pending QICLean #577 extraction.','QICLean #577 extraction.')
old='''original-proof rows. They remain `planned`/`proposed` with pending verification
until immutable source and exact native evidence are published. The earlier
minimum's verification records are not reused as evidence for these declarations.'''
new=f'''original-proof rows. This evidence child marks only these 18 rows as
`ported`/`declared`, with passing exact-source verification at published immutable
source revision [`{PUB}`](https://github.com/LionSR/TNLean/commit/{PUB}).
The source commit itself retained planned rows until this object existed.
Its tree is byte-identical to the locally checked commit
`{LOCAL}`. All 68 changed source, documentation, and evidence
files were checked against the published Git tree. The earlier minimum's
verification records are not reused as evidence for these declarations.

The later parent refresh `{CURRENT}` is separate from the
originally checked parent `{BASE}`. Integrating against
that newer parent and checking exact-head CI remain separate gates; no
recompilation or retrospective current-parent build claim is made here.'''
assert old in s;s=s.replace(old,new)
old='''No full Lake build, aggregate `checkdecls`, full blueprint web/PDF build, or
exact-head CI pass is claimed.'''
new='''All compiler and documentation logs are preserved byte for byte. This
metadata child performed no new compiler invocation. The publication attestation
is retained in
`docs/provenance/evidence/regularizedPatchStationarity8767/source-tree-attestation.json`.
Earlier validation reports remain historical snapshots, including their then-pending
publication status; the active ledger and this attestation record its resolution.
No full Lake build, aggregate `checkdecls`, full blueprint web/PDF build, or
exact-head CI pass is claimed.'''
assert old in s;s=s.replace(old,new);p.write_text(s)
(E/'README.md').write_text(f'''# Coordinate first variation: immutable-source evidence

Published source: `{PUB}`.
Locally checked source: `{LOCAL}`.
Exact shared tree: `{man['source_tree']}`.
Checked source parent: `{BASE}`, the then-published unmerged
TNLean #8822 head. Accepted QIC dependency: `{man['accepted_qic_revision']}`.

The publication attestation verifies all 68 changed files and all seven frozen
production, router, and regression source hashes against the published source.
The three production modules, router, three regression modules, and external
18-name axiom reporter passed the eight preserved strict bounded runs.
All 85 project-source/artifact links were audited. The public axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

This metadata child activates only the new 18 original-proof provenance rows.
No Lean source, dependency pin, raw compiler log, or raw documentation log is
changed. The `lean/` and `docs/` evidence directories are unmodified historical
snapshots, so their original pending-publication wording is retained honestly.
The active ledger and `source-tree-attestation.json` bind those exact checks
to the now-published immutable source. No compiler was rerun for this child.

The later published parent `{CURRENT}` is not substituted
for the checked parent. Current-parent integration, a full Lake build, aggregate
checkdecls, complete blueprint validation, and exact-head CI remain separate
gates owned by the parent task. No generic trace-duality converse, descending
commutation, KKT, telescope, energy or growth bound, or full Proposition 4.1
is claimed by this leaf.
''')
print('Verified 68 published files; activated only18 new rows; raw logs and Lean unchanged.')

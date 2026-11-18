from pathlib import Path
import subprocess,json,hashlib
r=Path('/workspace/tn-interaction-main16b');o=Path(__file__).parent;baseline=Path('/workspace/tn-peps-evidence/docs/audits/2026-11-18_interaction_main16b')
def g(*a):return subprocess.check_output(['git',*a],cwd=r,text=True)
def data(ref,path):return json.loads(g('show',ref+':'+path))
assert g('rev-parse','HEAD').strip()=='42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d';assert g('rev-parse','MERGE_HEAD').strip()=='16b1dfbd7e45f0e8fed7f2607e25313cf5a9f931'
lanes=[('MPS','1ee6bad71b740d5f054ecc5254f62c9eea2da462',data('6b302483','docs/audits/2026-11-18_mps_main16b_resolution/conflicts.json'),'final_sha256'),('PEPS','9e9528f64e90be49fabca7fbbb3b9a048d044e23',json.loads((o/'peps-author-resolution.json').read_text())['rows'],'sha256'),('docs','6d2196117fbe94dd7d42d3bc02ed12e2d12c401b',data('6d219611','docs/audits/2026-11-18_docs_main16b_resolution/resolution.json')['files'],'final_sha256')]
allpaths=set();verified=[]
for lane,ref,rows,key in lanes:
 expected=set((baseline/(lane+'-conflicts.txt')).read_text().splitlines());assert {x['path'] for x in rows}==expected;assert not allpaths&expected;allpaths|=expected
 for row in rows:
  b=subprocess.check_output(['git','show',ref+':'+row['path']],cwd=r);assert hashlib.sha256(b).hexdigest()==row[key],row['path'];verified.append(dict(lane=lane,path=row['path'],source_commit=ref,sha256=row[key]))
assert set(g('diff','--name-only','--diff-filter=U').splitlines())==allpaths
(o/'admitted-resolutions.json').write_text(json.dumps(verified,indent=2)+'\n')
# Materialize and stage all reviewed resolutions, including identical-to-parent blobs.
for lane,ref,rows,key in lanes:
 subprocess.run(['git','restore','--source='+ref,'--worktree','--staged','--pathspec-from-file='+str(baseline/(lane+'-conflicts.txt'))],cwd=r,check=True)
assert not g('ls-files','--unmerged')
for row in verified:assert hashlib.sha256((r/row['path']).read_bytes()).hexdigest()==row['sha256']
subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
(o/'final-staged.patch').write_text(g('diff','--cached'));(o/'final-staged-manifest.txt').write_text(g('diff','--cached','--name-status'))
print(g('diff','--cached','--stat'))

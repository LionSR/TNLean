from pathlib import Path
import subprocess,json,hashlib,tarfile,io,sys
repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-selective-source-preparation');b=Path(Path('/tmp/tnlean-selective-source-blueprint-dir').read_text().strip());rev=sys.argv[1]
archive=subprocess.check_output(['git','archive',rev,'TNLean','TNLean.lean','blueprint/src','lake-manifest.json','lean-toolchain'],cwd=repo)
checks={};skipped=[]
with tarfile.open(fileobj=io.BytesIO(archive)) as t:
 for m in t:
  if not m.isfile():continue
  if m.name=='blueprint/src/web.tex':skipped.append(m.name);continue
  if not (m.name.endswith(('.lean','.tex','.bib')) or m.name in ['lake-manifest.json','lean-toolchain']):continue
  d=t.extractfile(m).read();p=b/m.name
  assert p.exists() and p.read_bytes()==d,m.name
  checks[m.name]=hashlib.sha256(d).hexdigest()
(b/'snapshot-commit-check.json').write_text(json.dumps({'source_revision':rev,'verified_file_count':len(checks),'files_sha256':checks,'render_override_files':skipped,'note':'All .lean, .tex and .bib sources and dependency pins compared. web.tex deliberately uses the focused content router. Committed generated PDFs are not comparison inputs.'},indent=2)+'\n')
r=json.loads((b/'source-revision.json').read_text());r['source_revision']=rev;r['note']='All committed TNLean .lean files, blueprint .tex/.bib mathematical sources, and dependency pins were byte-compared with this commit. Only the web entry point is deliberately replaced by the focused router; focused.tex and content-focused.tex are disposable render additions.';(b/'source-revision.json').write_text(json.dumps(r,indent=2)+'\n')
mods=['AffectedOwners','GroupedBlockMap','PreparedSourceGate','SelectiveSourcePreparation','SelectiveSourceFactorization','WordAppendTail'];rels=['TNLean/PEPS/Approximation/'+n+'.lean' for n in mods]+['blueprint/src/chapter/ch24_peps_selective_source_preparation.tex','blueprint/src/content.tex','TNLean.lean','TNLean/PEPS/Approximation.lean'];(b/'source-sha256.json').write_text(json.dumps({s:checks[s] for s in rels},indent=2)+'\n')
print('Exact commit comparison passed:',len(checks),'files')

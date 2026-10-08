from pathlib import Path
import hashlib,json,shutil
b=Path('/private/tmp/tnlean-source-gaussian');q=json.loads(Path('/private/tmp/qic-source-transport-expansion/env.json').read_text());c=json.loads((b/'env.json').read_text());dst=Path(c['output_root']);chosen={}
for prefix in q['LEAN_PATH'].split(':'):
 root=Path(prefix)
 for p in [*root.glob('QICLean.*'),*((root/'QICLean').rglob('*') if (root/'QICLean').is_dir() else [])]:
  if p.is_file():chosen.setdefault(str(p.relative_to(root)),p)
rows=[]
for rel,p in chosen.items():
 t=dst/rel;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists() or t.is_symlink():
  assert t.is_symlink(),t
  t.unlink()
 t.symlink_to(p.resolve());rows.append({'path':rel,'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(b/'qic-artifact-links.json').write_text(json.dumps(rows,indent=2)+'\n');failed=b/'initial-audit';failed.mkdir(exist_ok=True)
for p in (b/'imported-audit').iterdir():
 if p.is_file():shutil.copy2(p,failed/p.name)
print('QIC_OVERLAY_COHERENT',len(rows))

from pathlib import Path
import hashlib,json,re,sys
r=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-gaussian');b=Path('/private/tmp/tnlean-source-gaussian');sys.dont_write_bytecode=True;sys.path.insert(0,str(r/'scripts'));from lean_import_syntax import strip_lean_comments
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def code(s):
 c,e=strip_lean_comments(s);assert e is None;return c
rows=[]
for rel in dict.fromkeys(x['path'] for x in json.loads((b/'declarations.json').read_text())):
 p=r/rel;raw=code(p.read_text());assert not re.search(r'\b(sorry|admit|axiom|unsafeCast|native_decide)\b',raw)
 original=b/'original-sources'/rel
 if original.exists():
  old=code(original.read_text())
  if p.stem=='PreparedSourceTransport':
   start='theorem Word.sourceContraction_preparedDensityCoefficient_selected_frames';old=old[old.index(start):].replace('multilinear_selected_sum','MultilinearMap.map_piecewise_sum_smul');new=raw[raw.index(start):];assert old.split()==new.split();mode='Actual prepared-word theorem tokens unchanged except the shared lemma name; two generic lemmas moved to their owning libraries.'
  else:assert old.split()==raw.split();mode='All noncomment tokens preserved.'
  oldsha=sha(original)
 else:
  src=code((b/'original-sources/TNLean/PEPS/Approximation/PreparedSourceTransport.lean').read_text());old=src[src.index('theorem multilinear_selected_sum'):src.index('theorem Word.sourceContraction_preparedDensityCoefficient_selected_frames')];old=old[:old.rfind('end')] if old.rstrip().endswith('end') else old
  oldbody=old[old.index(':= by'):].split('open QICLean.ComplexGaussian')[0].strip();newbody=raw[raw.index(':= by'):raw.rindex('end MultilinearMap')].strip();assert oldbody.split()==newbody.split(),(oldbody[-200:],newbody[-200:]);mode='Generic selected-argument lemma moved with the same proof body; namespace, name and direct imports adapted.';oldsha=None
 rows.append({'path':rel,'original_sha256':oldsha,'production_sha256':sha(p),'preservation':mode})
(b/'source-preservation-final.json').write_text(json.dumps({'base_revision':'329d192af8c46f7ff540610de918d5179d13d46e','sources':rows,'new_public_declarations':29,'existing_refactored_declarations':1},indent=2)+'\n');print('PRESERVATION_PASS',len(rows))

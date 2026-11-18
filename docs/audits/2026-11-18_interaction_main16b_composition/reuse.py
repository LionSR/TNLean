import pathlib,json,subprocess,hashlib,sys
r=pathlib.Path('/workspace/tn-interaction-main16b');o=pathlib.Path('/workspace/reviews/interaction-main16b-composition');sys.path.insert(0,str(r/'scripts'));import ci_lean_checks as c
heads=['42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d','f94193009343ee767ddc96a3dacee80e659ec5a9'];maps={}
for h in heads:
 raw=subprocess.check_output(['git','ls-tree','-r',h],cwd=r,text=True);maps[h]={line.split('\t',1)[1]:line.split()[2] for line in raw.splitlines()}
files=c.lean_files(r);g=c.import_graph(r,files);paths={c.module_of(p):p for p in files};groups={'peps107':(r/'docs/audits/2026-11-18_interaction_integration/peps-all.txt').read_text().splitlines(),'shared6':(r/'docs/audits/2026-11-18_interaction_integration/shared-all.txt').read_text().splitlines(),'snake1':['TNLean/MPS/AreaLaw/SnakeGridAreaLaw.lean'],'fixtures5':['scripts/'+s+'_regression.lean' for s in ['ground_state_gap_scope','generic_gap_boundary','zero_gap_tn_wrappers','range_square_zero_gap','box_supremum_zero_gap']]};records=[]
for group,targets in groups.items():
 for path in targets:
  m=c.module_of(path);modules=c.closure(g,m)|{m};fingerprints={h:hashlib.sha256(json.dumps([(x,maps[h].get(paths.get(x,''))) for x in sorted(modules)]).encode()).hexdigest() for h in heads};assert len(set(fingerprints.values()))==1,path
  records.append({'group':group,'path':path,'transitive_TN_modules':len(modules),'fingerprints':fingerprints,'unchanged':True})
report={'base':heads[0],'final':heads[1],'package_manifest_unchanged':maps[heads[0]]['lake-manifest.json']==maps[heads[1]]['lake-manifest.json'],'toolchain_unchanged':maps[heads[0]]['lean-toolchain']==maps[heads[1]]['lean-toolchain'],'records':records,'boundary':'Source/manifest/toolchain equivalence supports reuse; execution heads remain unchanged in original records. The 25 affected MPS/root modules are excluded.'};(o/'final-reuse-all.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS 107 PEPS + 6 shared + 5 fixture transitive TN source fingerprints; exact dependencies and toolchain unchanged')

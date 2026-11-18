import pathlib,sys,re,json,subprocess,hashlib,collections
r=pathlib.Path('/workspace/tn-pin729-other');out=pathlib.Path('/workspace/reviews/pin729-lattice-followup');sys.path.insert(0,str(r/'scripts'));from lean_import_syntax import strip_lean_comments
owners={'TNLean':r,'QICLean':r/'.lake/packages/qiclean'};closure={};imports={};order=[]
def visit(m):
 if m in closure:return closure[m]
 if m.split('.')[0] not in owners:return set()
 text,e=strip_lean_comments((owners[m.split('.')[0]]/(m.replace('.','/')+'.lean')).read_text());assert not e
 ds=[]
 for line in text.splitlines():
  z=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$',line)
  if z:ds+=z.group(1).split()
 imports[m]=ds;c={m};closure[m]=c
 for d in ds:c|=visit(d)
 order.append(m);return c
c=visit('TNLean.QCA');missing=set(m for m in c if not (owners[m.split('.')[0]]/'.lake/build/lib/lean'/m.replace('.','/')).with_suffix('.olean').is_file());mps={m for m in missing if m.startswith('TNLean.MPS.')};assert len(missing)==159 and len(mps)==98
rev='9630ab7e415a462145031d973eda757ffbdafcc6';pre='docs/audits/2026-11-18_pin729_mps_shard/'
def remote(n):return subprocess.check_output(['git','-C',str(r),'show',rev+':'+pre+n],text=True)
manifest=set(remote('manifest.txt').splitlines());rows=[json.loads(x) for x in remote('results.jsonl').splitlines()];built={x['file'] for x in rows if x.get('phase')=='build' and x.get('exit_code')==0};arts={x['file']:x for x in json.loads(remote('cache-artifacts.json'))};records=[]
for m in sorted(missing):
 p=m.replace('.','/')+'.lean';a=arts.get(p);h=hashlib.sha256((r/p).read_bytes()).hexdigest()
 records.append(dict(module=m,path=p,source_sha256=h,is_mps=m in mps,in_mps_manifest=p in manifest,mps_worker_build_record=p in built,export_metadata_present=a is not None,export_source_hash_matches=a is not None and a.get('source_sha256')==h,missing_dependencies=sorted((closure[m]&missing)-{m}),direct_imports=imports[m]))
(out/'qca-missing159.json').write_text(json.dumps(records,indent=2)+'\n')
for name,ms in [('qca-missing159.txt',missing),('qca-defer-mps98.txt',mps)]:
 (out/name).write_text('\n'.join(m.replace('.','/')+'.lean' for m in sorted(ms))+'\n')
eligible=[m for m in order if m in missing-mps and m!='TNLean.QCA' and not (closure[m]&mps)];deferred=[m for m in order if m in missing-mps and m!='TNLean.QCA' and closure[m]&mps]
plan={'source_sha':'6b7fb2e27dbc6856091e593e4226d350403beb8a','pin':'729428582b78ab7529b3796099193649f947354a','mps_evidence_sha':rev,'missing_total':len(missing),'defer_mps':len(mps),'mps_selected_overlap':sum(x['is_mps'] and x['in_mps_manifest'] for x in records),'mps_build_record_overlap':sum(x['is_mps'] and x['mps_worker_build_record'] for x in records),'mps_export_metadata_overlap':sum(x['is_mps'] and x['export_metadata_present'] for x in records),'mps_export_matching_source':sum(x['is_mps'] and x['export_source_hash_matches'] for x in records),'safe_non_mps_order_before_cache_transfer':eligible,'batch_plan_max10':[eligible[i:i+10] for i in range(0,len(eligible),10)],'non_mps_waiting_on_mps':deferred,'root_deferred':'TNLean.QCA','local_export_cache_exists':pathlib.Path('/tmp/pin729-mps-olean').exists(),'cache_reuse_decision':'No imported cache: export metadata is not artifact availability. Remote direct-Lean outputs lack Lake trace validation. Require authorized artifact transfer plus matching toolchain/package/source and transitive import hashes; do not bypass previously reported export restrictions.','execution':'Planning only; no QCA or MPS build/strict launched in this followup'}
(out/'qca-plan.json').write_text(json.dumps(plan,indent=2)+'\n');print(json.dumps({k:v for k,v in plan.items() if k not in ['safe_non_mps_order_before_cache_transfer','batch_plan_max10','non_mps_waiting_on_mps']},indent=2));print('eligible nonMPS',len(eligible),'deferred nonMPS',len(deferred));print('eligible',eligible)

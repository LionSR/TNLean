import pathlib,json,subprocess,sys,datetime,shutil
p=pathlib.Path('/workspace/reviews/interaction-peps-remaining');r=pathlib.Path('/workspace/tn-interaction-integration');targets=set(json.loads((p/'plan.json').read_text()))
def state():
 rows=[json.loads(s) for s in (p/'results.jsonl').read_text().splitlines()]
 return rows,{x['module'] for x in rows if x['phase']=='strict' and x['exit_code']==0}&targets
for batch in range(20):
 rows,passed=state()
 if len(passed)==90:print('COMPLETE 90/90',flush=True);break
 if shutil.disk_usage(r).free<2**30:raise SystemExit('1 GiB disk guard')
 print(datetime.datetime.now(datetime.timezone.utc).isoformat(),'BATCH',batch,'passed',len(passed),'remaining',sorted(targets-passed),flush=True)
 before=len(rows)
 for script in ['verify_helpers.py','verify.py']:
  subprocess.run([sys.executable,str(p/script),'20'],cwd=r,check=True)
  after,_=state()
  if any(x['exit_code']!=0 for x in after[before:]):raise SystemExit('recorded failure; stop')
 if len(state()[0])==before:raise SystemExit('no progress; inspect dependency gate')
else:raise SystemExit('batch cap exhausted')

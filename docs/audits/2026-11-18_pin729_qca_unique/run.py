import pathlib,subprocess,os,time,json,datetime,shutil,fcntl,signal,sys
r=pathlib.Path('/workspace/tn-pin729-other');out=pathlib.Path('/workspace/reviews/pin729-qca-unique');base='6b7fb2e27dbc6856091e593e4226d350403beb8a';pin='729428582b78ab7529b3796099193649f947354a'
lock=(r/'.lake/pin729-validation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert not subprocess.check_output(['git','diff',base,'--','TNLean','TNLean.lean','lake-manifest.json','lakefile.toml','lean-toolchain'],cwd=r)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages/qiclean',text=True).strip()==pin
allowed=json.loads(pathlib.Path('/workspace/reviews/pin729-lattice-followup/qca-plan.json').read_text())['optional_unique_non_mps_order']
assert len(allowed)==36 and all(not m.startswith('TNLean.MPS.') and m not in ['TNLean.QCA','TNLean.Algebra.ListOfFn'] for m in allowed)
(out/'allowed-targets.json').write_text(json.dumps(allowed,indent=2)+'\n');env=os.environ.copy();env.update(PATH='/workspace/elan/bin:'+env['PATH'],ELAN_HOME='/workspace/elan',XDG_CACHE_HOME='/workspace/cache',LEAN_NUM_THREADS='2')
flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']
start_index,end_index=map(int,sys.argv[1:])
selected=allowed[start_index:end_index]
commands=[(phase,m,cmd) for m in selected for phase,cmd in [('build',['lake','build',m]),('strict',['lake','env','lean',*flags,m.replace('.','/')+'.lean'])]]
for i,(phase,target,cmd) in enumerate(commands):
 assert target in allowed
 if shutil.disk_usage(r).free<2**30:raise SystemExit('disk < 1 GiB; stop before launch')
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();log=out/f'{start_index:02d}-{i:02d}-{phase}.log';reason=None
 with log.open('w') as f:
  p=subprocess.Popen(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  meta=dict(source_sha=base,pin=pin,cwd=str(r),target=target,phase=phase,command=cmd,pid=p.pid,pgid=p.pid,start=start,log=log.name)
  (out/'active.json').write_text(json.dumps(meta,indent=2)+'\n')
  while p.poll() is None:
   if shutil.disk_usage(r).free<2**30:reason='disk <1 GiB'
   elif time.monotonic()-t>600:reason='timeout 600s'
   if reason:
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=10)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
    break
   time.sleep(1)
  rc=p.wait()
 meta.update(end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-t,exit_code=rc,stop_reason=reason,disk_free_bytes=shutil.disk_usage(r).free)
 with (out/'results.jsonl').open('a') as f:f.write(json.dumps(meta)+'\n')
 print(json.dumps(meta),flush=True)
 if rc or reason:raise SystemExit(1)
(out/'active.json').unlink(missing_ok=True)

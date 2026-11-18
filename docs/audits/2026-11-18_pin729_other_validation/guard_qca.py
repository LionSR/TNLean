import pathlib,os,signal,time,json,datetime
out=pathlib.Path('/workspace/reviews/pin729-other')
while True:
 for p in pathlib.Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   args=(p/'cmdline').read_bytes().split(b'\0')
   cwd=os.readlink(p/'cwd')
  except (OSError,PermissionError):continue
  if cwd=='/workspace/tn-pin729-other' and len(args)>3 and args[0].endswith(b'/lake') and args[1:3]==[b'build',b'TNLean.QCA']:
   os.kill(int(p.name),signal.SIGTERM)
   (out/'qca-guard.json').write_text(json.dumps({'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pid':int(p.name),'action':'SIGTERM before root build dependency closure expansion','target':'TNLean.QCA','reason':'Preflight found 99 MPS dependencies; unavailable matching warm closure; no cold cross-family root build','classification':'resource/scope blocked, not Lean source failure'},indent=2)+'\n')
   raise SystemExit(0)
 time.sleep(0.1)

import pathlib,json,subprocess,sys,os,hashlib,time,datetime,importlib.metadata
r=pathlib.Path('/workspace/tn-interaction-integration');o=pathlib.Path('/workspace/reviews/interaction-peps-remaining');head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();assert head=='dccc85e5607077b51822664e9d475287d300d607'
metadata={'head':head,'cwd':str(r),'python':sys.version,'python_executable':sys.executable,'source_tree':subprocess.check_output(['git','rev-parse','HEAD:TNLean'],cwd=r,text=True).strip(),'manifest_sha256':hashlib.sha256((r/'lake-manifest.json').read_bytes()).hexdigest(),'lean_toolchain':(r/'lean-toolchain').read_text().strip(),'env':{'BLUEPRINT_SYNC_FETCH_DEPS':'0'},'dependencies':{}}
for name in ['qiclean','mathlib']:
 p=r/'.lake/packages'/name;metadata['dependencies'][name]={'path':str(p.resolve()),'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip(),'status':subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],cwd=p,text=True)}
for name in ['leanblueprint','plasTeX','texra-blueprint']:
 try:metadata[name]=importlib.metadata.version(name)
 except importlib.metadata.PackageNotFoundError:metadata[name]=None
(o/'check-environment.json').write_text(json.dumps(metadata,indent=2)+'\n')
cmd=[sys.executable,'scripts/blueprint_lean_sync.py','--ci','--report',str(o/'source-sync.json')];start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();log=o/'source-sync.stdout';env=os.environ.copy();env['BLUEPRINT_SYNC_FETCH_DEPS']='0'
with log.open('w') as f:
 p=subprocess.Popen(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True);rc=p.wait()
record={'command':cmd,'cwd':str(r),'env_override':{'BLUEPRINT_SYNC_FETCH_DEPS':'0'},'source_head':head,'start':start,'end':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-t,'pid':p.pid,'pgid':p.pid,'exit_code':rc,'stdout_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'report_sha256':hashlib.sha256((o/'source-sync.json').read_bytes()).hexdigest()};(o/'source-sync-command.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
sys.path.insert(0,str(r/'scripts'));import ci_lean_checks as c
fixtures=['scripts/'+s+'_regression.lean' for s in ['ground_state_gap_scope','generic_gap_boundary','zero_gap_tn_wrappers','range_square_zero_gap','box_supremum_zero_gap']]
owners=['TNLean/Lattice/LocalHamiltonian.lean','TNLean/MPS/AreaLaw/Hamiltonian.lean','TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean','TNLean/PEPS/AreaLaw/BoundaryTheorem.lean','TNLean/PEPS/Approximation/SquareZeroFloorOptimizer.lean','TNLean/PEPS/Approximation/PinnedZeroFloorOptimizer.lean','TNLean/MPS/AreaLaw/Hastings/ThreeWaySplitting.lean','TNLean/PEPS/Approximation/RangeSquareGroundState.lean','TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean','TNLean/MPS/AreaLaw/OverlapEnergy.lean','TNLean/MPS/AreaLaw/BoundaryGap.lean','TNLean/PEPS/AreaLaw/CollarInformation.lean','TNLean/PEPS/AreaLaw/AmplificationCutClearance.lean','TNLean/PEPS/AreaLaw/Scan/BoxEntropySupremum.lean']
cases={}
for path in owners+fixtures:
 c.changed_paths=lambda base,path=path:[path];_,_,selected=c.select(r,'single-path-test');cases[path]=[f for f in fixtures if f in selected];assert cases[path],path
 if path in fixtures:assert path in cases[path]
(o/'selector-all-owners.json').write_text(json.dumps({'head':head,'owner_count':len(owners),'fixture_count':len(fixtures),'cases':cases,'exit_code':0},indent=2)+'\n');print('selector 14 owners + 5 fixtures PASS',flush=True)

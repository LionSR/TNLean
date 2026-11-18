from pathlib import Path
import pathlib,sys,json
r=Path('/workspace/tn-interaction-final');o=Path('/workspace/reviews/interaction-final-release');head='42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d'
sys.path.insert(0,str(r/'scripts'));import ci_lean_checks as c
fixtures=['scripts/'+s+'_regression.lean' for s in ['ground_state_gap_scope','generic_gap_boundary','zero_gap_tn_wrappers','range_square_zero_gap','box_supremum_zero_gap']]
owners=['lake-manifest.json','TNLean/PEPS/Approximation/Basic.lean','TNLean/PEPS/AreaLaw/RectangularDomain.lean','TNLean/Lattice/LocalHamiltonian.lean','TNLean/MPS/AreaLaw/Hamiltonian.lean','TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean','TNLean/PEPS/AreaLaw/BoundaryTheorem.lean','TNLean/PEPS/Approximation/SquareZeroFloorOptimizer.lean','TNLean/PEPS/Approximation/PinnedZeroFloorOptimizer.lean','TNLean/MPS/AreaLaw/Hastings/ThreeWaySplitting.lean','TNLean/PEPS/Approximation/RangeSquareGroundState.lean','TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean','TNLean/MPS/AreaLaw/OverlapEnergy.lean','TNLean/MPS/AreaLaw/BoundaryGap.lean','TNLean/PEPS/AreaLaw/CollarInformation.lean','TNLean/PEPS/AreaLaw/AmplificationCutClearance.lean','TNLean/PEPS/AreaLaw/Scan/BoxEntropySupremum.lean']
cases={}
for path in owners+fixtures:
 c.changed_paths=lambda base,path=path:[path];_,_,selected=c.select(r,'single-path-test');cases[path]=[f for f in fixtures if f in selected];assert cases[path],path
 if path in fixtures:assert path in cases[path]
(o/'selector-all-owners.json').write_text(json.dumps({'head':head,'owner_case_count':len(owners),'lean_owner_count':len(owners)-1,'dependency_manifest_case':True,'fixture_count':len(fixtures),'cases':cases,'exit_code':0},indent=2)+'\n');print('selector',len(owners),'owners + 5 fixtures PASS',flush=True)

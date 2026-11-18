import sys,json
from pathlib import Path
sys.dont_write_bytecode=True;sys.path.insert(0,'scripts');import ci_lean_checks as c
root=Path.cwd();graph=c.import_graph(root,c.lean_files(root));c.import_graph=lambda *_:graph
pairs={
'ground_state_gap_scope':['TNLean/MPS/AreaLaw/Hamiltonian.lean','TNLean/MPS/AreaLaw/OverlapEnergy.lean','TNLean/MPS/AreaLaw/BoundaryGap.lean'],
'generic_gap_boundary':['TNLean/Lattice/LocalHamiltonian.lean','TNLean/PEPS/AreaLaw/BoundaryTheorem.lean'],
'zero_gap_tn_wrappers':['TNLean/Lattice/LocalHamiltonian.lean','TNLean/MPS/AreaLaw/Hamiltonian.lean','TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean','TNLean/PEPS/Approximation/SquareZeroFloorOptimizer.lean','TNLean/PEPS/Approximation/PinnedZeroFloorOptimizer.lean','TNLean/MPS/AreaLaw/Hastings/ThreeWaySplitting.lean'],
'range_square_zero_gap':['TNLean/Lattice/LocalHamiltonian.lean','TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean','TNLean/PEPS/Approximation/RangeSquareGroundState.lean'],
'box_supremum_zero_gap':['TNLean/Lattice/LocalHamiltonian.lean','TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean','TNLean/PEPS/AreaLaw/Scan/BoxEntropySupremum.lean']}
res=[]
for test,owners in pairs.items():
 test='scripts/'+test+'_regression.lean'
 for owner in owners+[test]:
  c.changed_paths=lambda _,owner=owner:[owner]
  _,_,tests=c.select(root,'synthetic-one-path')
  res.append(dict(changed=owner,expected=test,selected=test in tests))
Path('/tmp/joint-independent-dccc85e5/selector.json').write_text(json.dumps(res,indent=2)+'\n')
print(len(res),'cases;',sum(r['selected'] for r in res),'pass'); assert all(r['selected'] for r in res)

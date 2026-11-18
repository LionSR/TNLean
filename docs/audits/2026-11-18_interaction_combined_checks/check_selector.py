from pathlib import Path
import sys,json,subprocess
root=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(root/'scripts'))
import ci_lean_checks as checks
fixtures=['scripts/'+s+'_regression.lean' for s in ['ground_state_gap_scope','generic_gap_boundary','zero_gap_tn_wrappers','range_square_zero_gap','box_supremum_zero_gap']]
owners=['TNLean/Lattice/LocalHamiltonian.lean','TNLean/MPS/AreaLaw/Hamiltonian.lean','TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean']
result={}
for path in owners+fixtures:
    checks.changed_paths=lambda base,path=path:[path]
    _,_,selected=checks.select(root,'injected-single-change')
    result[path]=[f for f in fixtures if f in selected]
    if path in fixtures:assert path in selected
print(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'cases':result},indent=2))

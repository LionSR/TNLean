# Lean Sorry Inventory & Blueprint-Lean Alignment Report

**Date:** April 8, 2026
**Total sorries (excluding Archive/):** 28

## Summary
- 18 sorry theorems matched by blueprint `\notready` ✅
- 2 sorry theorems matched by blueprint entries with NO status tag ⚠
- 8 sorry theorems with NO matching blueprint entry ⚠
- 0 cases of blueprint `\leanok` with Lean sorry ✅✅
- ~10 cases of blueprint `\notready` but Lean is sorry-free (can upgrade to `\leanok`)

## Wedderburn (Ch9 / ch06_spectral.tex) — needs \notready tags
- `Kraus.fixedPointAlgebra_isSemisimpleRing` — sorry, no blueprint status
- `Kraus.fixedPointAlgebra_wedderburnArtin` — sorry, no blueprint status
- `Kraus.starSubalgebra_hasWedderburnBlockDecomp` — sorry, no blueprint match

## Entropy (Ch6 / ch04b_entropy.tex) — axiom alignment
- `strong_subadditivity` — axiom in Lean, no status tag in blueprint

## Operator Convexity (no blueprint) — sorry, no blueprint
- `trace_rpow_concave`, `trace_rpow_convex`, `lieb_concavity`
- `IsPositiveMap.rpow_concave_jensen`, `rpow_convex_jensen`, `log_concave_jensen`

## RFP (no blueprint) — sorry, no blueprint
- `MPSTensor.rfp_nt_structural`

## Action items
1. Add `\notready` to Wedderburn blueprint theorems (ch06_spectral.tex ~851-868)
2. Add status tag to entropy SSA theorem (ch04b_entropy.tex ~127)
3. Upgrade ~10 blueprint `\notready` to `\leanok` where Lean is sorry-free

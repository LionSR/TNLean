# Removal of the unused real-clearance exponent corollary

Baseline: TNLean main `152f3c81984a0d25599471bf700ecc967e13777f`.
Issue: #10152; original contribution: #9579.

## Removed surface and replacement

The removed declaration is
`TNLean.PEPS.AreaLaw.Scan.exists_uniform_boxEntropy_improvement_real` in
`TNLean/PEPS/AreaLaw/Scan/RealBoxEntropyImprovement.lean`. Its only source-tree
references were its declaration, the generated `Scan.lean` import, its isolated
Blueprint anchor `thm:area_law_real_box_improvement_after_area_law`, and the
candidate entry in `docs/tactic_patterns.md`. No production Lean theorem used it.
The generated import, the isolated Blueprint entry and the ledger candidate,
which falls below two occurrences, are removed as well.

The retained theorem
`TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_linear` in
`SafeRectangleAreaLaw.lean` gives a nonnegative coefficient `K`, independent of
real clearance, bounding each safe-rectangle entropy by `K` times its size.
For the literal real-clearance supremum `F_d(r)` of the removed theorem, this
implies `F_d(r) ≤ K r` by `Real.sSup_le`, including an empty collection. Hence
`F_d(r) ≤ max K 1 * r^(1+e')` for every `r ≥ 1` and `e' ≥ 0`.
No initial power-law bound, input coefficient, or source bootstrap is needed
for that consequence.

The coefficient is chosen from fixed `q`, `R`, `J` and `Δ` before the real
clearance and every physical instance. The retained clearance hypothesis is
literally the removed one, `d * Q.size < supDist t z` for every rectangle site
and boundary endpoint. The retained result allows every `d ≥ 0`, hence every
`d > 2R+10` in the removed statement. Its assumptions on the local Hamiltonian
and gapped ground vector are unchanged. Finally, the removed exponent is
`e' = (1 - BootstrapParameters.ell e₀) * e ≥ 0`, by the existing parameter
bounds, so the general linear consequence applies with the same quantifier order.

## Why deletion is the chosen resolution

The removed proof already used precisely this linear bound. Its initial bound
and input coefficient were unused, and its intermediate exponent was used only
to show the output exponent is nonnegative. Retaining a second theorem in the
shape of Proposition 9.5 would obscure that it contributes no independent
bootstrap argument. The general real-clearance linear theorem is the stronger
replacement; no compatibility alias is retained for this unused specialization.

The independent scanner theorem `exists_uniform_boxEntropy_improvement` in
`Scan/PhysicalBoxBootstrap.lean` remains. Its natural-clearance proof and the
source route of `08-scanner.tex:707–790` are unchanged. The real-clearance
recurrence and the safe-rectangle bound also remain. This deletion neither
reopens the area law nor claims a new formalization of the source bootstrap.

## Verification boundary

A repository-wide reference search found no production consumer of the removed
declaration or Blueprint label. Import aggregators are regenerated after the
module deletion. The change is written without local Lean builds or compilation
at the user's request; integration verification remains pending.

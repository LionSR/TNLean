# Issue #826 scouting report — algebra ⇒ fusion converse

Date: 2026-04-23; rebased on current `main` on 2026-04-25
Branch: `feat/826-algebra-to-fusion-v2`
Target issue: #826

## Scope

Issue #826 asks for the converse direction of the MPDO §4.5 equivalence:

given the algebra-structure formulation, derive the transfer-map fusion
formulation under the same trace-preserving and positive-definite fixed-point
side hypotheses used by the forward implication.

## Baseline context

When this branch was first opened, `origin/main` did not yet contain the
non-vacuous algebra-side layer from the issue #612 follow-ups. The branch
therefore started by copying the support-algebra tower and blocked-coordinate
layer that later landed on `main` through PRs #810, #814, #885, and #887.

After the 2026-04-25 rebase, `main` already contains that baseline plus the
adjoint fixed-point descent and the diagonal `χ` trace-power language. This PR
now contributes only the still-useful extra pieces:

- a public upstream transfer-map adjoint lemma in
  `TNLean/MPS/CanonicalForm/BlockingViaAdjoint.lean`;
- the stabilized-adjoint-fixed-point sufficient condition
  `MPOTensor.AlgebraStructureData.stationaryOfFaithfulFixedPoint_compatible_of_adjointFixedPoints_eq`;
- the corresponding wrapper
  `MPOTensor.isRFP_MPDO_via_algebra_of_adjointFixedPoints_eq_of_isTP_of_posDef_fixed`.

## Mathematical concern

The current compatibility predicate is still weaker than the full paper
statement. It only says that, for each positive blocked size `n`, the support
algebra `A n` agrees with the fixed-point algebra of
`(blockedTransferMap M n).adjoint`.

That condition is too weak by itself to force idempotence of
`blockedTransferMap M n`. A candidate counterexample is the two-Kraus dephasing
channel with Kraus family

- `K₀ = (3/5) I`
- `K₁ = (4/5) Z`

on `M₂(ℂ)`, viewed as an MPO with only two nonzero diagonal physical entries.
Then:

1. the channel is trace-preserving and unital;
2. `ρ = I` is a positive-definite fixed point;
3. the off-diagonal sector is scaled by `λ = -7/25`, so the channel is **not**
   idempotent;
4. for every `n > 0`, the `n`th power scales the off-diagonal sector by
   `λ^n ≠ 1`, so the adjoint fixed-point algebra stays equal to the diagonal
   algebra for all positive powers.

A machine-checked counterexample was not completed in this pass. Still, the
main-branch descent theorem from `IsRFP_MPDO_via_algebra` already shows that the
present predicate sees only equality of adjoint fixed-point spaces across
positive block lengths; it does not by itself recover the coefficient/BNT data
used in the paper's converse direction.

## Outcome of this pass

The explicit dephasing counterexample was **not** formalized in Lean during this
pass, so this audit does not claim a machine-checked disproof of the converse.

What did land is the strongest clean intermediate result verified on top of the
non-vacuous algebra layer:

- `MPOTensor.AlgebraStructureData.stationaryOfFaithfulFixedPoint_compatible_of_adjointFixedPoints_eq`
- `MPOTensor.isRFP_MPDO_via_algebra_of_adjointFixedPoints_eq_of_isTP_of_posDef_fixed`

These isolate the exact extra hypothesis that the current formal compatibility
predicate can genuinely see: stabilization of the adjoint fixed-point algebras
of the blocked transfer maps.

So the branch now gives an honest forward theorem and updated blueprint text,
but it does **not** prove the requested converse
`IsRFP_MPDO_via_algebra → IsRFP_MPDO_via_fusion`.
The remaining gap is still the stronger coefficient/BNT layer from
Appendix C.3–C.4.

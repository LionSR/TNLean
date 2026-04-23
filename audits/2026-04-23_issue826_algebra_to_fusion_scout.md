# Issue #826 scouting report — algebra ⇒ fusion converse

Date: 2026-04-23
Branch: `feat/826-algebra-to-fusion-v2`
Target issue: #826

## Scope

Issue #826 asks for the converse direction of the MPDO §4.5 equivalence:

given the algebra-structure formulation, derive the transfer-map fusion
formulation under the same trace-preserving and positive-definite fixed-point
side hypotheses used by the forward bridge.

## Baseline imported into this branch

`origin/main` still carries the **old vacuous scaffold** in
`TNLean/MPS/MPDO/AlgebraStructure.lean`, so the issue cannot even be stated
honestly there. As an initial scaffold, this branch copies in the current
algebra-side work from the open follow-up branch `origin/feat/612-coefficient-extraction`:

- `TNLean/MPS/MPDO/AlgebraStructure.lean`
- `blueprint/src/chapter/ch02b_mpdo.tex`

This gives the non-vacuous support-algebra tower, the blocked-coordinate layer,
and the forward bridge
`MPOTensor.isRFP_MPDO_via_algebra_of_isRFP_MPDO_via_fusion_of_isTP_of_posDef_fixed`.

## Preliminary mathematical concern

The current compatibility predicate in that branch is still weaker than the full
paper statement. It only says that, for each positive blocked size `n`, the
support algebra `A n` agrees with the fixed-point algebra of
`(blockedTransferMap M n).adjoint`.

That looks too weak to force idempotence of `blockedTransferMap M n`.
A candidate counterexample is the two-Kraus dephasing channel with Kraus family

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

If this formalizes cleanly, it shows that the present
`IsRFP_MPDO_via_algebra` does **not** imply `IsRFP_MPDO_via_fusion`, even under
TP + faithful fixed-point hypotheses. In that case the issue as stated is false
for the current Lean predicate, and the honest next step is either:

- strengthen the algebra-side hypothesis toward the paper’s coefficient/BNT
  data, or
- prove the converse only from an explicitly strengthened intermediate bridge
  assumption.

## Planned next steps in this branch

1. Verify that the imported algebra-side branch compiles cleanly on top of
   `origin/main`.
2. Add a reusable theorem giving algebra witnesses from a stationary faithful
   fixed-point support algebra whenever the blocked adjoint fixed-point algebras
   stabilize across positive powers.
3. Formalize the explicit dephasing MPO and prove:
   - it satisfies the current algebra predicate;
   - it does not satisfy the fusion predicate.
4. If the counterexample lands, update the blueprint/audit language to explain
   why the full converse still requires the coefficient/BNT layer from
   Appendix C.3–C.4.

## Current assessment

The issue may still allow a **strong honest forward step**, but the likely
outcome is not a proof of the requested converse theorem. The first thing to
settle is whether the current algebra predicate is already too weak; the
candidate dephasing example suggests that it is.

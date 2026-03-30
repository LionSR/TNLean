/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.RFP.Defs
import TNLean.MPS.RFP.ZeroCorrelationLength
import TNLean.Channel.FixedPoint.Algebra
import TNLean.MPS.BNT.Construction

/-!
# Structural form of RFP tensors

This file states the structural characterisation theorems for MPS tensors
that are renormalization fixed points, following arXiv:1606.00608 §3.4
(Cirac–Pérez-García–Schuch–Verstraete) and Appendix B.

## Main results

* **Lemma B.1** (`rfp_nt_structural`): RFP normal tensor implies rank-1 transfer map — `sorry`
* **Theorem 3.11** (`rfp_cf_structural`): RFP canonical-form block decomposition — proved
  from `rfp_nt_structural`
* **Corollary 3.12** (`rfp_bnt_structural`): BNT elements inherit structural form — proved
  from `rfp_nt_structural`

## Proof strategy

`rfp_cf_structural` and `rfp_bnt_structural` reduce to `rfp_nt_structural` via the bridge
`IsInjective.isNormal` (each CF/BNT block is injective, hence normal). The remaining sorry
is concentrated in `rfp_nt_structural`, which requires:
1. Rank-1 projector characterization of idempotent CP maps (not yet formalized)
2. Rectangular Kraus freedom theorem (not yet formalized)
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Lemma B.1** (arXiv:1606.00608, Appendix B): If a normal tensor `A` is RFP,
then there exist an invertible matrix `X`, a positive diagonal matrix `Λ`
with `tr(Λ) = 1`, and an isometry `U` on the physical index such that
`A i = X * Λ * U i * X⁻¹` for all `i`.

The proof uses: `E² = E` for a normal tensor means `E` is a rank-1
projector `|R)(L|`; decompose `R = Λ` (diagonal positive), `L = 𝟙`;
then any Kraus representation giving this CPM is related to the canonical
one by an isometry `U` (Stinespring).

TODO: prove — blocked on (1) rank-1 characterization of idempotent CPTP maps
and (2) rectangular Kraus freedom theorem. -/
theorem rfp_nt_structural (A : MPSTensor d D)
    (hNT : IsNormal A) (hRFP : IsRFP A) :
    ∃ (X : Matrix (Fin D) (Fin D) ℂ)
      (Λ : Fin D → ℝ)
      (U : Fin d → Matrix (Fin D) (Fin D) ℂ),
      IsUnit X ∧
      (∀ j, 0 ≤ Λ j) ∧
      (∑ j, (Λ j : ℂ) = 1) ∧
      (∀ i, (U i).conjTranspose * U i = 1) ∧
      ∀ i, A i = X * Matrix.diagonal (fun j => (Λ j : ℂ)) *
        U i * Ring.inverse X := by
  sorry

/-- **Theorem 3.11** (arXiv:1606.00608): For a canonical-form tensor that is
RFP, each block admits an invertible `X_k`, positive diagonal `Λ_k` with
`tr(Λ_k) = 1`, and isometries `U_k` from Lemma B.1.

The conclusion includes the representation equation
`A^i_k = X_k Λ_k U^i_k X_k⁻¹` from Lemma B.1 for each block `k`.

Proved by reducing to `rfp_nt_structural`: each CF block is injective
(from `IsCanonicalForm`), hence normal (via `IsInjective.isNormal`). -/
theorem rfp_cf_structural {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) (hRFP : ∀ k, IsRFP (A k)) :
    ∀ k, ∃ (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
           (Λ : Fin (dim k) → ℝ)
           (U : Fin d → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      IsUnit X ∧
      (∀ j, 0 ≤ Λ j) ∧
      (∑ j, (Λ j : ℂ) = 1) ∧
      (∀ i, (U i).conjTranspose * U i = 1) ∧
      ∀ i, A k i = X * Matrix.diagonal (fun j => (Λ j : ℂ)) *
        U i * Ring.inverse X := by
  intro k
  have hNormal : IsNormal (A k) := (hCF.block_injective k).isNormal
  exact rfp_nt_structural (A k) hNormal (hRFP k)

/-- **Corollary 3.12** (arXiv:1606.00608): The BNT elements of an RFP tensor
each have the form `A_j^i = X_j Λ_j U^i_j X_j⁻¹` from Lemma B.1.

Proved by reducing to `rfp_nt_structural`: `IsCanonicalFormBNT` extends
`IsCanonicalForm`, so each block is injective, hence normal. -/
theorem rfp_bnt_structural {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalFormBNT μ A) (hRFP : ∀ k, IsRFP (A k)) :
    ∀ k, ∃ (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
           (Λ : Fin (dim k) → ℝ)
           (U : Fin d → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      IsUnit X ∧
      (∀ j, 0 ≤ Λ j) ∧
      (∑ j, (Λ j : ℂ) = 1) ∧
      (∀ i, (U i).conjTranspose * U i = 1) ∧
      ∀ i, A k i = X * Matrix.diagonal (fun j => (Λ j : ℂ)) *
        U i * Ring.inverse X := by
  intro k
  have hNormal : IsNormal (A k) := (hCF.toIsCanonicalForm.block_injective k).isNormal
  exact rfp_nt_structural (A k) hNormal (hRFP k)

end MPSTensor

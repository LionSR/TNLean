/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ChainPaddingCoordinates
import QICLean.ManyBody.Hamiltonian.KroneckerSum

/-!
# The actual padded ground vector and its projector gap

Appending the prescribed basis state leaves the ground energy unchanged and keeps the gap,
capped at one. The ancillary operator is the actual sum of the appended on-site penalties, gapped
at zero with gap one, so the padded operator is a Kronecker sum and
`ManyBody.IsGapped.kronecker_add` and `ManyBody.groundSpace_kronecker_add_eq_span` apply.

Source: product-ancilla accuracy reduction for LVV13, arXiv:1307.5143v1,
final successive induction, lines 652--678. This is an auxiliary reduction;
no equality of spectral gaps or running-time bound is asserted.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Kronecker

open ManyBody (IsGapped groundSpace)

namespace TNLean.MPS.AreaLaw

/-- Attach the prescribed ancillary basis configuration to the original vector,
using the same prefix coordinates as the retained viable family. -/
noncomputable def paddedGroundVector {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) : EuclideanSpace ℂ (Fin N → Fin q) :=
  rightBasisExtension
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (leftConfigOfFinEquiv hi)) Γ) (fun _ ↦ z)

/-- The padded vector is normalized whenever the original vector is normalized. -/
theorem norm_paddedGroundVector {L N q : ℕ} (hi : L ≤ N) (z : Fin q)
    (Γ : EuclideanSpace ℂ (Fin L → Fin q)) :
    ‖paddedGroundVector hi z Γ‖ = ‖Γ‖ := by
  rw [paddedGroundVector, norm_rightBasisExtension, LinearIsometryEquiv.norm_map]

/-- The original ground vector, extended by the actual ancillary product state,
spans the ground space of the actual padded interaction, which is gapped with gap the
minimum of the original gap and one. -/
theorem isGapped_paddedInteraction {L N q : ℕ} (hL : 1 ≤ L) (hi : L ≤ N)
    (z : Fin q) (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    {E Delta : ℝ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} (hH : (∑ j, h j).IsHermitian)
    (hΩ : ‖Γ‖ = 1) (hgap : IsGapped (∑ j, h j) E Delta)
    (hspan : groundSpace (∑ j, h j) E = Submodule.span ℂ {Γ}) (hDelta : 0 < Delta) :
    ‖paddedGroundVector hi z Γ‖ = 1 ∧ IsGapped (∑ j, paddedInteraction hi z h j) E (min Delta 1) ∧
      groundSpace (∑ j, paddedInteraction hi z h j) E =
        Submodule.span ℂ {paddedGroundVector hi z Γ} := by
  classical
  let e := leftConfigOfFinEquiv (q := q) hi
  let H := ∑ j, h j
  let b0 : (v : {v : Fin N // v ∉ leftBlock N L}) → Fin q := fun _ ↦ z
  let A := Matrix.reindex e e H
  let B := QuantumCircuit.productBasisPenalty b0
  let c := ManyBody.cutEquiv (fun _ ↦ Fin q) (leftBlock N L)
  have hpad : ManyBody.cutOperator (leftBlock N L) (∑ j, paddedInteraction hi z h j) =
      A ⊗ₖ 1 + 1 ⊗ₖ B := by
    rw [sum_paddedInteraction hL hi z h]
    change ManyBody.cutOperator (leftBlock N L) (QuantumCircuit.embedOp (Fin.castLE hi) H) +
      ManyBody.cutOperator (leftBlock N L)
        (∑ v : {v : Fin N // v ∉ leftBlock N L},
          QuantumCircuit.siteOp v.val (QuantumCircuit.siteBasisPenalty z)) = _
    rw [cutOperator_embedOp_prefix hi b0 H,
      cutOperator_appended_penalty z (fun _ ↦ z)]
  have hA : A.IsHermitian := hH.submatrix _
  have hB : B.IsHermitian := QuantumCircuit.isHermitian_productBasisPenalty b0
  have hgA : IsGapped A E Delta := (ManyBody.isGapped_reindex_iff e).mpr hgap
  have hgB := QuantumCircuit.isGapped_productBasisPenalty b0
  have hgK := hgA.kronecker_add hA hB hgB (Or.inl hDelta.le)
  have hsK := ManyBody.groundSpace_kronecker_add_eq_span hA hB hgA hgB hDelta.le zero_le_one
    (ManyBody.groundSpace_reindex_eq_span e hspan)
    (QuantumCircuit.groundSpace_productBasisPenalty b0)
  rw [add_zero, ← hpad] at hgK hsK
  have hsP := ManyBody.groundSpace_reindex_eq_span c.symm hsK
  rw [show Matrix.reindex c.symm c.symm (ManyBody.cutOperator (leftBlock N L)
      (∑ j, paddedInteraction hi z h j)) = ∑ j, paddedInteraction hi z h j by
    ext σ τ
    exact congrArg₂ (∑ j, paddedInteraction hi z h j) (c.symm_apply_apply σ)
      (c.symm_apply_apply τ)] at hsP
  refine ⟨(norm_paddedGroundVector hi z Γ).trans hΩ, (ManyBody.isGapped_reindex_iff c).mp hgK,
    hsP.trans ?_⟩
  congr 2
  ext σ
  rw [show paddedGroundVector hi z Γ σ =
    if (c σ).2 = b0 then Γ (e.symm (c σ).1) else 0 from rfl]
  by_cases hb : (c σ).2 = b0 <;>
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hb, Pi.single_apply]

end TNLean.MPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceInputSchmidtFrames

/-!
# Local evaluation of a Schmidt input expansion

Canonical owner relabelling transports the input isometries into the two
actual local memories. Applying the two local words then gives the exact
Schmidt expansion of their joint output.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-localschmidtoutput-01
TNLean.PEPS.PairEffect.Word.HasSchmidtOutput
Provenance-ID: 8769-source-resource-localschmidtoutput-02
TNLean.PEPS.PairEffect.Word.hasSchmidtOutput_of_hasTensorPartition
-/


noncomputable section
open scoped TensorProduct Matrix
namespace TNLean.PEPS.PairEffect.Word

/-- An exact Schmidt expansion through two allowed local words. The input
isometries, local words, and probability weights are chosen before the corrected
coordinate. All input and output register lists are prescribed. -/
def HasSchmidtOutput {I : Type} [Fintype I] (a b : Layout Bool)
    (v : I → Mem (Layout.restrict (fun p : Bool ↦ p) b) ⊗[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p) b)) : Prop :=
  ∃ c : Word (Layout.restrict (fun p : Bool ↦ p) a)
      (Layout.restrict (fun p : Bool ↦ p) b),
    ∃ d : Word (Layout.restrict (fun p : Bool ↦ !p) a)
      (Layout.restrict (fun p : Bool ↦ !p) b),
      c.IsAllowed ∧ d.IsAllowed ∧ c.sources = [] ∧ d.sources = [] ∧
      ‖c.eval‖ ≤ 1 ∧ ‖d.eval‖ ≤ 1 ∧
      ∃ r : ℕ, ∃ lam : Fin r → ℝ,
        ∃ F : EuclideanSpace ℂ (I × Fin r) →ₗᵢ[ℂ]
          Mem (Layout.restrict (fun p : Bool ↦ p) a),
        ∃ G : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ]
          Mem (Layout.restrict (fun p : Bool ↦ !p) a),
          (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j) = 1 ∧ ∀ i : I,
            v i = ∑ j, (Real.sqrt (lam j) : ℂ) •
              (c.eval (F (EuclideanSpace.basisFun _ ℂ (i, j))) ⊗ₜ[ℂ]
                d.eval (G (EuclideanSpace.basisFun _ ℂ j)))

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.Word
open SourceInventory TNLean.PEPS.Approximation
variable {P : Type} {a b : Layout P}
/-- Partitioning commutes with the canonical identification of equal register lists. -/
private theorem partitionIso_memCongr_symm {Q : Type} (f : Q → Bool)
    {L K : Layout Q} (h : L = K) (x : Mem K) :
    Layout.partitionIso f L ((Layout.memCongr h).symm x) =
      TensorProduct.mapIsometry
        ((Layout.memCongr (congrArg (Layout.restrict f) h)).symm.toLinearIsometry)
        ((Layout.memCongr (congrArg (Layout.restrict (fun p ↦ !f p)) h)).symm.toLinearIsometry)
        (Layout.partitionIso f K x) := by
  cases h
  change Layout.partitionIso f L x =
    TensorProduct.map (LinearMap.id) (LinearMap.id) (Layout.partitionIso f L x)
  rw [TensorProduct.map_id]
  rfl

/-- The canonical owner identification transports both Schmidt frames into
exactly the two input memories of the local factors. -/
private theorem exists_mappedInputFrames {Q I : Type} [Fintype I]
    (f : Q → Bool) (C T : Layout Q)
    (frame : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem (Layout.mapOwner f C))
    (x : I → Mem C) (y : Mem T)
    (hx : ∀ i, frame (EuclideanSpace.basisFun I ℂ i) = Layout.mapOwnerIso f C (x i))
    (hf : HasSchmidtInputFrames (Layout.mapOwner f C) (Layout.mapOwner f T) frame
      (Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner f T)
        (Layout.mapOwnerIso f T y))) :
    ∃ r : ℕ, ∃ lam : Fin r → ℝ,
      ∃ A : EuclideanSpace ℂ (I × Fin r) →ₗᵢ[ℂ]
        Mem (Layout.restrict (fun p : Bool ↦ p) (Layout.mapOwner f (C ++ T))),
      ∃ B : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ]
        Mem (Layout.restrict (fun p : Bool ↦ !p) (Layout.mapOwner f (C ++ T))),
      (∀ j, 0 ≤ lam j) ∧ (∑ j, lam j) = 1 ∧ ∀ i : I,
        Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner f (C ++ T))
          (Layout.mapOwnerIso f (C ++ T) ((appendIso C T).symm (x i ⊗ₜ[ℂ] y))) =
            ∑ j, (Real.sqrt (lam j) : ℂ) •
              (A (EuclideanSpace.basisFun _ ℂ (i, j)) ⊗ₜ[ℂ]
                B (EuclideanSpace.basisFun _ ℂ j)) := by
  obtain ⟨r, lam, A, B, hlam, hsum, he⟩ := hf
  let h := Layout.mapOwner_append f C T
  let e₁ := (Layout.memCongr (congrArg (Layout.restrict (fun p : Bool ↦ p)) h)).symm
  let e₂ := (Layout.memCongr (congrArg (Layout.restrict (fun p : Bool ↦ !p)) h)).symm
  refine ⟨r, lam, e₁.toLinearIsometry.comp A, e₂.toLinearIsometry.comp B,
    hlam, hsum, ?_⟩
  intro i
  have hi : Layout.mapOwnerIso f (C ++ T) ((appendIso C T).symm (x i ⊗ₜ[ℂ] y)) =
      (Layout.memCongr h).symm ((appendIso (Layout.mapOwner f C) (Layout.mapOwner f T)).symm
        (Layout.mapOwnerIso f C (x i) ⊗ₜ[ℂ] Layout.mapOwnerIso f T y)) := by
    apply (Layout.memCongr h).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact Layout.mapOwnerIso_append_tmul f C T (x i) y
  rw [hi, partitionIso_memCongr_symm]
  have he' := he i
  rw [hx, LinearIsometryEquiv.symm_apply_apply] at he'
  rw [he']
  simp only [map_sum, map_smul, TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    LinearIsometry.coe_toLinearMap]
  rfl

/-- Apply the two actual local words to the transported Schmidt input sum. -/
theorem hasSchmidtOutput_of_hasTensorPartition {Q I : Type} [Fintype I]
    (f : Q → Bool) (C T out : Layout Q) (v : Word (C ++ T) out)
    (hv : Word.HasTensorPartition f v)
    (frame : EuclideanSpace ℂ I →ₗᵢ[ℂ] Mem (Layout.mapOwner f C))
    (x : I → Mem C) (y : Mem T)
    (hx : ∀ i, frame (EuclideanSpace.basisFun I ℂ i) = Layout.mapOwnerIso f C (x i))
    (hf : HasSchmidtInputFrames (Layout.mapOwner f C) (Layout.mapOwner f T) frame
      (Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner f T)
        (Layout.mapOwnerIso f T y))) :
    Word.HasSchmidtOutput (Layout.mapOwner f (C ++ T)) (Layout.mapOwner f out)
      (fun i : I ↦ Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner f out)
        (Layout.mapOwnerIso f out (v.eval ((appendIso C T).symm (x i ⊗ₜ[ℂ] y))))) := by
  obtain ⟨c, d, hc, hd, hcs, hds, hcn, hdn, hprod⟩ := hv
  obtain ⟨r, lam, F, G, hlam, hsum, he⟩ := exists_mappedInputFrames f C T frame x y hx hf
  refine ⟨c, d, hc, hd, hcs, hds, hcn, hdn, r, lam, F, G, hlam, hsum, ?_⟩
  intro i
  dsimp only
  rw [hprod, he]
  simp only [map_sum, map_smul, TensorProduct.mapL_tmul]


end TNLean.PEPS.PairEffect.Word

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.KrausRepresentation
import QICLean.Kraus.Transfer
import TNLean.MPS.Core.CanonicalNormalization

/-!
# Physical-index mixing of MPS tensors

This module collects generic facts about replacing a finite family of MPS
matrices by fixed linear combinations of that family.  Isometric mixing
preserves the transfer map and left-canonical normalization, while arbitrary
mixing preserves a common virtual gauge.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Isometric Kraus mixing -/

/-- For a possibly rectangular isometry `W`, the family
`C τ = ∑ σ, W τ σ • B σ` has the same transfer map as `B`. -/
theorem transferMap_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    Kraus.transferMap (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ) = Kraus.transferMap B := by
  ext X : 1
  simpa [Kraus.transferMap_apply] using
    kraus_same_map_of_isometry_combination
      (K := fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ)
      (K' := B) W hW (fun _ ↦ rfl) X

/-- A physical-index isometry preserves left-canonicality. -/
theorem isLeftCanonical_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : IsLeftCanonical B) :
    IsLeftCanonical (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ) := by
  let C : MPSTensor m D := fun τ ↦ ∑ σ : Fin d, W τ σ • B σ
  have hCh : IsChannel (Kraus.transferMap C) := by
    have hEq : Kraus.transferMap C = Kraus.transferMap B := by
      simpa [C] using transferMap_kraus_isometry B W hW
    simpa [hEq] using Kraus.isChannel_mapLM B hB
  change IsLeftCanonical C
  rw [IsLeftCanonical]
  exact kraus_sum_conjTranspose_mul_of_tp C (Kraus.transferMap C)
    (fun X ↦ by simp [Kraus.transferMap_apply]) hCh.tp

/-- An isometric physical-index mixing of an injective matrix family remains
injective.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this lemma. -/
theorem isInjective_kraus_isometry
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1)
    (hB : Kraus.IsInjective B) :
    Kraus.IsInjective (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ) := by
  let C : MPSTensor m D := fun τ ↦ ∑ σ : Fin d, W τ σ • B σ
  have hrecover (sigma : Fin d) :
      ∑ tau : Fin m, star (W tau sigma) • C tau = B sigma := by
    ext i j
    simp only [C, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    calc
      ∑ tau : Fin m, star (W tau sigma) * ∑ rho : Fin d, W tau rho * B rho i j =
          ∑ tau : Fin m, ∑ rho : Fin d,
            (star (W tau sigma) * W tau rho) * B rho i j := by
              apply Finset.sum_congr rfl
              intro tau _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro rho _
              ring
      _ = ∑ rho : Fin d, ∑ tau : Fin m,
          (star (W tau sigma) * W tau rho) * B rho i j := Finset.sum_comm
      _ = ∑ rho : Fin d,
          (∑ tau : Fin m, star (W tau sigma) * W tau rho) * B rho i j := by
            apply Finset.sum_congr rfl
            intro rho _
            rw [Finset.sum_mul]
      _ = B sigma i j := by
        have hentry (rho : Fin d) :
            (∑ tau : Fin m, star (W tau sigma) * W tau rho) =
              if sigma = rho then 1 else 0 := by
          simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
            Matrix.one_apply] using
            congrFun (congrFun hW sigma) rho
        simp_rw [hentry]
        simp
  rw [Kraus.IsInjective, eq_top_iff]
  intro X _
  have hle : Submodule.span ℂ (Set.range B) ≤
      Submodule.span ℂ (Set.range C) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨sigma, rfl⟩
    rw [← hrecover sigma]
    apply Submodule.sum_mem
    intro tau _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨tau, rfl⟩)
  apply hle
  rw [hB]
  exact Submodule.mem_top

/-- A linearly mixed family can be injective only if the original family is
injective.  No isometry hypothesis is needed.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this lemma. -/
theorem isInjective_of_kraus_mixing_isInjective
    {m : ℕ} (B : MPSTensor d D) (W : Matrix (Fin m) (Fin d) ℂ)
    (hC : Kraus.IsInjective
      (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ)) :
    Kraus.IsInjective B := by
  let C : MPSTensor m D := fun τ ↦ ∑ σ : Fin d, W τ σ • B σ
  rw [Kraus.IsInjective, eq_top_iff]
  intro X _
  have hle : Submodule.span ℂ (Set.range C) ≤
      Submodule.span ℂ (Set.range B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨tau, rfl⟩
    apply Submodule.sum_mem
    intro sigma _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨sigma, rfl⟩)
  apply hle
  rw [show Kraus.IsInjective C from hC]
  exact Submodule.mem_top

/-- Isometric physical-index mixing preserves and reflects one-site
injectivity.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this equivalence. -/
theorem isInjective_kraus_isometry_iff
    {m : ℕ} (B : MPSTensor d D)
    (W : Matrix (Fin m) (Fin d) ℂ) (hW : Wᴴ * W = 1) :
    Kraus.IsInjective (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ) ↔
      Kraus.IsInjective B := by
  constructor
  · exact isInjective_of_kraus_mixing_isInjective B W
  · exact isInjective_kraus_isometry B W hW

/-! ### Gauge covariance -/

/-- Applying the same physical-index mixing to two gauge-equivalent tensors
preserves their virtual gauge.  No isometry hypothesis is needed.

This is project-derived coordinate algebra used for the normal-block
construction surrounding arXiv:1606.00608, lines 217--246 and 1628--1665;
the paper does not state this lemma. -/
theorem GaugeEquiv.sum_smul
    {m : ℕ} {A B : MPSTensor d D}
    (hAB : GaugeEquiv A B) (W : Matrix (Fin m) (Fin d) ℂ) :
    GaugeEquiv
      (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • A σ)
      (fun τ : Fin m ↦ ∑ σ : Fin d, W τ σ • B σ) := by
  obtain ⟨X, hX⟩ := hAB
  refine ⟨X, fun τ ↦ ?_⟩
  simp_rw [hX]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp

end MPSTensor

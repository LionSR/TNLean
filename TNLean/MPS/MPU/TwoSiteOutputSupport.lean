/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RectangularUnitaryConjugation
import TNLean.MPS.MPU.TwoSiteStandardFormOpenWord
import TNLean.QCA.BipartiteSupportAlgebra
import QICLean.Algebra.SkolemNoetherUnitary
import Mathlib.Data.Matrix.Basis

/-!
# Actual finite output support factors of supplied MPU gates

The full observable family on one unshifted pair is transported through
its actual supplied unitary gates. Its left output factor carries the
intermediate dimension ℓ, and its right factor carries r. The factors
are derived from the actual two-link output observable, rather than
supplied as presentations of a selected support algebra.

Source: arXiv:1703.09188, StandardForm/SF and Appendix index comparison,
lines 603–622 and 2313–2334.

**Local fix (Appendix gate orientation):** Main-text line 543 directs v
from the intermediate space to the physical pair, so actual forward
conjugation gives v(1⊗X)v†. Appendix line 2333 prints the adjoints in
the reverse order. The left intermediate factor still has size ℓ;
see `docs/paper-gaps/mpu_qca_index_normalization.tex`.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

private def twoLinkMiddleIndexEquiv (ℓ r : ℕ) :
    (Fin r × ((Fin ℓ × Fin r) × Fin ℓ)) ≃ ((Fin r × Fin ℓ) × (Fin r × Fin ℓ)) where
  toFun x := ((x.1, x.2.1.1), (x.2.1.2, x.2.2))
  invFun x := (x.1.1, ((x.1.2, x.2.1), x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def twoLinkMiddleMap (ℓ r : ℕ) :
    Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ →⋆ₐ[ℂ]
      Matrix ((Fin r × Fin ℓ) × (Fin r × Fin ℓ))
        ((Fin r × Fin ℓ) × (Fin r × Fin ℓ)) ℂ :=
  (Matrix.matrixReindexStarAlgEquiv (twoLinkMiddleIndexEquiv ℓ r)).toStarAlgHom.comp
    ((Matrix.rightKroneckerEmbed (m := Fin r)).comp
      (Matrix.leftKroneckerEmbed (n := Fin ℓ)))

private theorem twoLinkMiddleMap_apply {ℓ r : ℕ}
    (C : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) :
    twoLinkMiddleMap ℓ r C = twoLinkMiddleLift C := by
  ext x y
  change (1 : Matrix (Fin r) (Fin r) ℂ) x.1.1 y.1.1 *
      (C (x.1.2, x.2.1) (y.1.2, y.2.1) *
        (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) x.2.2 y.2.2) = _
  exact (mul_assoc _ _ _).symm

private noncomputable def twoLinkShiftedMap {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (hv : v.IsUnitaryBetween) :
    Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ →⋆ₐ[ℂ]
      Matrix ((Fin d × Fin d) × (Fin d × Fin d))
        ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  (Matrix.IsUnitaryBetween.conjStarAlgEquiv (v ⊗ₖ v)
    (Matrix.IsUnitaryBetween.kronecker v v hv hv)).toStarAlgHom.comp (twoLinkMiddleMap ℓ r)

/-- The actual two-link observable family as a bundled star-homomorphism.
Source: arXiv:1703.09188, StandardForm/SF, lines 603–622. -/
noncomputable def twoLinkOutputMap {d ℓ r : ℕ}
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →⋆ₐ[ℂ]
      Matrix ((Fin d × Fin d) × (Fin d × Fin d))
        ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  (twoLinkShiftedMap v hv).comp
    (Matrix.IsUnitaryBetween.conjStarAlgEquiv u hu).toStarAlgHom

/-- The bundled map is exactly the actual finite observable already used
in the standard-form conjugation identity. Source: arXiv:1703.09188,
StandardForm/SF, lines 603–622. -/
@[simp] theorem twoLinkOutputMap_apply {d ℓ r : ℕ}
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoLinkOutputMap u v hu hv A = twoLinkOutputObservable u v A := by
  change (v ⊗ₖ v) * twoLinkMiddleMap ℓ r (u * A * uᴴ) * (v ⊗ₖ v)ᴴ = _
  rw [twoLinkMiddleMap_apply]
  rfl

/-- The left shifted output factor carries the source intermediate
ℓ-index. Source: arXiv:1703.09188, Appendix, line 2333. -/
noncomputable def twoLinkLeftOutputMap {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (hv : v.IsUnitaryBetween) :
    Matrix (Fin ℓ) (Fin ℓ) ℂ →⋆ₐ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Matrix.IsUnitaryBetween.conjStarAlgEquiv v hv).toStarAlgHom.comp
    (Matrix.rightKroneckerEmbed (m := Fin r))

/-- The right shifted output factor carries the source intermediate
r-index. Source: arXiv:1703.09188, StandardForm and Appendix,
lines 603–622 and 2313–2334. -/
noncomputable def twoLinkRightOutputMap {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (hv : v.IsUnitaryBetween) :
    Matrix (Fin r) (Fin r) ℂ →⋆ₐ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Matrix.IsUnitaryBetween.conjStarAlgEquiv v hv).toStarAlgHom.comp
    (Matrix.leftKroneckerEmbed (n := Fin ℓ))

private theorem twoLinkMiddleLift_kronecker {ℓ r : ℕ}
    (A : Matrix (Fin ℓ) (Fin ℓ) ℂ) (B : Matrix (Fin r) (Fin r) ℂ) :
    twoLinkMiddleLift (A ⊗ₖ B) =
      Matrix.rightKroneckerEmbed (m := Fin r) A ⊗ₖ
        Matrix.leftKroneckerEmbed (n := Fin ℓ) B := by
  ext x y
  simp only [twoLinkMiddleLift, Matrix.kronecker_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.leftKroneckerEmbed_apply]
  ring

private theorem twoLinkShiftedMap_kronecker {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (hv : v.IsUnitaryBetween)
    (A : Matrix (Fin ℓ) (Fin ℓ) ℂ) (B : Matrix (Fin r) (Fin r) ℂ) :
    twoLinkShiftedMap v hv (A ⊗ₖ B) =
      twoLinkLeftOutputMap v hv A ⊗ₖ twoLinkRightOutputMap v hv B := by
  change (v ⊗ₖ v) * twoLinkMiddleMap ℓ r (A ⊗ₖ B) * (v ⊗ₖ v)ᴴ = _
  rw [twoLinkMiddleMap_apply, twoLinkMiddleLift_kronecker]
  change (v ⊗ₖ v) * _ * (v ⊗ₖ v)ᴴ =
    (v * Matrix.rightKroneckerEmbed A * vᴴ) ⊗ₖ
      (v * Matrix.leftKroneckerEmbed B * vᴴ)
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

/-- Product inputs in intermediate coordinates give the actual product
of the two shifted output factors. The arbitrary physical input is
recovered by the inverse of the supplied unshifted gate.
Source: arXiv:1703.09188, StandardForm and Appendix, lines 603–622 and 2333. -/
theorem twoLinkOutputMap_inverse_conj_kronecker {d ℓ r : ℕ}
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (A : Matrix (Fin ℓ) (Fin ℓ) ℂ) (B : Matrix (Fin r) (Fin r) ℂ) :
    twoLinkOutputMap u v hu hv
      ((Matrix.IsUnitaryBetween.conjStarAlgEquiv u hu).symm (A ⊗ₖ B)) =
      twoLinkLeftOutputMap v hv A ⊗ₖ twoLinkRightOutputMap v hv B := by
  change twoLinkShiftedMap v hv ((Matrix.IsUnitaryBetween.conjStarAlgEquiv u hu)
    ((Matrix.IsUnitaryBetween.conjStarAlgEquiv u hu).symm (A ⊗ₖ B))) = _
  rw [StarAlgEquiv.apply_symm_apply]
  exact twoLinkShiftedMap_kronecker v hv A B

private theorem twoLinkShiftedMap_left_slice_mem {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) (hv : v.IsUnitaryBetween)
    (C : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) (i j : Fin d × Fin d) :
    Matrix.bipartiteSlice (twoLinkShiftedMap v hv C) i j ∈
      (twoLinkLeftOutputMap v hv).range := by
  classical
  induction C using Matrix.induction_on' with
  | h_zero =>
      rw [map_zero, Matrix.bipartiteSlice_zero]
      exact (twoLinkLeftOutputMap v hv).range.zero_mem
  | h_add C D hC hD =>
      rw [map_add, Matrix.bipartiteSlice_add]
      exact (twoLinkLeftOutputMap v hv).range.add_mem hC hD
  | h_std_basis p q c =>
      obtain ⟨t, s⟩ := p
      obtain ⟨t', s'⟩ := q
      have hsingle : Matrix.single (t, s) (t', s') c =
          Matrix.single t t' c ⊗ₖ Matrix.single s s' (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, mul_one]
      rw [hsingle, twoLinkShiftedMap_kronecker]
      have hcoeff : Matrix.bipartiteSlice
          (twoLinkLeftOutputMap v hv (Matrix.single t t' c) ⊗ₖ
            twoLinkRightOutputMap v hv (Matrix.single s s' 1)) i j =
          (twoLinkRightOutputMap v hv (Matrix.single s s' 1) i j) •
            twoLinkLeftOutputMap v hv (Matrix.single t t' c) := by
        ext x y
        simp only [Matrix.bipartiteSlice_apply, Matrix.kronecker_apply,
          Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hcoeff]
      exact (twoLinkLeftOutputMap v hv).range.smul_mem _ ⟨Matrix.single t t' c, rfl⟩

/-- The least left support algebra of the actual finite output family is
exactly the conjugated ℓ-factor, with no support-factor presentation premise.
Source: arXiv:1703.09188, Appendix, lines 2322–2334. -/
theorem leftSupportAlgebra_twoLinkOutputMap {d ℓ r : ℕ}
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) (hd : 0 < d) :
    Matrix.leftSupportAlgebra (twoLinkOutputMap u v hu hv).range =
      (twoLinkLeftOutputMap v hv).range := by
  classical
  apply le_antisymm
  · apply (Matrix.left_support_algebra_le_iff _ _).mpr
    intro X hX i j
    obtain ⟨A, rfl⟩ := hX
    exact twoLinkShiftedMap_left_slice_mem v hv (u * A * uᴴ) i j
  · rintro X ⟨A, rfl⟩
    let j : Fin d × Fin d := (⟨0, hd⟩, ⟨0, hd⟩)
    have hX : twoLinkOutputMap u v hu hv
        ((Matrix.IsUnitaryBetween.conjStarAlgEquiv u hu).symm (A ⊗ₖ 1)) ∈
        (twoLinkOutputMap u v hu hv).range := ⟨_, rfl⟩
    have h := Matrix.bipartite_slice_mem_left_support_algebra
      (twoLinkOutputMap u v hu hv).range hX j j
    rw [twoLinkOutputMap_inverse_conj_kronecker, map_one] at h
    have hslice : Matrix.bipartiteSlice (twoLinkLeftOutputMap v hv A ⊗ₖ 1) j j =
        twoLinkLeftOutputMap v hv A := by
      ext x y
      simp only [Matrix.bipartiteSlice_apply, Matrix.kronecker_apply,
        Matrix.one_apply_eq, mul_one]
    rw [hslice] at h
    exact h

private theorem twoLinkLeftOutputMap_injective {d ℓ r : ℕ}
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hv : v.IsUnitaryBetween) (hr : 0 < r) :
    Function.Injective (twoLinkLeftOutputMap v hv) := by
  intro A B hAB
  have hK := (Matrix.IsUnitaryBetween.conjStarAlgEquiv v hv).injective hAB
  ext t t'
  have h := congrArg (fun C => C (⟨0, hr⟩, t) (⟨0, hr⟩, t')) hK
  simpa only [Matrix.rightKroneckerEmbed_apply, Matrix.kronecker_apply,
    Matrix.one_apply_eq, one_mul] using h

/-- The actual least left support algebra has matrix size ℓ. This
presentation is derived from the supplied gates and their actual output
family. Source: arXiv:1703.09188, Appendix, line 2333. -/
noncomputable def twoLinkLeftSupportEquiv {d ℓ r : ℕ}
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween) (hd : 0 < d) (hr : 0 < r) :
    ↥(Matrix.leftSupportAlgebra (twoLinkOutputMap u v hu hv).range) ≃⋆ₐ[ℂ]
      Matrix (Fin ℓ) (Fin ℓ) ℂ := by
  rw [leftSupportAlgebra_twoLinkOutputMap u v hu hv hd]
  exact (StarAlgEquiv.ofInjective (twoLinkLeftOutputMap v hv)
    (twoLinkLeftOutputMap_injective v hv hr)).symm

end MPOTensor

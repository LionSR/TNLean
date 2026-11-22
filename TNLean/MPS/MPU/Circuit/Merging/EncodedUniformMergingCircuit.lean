/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import TNLean.MPS.MPU.Circuit.Merging.CompatibleBondDilationCircuit
import TNLean.MPS.MPU.Circuit.Merging.SuccessAttenuationCircuit
import TNLean.MPS.MPU.Circuit.Merging.ExactCleanAmplificationCircuit
import TNLean.MPS.MPU.Circuit.Merging.SupportedAmplification
import QICLean.Circuit.Model.UnitaryPlacement
import QICLean.Circuit.Compile.ChainPlacement
import QICLean.Circuit.Protocol.ZeroRegister.GateCount
import TNLean.MPS.MPU.Circuit.Merging.SingleSiteCircuit
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact encoded interval merging circuits

A prescribed product encoding is used for the two joining bond registers.
The two child circuits act cleanly on the same initialized auxiliary register.
Their joint output columns and the isometry of the normalized joining
contraction are the induction data.

The normalized bond dilation, the attenuation rotation, and both zero-register
reflections are constructed from matrices. The success probability is derived
from the parent isometry. Exact amplitude amplification then produces the
normalized parent columns, with the phase and all initialized flags retained.
The resulting physical circuit implements a complete logical unitary and its
adjoint cleanly on every padded logical input.

The statement is one interval-merging step. Deriving the joint child columns
from separately supported child circuits and assembling the complete interval
tree are separate arguments. Source: the constructive circuit argument in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix MPSTensor MPSPreparation QuantumCircuit
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- Concatenation of two prescribed physical basis encodings. -/
def appendBasisEmbedding {d a b : ℕ} {ρ κ : Type*}
    (e : ρ ↪ Cfg d a) (f : κ ↪ Cfg d b) : (ρ × κ) ↪ Cfg d (a + b) where
  toFun p := Fin.append (e p.1) (f p.2)
  inj' p q h := by
    apply Prod.ext
    · apply e.injective
      funext j
      have hj := congrFun h (Fin.castAdd b j)
      simpa only [Fin.append_left] using hj
    · apply f.injective
      funext j
      have hj := congrFun h (Fin.natAdd a j)
      simpa only [Fin.append_right] using hj

/-- A placed suffix operator is the tensor product with the identity on the prefix. -/
theorem placeAlong_natAddEmb_eq_reindex {d a b : ℕ}
    (U : Matrix (Cfg d b) (Cfg d b) ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb a) U =
      Matrix.reindex (Fin.appendEquiv a b) (Fin.appendEquiv a b)
        ((1 : Matrix (Cfg d a) (Cfg d a) ℂ) ⊗ₖ U) := by
  ext x y
  rw [ManyBody.placeAlong_apply]
  simp only [Fin.natAddEmb_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.appendEquiv_symm_apply]
  have hAg : (∀ v, (∀ u, Fin.natAdd a u ≠ v) → x v = y v) ↔
      (fun i : Fin a ↦ x (Fin.castAdd b i)) = (fun i ↦ y (Fin.castAdd b i)) := by
    constructor
    · intro h
      funext i
      exact h _ (fun j hij ↦ by
        have hv := congrArg Fin.val hij
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega)
    · intro h i hi
      induction i using Fin.addCases with
      | left j => exact congrFun h j
      | right j => exact (hi j rfl).elim
  simp only [hAg]
  split_ifs <;> simp only [one_mul, zero_mul]
  rfl

/-- Basis inclusions respect concatenation of prescribed product encodings. -/
theorem basisInclusion_appendBasisEmbedding {d a b : ℕ}
    {ρ κ : Type*}
    (e : ρ ↪ Cfg d a) (f : κ ↪ Cfg d b) :
    basisInclusion (appendBasisEmbedding e f) =
      (basisInclusion e ⊗ₖ basisInclusion f).submatrix
        (Fin.appendEquiv a b).symm id := by
  classical
  ext x p
  obtain ⟨⟨x₁, x₂⟩, rfl⟩ := (Fin.appendEquiv a b).surjective x
  simp only [basisInclusion, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, appendBasisEmbedding]
  have h : Fin.append x₁ x₂ = Fin.append (e p.1) (f p.2) ↔
      x₁ = e p.1 ∧ x₂ = f p.2 := by
    change (Fin.appendEquiv a b) (x₁, x₂) =
      (Fin.appendEquiv a b) (e p.1, f p.2) ↔ _
    rw [(Fin.appendEquiv a b).injective.eq_iff, Prod.mk.injEq]
  change (if Fin.append x₁ x₂ = Fin.append (e p.1) (f p.2) then (1 : ℂ) else 0) = _
  simp only [h, Fin.appendEquiv_symm_apply, id_eq]
  split_ifs <;> simp_all

/-- A clean packet action is unchanged when arbitrary encoded spectators are prefixed. -/
theorem isCleanImplementation_placeAlong_natAddEmb {d a b : ℕ}
    {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq ρ]
    (e : ρ ↪ Cfg d a) (f : κ ↪ Cfg d b)
    {U : Matrix (Cfg d b) (Cfg d b) ℂ} {Z : Matrix κ κ ℂ}
    (h : IsCleanImplementation (basisInclusion f) U Z) :
    IsCleanImplementation (basisInclusion (appendBasisEmbedding e f))
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb a) U)
      ((1 : Matrix ρ ρ ℂ) ⊗ₖ Z) := by
  classical
  change ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb a) U *
    basisInclusion (appendBasisEmbedding e f) = _
  rw [placeAlong_natAddEmb_eq_reindex, basisInclusion_appendBasisEmbedding]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
  change ((1 * basisInclusion e) ⊗ₖ (U * basisInclusion f)).submatrix
    (Fin.appendEquiv a b).symm id =
    ((basisInclusion e ⊗ₖ basisInclusion f) *
      ((1 : Matrix ρ ρ ℂ) ⊗ₖ Z)).submatrix (Fin.appendEquiv a b).symm id
  rw [← Matrix.mul_kronecker_mul]
  change ((1 * basisInclusion e) ⊗ₖ (U * basisInclusion f)).submatrix
    (Fin.appendEquiv a b).symm id =
    ((basisInclusion e * 1) ⊗ₖ (basisInclusion f * Z)).submatrix
      (Fin.appendEquiv a b).symm id
  simpa only [Matrix.one_mul, Matrix.mul_one] using congrArg
    (fun V ↦ (basisInclusion e ⊗ₖ V).submatrix (Fin.appendEquiv a b).symm id) h

/-- A placed prefix operator is the tensor product with the identity on the suffix. -/
theorem placeAlong_castAddEmb_eq_reindex {d a b : ℕ}
    (U : Matrix (Cfg d a) (Cfg d a) ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb b) U =
      Matrix.reindex (Fin.appendEquiv a b) (Fin.appendEquiv a b)
        (U ⊗ₖ (1 : Matrix (Cfg d b) (Cfg d b) ℂ)) := by
  ext x y
  rw [ManyBody.placeAlong_apply]
  simp only [Fin.castAddEmb_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fin.appendEquiv_symm_apply]
  have hAg : (∀ v, (∀ u, Fin.castAdd b u ≠ v) → x v = y v) ↔
      (fun i : Fin b ↦ x (Fin.natAdd a i)) = (fun i ↦ y (Fin.natAdd a i)) := by
    constructor
    · intro h
      funext i
      exact h _ (fun j hij ↦ by
        have hv := congrArg Fin.val hij
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega)
    · intro h i hi
      induction i using Fin.addCases with
      | left j => exact (hi j rfl).elim
      | right j => exact congrFun h j
  simp only [hAg]
  split_ifs <;> simp only [mul_one, mul_zero]

/-- A clean prefix action is unchanged when arbitrary encoded spectators are appended. -/
theorem isCleanImplementation_placeAlong_castAddEmb {d a b : ℕ}
    {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (e : ρ ↪ Cfg d a) (f : κ ↪ Cfg d b)
    {U : Matrix (Cfg d a) (Cfg d a) ℂ} {Z : Matrix ρ ρ ℂ}
    (h : IsCleanImplementation (basisInclusion e) U Z) :
    IsCleanImplementation (basisInclusion (appendBasisEmbedding e f))
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb b) U)
      (Z ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  classical
  change ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb b) U *
    basisInclusion (appendBasisEmbedding e f) = _
  rw [placeAlong_castAddEmb_eq_reindex, basisInclusion_appendBasisEmbedding]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
  change ((U * basisInclusion e) ⊗ₖ (1 * basisInclusion f)).submatrix
    (Fin.appendEquiv a b).symm id =
    ((basisInclusion e ⊗ₖ basisInclusion f) *
      (Z ⊗ₖ (1 : Matrix κ κ ℂ))).submatrix (Fin.appendEquiv a b).symm id
  rw [← Matrix.mul_kronecker_mul]
  change ((U * basisInclusion e) ⊗ₖ (1 * basisInclusion f)).submatrix
    (Fin.appendEquiv a b).symm id =
    ((basisInclusion e * Z) ⊗ₖ (basisInclusion f * 1)).submatrix
      (Fin.appendEquiv a b).symm id
  simpa only [Matrix.one_mul, Matrix.mul_one] using congrArg
    (fun V ↦ (V ⊗ₖ basisInclusion f).submatrix (Fin.appendEquiv a b).symm id) h

/-- The compatible bond and dilation registers, before appending attenuation. -/
def compatibleBondFlagEmbedding {d r q : ℕ} (hd : 2 ≤ d) (e : Fin r ↪ Cfg d q) :
    ((Fin r × Fin r) ⊕ (Fin r × Fin r)) ↪ Cfg d (2 * q + 1) where
  toFun s := fun j ↦ compatibleBondDilationCfg hd e (s, Fin.castLE hd 0) (Fin.castAdd 1 j)
  inj' s t h := by
    have hs : (s, Fin.castLE hd 0) = (t, Fin.castLE hd 0) := by
      apply compatibleBondDilationCfg_injective hd e
      funext k
      refine Fin.addCases (m := 2 * q + 1) (n := 1) ?_ ?_ k
      · intro j
        exact congrFun h j
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp [compatibleBondDilationCfg]
    exact congrArg Prod.fst hs

/-- Encoding a single physical qudit as a one-site configuration. -/
def oneSiteBasisEmbedding {d : ℕ} : Fin d ↪ Cfg d 1 :=
  (Equiv.funUnique (Fin 1) (Fin d)).symm.toEmbedding

/-- The compatible packet is precisely the product of its bond-and-dilation
registers with the full attenuation qudit. -/
theorem compatibleBondDilationEmbedding_eq_append {d r q : ℕ}
    (hd : 2 ≤ d) (e : Fin r ↪ Cfg d q) :
    compatibleBondDilationEmbedding hd e =
      appendBasisEmbedding (compatibleBondFlagEmbedding hd e) oneSiteBasisEmbedding := by
  apply Function.Embedding.ext
  intro p
  funext k
  refine Fin.addCases (m := 2 * q + 1) (n := 1) ?_ ?_ k
  · intro j
    have ha := Fin.append_left ((compatibleBondFlagEmbedding hd e) p.1)
      (oneSiteBasisEmbedding p.2) j
    change compatibleBondDilationCfg hd e p (Fin.castAdd 1 j) =
      Fin.append ((compatibleBondFlagEmbedding hd e) p.1)
        (oneSiteBasisEmbedding p.2) (Fin.castAdd 1 j)
    rw [ha]
    change compatibleBondDilationCfg hd e p (Fin.castAdd 1 j) =
      compatibleBondDilationCfg hd e (p.1, Fin.castLE hd 0) (Fin.castAdd 1 j)
    simp only [compatibleBondDilationCfg, Fin.val_castAdd]
    split_ifs <;> simp_all
    omega
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change compatibleBondDilationCfg hd e p ⟨2 * q + 1, by omega⟩ = _
    rw [compatibleBondDilationCfg_attenuation]
    simp [appendBasisEmbedding, oneSiteBasisEmbedding]

/-- Every one-qudit matrix has its exact clean action under the one-site basis encoding. -/
theorem isCleanImplementation_oneSiteBasis {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) :
    IsCleanImplementation (basisInclusion oneSiteBasisEmbedding)
      (U.submatrix (Equiv.funUnique (Fin 1) (Fin d))
        (Equiv.funUnique (Fin 1) (Fin d))) U := by
  classical
  change _ * basisInclusion oneSiteBasisEmbedding = _
  rw [show ∀ M : Matrix (Cfg d 1) (Cfg d 1) ℂ, M * basisInclusion oneSiteBasisEmbedding =
      M.submatrix id oneSiteBasisEmbedding from
    fun M ↦ Matrix.mul_submatrix_one (Equiv.refl _) _ M]
  change (U.submatrix (Equiv.funUnique (Fin 1) (Fin d))
    (Equiv.funUnique (Fin 1) (Fin d))).submatrix id oneSiteBasisEmbedding = _
  simp only [Matrix.submatrix_submatrix, Function.comp_def,
    oneSiteBasisEmbedding, Equiv.toEmbedding_apply, Equiv.apply_symm_apply, id_eq]
  change U.submatrix (Equiv.funUnique (Fin 1) (Fin d)) id =
    (1 : Matrix (Cfg d 1) (Cfg d 1) ℂ).submatrix id
      (Equiv.funUnique (Fin 1) (Fin d)).symm * U
  rw [Matrix.one_submatrix_mul]
  rfl

/-- The matrix at the last site of `n + 1` sites is its one-site matrix placed on the suffix of
one site. -/
theorem placeAt_last_eq_placeAlong_natAddEmb {d n : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ManyBody.placeAt (X := fun _ ↦ Fin d) (Fin.last n) A =
      ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb n)
        (A.submatrix (Equiv.funUnique (Fin 1) (Fin d)) (Equiv.funUnique (Fin 1) (Fin d))) := by
  ext σ τ
  rw [ManyBody.placeAt_apply, ManyBody.placeAlong_apply]
  have hc : (∀ u, u ≠ Fin.last n → σ u = τ u) ↔
      ∀ v, (∀ u, Fin.natAddEmb n u ≠ v) → σ v = τ v := by
    refine ⟨fun h v hv ↦ h v fun hv' ↦ hv 0 (by subst hv'; rfl),
      fun h u hu ↦ h u fun j hj ↦ hu ?_⟩
    rw [← hj, Subsingleton.elim j 0]
    rfl
  by_cases h : ∀ u, u ≠ Fin.last n → σ u = τ u
  · rw [ite_eq_left h, ite_eq_left (hc.mp h)]
    rfl
  · rw [ite_eq_right h, ite_eq_right (mt hc.mpr h)]

/-- The physical attenuation site acts on the full encoded qudit, including
all nonbinary levels, while retaining every bond and dilation label. -/
theorem isCleanImplementation_compatible_attenuation {d r q : ℕ}
    (hd : 2 ≤ d) (e : Fin r ↪ Cfg d q) (t : ℝ) :
    IsCleanImplementation (basisInclusion (compatibleBondDilationEmbedding hd e))
      (ManyBody.placeAt (X := fun _ ↦ Fin d) ⟨2 * q + 1, by omega⟩
        (attenuationQuditRotation hd t))
      ((1 : Matrix ((Fin r × Fin r) ⊕ (Fin r × Fin r))
        ((Fin r × Fin r) ⊕ (Fin r × Fin r)) ℂ) ⊗ₖ attenuationQuditRotation hd t) := by
  rw [compatibleBondDilationEmbedding_eq_append]
  have h := isCleanImplementation_placeAlong_natAddEmb (compatibleBondFlagEmbedding hd e)
    oneSiteBasisEmbedding (isCleanImplementation_oneSiteBasis (attenuationQuditRotation hd t))
  convert h using 1
  exact placeAt_last_eq_placeAlong_natAddEmb (n := 2 * q + 1) (attenuationQuditRotation hd t)

/-- Both fixed-size merger primitives have one actual circuit on the prescribed
child product encoding. The complete attenuation qudit remains in the logical
space, so the clean equality includes all its inputs. -/
theorem exists_compatible_merging_preparation_circuit {d r q : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    ∃ U : Matrix (Cfg d (2 * q + 2)) (Cfg d (2 * q + 2)) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (2 * q + 2)))
        (2 * (2 * q + 2) + 38 * (d ^ (2 * q + 2)) ^ 6) U ∧
      IsCleanImplementation (basisInclusion (compatibleBondDilationEmbedding hd e)) U
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
          attenuationQuditRotation hd (mergingAttenuation r)) := by
  obtain ⟨D, _, hD, hDclean⟩ := exists_compatibleNormalizedBondDilation_circuit hd hr e he hP
  let T : Matrix (Cfg d (2 * q + 2)) (Cfg d (2 * q + 2)) ℂ :=
    ManyBody.placeAt (X := fun _ ↦ Fin d) ⟨2 * q + 1, by omega⟩
      (attenuationQuditRotation hd (mergingAttenuation r))
  have hT := isGateProduct_placeAt_mergingAttenuation hd (n := 2 * q + 2)
    ⟨2 * q + 1, by omega⟩ r hr (2 * (2 * q + 2))
  have hTclean := isCleanImplementation_compatible_attenuation hd e (mergingAttenuation r)
  refine ⟨T * D, hT.mul hD, ?_⟩
  simpa only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one] using
    hTclean.mul hDclean

/-- The derived merger primitives are placed beside arbitrary encoded spectators.
The packet occupies consecutive sites, so its gate count is unchanged; the stated bound
retains a linear routing factor. -/
theorem exists_placed_compatible_merging_preparation_circuit {d r q a : ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    ∃ U : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (a + (2 * q + 2))))
        ((2 * (2 * q + 2) + 38 * (d ^ (2 * q + 2)) ^ 6) *
          (2 * (a + (2 * q + 2)))) U ∧
      IsCleanImplementation
        (basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e))) U
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
            attenuationQuditRotation hd (mergingAttenuation r))) := by
  obtain ⟨U, hU, hclean⟩ := exists_compatible_merging_preparation_circuit hd hr e he hP
  exact ⟨ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb a) U,
    (IsGateProduct.placeAlong_pathGraph_of_succ (Fin.natAddEmb a) (fun p p' h ↦ by
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd]; omega) hU).mono
      (Nat.le_mul_of_pos_right _ (by omega)),
    isCleanImplementation_placeAlong_natAddEmb f _ hclean⟩

/-- Joining bonds with both physical flags initialized to zero. -/
def joiningChildBasisEmbedding {d r : ℕ} (hd : 2 ≤ d) :
    (Fin r × Fin r) ↪ (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) where
  toFun p := (Sum.inl p, Fin.castLE hd 0)
  inj' _ _ h := Sum.inl_injective (congrArg Prod.fst h)

/-- The success projection tests the zero dilation and zero attenuation values. -/
def joiningSuccessProjection {d r : ℕ} (hd : 2 ≤ d) :
    Matrix (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d)
      (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) ℂ :=
  Matrix.diagonal fun p ↦ if (∃ x, p.1 = Sum.inl x) ∧ p.2 = Fin.castLE hd 0 then 1 else 0

/-- The successful encoded branch is the actual normalized bond reset, times
the prescribed physical attenuation coefficient; all phases are retained. -/
theorem joiningSuccessProjection_merging_preparation {d r : ℕ}
    (hd : 2 ≤ d) (hr : 0 < r) (P : Matrix (Fin r) (Fin r) ℂ) :
    joiningSuccessProjection (r := r) hd *
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
          attenuationQuditRotation hd (mergingAttenuation r)) *
        basisInclusion (joiningChildBasisEmbedding (r := r) hd) =
      (mergingAttenuation r : ℂ) •
        (basisInclusion (joiningChildBasisEmbedding (r := r) hd) *
          normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩)) := by
  have ht : attenuationQuditRotation hd (mergingAttenuation r)
      (Fin.castLE hd 0) (Fin.castLE hd 0) = (mergingAttenuation r : ℂ) := by
    have h := congrFun (attenuationQuditRotation_mulVec_zero hd (mergingAttenuation r))
      (Fin.castLE hd 0)
    simpa [Matrix.mulVec_single_one, Pi.single_apply, Fin.ext_iff] using h
  rw [Matrix.mul_assoc, show ∀ M : Matrix (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d)
      (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d) ℂ,
      M * basisInclusion (joiningChildBasisEmbedding (r := r) hd) =
        M.submatrix id (joiningChildBasisEmbedding (r := r) hd) from
    fun M ↦ Matrix.mul_submatrix_one (Equiv.refl _) _ M]
  simp only [joiningSuccessProjection]
  ext ⟨s, a⟩ p
  cases s with
  | inl x =>
    rw [Matrix.diagonal_mul]
    simp only [Sum.inl.injEq, exists_eq', Fin.isValue, true_and, submatrix_apply,
      id_eq, kroneckerMap_apply, ite_mul, one_mul, zero_mul, Matrix.smul_apply, smul_eq_mul]
    simp only [basisInclusion, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.one_apply, id_eq, ite_mul, one_mul, zero_mul]
    change (if a = Fin.castLE hd 0 then
      normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) (Sum.inl x) (Sum.inl p) *
        attenuationQuditRotation hd (mergingAttenuation r) a (Fin.castLE hd 0) else 0) =
      (mergingAttenuation r : ℂ) * ∑ j,
        if ((Sum.inl x : (Fin r × Fin r) ⊕ (Fin r × Fin r)), a) =
          (Sum.inl j, Fin.castLE hd 0) then
          normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩) j p else 0
    by_cases ha : a = Fin.castLE hd 0
    · subst a
      simp [ht, normalizedBondDilation, partialIsometryDilation, mul_comm]
    · simp [ha]
  | inr x =>
    rw [Matrix.diagonal_mul]
    simp only [reduceCtorEq, exists_false, Fin.isValue, false_and, ↓reduceIte,
      submatrix_apply, id_eq, kroneckerMap_apply, zero_mul, Matrix.smul_apply,
      smul_eq_mul, zero_eq_mul, Complex.ofReal_eq_zero]
    right
    simp only [basisInclusion, Matrix.mul_apply, Matrix.submatrix_apply,
      Matrix.one_apply, id_eq, ite_mul, one_mul, zero_mul]
    change (∑ j, if ((Sum.inr x : (Fin r × Fin r) ⊕ (Fin r × Fin r)), a) =
      (Sum.inl j, Fin.castLE hd 0) then
      normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩) j p else 0) = 0
    simp

/-- A diagonal physical operator restricts to its exact values on encoded basis states. -/
theorem diagonal_mul_basisInclusion {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ ι) (f : ι → ℂ) :
    diagonal f * basisInclusion e =
      basisInclusion e * diagonal (f ∘ e) := by
  ext x k
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : x = e k
  · subst x
    exact mul_comm _ _
  · change f x * (if x = e k then 1 else 0) =
      (if x = e k then 1 else 0) * f (e k)
    simp [h]

/-- The last two sites of the joining packet carry its two success flags. -/
def mergingFlagSites (a q : ℕ) : Fin 2 ↪ Fin (a + (2 * q + 2)) where
  toFun j := ⟨a + 2 * q + j.val, by have := j.isLt; omega⟩
  inj' i j h := Fin.ext (by have hv := congrArg Fin.val h; simp only at hv; omega)

/-- The physical selected-zero test is exactly the two encoded success tests. -/
theorem appendBasisEmbedding_merging_flags {d r q a : ℕ}
    {ρ : Type*} [NeZero d]
    (hd : 2 ≤ d) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (p : ρ × (((Fin r × Fin r) ⊕ (Fin r × Fin r)) × Fin d)) :
    (∀ j, appendBasisEmbedding f (compatibleBondDilationEmbedding hd e) p
      (mergingFlagSites a q j) = 0) ↔
      (∃ x, p.2.1 = Sum.inl x) ∧ p.2.2 = Fin.castLE hd 0 := by
  have h₀ : appendBasisEmbedding f (compatibleBondDilationEmbedding hd e) p
      (mergingFlagSites a q 0) = joiningDilationFlag hd p.2.1 := by
    change Fin.append (f p.1) (compatibleBondDilationCfg hd e p.2)
      (Fin.natAdd a ⟨2 * q, by omega⟩) = _
    rw [Fin.append_right, compatibleBondDilationCfg_dilation]
  have h₁ : appendBasisEmbedding f (compatibleBondDilationEmbedding hd e) p
      (mergingFlagSites a q 1) = p.2.2 := by
    change Fin.append (f p.1) (compatibleBondDilationCfg hd e p.2)
      (Fin.natAdd a ⟨2 * q + 1, by omega⟩) = _
    rw [Fin.append_right, compatibleBondDilationCfg_attenuation]
  rw [Fin.forall_fin_two, h₀, h₁]
  have hc : (Fin.castLE hd 0 : Fin d) = 0 := Fin.ext rfl
  rw [← hc]
  cases p.2.1 <;> simp only [joiningDilationFlag, Sum.elim_inl, Sum.elim_inr,
    Fin.castLE_inj, Fin.isValue, reduceCtorEq, exists_false, false_and,
    Sum.inl.injEq, exists_eq', true_and]
  norm_num

/-- The actual physical two-zero-flags projection restricts to the logical
successful branch on the prescribed child product encoding. -/
theorem mergingFlagProjection_mul_encoded_basis {d r q a : ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ] [NeZero d]
    (hd : 2 ≤ d) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q) :
    (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)) *
        (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)))ᴴ) *
      basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) =
      basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ joiningSuccessProjection (r := r) hd) := by
  rw [zeroFlagEmbedding_range_projection, diagonal_mul_basisInclusion]
  congr 1
  rw [show (1 : Matrix ρ ρ ℂ) = diagonal (fun _ ↦ (1 : ℂ)) by simp]
  rw [joiningSuccessProjection, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext p
  simp only [Function.comp_apply, one_mul]
  simp only [appendBasisEmbedding_merging_flags hd f e p]

/-- The exact successful branch of the placed, encoded merger is the normalized
bond contraction, with both flags zero. The child column identity is induction
data; no postselection probability is assumed. -/
theorem encoded_merging_preparation_success {d r q a : ℕ}
    {ρ m : Type*} [Fintype ρ] [DecidableEq ρ] [NeZero d]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (P : Matrix (Fin r) (Fin r) ℂ)
    (U C : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ)
    (E : Matrix (Cfg d (a + (2 * q + 2))) m ℂ)
    (V : Matrix (ρ × (Fin r × Fin r)) m ℂ)
    (hU : IsCleanImplementation
      (basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e))) U
      ((1 : Matrix ρ ρ ℂ) ⊗ₖ
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
          attenuationQuditRotation hd (mergingAttenuation r))))
    (hchild : C * E =
      basisInclusion
        (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          basisInclusion (joiningChildBasisEmbedding (r := r) hd)) * V) :
    (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)) *
        (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)))ᴴ) *
      (U * C) * E =
      (Real.sin (amplificationAngle r) : ℂ) •
        (basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
          ((1 : Matrix ρ ρ ℂ) ⊗ₖ
            basisInclusion (joiningChildBasisEmbedding (r := r) hd)) *
          ((r : ℂ) • (((1 : Matrix ρ ρ ℂ) ⊗ₖ
            normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩)) * V))) := by
  have hb := joiningSuccessProjection_merging_preparation hd hr P
  have hbt : ((1 : Matrix ρ ρ ℂ) ⊗ₖ joiningSuccessProjection (r := r) hd) *
      ((1 : Matrix ρ ρ ℂ) ⊗ₖ
        (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
          attenuationQuditRotation hd (mergingAttenuation r))) *
      ((1 : Matrix ρ ρ ℂ) ⊗ₖ
        basisInclusion (joiningChildBasisEmbedding (r := r) hd)) =
    (mergingAttenuation r : ℂ) •
      (((1 : Matrix ρ ρ ℂ) ⊗ₖ
          basisInclusion (joiningChildBasisEmbedding (r := r) hd)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩))) := by
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, hb, Matrix.kronecker_smul]
  let J := basisInclusion
    (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e))
  let E₀ := (1 : Matrix ρ ρ ℂ) ⊗ₖ
    basisInclusion (joiningChildBasisEmbedding (r := r) hd)
  let D := (1 : Matrix ρ ρ ℂ) ⊗ₖ
    (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
      attenuationQuditRotation hd (mergingAttenuation r))
  let Q := (1 : Matrix ρ ρ ℂ) ⊗ₖ joiningSuccessProjection (r := r) hd
  let A := (1 : Matrix ρ ρ ℂ) ⊗ₖ normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩)
  let S₀ := basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)) *
    (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)))ᴴ
  change C * E = J * E₀ * V at hchild
  change U * J = J * D at hU
  change Q * D * E₀ = (mergingAttenuation r : ℂ) • (E₀ * A) at hbt
  have hS₀ := mergingFlagProjection_mul_encoded_basis hd f e
  change S₀ * J = J * Q at hS₀
  change S₀ * (U * C) * E =
    (Real.sin (amplificationAngle r) : ℂ) • (J * E₀ * ((r : ℂ) • (A * V)))
  calc
    S₀ * (U * C) * E = S₀ * U * (C * E) := by simp only [Matrix.mul_assoc]
    _ = S₀ * U * (J * E₀ * V) := by rw [hchild]
    _ = (S₀ * (U * J)) * E₀ * V := by simp only [Matrix.mul_assoc]
    _ = (S₀ * J) * D * E₀ * V := by rw [hU]; simp only [Matrix.mul_assoc]
    _ = J * (Q * D * E₀) * V := by rw [hS₀]; simp only [Matrix.mul_assoc]
    _ = J * ((mergingAttenuation r : ℂ) • (E₀ * A)) * V := by rw [hbt]
    _ = (Real.sin (amplificationAngle r) : ℂ) • (J * E₀ * ((r : ℂ) • (A * V))) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      congr 1
      simp [mergingAttenuation, Complex.ofReal_mul, mul_comm]

/-- The full physical packet circuit has no local workspace to initialize.
Lifting it to a larger common workspace preserves every logical input. -/
theorem isCleanImplementation_zeroWorkspace_empty {d n : ℕ} [NeZero d]
    (U : Matrix (Cfg d n) (Cfg d n) ℂ) :
    IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := n) (0 : Fin 0 → Fin d))) U U := by
  have hJ : basisInclusion
      (workspaceEmbedding (n := n) (0 : Fin 0 → Fin d)) =
        (1 : Matrix (Cfg d n) (Cfg d n) ℂ) := by
    ext x y
    change (if x = Fin.append y (0 : Cfg d 0) then (1 : ℂ) else 0) =
      if x = y then 1 else 0
    simp [Fin.append_right_nil]
  rw [IsCleanImplementation, hJ]
  simp

/-- The exact local preparation cost after placement in the common workspace. -/
def mergingPreparationGateCount (d q n A : ℕ) : ℕ :=
  (2 * (2 * q + 2) + 38 * (d ^ (2 * q + 2)) ^ 6) * (2 * (n + A))

/-- The derived packet primitives have a complete clean action on every padded
logical state in one common initialized workspace. Their action on the active
child encoding is recorded separately and does not replace that full-space
cleanup identity. The logical operator acts only on the joining suffix packet. -/
theorem exists_clean_encoded_merging_preparation {d r q a A : ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ] [NeZero d]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef) :
    ∃ Z : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ,
    ∃ U : Matrix (Cfg d ((a + (2 * q + 2)) + A))
        (Cfg d ((a + (2 * q + 2)) + A)) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph ((a + (2 * q + 2)) + A)))
        (mergingPreparationGateCount d q (a + (2 * q + 2)) A) U ∧
      IsCleanImplementation
        (basisInclusion
          (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))) U Z ∧
      IsCleanImplementation
        (basisInclusion
          (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e))) Z
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          (normalizedBondDilation P (⟨0, hr⟩, ⟨0, hr⟩) ⊗ₖ
            attenuationQuditRotation hd (mergingAttenuation r))) ∧
      Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.image (Fin.natAdd a : Fin (2 * q + 2) → Fin (a + (2 * q + 2)))) := by
  obtain ⟨T, hT, hTactive⟩ := exists_compatible_merging_preparation_circuit hd hr e he hP
  let Z := ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.natAddEmb a) T
  have hZ := IsGateProduct.placeAlong_pathGraph_of_succ (Fin.natAddEmb a) (fun p p' h ↦ by
    simp only [Fin.natAddEmb_apply, Fin.val_natAdd]; omega) hT
  have hU := IsGateProduct.placeAlong_pathGraph_of_succ (Fin.castAddEmb A)
    (fun p p' h ↦ by simpa only [Fin.castAddEmb_apply, Fin.val_castAdd] using h) hZ
  refine ⟨Z, ManyBody.placeAlong (X := fun _ ↦ Fin d) (Fin.castAddEmb A) Z,
    hU.mono (Nat.le_mul_of_pos_right _ (by omega)), isCleanImplementation_placeAlong_workspace Z,
    isCleanImplementation_placeAlong_natAddEmb f _ hTactive, ?_⟩
  have h := ManyBody.placeAlong_mem_supportedOperators (X := fun _ ↦ Fin d) (Fin.natAddEmb a) T
  rwa [Finset.map_eq_image] at h

/-- A uniform projected column identity determines the exact postselection
probability from the normalized parent Gram. -/
theorem success_gram_of_encoded_columns {ι m : Type*}
    [Fintype ι] [DecidableEq m]
    (V F : Matrix ι m ℂ) (P : Matrix ι ι ℂ) (hP : IsStarProjection P)
    (hF : F.IsIsometry) (s : ℝ) (hcolumns : P * V = (s : ℂ) • F) :
    Vᴴ * P * V = (s : ℂ) ^ 2 • (1 : Matrix m m ℂ) := by
  change Fᴴ * F = 1 at hF
  have hself : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  have hgram : (P * V)ᴴ * (P * V) = Vᴴ * P * V := by
    simp only [conjTranspose_mul, hself, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Vᴴ P P, hP.isIdempotentElem.eq]
  rw [← hgram, hcolumns]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def, Complex.conj_ofReal, hF, pow_two]

/-- The actual joining contraction with its reciprocal success amplitude removed. -/
noncomputable def normalizedJoiningParent {r : ℕ} {ρ m : Type*}
    [Fintype ρ] [DecidableEq ρ] (hr : 0 < r)
    (P : Matrix (Fin r) (Fin r) ℂ) (V : Matrix (ρ × (Fin r × Fin r)) m ℂ) :
    Matrix (ρ × (Fin r × Fin r)) m ℂ :=
  (r : ℂ) • (((1 : Matrix ρ ρ ℂ) ⊗ₖ
    normalizedBondReset P (⟨0, hr⟩, ⟨0, hr⟩)) * V)

/-- The normalized parent in the given physical product encoding, with both
joining flags initialized. The joining pair is reset by the actual contraction. -/
noncomputable def encodedJoiningParent {d r q a : ℕ} {ρ m : Type*}
    [Fintype ρ] [DecidableEq ρ]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (P : Matrix (Fin r) (Fin r) ℂ) (V : Matrix (ρ × (Fin r × Fin r)) m ℂ) :
    Matrix (Cfg d (a + (2 * q + 2))) m ℂ :=
  basisInclusion (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
    ((1 : Matrix ρ ρ ℂ) ⊗ₖ basisInclusion (joiningChildBasisEmbedding (r := r) hd)) *
      normalizedJoiningParent hr P V

/-- The gate budget of an encoded merger, with the two child costs left as
induction data and both zero-register reflections constructed in the common pool.
The budget reserves one gate per amplification round beyond the circuit, whose global
phase is free. -/
noncomputable def encodedUniformMergingGateCount (d q n A b K₁ K₂ r : ℕ) : ℕ :=
  let K := mergingPreparationGateCount d q n A + (K₁ + K₂)
  amplificationRounds r *
      (1 + (2 * K + 2 * (n + A) * zeroRegisterReflectionGateCount d b +
        2 * (n + A) * zeroRegisterReflectionGateCount d 2)) + K

/-- Two full clean child circuits and their explicit joint-output column identity
give an actual exact merger circuit. The parent isometry is the normalized
joining contraction, rather than a supplied probability statement. Bond dilation,
attenuation, initial reflection, and success reflection are all constructed.
The complete parent unitary and its adjoint return the common pool to zero on
every padded logical input. Its support is contained in every set containing
the child supports, the initialized input flags, and the joining packet.

This is an induction step for the product encodings displayed in the statement.
Identification of an arbitrary interval representation with these columns, and
the recursive assembly on disjoint interval supports, are separate steps.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_encoded_uniform_merging_circuit {d r q a A b K₁ K₂ : ℕ}
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ] [NeZero d]
    (hd : 2 ≤ d) (hr : 0 < r) (f : ρ ↪ Cfg d a) (e : Fin r ↪ Cfg d q)
    (he : e ⟨0, hr⟩ = fun _ ↦ Fin.castLE hd 0)
    {P : Matrix (Fin r) (Fin r) ℂ} (hP : P.PosDef)
    (s : Fin b ↪ Fin (a + (2 * q + 2))) (hpool : b ≤ A) (hpool₂ : 2 ≤ A)
    (C₁ C₂ : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ)
    (U₁ U₂ : Matrix (Cfg d ((a + (2 * q + 2)) + A))
      (Cfg d ((a + (2 * q + 2)) + A)) ℂ)
    (hU₁ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph ((a + (2 * q + 2)) + A))) K₁ U₁)
    (hU₂ : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph ((a + (2 * q + 2)) + A))) K₂ U₂)
    (hclean₁ : IsCleanImplementation
      (basisInclusion
        (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))) U₁ C₁)
    (hclean₂ : IsCleanImplementation
      (basisInclusion
        (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))) U₂ C₂)
    (V : Matrix (ρ × (Fin r × Fin r))
      ({i : Fin (a + (2 * q + 2)) // i ∉ Set.range s} → Fin d) ℂ)
    (hchild : (C₁ * C₂) * basisInclusion (zeroFlagEmbedding (d := d) s) =
      basisInclusion
        (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e)) *
        ((1 : Matrix ρ ρ ℂ) ⊗ₖ
          basisInclusion (joiningChildBasisEmbedding (r := r) hd)) * V)
    (hparent : (normalizedJoiningParent hr P V).IsIsometry) :
    ∃ Z : Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ,
    ∃ W : Matrix (Cfg d ((a + (2 * q + 2)) + A))
        (Cfg d ((a + (2 * q + 2)) + A)) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph ((a + (2 * q + 2)) + A)))
        (encodedUniformMergingGateCount d q (a + (2 * q + 2)) A b K₁ K₂ r) W ∧
      Z ∈ unitary (Matrix (Cfg d (a + (2 * q + 2))) (Cfg d (a + (2 * q + 2))) ℂ) ∧
      IsCleanImplementation
        (basisInclusion
          (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))) W Z ∧
      IsCleanImplementation
        (basisInclusion
          (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))) Wᴴ Zᴴ ∧
      W * (basisInclusion
          (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d)) *
        basisInclusion (zeroFlagEmbedding (d := d) s)) =
        basisInclusion
          (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d)) *
          encodedJoiningParent hd hr f e P V ∧
      ∀ support : Finset (Fin (a + (2 * q + 2))),
        C₁ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support →
        C₂ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support →
        Set.range s ⊆ support →
        Set.range (Fin.natAdd a : Fin (2 * q + 2) → Fin (a + (2 * q + 2))) ⊆ support →
        Z ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support := by
  obtain ⟨T, U, hU, hUclean, hTactive, hTsupport⟩ :=
    exists_clean_encoded_merging_preparation (A := A) hd hr f e he hP
  let J := basisInclusion
    (workspaceEmbedding (n := a + (2 * q + 2)) (0 : Fin A → Fin d))
  let E := basisInclusion (zeroFlagEmbedding (d := d) s)
  let F := encodedJoiningParent hd hr f e P V
  let S := basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)) *
    (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)))ᴴ
  let Z₀ := T * (C₁ * C₂)
  have hjoint := hU.mul (hU₁.mul hU₂)
  have hjointClean := hUclean.mul (hclean₁.mul hclean₂)
  have hsuccess := encoded_merging_preparation_success hd hr f e P T (C₁ * C₂) E V
    hTactive hchild
  change S * Z₀ * E = (Real.sin (amplificationAngle r) : ℂ) • F at hsuccess
  have hI : (1 : Matrix ρ ρ ℂ).IsIsometry := by simp [Matrix.IsIsometry]
  have hflag := Matrix.IsIsometry.kronecker (1 : Matrix ρ ρ ℂ)
    (basisInclusion (joiningChildBasisEmbedding (r := r) hd)) hI
    (basisInclusion_isIsometry _)
  have hF : F.IsIsometry :=
    ((basisInclusion_isIsometry
      (appendBasisEmbedding f (compatibleBondDilationEmbedding hd e))).mul _ _ hflag).mul
        _ _ hparent
  have hS : IsStarProjection S :=
    isStarProjection_zeroFlagEmbedding_range (mergingFlagSites a q)
  have hprob := success_gram_of_encoded_columns (Z₀ * E) F S hS hF
    (Real.sin (amplificationAngle r))
    (by simpa only [Matrix.mul_assoc] using hsuccess)
  have hJ : J.IsIsometry := basisInclusion_isIsometry _
  have hE : E.IsIsometry := basisInclusion_isIsometry _
  obtain ⟨R, hR, hRclean⟩ := exists_isGateProduct_isCleanImplementation_zeroFlagReflection
    hd (by omega : 0 < a + (2 * q + 2)) s hpool
  obtain ⟨G, hG, hGclean⟩ := exists_isGateProduct_isCleanImplementation_zeroFlagReflection
    hd (by omega : 0 < a + (2 * q + 2)) (mergingFlagSites a q) hpool₂
  obtain ⟨W, hW, hWclean, hcolumns⟩ := exists_exact_clean_amplification_circuit
    (by omega : 2 ≤ (a + (2 * q + 2)) + A) J hJ E hE Z₀ (U * (U₁ * U₂)) R G
    hjoint hjointClean hR hRclean S hS hG hGclean
    (amplificationRounds r) (amplificationRounds_pos r hr)
    (by simpa only [amplificationAngle] using hprob)
  have hs : Real.sin (amplificationAngle r) ≠ 0 :=
    (amplificationAngle_sin_pos_le_inv r hr).1.ne'
  have hnorm : postselectionSuccess (Z₀ * E) S (Real.sin (amplificationAngle r)) = F := by
    rw [postselectionSuccess, ← Matrix.mul_assoc, hsuccess, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_smul]
  have hZ := hWclean.logical_mem_unitaryGroup hJ hW.mem_unitaryGroup
  refine ⟨postselectionAmplificationStep (Z₀ * E) S ^ amplificationRounds r * Z₀,
    W, hW.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) _), hZ,
    hWclean, hWclean.conjTranspose_of_isometry hJ hW.mem_unitaryGroup, ?_, ?_⟩
  · change W * (J * E) = J * F
    change W * (J * E) = J * postselectionSuccess (Z₀ * E) S
      (Real.sin (amplificationAngle r)) at hcolumns
    simpa only [hnorm] using hcolumns
  · intro support hC₁support hC₂support hinputSupport hpacketSupport
    have hZ₀unitary := hjointClean.logical_mem_unitaryGroup hJ hjoint.mem_unitaryGroup
    have hZ₀support : Z₀ ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support :=
      mul_mem (ManyBody.supportedOperators_mono (fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_coe.mp (hpacketSupport ⟨i, rfl⟩)) hTsupport)
        (mul_mem hC₁support hC₂support)
    have hinputReflection :
        subspaceReflection (E * Eᴴ) ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support := by
      change subspaceReflection
        (basisInclusion (zeroFlagEmbedding (d := d) s) *
          (basisInclusion (zeroFlagEmbedding (d := d) s))ᴴ) ∈ _
      rw [← selectedZeroRegisterLogical_eq_subspaceReflection]
      exact ManyBody.supportedOperators_mono (Finset.coe_subset.mp (by simpa using hinputSupport))
        (selectedZeroRegisterLogical_mem_supportedOperators s)
    have hsuccessSupport : Set.range (mergingFlagSites a q) ⊆ support := by
      rintro i ⟨p, rfl⟩
      apply hpacketSupport
      refine ⟨⟨2 * q + p.val, by have := p.isLt; omega⟩, ?_⟩
      apply Fin.ext
      change a + (2 * q + p.val) = a + 2 * q + p.val
      omega
    have hsuccessReflection :
        subspaceReflection S ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) support := by
      change subspaceReflection
        (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)) *
          (basisInclusion (zeroFlagEmbedding (d := d) (mergingFlagSites a q)))ᴴ) ∈ _
      rw [← selectedZeroRegisterLogical_eq_subspaceReflection]
      exact ManyBody.supportedOperators_mono
        (Finset.coe_subset.mp (by simpa using hsuccessSupport))
        (selectedZeroRegisterLogical_mem_supportedOperators (mergingFlagSites a q))
    exact postselectionAmplification_mem_supportedOperators Z₀ E S hZ₀unitary hZ₀support
      hinputReflection hsuccessReflection (amplificationRounds r)

end MPUCircuit

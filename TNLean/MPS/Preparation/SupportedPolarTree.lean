/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.IsometryTree
import TNLean.MPS.Preparation.PolarMerge
import TNLean.MPS.Preparation.SupportedPolar

/-!
# Coherent polar trees on the supported virtual space

For a tensor injective on a fixed set of bond pairs, its polar factor is an isometry
only on those pairs. Choosing an injective enumeration `e` of that set gives the genuine
isometry `V_n J`, where `J` is the coordinate inclusion determined by `e`. Restricting both
outputs and the input of the polar merge gives an isometry between these supported spaces.
It acts on every superposition of the supported pairs, including superpositions of different
canonical sectors.

The proof first establishes the exact factorization after restriction. The two descendants
are isometries, so the merge has Gram matrix equal to the Gram matrix of `V_n J`, namely the
identity. This proves a genuine binary tree, rather than a partial-isometry factorization.

Source: arXiv:2307.01696, eq. (16), the paragraph "Long-range MPS using measurements", and
Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors".

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and
  "Long-range MPS using measurements".
-/

open Matrix MPSTensor
open scoped BigOperators ComplexOrder

namespace MPSPreparation

variable {d D χ : ℕ}

/-- The polar factor restricted to an enumerated set of supported bond pairs. -/
noncomputable def supportedCfgPolarIso (A : MPSTensor d D)
    (e : Fin χ ↪ Fin (D * D)) (n : ℕ) : Matrix (Cfg d n) (Fin χ) ℂ :=
  (cfgPolarIso A n).submatrix id e

private theorem cfgPolarIso_eq_zero_of_notMem {A : MPSTensor d D} {n : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (hinj : IsInjectiveOn (blockTensor A n) (Set.range (virtualPairEquiv D ∘ e)))
    {x : Fin (D * D)} (hx : x ∉ Set.range e) (τ : Cfg d n) :
    cfgPolarIso A n τ x = 0 := by
  classical
  have hxS : virtualPairEquiv D x ∉ Set.range (virtualPairEquiv D ∘ e) := by
    rintro ⟨y, hy⟩
    exact hx ⟨y, (virtualPairEquiv D).injective hy⟩
  have h := MPSTensor.sum_star_polarIsoMatrix_mul hinj x x
  rw [ite_eq_right (by simp [hxS])] at h
  have hz : (fun i => polarIsoMatrix (blockTensor A n) i x) = 0 :=
    dotProduct_star_self_eq_zero.mp h
  exact congrFun hz ((decodeBlockEquiv d n).symm τ)

/-- The polar factor is a genuine isometry on an injectively enumerated support. -/
theorem isIsometry_supportedCfgPolarIso {A : MPSTensor d D} {n : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (hinj : IsInjectiveOn (blockTensor A n) (Set.range (virtualPairEquiv D ∘ e))) :
    (supportedCfgPolarIso A e n).IsIsometry := by
  classical
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [supportedCfgPolarIso, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    id_eq, cfgPolarIso]
  rw [(decodeBlockEquiv d n).symm.sum_comp (fun i =>
    star (polarIsoMatrix (blockTensor A n) i (e x)) *
      polarIsoMatrix (blockTensor A n) i (e y))]
  rw [MPSTensor.sum_star_polarIsoMatrix_mul hinj]
  simp only [e.injective.eq_iff, Set.mem_range, Function.comp_apply]
  simp

private theorem pairIndexEquiv_symm_fst (κ : ℕ) (a b : Fin κ) :
    decodeBlock κ 2 ((IsometryTree.pairIndexEquiv κ).symm (a, b)) 0 = a := by
  change (IsometryTree.pairIndexEquiv κ
    ((IsometryTree.pairIndexEquiv κ).symm (a, b))).1 = a
  rw [Equiv.apply_symm_apply]

private theorem pairIndexEquiv_symm_snd (κ : ℕ) (a b : Fin κ) :
    decodeBlock κ 2 ((IsometryTree.pairIndexEquiv κ).symm (a, b)) 1 = b := by
  change (IsometryTree.pairIndexEquiv κ
    ((IsometryTree.pairIndexEquiv κ).symm (a, b))).2 = b
  rw [Equiv.apply_symm_apply]

/-- The polar merge restricted to the supported input and the supported outputs of its
children. The two output labels are encoded in the same order as an isometry tree. -/
noncomputable def supportedMergeIso (A : MPSTensor d D)
    (e : Fin χ ↪ Fin (D * D)) (n₁ n₂ : ℕ) :
    Matrix (Fin (blockPhysDim χ 2)) (Fin χ) ℂ := fun t x =>
  mergeIso A n₁ n₂
    ((IsometryTree.pairIndexEquiv (D * D)).symm
      (e (decodeBlock χ 2 t 0), e (decodeBlock χ 2 t 1))) (e x)

/-- The supported polar factor of a joined block factors exactly through its two supported
children. This equality preserves all supported input vectors simultaneously. -/
theorem supportedCfgPolarIso_append {A : MPSTensor d D} {n₁ n₂ : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (h₁ : IsInjectiveOn (blockTensor A n₁) (Set.range (virtualPairEquiv D ∘ e)))
    (h₂ : IsInjectiveOn (blockTensor A n₂) (Set.range (virtualPairEquiv D ∘ e)))
    (τ₁ : Cfg d n₁) (τ₂ : Cfg d n₂) (x : Fin χ) :
    supportedCfgPolarIso A e (n₁ + n₂) (Fin.append τ₁ τ₂) x =
      ∑ t, supportedCfgPolarIso A e n₁ τ₁ (decodeBlock χ 2 t 0) *
        supportedCfgPolarIso A e n₂ τ₂ (decodeBlock χ 2 t 1) *
        supportedMergeIso A e n₁ n₂ t x := by
  classical
  change cfgPolarIso A (n₁ + n₂) (Fin.append τ₁ τ₂) (e x) = _
  rw [cfgPolarIso_append, ← (IsometryTree.pairIndexEquiv (D * D)).symm.sum_comp,
    ← (IsometryTree.pairIndexEquiv χ).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [supportedCfgPolarIso, Matrix.submatrix_apply, id_eq, supportedMergeIso,
    pairIndexEquiv_symm_fst, pairIndexEquiv_symm_snd]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro a ha
    simp [cfgPolarIso_eq_zero_of_notMem h₁ ha]
  · intro a
    apply Fintype.sum_of_injective e e.injective
    · intro b hb
      simp [cfgPolarIso_eq_zero_of_notMem h₂ hb]
    · intro b
      rfl

/-- The supported polar-merge identity after identifying the sum of the two child lengths
with the parent length. -/
theorem supportedCfgPolarIso_split {A : MPSTensor d D} {n₁ n₂ n : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (h₁ : IsInjectiveOn (blockTensor A n₁) (Set.range (virtualPairEquiv D ∘ e)))
    (h₂ : IsInjectiveOn (blockTensor A n₂) (Set.range (virtualPairEquiv D ∘ e)))
    (hn : n₁ + n₂ = n) (τ : Cfg d n) (x : Fin χ) :
    supportedCfgPolarIso A e n τ x =
      ∑ t, supportedCfgPolarIso A e n₁ (fun i => τ ⟨i.val, by omega⟩)
          (decodeBlock χ 2 t 0) *
        supportedCfgPolarIso A e n₂ (fun i => τ ⟨n₁ + i.val, by omega⟩)
          (decodeBlock χ 2 t 1) * supportedMergeIso A e n₁ n₂ t x := by
  subst n
  have hτ : Fin.append (fun i : Fin n₁ => τ ⟨i.val, by omega⟩)
      (fun i : Fin n₂ => τ ⟨n₁ + i.val, by omega⟩) = τ := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  have h := supportedCfgPolarIso_append h₁ h₂ (fun i => τ ⟨i.val, by omega⟩)
    (fun i => τ ⟨n₁ + i.val, by omega⟩) x
  rwa [hτ] at h

/-- Matrix form of the exact supported polar-merge identity. -/
theorem supportedCfgPolarIso_eq_joinMatrix_mul {A : MPSTensor d D} {n₁ n₂ : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (h₁ : IsInjectiveOn (blockTensor A n₁) (Set.range (virtualPairEquiv D ∘ e)))
    (h₂ : IsInjectiveOn (blockTensor A n₂) (Set.range (virtualPairEquiv D ∘ e))) :
    supportedCfgPolarIso A e (n₁ + n₂) =
      IsometryTree.joinMatrix (supportedCfgPolarIso A e n₁) (supportedCfgPolarIso A e n₂) *
        supportedMergeIso A e n₁ n₂ := by
  ext τ x
  obtain ⟨⟨τ₁, τ₂⟩, rfl⟩ := (Fin.appendEquiv n₁ n₂).surjective τ
  simpa [Matrix.mul_apply, IsometryTree.joinMatrix_apply, Fin.appendEquiv] using
    supportedCfgPolarIso_append h₁ h₂ τ₁ τ₂ x

/-- The supported polar merge has identity Gram matrix, not merely a support projector.
The input and both children may contain several canonical sectors. -/
theorem isIsometry_supportedMergeIso {A : MPSTensor d D} {n₁ n₂ : ℕ}
    {e : Fin χ ↪ Fin (D * D)}
    (h₁ : IsInjectiveOn (blockTensor A n₁) (Set.range (virtualPairEquiv D ∘ e)))
    (h₂ : IsInjectiveOn (blockTensor A n₂) (Set.range (virtualPairEquiv D ∘ e)))
    (h : IsInjectiveOn (blockTensor A (n₁ + n₂))
      (Set.range (virtualPairEquiv D ∘ e))) :
    (supportedMergeIso A e n₁ n₂).IsIsometry := by
  have hV := isIsometry_supportedCfgPolarIso h
  have hJ := IsometryTree.isIsometry_joinMatrix
    (isIsometry_supportedCfgPolarIso h₁) (isIsometry_supportedCfgPolarIso h₂)
  rw [Matrix.IsIsometry, supportedCfgPolarIso_eq_joinMatrix_mul h₁ h₂,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc
      (IsometryTree.joinMatrix _ _)ᴴ, hJ, Matrix.one_mul] at hV
  exact hV

private theorem supportedCfgPolarIso_cast (A : MPSTensor d D)
    (e : Fin χ ↪ Fin (D * D)) {n n' : ℕ} (hn : n = n') (τ : Cfg d n') (x : Fin χ) :
    supportedCfgPolarIso A e n (fun i => τ (Fin.cast hn i)) x =
      supportedCfgPolarIso A e n' τ x := by
  subst n'
  rfl

/-- A bounded-leaf binary tree for the polar factor on its supported virtual space.
The support and its enumeration are fixed before the block length and tree depth.

Source: arXiv:2307.01696, eq. (16) and "Long-range MPS using measurements". -/
theorem exists_isometryTree_matrix_eq_supportedCfgPolarIso {s : ℕ} (A : MPSTensor d D)
    (e : Fin χ ↪ Fin (D * D)) (hs : 0 < s)
    (hinj : ∀ m, s ≤ m →
      IsInjectiveOn (blockTensor A m) (Set.range (virtualPairEquiv D ∘ e)))
    (h n c : ℕ) (hlower : 2 ^ h * s ≤ n) (hupper : n ≤ 2 ^ h * c) :
    ∃ T : IsometryTree d χ c h n, T.matrix = supportedCfgPolarIso A e n := by
  induction h generalizing n with
  | zero =>
    have hsn : s ≤ n := by simpa using hlower
    exact ⟨.leaf _ (isIsometry_supportedCfgPolarIso (hinj n hsn))
      (hs.trans_le hsn) (by simpa using hupper), rfl⟩
  | succ h ih =>
    have hlo : 2 * (2 ^ h * s) ≤ n := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlower
    have hhi : n ≤ 2 * (2 ^ h * c) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hupper
    have hsum : n / 2 + (n - n / 2) = n := by omega
    obtain ⟨T₁, hT₁⟩ := ih (n / 2) (by omega) (by omega)
    obtain ⟨T₂, hT₂⟩ := ih (n - n / 2) (by omega) (by omega)
    have hpow : s ≤ 2 ^ h * s := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos h)
    have h₁ := hinj (n / 2) (by omega)
    have h₂ := hinj (n - n / 2) (by omega)
    have hW := isIsometry_supportedMergeIso h₁ h₂ (hinj _ (by omega))
    refine ⟨(IsometryTree.fork T₁ T₂ _ hW).cast hsum, ?_⟩
    ext τ x
    rw [IsometryTree.matrix_cast, IsometryTree.matrix_fork_apply, hT₁, hT₂]
    have hτ : Fin.append (fun i : Fin (n / 2) => τ ⟨i.val, by omega⟩)
        (fun i : Fin (n - n / 2) => τ ⟨n / 2 + i.val, by omega⟩) =
          fun i => τ (Fin.cast hsum i) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; rfl
      · rw [Fin.append_right]; rfl
    have heq := supportedCfgPolarIso_append h₁ h₂
      (fun i : Fin (n / 2) => τ ⟨i.val, by omega⟩)
      (fun i : Fin (n - n / 2) => τ ⟨n / 2 + i.val, by omega⟩) x
    rw [hτ] at heq
    rw [supportedCfgPolarIso_cast] at heq
    exact heq.symm

end MPSPreparation

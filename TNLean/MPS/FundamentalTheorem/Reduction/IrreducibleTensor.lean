/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import QICLean.Algebra.MatrixFamilyAction
import TNLean.MPS.FundamentalTheorem.Reduction.SimpleSeparation
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks

/-!
# Irreducible tensors: Schur's lemma, density and independence of traces

A tensor `C` of bond dimension `D` is *irreducible* (`Matrix.IsIrreducibleAction C`) when its
letters have no common invariant subspace other than `0` and `ℂ^D`. This file proves the lemmas on
irreducible tensors on which the asymmetric fundamental theorem rests (*The asymmetric fundamental
theorem of matrix product states*, Sections 3 and 4):

* irreducible tensors of positive bond dimension are exactly those whose word module is simple, and
  normal tensors are irreducible (blueprint `lem:asym_normal_simple`);
* Schur's lemma: an intertwiner of two irreducible tensors is zero or invertible, a self-intertwiner
  is a scalar, and the intertwiners between two gauge equivalent irreducible tensors form a line
  (*The asymmetric fundamental theorem of matrix product states*, Lemma 3.1);
* the density theorem: for finitely many irreducible, pairwise not gauge equivalent tensors, one
  combination of words reaches any family of target matrices, with augmentation zero when every
  tensor has a nonzero letter (*The asymmetric fundamental theorem of matrix product states*,
  Theorem 4.2);
* the independence of the word traces of such tensors (*The asymmetric fundamental theorem of matrix
  product states*, Corollary 4.3).

A combination of words `a` is an element of the word algebra; it is evaluated on `C` as
`MPSTensor.wordEval C a = LinearMap.toMatrix' (C.wordRep.asAlgebraHom a)`, an algebra map with
`wordEval C (ofWord w) = C^w`.

## Main definitions

* `MPSTensor.wordEval`: the evaluation of a combination of words on a tensor.

## Main results

* `MPSTensor.isIrreducibleAction_and_pos_iff_isSimpleModule`,
  `MPSTensor.isIrreducibleAction_of_isNormal`: irreducible tensors and simple modules.
* `MPSTensor.eq_zero_or_exists_inverse_of_intertwines`,
  `MPSTensor.exists_eq_smul_one_of_intertwines`, `MPSTensor.exists_eq_smul_of_intertwines`: Schur's
  lemma.
* `MPSTensor.exists_eval_eq_of_pairwise_not_isGaugeRelated`,
  `MPSTensor.exists_aug_eq_zero_eval_eq_of_pairwise_not_isGaugeRelated`: the density theorem.
* `MPSTensor.eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero`: independence of traces.
* `MPSTensor.eq_zero_of_intertwines_of_not_isGaugeRelated`,
  `MPSTensor.exists_ne_zero_eq_smul_reindex_one_of_intertwines`: the forms of Schur's lemma used for
  split reductions and for equal blocks.

## References

Blueprint chapter *The Multi-Block Asymmetric Fundamental Theorem* (`ch:asymmetric_ft`):
`lem:asym_normal_simple`, `thm:asym_uniq_density`, *The density theorem with targets*, and
`cor:asym_uniq_trace_independence`, *Independence of the word traces*; *The asymmetric fundamental
theorem of matrix product states*, Lemma 3.1, Theorem 4.2 and Corollary 4.3.
-/

open scoped Matrix

namespace MPSTensor

open WordAlgebra

variable {d : ℕ}

/-! ### Irreducible tensors and simple modules -/

/-- **Irreducible tensors are simple modules** (the definition of irreducible tensors in *The
asymmetric fundamental theorem of matrix product states*, Section 1): a tensor of positive bond
dimension is irreducible exactly when its word module is simple, because a subspace is invariant
under every letter exactly when it is a submodule. -/
theorem isIrreducibleAction_and_pos_iff_isSimpleModule {D : ℕ} (C : MPSTensor d D) :
    Matrix.IsIrreducibleAction C ∧ 0 < D ↔ IsSimpleModule (WordAlgebra d) C.WordModule := by
  constructor
  · rintro ⟨hC, hD⟩
    have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
    have : Nontrivial C.WordModule := C.wordRep.asModuleEquiv.toEquiv.nontrivial
    refine (isSimpleModule_iff (WordAlgebra d) C.WordModule).2 ⟨fun N => ?_⟩
    have hinv : Matrix.IsInvariantSubmodule C
        ((N.restrictScalars ℂ).map (WordModule.toVec C).toLinearMap) := by
      rintro i _ ⟨x, hx, rfl⟩
      exact ⟨(ofWord [i] : WordAlgebra d) • x, N.smul_mem _ hx, asModuleEquiv_letter_smul C i x⟩
    rcases hC _ hinv with h | h
    · refine Or.inl ((Submodule.eq_bot_iff N).2 fun x hx => ?_)
      have hmem : WordModule.toVec C x ∈
          (N.restrictScalars ℂ).map (WordModule.toVec C).toLinearMap := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact (WordModule.toVec C).map_eq_zero_iff.1 hmem
    · refine Or.inr (eq_top_iff.2 fun x _ => ?_)
      have hmem : WordModule.toVec C x ∈
          (N.restrictScalars ℂ).map (WordModule.toVec C).toLinearMap := h ▸ Submodule.mem_top
      obtain ⟨y, hy, hyx⟩ := hmem
      rwa [(WordModule.toVec C).injective hyx] at hy
  · intro hS
    have hnt : Nontrivial C.WordModule := IsSimpleModule.nontrivial (WordAlgebra d) _
    refine ⟨fun W hW => ?_, ?_⟩
    · let N : Submodule (WordAlgebra d) C.WordModule :=
        submoduleOfLetterInvariant (W.comap (WordModule.toVec C).toLinearMap) fun i x hx => by
          rw [Submodule.mem_comap] at hx ⊢
          change WordModule.toVec C _ ∈ W
          rw [asModuleEquiv_letter_smul]
          exact hW i _ hx
      rcases IsSimpleOrder.eq_bot_or_eq_top N with h | h
      · refine Or.inl ((Submodule.eq_bot_iff W).2 fun v hv => ?_)
        have hmem : (WordModule.toVec C).symm v ∈ N := by
          change WordModule.toVec C ((WordModule.toVec C).symm v) ∈ W
          rwa [LinearEquiv.apply_symm_apply]
        rw [h, Submodule.mem_bot] at hmem
        simpa using hmem
      · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
        have hmem : (WordModule.toVec C).symm v ∈ N := h ▸ Submodule.mem_top
        change WordModule.toVec C ((WordModule.toVec C).symm v) ∈ W at hmem
        rwa [LinearEquiv.apply_symm_apply] at hmem
    · rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD
        obtain ⟨x, y, hxy⟩ := hnt
        exact absurd ((WordModule.toVec C).injective (Subsingleton.elim _ _)) hxy
      · exact hD

/-- **Normal tensors are irreducible** (blueprint `lem:asym_normal_simple`, *Normal tensors define
simple modules*): a normal tensor of positive bond dimension has a simple word module. -/
theorem isIrreducibleAction_of_isNormal {D : ℕ} (C : MPSTensor d D) (hC : Kraus.IsNormal C)
    (hD : 0 < D) : Matrix.IsIrreducibleAction C :=
  ((isIrreducibleAction_and_pos_iff_isSimpleModule C).2
    (isSimpleModule_wordModule_of_isNormal C hC hD)).1

/-! ### Schur's lemma -/

/-- **Schur's lemma, first assertion** (*The asymmetric fundamental theorem of matrix product
states*, Lemma 3.1): an intertwiner `X C^i = C'^i X` of two irreducible tensors is zero or
invertible, and then the bond dimensions agree. The kernel of `X` is invariant under `C` and its
range under `C'`. -/
theorem eq_zero_or_exists_inverse_of_intertwines {D D' : ℕ} {C : MPSTensor d D}
    {C' : MPSTensor d D'} (hC : Matrix.IsIrreducibleAction C)
    (hC' : Matrix.IsIrreducibleAction C') {X : Matrix (Fin D') (Fin D) ℂ}
    (hX : ∀ i, X * C i = C' i * X) :
    X = 0 ∨ ∃ Y : Matrix (Fin D) (Fin D') ℂ, X * Y = 1 ∧ Y * X = 1 ∧ D = D' := by
  by_cases hX0 : X = 0
  · exact Or.inl hX0
  right
  have hker : Matrix.IsInvariantSubmodule C (LinearMap.ker (Matrix.toLin' X)) := by
    intro i v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hX i, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hran : Matrix.IsInvariantSubmodule C' (LinearMap.range (Matrix.toLin' X)) := by
    rintro i _ ⟨v, rfl⟩
    refine ⟨C i *ᵥ v, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hX i]
  have hinj : LinearMap.ker (Matrix.toLin' X) = ⊥ := (hC _ hker).resolve_right fun h =>
    hX0 (Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.ker_eq_top.1 h))
  have hsurj : LinearMap.range (Matrix.toLin' X) = ⊤ := (hC' _ hran).resolve_left fun h =>
    hX0 (Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.range_eq_bot.1 h))
  let e := LinearEquiv.ofBijective (Matrix.toLin' X)
    ⟨LinearMap.ker_eq_bot.1 hinj, LinearMap.range_eq_top.1 hsurj⟩
  refine ⟨LinearMap.toMatrix' (e.symm : (Fin D' → ℂ) →ₗ[ℂ] (Fin D → ℂ)), ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact LinearMap.ext fun v => e.apply_symm_apply v
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact LinearMap.ext fun v => e.symm_apply_apply v
  · simpa using e.finrank_eq

/-- **Schur's lemma, second assertion** (*The asymmetric fundamental theorem of matrix product
states*, Lemma 3.1): a self-intertwiner of an irreducible tensor is a scalar. For `D ≥ 1`, `X` has
an eigenvalue `c`, and `X - c` is an intertwiner that is not invertible, hence zero by the first
assertion. -/
theorem exists_eq_smul_one_of_intertwines {D : ℕ} {C : MPSTensor d D}
    (hC : Matrix.IsIrreducibleAction C) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : ∀ i, X * C i = C i * X) : ∃ c : ℂ, X = c • 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    exact ⟨0, Subsingleton.elim _ _⟩
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' X)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hint : ∀ i, (X - c • 1) * C i = C i * (X - c • 1) := by
    intro i
    rw [Matrix.sub_mul, Matrix.mul_sub, hX i, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  rcases eq_zero_or_exists_inverse_of_intertwines hC hC hint with h | ⟨Y, -, hYX, -⟩
  · exact sub_eq_zero.1 h
  · exfalso
    have h1 : (X - c • 1) *ᵥ v = 0 := by
      have := hv.apply_eq_smul
      rw [Matrix.toLin'_apply] at this
      rw [Matrix.sub_mulVec, this, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    refine hv.2 ?_
    calc v = (Y * (X - c • 1)) *ᵥ v := by rw [hYX, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

/-- **Schur's lemma, third assertion** (*The asymmetric fundamental theorem of matrix product
states*, Lemma 3.1): if an invertible `X₀` intertwines the irreducible tensor `C` with `C'`, every
intertwiner from `C` to `C'` is a multiple of `X₀`, since `X₀⁻¹ X` intertwines `C` with itself. Only
`C` need be irreducible. -/
theorem exists_eq_smul_of_intertwines {D D' : ℕ} {C : MPSTensor d D} {C' : MPSTensor d D'}
    (hC : Matrix.IsIrreducibleAction C)
    {X₀ : Matrix (Fin D') (Fin D) ℂ} {Y₀ : Matrix (Fin D) (Fin D') ℂ}
    (hXY : X₀ * Y₀ = 1) (hYX : Y₀ * X₀ = 1) (hX₀ : ∀ i, X₀ * C i = C' i * X₀)
    {X : Matrix (Fin D') (Fin D) ℂ} (hX : ∀ i, X * C i = C' i * X) :
    ∃ c : ℂ, X = c • X₀ := by
  have hY₀ : ∀ i, Y₀ * C' i = C i * Y₀ := fun i => by
    calc Y₀ * C' i = Y₀ * (C' i * X₀) * Y₀ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hXY, Matrix.mul_one]
      _ = C i * Y₀ := by rw [← hX₀, ← Matrix.mul_assoc, hYX, Matrix.one_mul]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_intertwines hC (X := Y₀ * X) fun i => by
    rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hY₀, Matrix.mul_assoc]
  refine ⟨c, ?_⟩
  calc X = X₀ * (Y₀ * X) := by rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
    _ = c • X₀ := by rw [hc, Matrix.mul_smul, Matrix.mul_one]

/-- **Schur's lemma for tensors that are not gauge equivalent** (*The asymmetric fundamental theorem
of matrix product states*, Lemma 3.1): an intertwiner of two irreducible tensors that are not gauge
equivalent is zero. -/
theorem eq_zero_of_intertwines_of_not_isGaugeRelated {D D' : ℕ} {C : MPSTensor d D}
    {C' : MPSTensor d D'} (hC : Matrix.IsIrreducibleAction C)
    (hC' : Matrix.IsIrreducibleAction C') {X : Matrix (Fin D') (Fin D) ℂ}
    (hX : ∀ i, X * C i = C' i * X) (hne : ¬ IsGaugeRelated C C') : X = 0 := by
  refine (eq_zero_or_exists_inverse_of_intertwines hC hC' hX).resolve_right ?_
  rintro ⟨Y, hXY, hYX, -⟩
  refine hne ⟨Y, X, hYX, hXY, fun i => ?_⟩
  calc C i * Y = Y * (X * C i) * Y := by rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
    _ = Y * C' i := by rw [hX, Matrix.mul_assoc, Matrix.mul_assoc, hXY, Matrix.mul_one]

/-- **Equal irreducible tensors give a scalar** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 2.2(c)): if `C'` is the irreducible tensor `C` read through an
identification of the bond dimensions, an invertible intertwiner from `C` to `C'` is a nonzero
multiple of that identification. -/
theorem exists_ne_zero_eq_smul_reindex_one_of_intertwines {n n' : ℕ} (hdim : n = n')
    {A : MPSTensor d n} {A' : MPSTensor d n'} (hA : Matrix.IsIrreducibleAction A)
    (heq : ∀ i, Matrix.reindex (finCongr hdim) (finCongr hdim) (A i) = A' i)
    {X : Matrix (Fin n') (Fin n) ℂ} {Y : Matrix (Fin n) (Fin n') ℂ} (hXY : X * Y = 1)
    (hint : ∀ i, X * A i = A' i * X) :
    ∃ c : ℂ, c ≠ 0 ∧ X = c • Matrix.reindex (finCongr hdim) (Equiv.refl _)
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  subst hdim
  have hA' : A' = A := funext fun i => by simpa using (heq i).symm
  subst hA'
  obtain ⟨c, rfl⟩ := exists_eq_smul_one_of_intertwines hA hint
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ⟨c, fun hc => ?_, by simp⟩
    rw [hc, zero_smul, Matrix.zero_mul] at hXY
    exact zero_ne_one hXY

/-! ### Combinations of words -/

/-- The evaluation `a ↦ a(C) = ∑_w a_w C^w` of a combination of words on a tensor (*The asymmetric
fundamental theorem of matrix product states*, Section 4), as an algebra map into the matrices: the
matrix of the action of `a` through the word representation. -/
noncomputable def wordEval {D : ℕ} (C : MPSTensor d D) :
    WordAlgebra d →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (LinearMap.toMatrixAlgEquiv' : ((Fin D → ℂ) →ₗ[ℂ] Fin D → ℂ) ≃ₐ[ℂ] _).toAlgHom.comp
    C.wordRep.asAlgebraHom

theorem wordEval_apply {D : ℕ} (C : MPSTensor d D) (a : WordAlgebra d) :
    C.wordEval a = LinearMap.toMatrix' (C.wordRep.asAlgebraHom a) := rfl

/-- A word evaluates to its matrix product, `wordEval C (ofWord w) = C^w`. -/
theorem wordEval_ofWord {D : ℕ} (C : MPSTensor d D) (w : List (Fin d)) :
    C.wordEval (ofWord w) = Kraus.evalWord C w := by
  rw [wordEval_apply, ofWord, Representation.asAlgebraHom_of, wordRep_ofList,
    LinearMap.toMatrix'_toLin']

/-- In coordinates, a combination of words acts on the word module by its evaluation. -/
theorem toVec_smul_eq_wordEval_mulVec {D : ℕ} (C : MPSTensor d D) (a : WordAlgebra d)
    (v : C.WordModule) :
    WordModule.toVec C (a • v) = C.wordEval a *ᵥ WordModule.toVec C v := by
  rw [wordEval_apply, LinearMap.toMatrix'_mulVec]
  rfl

/-- The evaluation of a combination of words is determined by its action on the word module. -/
theorem wordEval_eq_of_forall_toVec_smul {D : ℕ} (C : MPSTensor d D) {a : WordAlgebra d}
    {M : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ v : C.WordModule, WordModule.toVec C (a • v) = M *ᵥ WordModule.toVec C v) :
    C.wordEval a = M := by
  refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  have := h ((WordModule.toVec C).symm u)
  rwa [toVec_smul_eq_wordEval_mulVec, LinearEquiv.apply_symm_apply] at this

/-- On a tensor whose letters all vanish, a combination of words acts by its augmentation. -/
theorem wordEval_eq_aug_smul_one {D : ℕ} (C : MPSTensor d D) (h0 : ∀ i, C i = 0)
    (a : WordAlgebra d) : C.wordEval a = aug a • 1 := by
  refine wordEval_eq_of_forall_toVec_smul C fun v => ?_
  have hzero : ∀ (i : Fin d) (m : C.WordModule), (ofWord [i] : WordAlgebra d) • m = 0 := by
    intro i m
    apply (WordModule.toVec C).injective
    rw [asModuleEquiv_letter_smul, h0, Matrix.zero_mulVec, map_zero]
  rw [smul_eq_aug_smul hzero a v, map_smul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- A tensor with a nonzero letter has positive bond dimension. -/
theorem dim_pos_of_exists_ne_zero {D : ℕ} {C : MPSTensor d D} (h : ∃ i, C i ≠ 0) : 0 < D := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    obtain ⟨i, hi⟩ := h
    exact absurd (Subsingleton.elim _ _) hi
  · exact hD

/-- An irreducible tensor of positive bond dimension whose letters all vanish has bond dimension
one, since every line is then invariant (*The asymmetric fundamental theorem of matrix product
states*, proof of Theorem 4.2). -/
theorem dim_eq_one_of_forall_eq_zero {D : ℕ} {C : MPSTensor d D} (hC : Matrix.IsIrreducibleAction C)
    (hD : 0 < D) (h0 : ∀ i, C i = 0) : D = 1 := by
  have hv : (Pi.single (⟨0, hD⟩ : Fin D) (1 : ℂ) : Fin D → ℂ) ≠ 0 := by
    intro h
    simpa using congrFun h ⟨0, hD⟩
  have hinv : Matrix.IsInvariantSubmodule C (ℂ ∙ (Pi.single (⟨0, hD⟩ : Fin D) (1 : ℂ))) := by
    intro i v _
    rw [h0, Matrix.zero_mulVec]
    exact zero_mem _
  rcases hC _ hinv with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.1 h) hv
  · have := finrank_span_singleton (K := ℂ) hv
    rwa [h, finrank_top, Module.finrank_fin_fun] at this

/-- Two tensors of bond dimension one whose letters all vanish are gauge equivalent. -/
theorem isGaugeRelated_of_forall_eq_zero {D₁ D₂ : ℕ} {C₁ : MPSTensor d D₁}
    {C₂ : MPSTensor d D₂} (h₁ : D₁ = 1) (h₂ : D₂ = 1) (hC₁ : ∀ i, C₁ i = 0)
    (hC₂ : ∀ i, C₂ i = 0) : IsGaugeRelated C₁ C₂ := by
  subst h₁ h₂
  refine ⟨1, 1, Matrix.mul_one 1, Matrix.mul_one 1, fun i => ?_⟩
  rw [hC₁, hC₂, Matrix.zero_mul, Matrix.mul_zero]

/-- **Burnside's theorem for a tensor with a simple word module** (blueprint `thm:asym_burnside`,
*Burnside's theorem at module level*, in matrix form): every matrix is the evaluation of some
combination of words. -/
theorem exists_wordEval_eq_of_isSimpleModule {D : ℕ} (C : MPSTensor d D)
    [IsSimpleModule (WordAlgebra d) C.WordModule] (Y : Matrix (Fin D) (Fin D) ℂ) :
    ∃ b : WordAlgebra d, C.wordEval b = Y := by
  obtain ⟨b, hb⟩ := exists_smul_eq_of_isSimpleModule (d := d) C.WordModule
    (((WordModule.toVec C).symm.toLinearMap ∘ₗ Matrix.toLin' Y) ∘ₗ
      (WordModule.toVec C).toLinearMap)
  refine ⟨b, wordEval_eq_of_forall_toVec_smul C fun v => ?_⟩
  rw [hb]
  simp [Matrix.toLin'_apply]

/-! ### The density theorem and the independence of traces -/

variable {J : Type*} [Finite J] {D : J → ℕ}

/-- **Separation** (blueprint `thm:asym_separation`, *Separating a simple module from a finite
non-isomorphic family*, for tensors): for a finite family of irreducible, pairwise not gauge
equivalent tensors and a member with a nonzero letter, a combination of words with augmentation zero
evaluates to `1` on that member and to `0` on every other member. -/
theorem exists_aug_eq_zero_wordEval_eq_one (C : ∀ j, MPSTensor d (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k)) (j : J) (hj : ∃ i, C j i ≠ 0) :
    ∃ p : WordAlgebra d, aug p = 0 ∧ (C j).wordEval p = 1 ∧
      ∀ k, k ≠ j → (C k).wordEval p = 0 := by
  classical
  have := Fintype.ofFinite J
  have : IsSimpleModule (WordAlgebra d) (C j).WordModule :=
    (isIrreducibleAction_and_pos_iff_isSimpleModule (C j)).1 ⟨hirr j, dim_pos_of_exists_ne_zero hj⟩
  have hQ : ∃ (i : Fin d) (q : (C j).WordModule), (ofWord [i] : WordAlgebra d) • q ≠ 0 := by
    obtain ⟨i, hi⟩ := hj
    obtain ⟨u, hu⟩ : ∃ u, C j i *ᵥ u ≠ 0 := by
      by_contra h
      push Not at h
      exact hi (Matrix.toLin'.map_eq_zero_iff.1 (LinearMap.ext fun u => by
        rw [Matrix.toLin'_apply, h u, LinearMap.zero_apply]))
    refine ⟨i, (WordModule.toVec (C j)).symm u, fun h => hu ?_⟩
    have := congrArg (WordModule.toVec (C j)) h
    rwa [asModuleEquiv_letter_smul, LinearEquiv.apply_symm_apply, map_zero] at this
  obtain ⟨p, hp, hpj, hpS⟩ := exists_aug_eq_zero_of_forall_isEmpty_linearEquiv (C j).WordModule hQ
    (Finset.univ.filter fun k => k ≠ j ∧ ∃ i, C k i ≠ 0) C
    (fun k hk => (isIrreducibleAction_and_pos_iff_isSimpleModule (C k)).1
      ⟨hirr k, dim_pos_of_exists_ne_zero (Finset.mem_filter.1 hk).2.2⟩)
    (fun k hk => ⟨fun e => hne (Finset.mem_filter.1 hk).2.1.symm
      (isGaugeRelated_of_linearEquiv e)⟩)
  refine ⟨p, hp, wordEval_eq_of_forall_toVec_smul _ fun v => by rw [hpj, Matrix.one_mulVec],
    fun k hkj => ?_⟩
  by_cases hk : ∃ i, C k i ≠ 0
  · exact wordEval_eq_of_forall_toVec_smul _ fun v => by
      rw [hpS k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hkj, hk⟩) v, map_zero,
        Matrix.zero_mulVec]
  · push Not at hk
    rw [wordEval_eq_aug_smul_one _ hk, hp, zero_smul]

/-- **The density construction** (*The asymmetric fundamental theorem of matrix product states*,
Theorem 4.2): for a finite family of irreducible, pairwise not gauge equivalent tensors, one
combination of words evaluates to any prescribed matrices, with augmentation zero when every tensor
has a nonzero letter. With `b_j` from Burnside's theorem and the separating `p_j`, the combination
is `∑_j b_j p_j + Y_{j₀} (1 - ∑_j p_j)`, the second term for the at most one tensor `C_{j₀}` of
positive bond dimension whose letters all vanish. -/
theorem exists_wordEval_eq_and_aug_eq_zero (C : ∀ j, MPSTensor d (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k))
    (Y : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) :
    ∃ a : WordAlgebra d, ((∀ j, ∃ i, C j i ≠ 0) → aug a = 0) ∧ ∀ j, (C j).wordEval a = Y j := by
  classical
  have := Fintype.ofFinite J
  set G := Finset.univ.filter fun j => ∃ i, C j i ≠ 0 with hG
  set Z := Finset.univ.filter fun j => ¬ ∃ i, C j i ≠ 0 with hZ
  have hb : ∀ j, ∃ b : WordAlgebra d, (∃ i, C j i ≠ 0) → (C j).wordEval b = Y j := by
    intro j
    by_cases hj : ∃ i, C j i ≠ 0
    · have := (isIrreducibleAction_and_pos_iff_isSimpleModule (C j)).1
        ⟨hirr j, dim_pos_of_exists_ne_zero hj⟩
      obtain ⟨b, hb⟩ := exists_wordEval_eq_of_isSimpleModule (C j) (Y j)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hj⟩
  have hp : ∀ j, ∃ p : WordAlgebra d, aug p = 0 ∧ ((∃ i, C j i ≠ 0) →
      (C j).wordEval p = 1 ∧ ∀ k, k ≠ j → (C k).wordEval p = 0) := by
    intro j
    by_cases hj : ∃ i, C j i ≠ 0
    · obtain ⟨p, h1, h2, h3⟩ := exists_aug_eq_zero_wordEval_eq_one C hirr hne j hj
      exact ⟨p, h1, fun _ => ⟨h2, h3⟩⟩
    · exact ⟨0, map_zero _, fun h => absurd h hj⟩
  choose b hb using hb
  choose p hpaug hp using hp
  let c : J → ℂ := fun j => if h : 0 < D j then Y j ⟨0, h⟩ ⟨0, h⟩ else 0
  refine ⟨∑ j ∈ G, b j * p j + ∑ j ∈ Z, c j • (1 - ∑ k ∈ G, p k), fun hlet => ?_, fun m => ?_⟩
  · have hZ0 : Z = ∅ := Finset.filter_false_of_mem fun j _ => not_not.2 (hlet j)
    rw [hZ0, Finset.sum_empty, add_zero, map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, hpaug j, mul_zero]
  by_cases hm : ∃ i, C m i ≠ 0
  · have hmG : m ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩
    have hoff : ∀ j ∈ G, j ≠ m → (C m).wordEval (p j) = 0 := fun j hj hjm =>
      (hp j (Finset.mem_filter.1 hj).2).2 m (Ne.symm hjm)
    have h1 : ∑ j ∈ G, (C m).wordEval (b j * p j) = Y m := by
      rw [Finset.sum_eq_single m (fun j hj hjm => by rw [map_mul, hoff j hj hjm, Matrix.mul_zero])
        (fun h => absurd hmG h), map_mul, hb m hm, (hp m hm).1, Matrix.mul_one]
    have h2 : (C m).wordEval (1 - ∑ k ∈ G, p k) = 0 := by
      rw [map_sub, map_one, map_sum, Finset.sum_eq_single m (fun j hj hjm => hoff j hj hjm)
        (fun h => absurd hmG h), (hp m hm).1, sub_self]
    rw [map_add, map_sum, h1, map_sum]
    simp only [map_smul, h2, smul_zero, Finset.sum_const_zero, add_zero]
  · push Not at hm
    rcases Nat.eq_zero_or_pos (D m) with hD0 | hDm
    · have : IsEmpty (Fin (D m)) := by rw [hD0]; infer_instance
      exact Subsingleton.elim _ _
    have hm1 := dim_eq_one_of_forall_eq_zero (hirr m) hDm hm
    have hmZ : m ∈ Z := Finset.mem_filter.2 ⟨Finset.mem_univ _, not_exists.2 fun i h => h (hm i)⟩
    have hcj : ∀ j ∈ Z, j ≠ m → c j = 0 := by
      intro j hj hjm
      have hj0 : ∀ i, C j i = 0 := by
        have := (Finset.mem_filter.1 hj).2
        push Not at this
        exact this
      simp only [c]
      split_ifs with hDj
      · exact absurd (isGaugeRelated_of_forall_eq_zero
          (dim_eq_one_of_forall_eq_zero (hirr j) hDj hj0) hm1 hj0 hm) (hne hjm)
      · rfl
    have haug : aug (∑ j ∈ G, b j * p j + ∑ j ∈ Z, c j • (1 - ∑ k ∈ G, p k)) = c m := by
      have h1 : aug (1 - ∑ k ∈ G, p k) = 1 := by
        rw [map_sub, map_one, map_sum, Finset.sum_eq_zero fun k _ => hpaug k, sub_zero]
      rw [map_add, map_sum, map_sum, Finset.sum_eq_zero fun j _ => by
        rw [map_mul, hpaug j, mul_zero], zero_add]
      simp only [map_smul, h1, smul_eq_mul, mul_one]
      exact Finset.sum_eq_single m (fun j hj hjm => hcj j hj hjm) fun h => absurd hmZ h
    rw [wordEval_eq_aug_smul_one _ hm, haug]
    have : Subsingleton (Fin (D m)) := by rw [hm1]; infer_instance
    ext x y
    obtain rfl : x = ⟨0, hDm⟩ := Subsingleton.elim _ _
    obtain rfl : y = ⟨0, hDm⟩ := Subsingleton.elim _ _
    simp [c, hDm]

/-- **The density theorem** (*The asymmetric fundamental theorem of matrix product states*, Theorem
4.2, first sentence): for finitely many irreducible, pairwise not gauge equivalent tensors and any
target matrices `Y_j`, one combination of words `a` satisfies `a(C_j) = Y_j` for every `j`. -/
theorem exists_eval_eq_of_pairwise_not_isGaugeRelated (C : ∀ j, MPSTensor d (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k))
    (Y : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) :
    ∃ a : WordAlgebra d, ∀ j, LinearMap.toMatrix' ((C j).wordRep.asAlgebraHom a) = Y j := by
  obtain ⟨a, -, ha⟩ := exists_wordEval_eq_and_aug_eq_zero C hirr hne Y
  exact ⟨a, ha⟩

/-- **The density theorem without the empty word** (*The asymmetric fundamental theorem of matrix
product states*, Theorem 4.2, second sentence): if moreover every tensor has a nonzero letter, the
combination of words can be chosen with augmentation zero. -/
theorem exists_aug_eq_zero_eval_eq_of_pairwise_not_isGaugeRelated (C : ∀ j, MPSTensor d (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k)) (hlet : ∀ j, ∃ i, C j i ≠ 0)
    (Y : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ) :
    ∃ a : WordAlgebra d, aug a = 0 ∧
      ∀ j, LinearMap.toMatrix' ((C j).wordRep.asAlgebraHom a) = Y j := by
  obtain ⟨a, h0, ha⟩ := exists_wordEval_eq_and_aug_eq_zero C hirr hne Y
  exact ⟨a, h0 hlet, ha⟩

omit [Finite J] in
/-- **Traces are independent** (*The asymmetric fundamental theorem of matrix product states*,
Corollary 4.3): for irreducible, pairwise not gauge equivalent tensors, each with a nonzero letter,
a linear relation `∑_j c_j tr C_j^w = 0` on every nonempty word is trivial. The relation extends
linearly to combinations of words without empty word, and the combination `a_j` of the density
theorem with `a_j(C_k) = δ_{jk} 1` gives `c_j D_j = 0`. -/
theorem eq_zero_of_forall_sum_mul_trace_evalWord_eq_zero [Fintype J]
    (C : ∀ j, MPSTensor d (D j))
    (hirr : ∀ j, Matrix.IsIrreducibleAction (C j))
    (hne : Pairwise fun j k => ¬ IsGaugeRelated (C j) (C k)) (hlet : ∀ j, ∃ i, C j i ≠ 0)
    (c : J → ℂ)
    (h : ∀ w : List (Fin d), w ≠ [] → ∑ j, c j * (Kraus.evalWord (C j) w).trace = 0) :
    c = 0 := by
  classical
  funext j
  obtain ⟨a, ha, hY⟩ := exists_wordEval_eq_and_aug_eq_zero C hirr hne
    (fun k => if k = j then 1 else 0)
  let χ : WordAlgebra d →ₗ[ℂ] ℂ :=
    ∑ k, c k • ((Matrix.traceLinearMap (Fin (D k)) ℂ ℂ) ∘ₗ (C k).wordEval.toLinearMap)
  have hχ : ∀ w : List (Fin d), w ≠ [] →
      χ (ofWord w) = (0 : WordAlgebra d →ₗ[ℂ] ℂ) (ofWord w) := by
    intro w hw
    simpa [χ, wordEval_ofWord] using h w hw
  have h0 := linearMap_eq_on_ker_aug hχ (ha hlet)
  have hχa : χ a = c j * D j := by
    simp only [χ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, hY, Matrix.traceLinearMap_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun k _ hkj => by simp [hkj])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp
  have hD : (D j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos_of_exists_ne_zero (hlet j)).ne'
  rw [hχa, LinearMap.zero_apply] at h0
  simpa [hD] using h0

end MPSTensor

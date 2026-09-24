/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.ParentHamiltonian.Nonvanishing
import TNLean.MPS.Symmetry.MPOSymmetry.NIMRep

/-!
# Matrix product operator symmetries: single blocks, fusion characters and invertible labels

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex` lines 607–636 (a single injective block without
multiplicity is invariant only under an algebra with trivial `F`-symbols), line 660 (unit and
inverses of a group-like algebra), line 683 (for groups, the multiplicity matrices form a
representation of `G` by permutation matrices) and lines 1062–1064 (the periodic form
`U_g ψ_{A_x} = ψ_{A_{g·x}}`).

**Formalized here.** A single normal tensor symmetric under a matrix product operator fusion
algebra, with the unit acting trivially, carries a fusion character with values in `ℕ`, so no
such tensor exists when the fusion ring has no such character. Invertible labels take the value
one under every such character and hence fix a symmetric normal tensor. For a family of blocks
on which the unit acts trivially, an invertible label acts by a permutation of the blocks, the
source's statement of line 683 for arbitrary fusion rings.

The single-block obstruction proved here is the fusion-ring one. The source's obstruction of
lines 607–636 is cohomological: it shows that the `F`-symbols are trivial, which also excludes
group-like algebras with a nontrivial three-cocycle (line 738). That cohomological statement is
not formalized here; a group-like fusion ring always has the trivial character.

**Scope restriction (periodic boundary):** the symmetry hypotheses are the periodic-boundary
forms `MPOTensor.IsMPOSymmetric` and `MPOTensor.IsMPOSymmetricFamily` of the source's invariance
of the arbitrary-boundary subspace (lines 431–434); documented in
`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.

## Main results

* `MPOTensor.exists_isFusionCharacter_of_isMPOSymmetric`: a symmetric normal tensor gives a
  fusion character in `ℕ`.
* `MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter`: the rank-one no-go.
* `MPOTensor.IsFusionCharacter.eq_one_of_isInvertibleLabel`,
  `MPOTensor.mpo_mulVec_eq_of_isInvertibleLabel`: invertible labels fix a symmetric normal
  tensor.
* `MPOTensor.IsNIMRep.exists_eq_one_of_isInvertibleLabel`,
  `MPOTensor.exists_mpo_mulVec_eq_of_isInvertibleLabel`: invertible labels permute the blocks.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
-/

open scoped Matrix

namespace MPOTensor

open MPSTensor

variable {d : ℕ} {ι κ : Type*} [Fintype ι] {χ : ι → ℕ}

/-! ### The single-block case -/

/-- **A single symmetric normal tensor carries a fusion character in `ℕ`.**

Source: arXiv:2203.12563, lines 607–613 and line 683: for a single normal block `x` on which
the unit acts trivially, the action of every label is a length-independent scalar `c_a`, these
scalars are nonnegative integers (the multiplicities `M_{a,x}^x`), and associativity of the action
makes `a ↦ c_a` a one-dimensional representation of the fusion ring. -/
theorem exists_isFusionCharacter_of_isMPOSymmetric {O : ∀ a, MPOTensor d (χ a)}
    {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N) {D : ℕ} [NeZero D]
    {A : MPSTensor d D} (hA : Kraus.IsNormal A) {c : ι → ℂ} (hsym : IsMPOSymmetric O A c)
    {e : ι} (he : c e = 1) :
    ∃ m : ι → ℕ, (∀ a, c a = m a) ∧ IsFusionCharacter N e m := by
  choose m hm using fun a => exists_nat_eq_of_mpo_mulVec_mpv_eq_smul (O a) A hA (c a) (hsym a)
  refine ⟨m, hm, ?_, fun a b => ?_⟩
  · exact_mod_cast (hm e).symm.trans he
  obtain ⟨ℓ, hℓ, hinj⟩ := hA
  have hL : 0 < ℓ + 1 := Nat.succ_pos ℓ
  have hv0 : (fun σ : Fin (ℓ + 1) → Fin d => mpv A σ) ≠ 0 :=
    mpv_ne_zero_of_isNBlkInjective hinj hℓ le_rfl
  have hprod : (mpo (O a) (ℓ + 1) * mpo (O b) (ℓ + 1)) *ᵥ
      (fun σ : Fin (ℓ + 1) → Fin d => mpv A σ) =
        (c a * c b) • fun σ : Fin (ℓ + 1) → Fin d => mpv A σ := by
    rw [← Matrix.mulVec_mulVec, hsym b _ hL, Matrix.mulVec_smul, hsym a _ hL, smul_smul,
      mul_comm]
  have hsum : (mpo (O a) (ℓ + 1) * mpo (O b) (ℓ + 1)) *ᵥ
      (fun σ : Fin (ℓ + 1) → Fin d => mpv A σ) =
        (∑ k, (N a b k : ℂ) * c k) • fun σ : Fin (ℓ + 1) → Fin d => mpv A σ := by
    rw [hfus a b _ hL, Matrix.sum_mulVec, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, hsym k _ hL, smul_smul]
  have h := smul_left_injective ℂ hv0 (hprod.symm.trans hsum)
  simp only [hm] at h
  exact_mod_cast h

/-- **No single normal tensor is symmetric under a fusion ring without a fusion character in
`ℕ`.**

Source: arXiv:2203.12563, lines 632–636 and line 738: a matrix product operator symmetry that
admits no one-block solution allows no injective symmetric matrix product state. The obstruction
formalized here is the fusion-ring one: a single block would give a ring homomorphism from the
fusion ring to `ℤ` taking nonnegative values on the labels. -/
theorem not_isMPOSymmetric_of_forall_not_isFusionCharacter {O : ∀ a, MPOTensor d (χ a)}
    {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N) {e : ι}
    (hno : ∀ m : ι → ℕ, ¬ IsFusionCharacter N e m) {D : ℕ} [NeZero D]
    {A : MPSTensor d D} (hA : Kraus.IsNormal A) {c : ι → ℂ} (he : c e = 1) :
    ¬ IsMPOSymmetric O A c := by
  intro hsym
  obtain ⟨m, -, hm⟩ := exists_isFusionCharacter_of_isMPOSymmetric hfus hA hsym he
  exact hno m hm

/-- A fusion character in `ℕ` takes the value `1` on every invertible label. -/
theorem IsFusionCharacter.eq_one_of_isInvertibleLabel [DecidableEq ι] {N : ι → ι → ι → ℕ}
    {e : ι} {m : ι → ℕ} (hm : IsFusionCharacter N e m) {a : ι} (ha : IsInvertibleLabel N e a) :
    m a = 1 := by
  obtain ⟨b, hb⟩ := ha
  have h := hm.2 a b
  simp only [fun k => (hb k).1, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hm.1] at h
  exact Nat.eq_one_of_mul_eq_one_right h

/-- **Invertible labels fix a symmetric normal tensor.**

Source: arXiv:2203.12563, lines 683–684 and line 997 (the group case): an invertible label acts on
the periodic vector of a single normal symmetric block as the identity, `O_g ψ = ψ`; for a
group-like fusion ring this is the invariance `U_g |ψ_{A_x}⟩ = |ψ_{A_{g·x}}⟩` with one block. -/
theorem mpo_mulVec_eq_of_isInvertibleLabel [DecidableEq ι] {O : ∀ a, MPOTensor d (χ a)}
    {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N) {D : ℕ} [NeZero D]
    {A : MPSTensor d D} (hA : Kraus.IsNormal A) {c : ι → ℂ} (hsym : IsMPOSymmetric O A c)
    {e : ι} (he : c e = 1) {a : ι} (ha : IsInvertibleLabel N e a) (L : ℕ) (hL : 0 < L) :
    mpo (O a) L *ᵥ (fun τ : Fin L → Fin d => mpv A τ) = fun σ : Fin L → Fin d => mpv A σ := by
  obtain ⟨m, hm, hchar⟩ := exists_isFusionCharacter_of_isMPOSymmetric hfus hA hsym he
  rw [hsym a L hL, hm a, hchar.eq_one_of_isInvertibleLabel ha, Nat.cast_one, one_smul]

/-! ### Invertible labels permute the blocks -/

section Permutation

variable [Fintype κ]

/-- **An invertible label acts on the blocks by a permutation.**

Source: arXiv:2203.12563, line 683: when the unit acts trivially, `M_e = 1`, the relation
`1 = M_e = M_g M_{g⁻¹}` between matrices of nonnegative integers forces `M_g` to be a permutation
matrix: for every block `x` there is a unique block `y` with `M_{g,x}^y ≠ 0`, and
`M_{g,x}^y = 1`. -/
theorem IsNIMRep.exists_eq_one_of_isInvertibleLabel [DecidableEq ι] [DecidableEq κ]
    {N : ι → ι → ι → ℕ} {M : ι → κ → κ → ℕ} (hM : IsNIMRep N M) {e : ι}
    (he : ∀ x y, M e x y = if y = x then 1 else 0) {a : ι} (ha : IsInvertibleLabel N e a)
    (x : κ) : ∃ y, M a x y = 1 ∧ ∀ y', y' ≠ y → M a x y' = 0 := by
  obtain ⟨b, hb⟩ := ha
  -- `M_a M_b = 1` and `M_b M_a = 1`, in the row convention of `IsNIMRep`
  have hPQ : ∀ x y, ∑ z, M a x z * M b z y = if y = x then 1 else 0 := by
    intro x y
    rw [← hM b a x y, ← he x y]
    simp [fun k => (hb k).2]
  have hQP : ∀ x y, ∑ z, M b x z * M a z y = if y = x then 1 else 0 := by
    intro x y
    rw [← hM a b x y, ← he x y]
    simp [fun k => (hb k).1]
  have hxx := hPQ x x
  simp only [↓reduceIte] at hxx
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M a x z * M b z x) (by rw [hxx]; exact one_ne_zero)
  have hle : ∀ z, M a x z * M b z x ≤ 1 := fun z =>
    hxx ▸ Finset.single_le_sum (f := fun z => M a x z * M b z x) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ z)
  have hz₀' : M a x z₀ = 1 := by
    have := hle z₀
    rcases Nat.eq_zero_or_pos (M b z₀ x) with h0 | hpos
    · exact absurd (by rw [h0, mul_zero]) hz₀
    · rcases Nat.eq_zero_or_pos (M a x z₀) with h1 | h1
      · exact absurd (by rw [h1, zero_mul]) hz₀
      · nlinarith
  refine ⟨z₀, hz₀', fun y' hy' => ?_⟩
  by_contra hne
  -- some `w` with `M_b(y', w) M_a(w, y') ≠ 0`; then `w = x`
  have hyy := hQP y' y'
  simp only [↓reduceIte] at hyy
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun z => M b y' z * M a z y') (by rw [hyy]; exact one_ne_zero)
  have hwne : M b y' w ≠ 0 := fun h => hw (by simp [h])
  have hxw : w = x := by
    by_contra hwx
    have h0 := hPQ x w
    simp only [hwx, ↓reduceIte] at h0
    have := Finset.single_le_sum (f := fun z => M a x z * M b z w) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ y')
    rw [h0] at this
    exact Nat.mul_ne_zero hne hwne (Nat.le_zero.1 this)
  subst hxw
  have htwo : M a w z₀ * M b z₀ w + M a w y' * M b y' w ≤ 1 := by
    calc _ = ∑ z ∈ {z₀, y'}, M a w z * M b z w := (Finset.sum_pair hy'.symm).symm
      _ ≤ ∑ z, M a w z * M b z w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = 1 := hxx
  have h1 : 1 ≤ M a w z₀ * M b z₀ w := Nat.one_le_iff_ne_zero.2 hz₀
  have h2 : 1 ≤ M a w y' * M b y' w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hne hwne)
  omega

/-- **Invertible labels permute the blocks of a symmetric family.**

Source: arXiv:2203.12563, line 683 and lines 1062–1064: if the unit acts trivially on every block
(line 683), then for an invertible label `g` and a block `x` there is a block `y = g · x` with
`O_g ψ_x = ψ_y` at every positive length. The blocks are normal with linearly independent
periodic vectors at one positive length, a consequence of the standing assumption of line 317
(compare `MPSTensor.IsBNT.eventually_li`). -/
theorem exists_mpo_mulVec_eq_of_isInvertibleLabel [DecidableEq ι] {D : κ → ℕ}
    {O : ∀ a, MPOTensor d (χ a)} {N : ι → ι → ι → ℕ} (hfus : IsMPOFusionAlgebra O N)
    {A : ∀ x, MPSTensor d (D x)} {M : ι → κ → κ → ℂ} (hsym : IsMPOSymmetricFamily O A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x) {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x => fun σ : Fin L₀ → Fin d => mpv (A x) σ) {e : ι}
    (hunit : ∀ x, ∀ L : ℕ, 0 < L →
      mpo (O e) L *ᵥ (fun τ : Fin L → Fin d => mpv (A x) τ) = fun σ : Fin L → Fin d => mpv (A x) σ)
    {a : ι} (ha : IsInvertibleLabel N e a) (x : κ) :
    ∃ y, ∀ L : ℕ, 0 < L →
      mpo (O a) L *ᵥ (fun τ : Fin L → Fin d => mpv (A x) τ) =
        fun σ : Fin L → Fin d => mpv (A y) σ := by
  classical
  obtain ⟨M', hMM', hM'⟩ := exists_isNIMRep_of_isMPOSymmetricFamily hfus hsym hA hD hL₀ hli
  have he : ∀ x y, M' e x y = if y = x then 1 else 0 := by
    intro x y
    have h1 := hsym.mulVec_eq_sum e x hL₀
    rw [hunit x L₀ hL₀] at h1
    have h2 : (fun σ : Fin L₀ → Fin d => mpv (A x) σ) =
        ∑ y, (if y = x then (1 : ℂ) else 0) • fun σ : Fin L₀ → Fin d => mpv (A y) σ := by
      simp
    have := Fintype.linearIndependent_iffₛ.1 hli _ _ (h2.symm.trans h1) y
    rw [hMM'] at this
    split_ifs at this ⊢ <;> exact_mod_cast this.symm
  obtain ⟨y, hy1, hy0⟩ := hM'.exists_eq_one_of_isInvertibleLabel he ha x
  refine ⟨y, fun L hL => ?_⟩
  rw [hsym a x L hL]
  funext σ
  rw [Finset.sum_eq_single y (fun y' _ hy' => by rw [hMM', hy0 y' hy', Nat.cast_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ y) h), hMM', hy1, Nat.cast_one, one_mul]

end Permutation

end MPOTensor

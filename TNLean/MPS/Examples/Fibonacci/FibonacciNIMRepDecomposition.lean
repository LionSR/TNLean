/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciNIMRepClassification
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Fibonacci representations as direct sums of the regular representation

Every finite matrix with natural entries satisfying `T² = I + T` is a direct sum of
`[[0, 1], [1, 1]]`. No symmetry hypothesis is needed: the equation itself forces symmetry.
The summands are indexed by the diagonal-zero entries.

**Source.** Garre-Rubio, Lootens and Molnár, arXiv:2203.12563, Section `sec:examples`,
`Papers/2203.12563/REsubmission.tex` lines 1991–1993.

**Local fix (missing indecomposability hypothesis):** The printed two-block uniqueness claim
omits indecomposability and is false without that hypothesis: two regular summands give a
four-block solution. Here the unrestricted direct sums are classified, and two-block uniqueness
is proved only for nonempty indecomposable families. This corrects the literal source claim;
it is not an assumption stated in the paper. See
`docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`.

## Unrestricted Fibonacci actions on families of normal states

The multiplicities of a finite normal family invariant under a Fibonacci MPO algebra
are a direct sum of regular two-label actions, provided the unit fixes the family.
The number of state blocks is unrestricted and may be zero. The representatives of the
regular summands are exactly the labels with zero diagonal coefficient in the tau action.

The physical unit condition is required only at the positive length where the periodic
state vectors are linearly independent. Coefficient uniqueness derives the identity action
of the unit; it is not inferred from the fusion relation or from invariance alone.

Source: Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, lines 458--460,
564--568, and 1991--1993. The missing indecomposability hypothesis in the printed
two-block claim is corrected in `docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`.
This result concerns action multiplicities. It does not classify the L-symbols or prove
their gauge equivalence to the Fibonacci F-symbols.

**Scope restriction (periodic boundary):** the input is the periodic symmetry condition
of lines 567--568, as documented in `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.
-/

open MPTensor

section

open MPSTensor MPOTensor

namespace FibonacciCompression

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private theorem exists_reciprocal_partner (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (x : κ) : ∃ y, x ≠ y ∧ T x y = 1 ∧ T y x = 1 ∧
      ∀ z, z ≠ x → z ≠ y → T x z * T z x = 0 := by
  have hd := hsq x x
  simp only [ite_true] at hd
  have hle := Finset.single_le_sum (fun z _ => Nat.zero_le (T x z * T z x))
    (Finset.mem_univ x)
  have hxx : T x x ≤ 1 := by nlinarith
  have hxxsq : T x x * T x x = T x x := by
    interval_cases h : T x x <;> simp
  have hsum : ∑ z ∈ Finset.univ.erase x, T x z * T z x = 1 := by
    have hs := Finset.sum_erase_add Finset.univ (fun z => T x z * T z x)
      (Finset.mem_univ x)
    omega
  obtain ⟨y, hy, hpos⟩ := Finset.sum_pos_iff.mp (show
    0 < ∑ z ∈ Finset.univ.erase x, T x z * T z x by omega)
  have hyle := Finset.single_le_sum (fun z _ => Nat.zero_le (T x z * T z x)) hy
  have hprod : T x y * T y x = 1 := by omega
  have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
  refine ⟨y, hxy, Nat.eq_one_of_mul_eq_one_right hprod,
    Nat.eq_one_of_mul_eq_one_left hprod, ?_⟩
  intro z hzx hzy
  have hs := Finset.sum_erase_add (Finset.univ.erase x)
    (fun z => T x z * T z x) hy
  have hz := Finset.single_le_sum (fun z _ => Nat.zero_le (T x z * T z x))
    (show z ∈ (Finset.univ.erase x).erase y by simp [hzx, hzy])
  omega

private theorem isolated_pair_of_diagonal (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    {x y : κ} (hxy : x ≠ y) (hxy' : T x y = 1) (hyx : T y x = 1)
    (hyy : T y y = 1) (z : κ) (hzx : z ≠ x) (hzy : z ≠ y) :
    T x z = 0 ∧ T y z = 0 := by
  have hxz := hsq x z
  have hyz := hsq y z
  simp only [Ne.symm hzx, Ne.symm hzy, ite_false, zero_add] at hxz hyz
  have h₁ := Finset.single_le_sum (fun k _ => Nat.zero_le (T x k * T k z))
    (Finset.mem_univ y)
  have h₂ := Finset.add_le_sum (fun k _ => Nat.zero_le (T y k * T k z))
    (Finset.mem_univ x) (Finset.mem_univ y) hxy
  rw [hxy'] at h₁
  rw [hyx, hyy] at h₂
  simp only [one_mul] at h₁ h₂
  omega

/-- Every vertex of a nonnegative integral Fibonacci matrix has a unique partner, with
complementary diagonal entries and no matrix entries leaving their pair (GLM23, line 1993). -/
theorem exists_fibNim_pair (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (x : κ) : ∃ y, x ≠ y ∧ T x y = 1 ∧ T y x = 1 ∧ T x x + T y y = 1 ∧
      ∀ z, z ≠ x → z ≠ y → T x z = 0 ∧ T y z = 0 := by
  obtain ⟨y, hxy, hxy', hyx, hzero⟩ := exists_reciprocal_partner T hsq x
  have hcross : ∀ z, z ≠ x → z ≠ y → T x z * T z y = 0 := by
    intro z hzx hzy
    have hz := hsq z x
    simp only [hzx, ite_false, zero_add] at hz
    have hle := Finset.single_le_sum (fun k _ => Nat.zero_le (T z k * T k x))
      (Finset.mem_univ y)
    rw [hyx, mul_one] at hle
    have hprod := hzero z hzx hzy
    have hm := Nat.mul_le_mul_left (T x z) (show T z y ≤ T z x by omega)
    omega
  have hdiag : T x x + T y y = 1 := by
    have h := hsq x y
    rw [Finset.sum_eq_add_of_mem x y (Finset.mem_univ x) (Finset.mem_univ y) hxy
      (fun z _ hz => hcross z hz.1 hz.2)] at h
    simpa [hxy, hxy'] using h.symm
  refine ⟨y, hxy, hxy', hyx, hdiag, ?_⟩
  intro z hzx hzy
  rcases Nat.eq_zero_or_pos (T y y) with hyy | hyy
  · have hxx : T x x = 1 := by omega
    exact (isolated_pair_of_diagonal T hsq hxy.symm hyx hxy' hxx z hzy hzx).symm
  · exact isolated_pair_of_diagonal T hsq hxy hxy' hyx (by omega) z hzx hzy

/-- The other vertex in the regular Fibonacci summand containing `x` (GLM23, line 1993). -/
noncomputable def fibNimPartner (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (x : κ) : κ :=
  Classical.choose (exists_fibNim_pair T hsq x)

private theorem fibNimPartner_spec (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (x : κ) : x ≠ fibNimPartner T hsq x ∧ T x (fibNimPartner T hsq x) = 1 ∧
      T (fibNimPartner T hsq x) x = 1 ∧
      T x x + T (fibNimPartner T hsq x) (fibNimPartner T hsq x) = 1 ∧
      ∀ z, z ≠ x → z ≠ fibNimPartner T hsq x →
        T x z = 0 ∧ T (fibNimPartner T hsq x) z = 0 :=
  Classical.choose_spec (exists_fibNim_pair T hsq x)

/-- The partner operation is an involution without fixed points (GLM23, line 1993). -/
theorem fibNimPartner_involutive (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y) :
    Function.Involutive (fibNimPartner T hsq) := by
  intro x
  have hx := fibNimPartner_spec T hsq x
  have hy := fibNimPartner_spec T hsq (fibNimPartner T hsq x)
  by_contra h
  have hz := hx.2.2.2.2 _ h hy.1.symm
  have hentry := hy.2.1
  omega

/-- Symmetry follows from the Fibonacci equation over the natural numbers; it is not an
additional hypothesis in the decomposition (GLM23, line 1993). -/
theorem fibNim_symmetric_of_sq (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y) :
    ∀ x y, T x y = T y x := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  have hx := fibNimPartner_spec T hsq x
  have hy := fibNimPartner_spec T hsq y
  by_cases hyp : y = fibNimPartner T hsq x
  · subst y
    exact hx.2.1.trans hx.2.2.1.symm
  have hxp : x ≠ fibNimPartner T hsq y := by
    intro h
    apply hyp
    rw [h, fibNimPartner_involutive]
  rw [(hx.2.2.2.2 y (Ne.symm hxy) hyp).1, (hy.2.2.2.2 x hxy hxp).1]

private noncomputable def fibNimBlockMap (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (v : {x // T x x = 0} × Fin 2) : κ :=
  if v.2 = 0 then v.1 else fibNimPartner T hsq v.1

private theorem fibNimBlockMap_bijective (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y) :
    Function.Bijective (fibNimBlockMap T hsq) := by
  have hp := fibNimPartner_involutive T hsq
  have hd (x : {x // T x x = 0}) :
      T (fibNimPartner T hsq x) (fibNimPartner T hsq x) = 1 := by
    have h := (fibNimPartner_spec T hsq x).2.2.2.1
    rw [x.property, zero_add] at h
    exact h
  constructor
  · rintro ⟨x, i⟩ ⟨y, j⟩ h
    fin_cases i <;> fin_cases j
    · change (x : κ) = y at h
      exact Prod.ext (Subtype.ext h) rfl
    · change (x : κ) = fibNimPartner T hsq y at h
      have hdiag := hd y
      rw [← h, x.property] at hdiag
      contradiction
    · change fibNimPartner T hsq x = (y : κ) at h
      have hdiag := hd x
      rw [h, y.property] at hdiag
      contradiction
    · change fibNimPartner T hsq x = fibNimPartner T hsq y at h
      exact Prod.ext (Subtype.ext (hp.injective h)) rfl
  · intro x
    by_cases hxx : T x x = 0
    · exact ⟨(⟨x, hxx⟩, 0), by simp [fibNimBlockMap]⟩
    · have hy : T (fibNimPartner T hsq x) (fibNimPartner T hsq x) = 0 := by
        have h := (fibNimPartner_spec T hsq x).2.2.2.1
        omega
      exact ⟨(⟨fibNimPartner T hsq x, hy⟩, 1), by simp [fibNimBlockMap, hp x]⟩

private theorem fibNimBlockMap_entries (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y)
    (u v : {x // T x x = 0}) (i j : Fin 2) :
    T (fibNimBlockMap T hsq (u, i)) (fibNimBlockMap T hsq (v, j)) =
      if u = v then fibFusionMatrix i j else 0 := by
  have hu := fibNimPartner_spec T hsq u
  have hv := fibNimPartner_spec T hsq v
  have hdu : T (fibNimPartner T hsq u) (fibNimPartner T hsq u) = 1 := by
    simpa [u.property] using hu.2.2.2.1
  have hdv : T (fibNimPartner T hsq v) (fibNimPartner T hsq v) = 1 := by
    simpa [v.property] using hv.2.2.2.1
  by_cases huv : u = v
  · subst v
    fin_cases i <;> fin_cases j <;>
      simp [fibNimBlockMap, fibFusionMatrix, u.property, hu.2.1, hu.2.2.1, hdu]
  · have hvu : (v : κ) ≠ u := fun h => huv (Subtype.ext h.symm)
    have hvpu : (v : κ) ≠ fibNimPartner T hsq u := by
      intro h
      rw [← h, v.property] at hdu
      contradiction
    have hpvu : fibNimPartner T hsq v ≠ u := by
      intro h
      rw [h, u.property] at hdv
      contradiction
    have hpvpu : fibNimPartner T hsq v ≠ fibNimPartner T hsq u := by
      intro h
      exact hvu ((fibNimPartner_involutive T hsq).injective h)
    have hz₀ := hu.2.2.2.2 v hvu hvpu
    have hz₁ := hu.2.2.2.2 (fibNimPartner T hsq v) hpvu hpvpu
    fin_cases i <;> fin_cases j <;>
      simp [fibNimBlockMap, huv, hz₀.1, hz₀.2, hz₁.1, hz₁.2]

/-- **Unrestricted finite Fibonacci matrix classification.** The diagonal-zero vertices index
regular two-dimensional summands, with zero coefficients between different summands.
This states the direct-sum form of the two-block action in GLM23, line 1993. -/
theorem exists_equiv_prod_of_fibNim_sq (T : κ → κ → ℕ)
    (hsq : ∀ x y, (if x = y then 1 else 0) + T x y = ∑ z, T x z * T z y) :
    ∃ σ : κ ≃ {x // T x x = 0} × Fin 2, ∀ x y,
      T x y = if (σ x).1 = (σ y).1 then fibFusionMatrix (σ x).2 (σ y).2 else 0 := by
  let e := Equiv.ofBijective (fibNimBlockMap T hsq) (fibNimBlockMap_bijective T hsq)
  refine ⟨e.symm, ?_⟩
  intro x y
  obtain ⟨⟨u, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨v, j⟩, rfl⟩ := e.surjective y
  simp only [Equiv.symm_apply_apply]
  exact fibNimBlockMap_entries T hsq u v i j

/-- **Every unital Fibonacci NIM-representation is a direct sum of regular representations.**
There is no restriction on the number of blocks and no assumed symmetry of the multiplicities
(GLM23, lines 564–565 and 1993). -/
theorem exists_equiv_prod_of_isNIMRep_fibNim {M : Fin 2 → κ → κ → ℕ}
    (hM : IsNIMRep fibNim M) (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0) :
    ∃ σ : κ ≃ {x // M 1 x x = 0} × Fin 2, ∀ a x y,
      M a x y = if (σ x).1 = (σ y).1 then fibNim a (σ x).2 (σ y).2 else 0 := by
  obtain ⟨σ, hσ⟩ := exists_equiv_prod_of_fibNim_sq (M 1)
    (fibNim_tau_sq_of_isNIMRep hM hunit)
  refine ⟨σ, fun a x y => ?_⟩
  fin_cases a
  · have he : x = y ↔ (σ x).1 = (σ y).1 ∧ (σ x).2 = (σ y).2 := by
      rw [← Prod.ext_iff]
      exact σ.injective.eq_iff.symm
    change M 0 x y = _
    rw [hunit]
    simp only [fibNim, Matrix.one_apply]
    by_cases h₁ : (σ x).1 = (σ y).1 <;>
      by_cases h₂ : (σ x).2 = (σ y).2 <;> simp [he, h₁, h₂]
  · exact hσ x y

/-- A nonempty indecomposable Fibonacci NIM-representation has exactly two blocks, carrying
the regular action `τ · x₁ = xτ`, `τ · xτ = x₁ + xτ` (GLM23, line 1993).
Indecomposability is the standard matrix condition on the action of `τ`. -/
theorem exists_equiv_of_isIndecomposable_fibNim [Nonempty κ]
    {M : Fin 2 → κ → κ → ℕ} (hM : IsNIMRep fibNim M)
    (hunit : ∀ x y, M 0 x y = if x = y then 1 else 0)
    (hind : Matrix.IsIndecomposable (M 1)) :
    Fintype.card κ = 2 ∧ ∃ σ : κ ≃ Fin 2, ∀ a x y, M a x y = fibNim a (σ x) (σ y) := by
  let x : κ := Classical.choice inferInstance
  let hsq := fibNim_tau_sq_of_isNIMRep hM hunit
  let y := fibNimPartner (M 1) hsq x
  have hp := fibNimPartner_spec (M 1) hsq x
  have hxy : x ≠ y := hp.1
  let b : κ → ℕ := fun z => if z = x ∨ z = y then 1 else 0
  have hb : Matrix.BlockTriangular (M 1) b := by
    intro i j hij
    by_cases hi : i = x ∨ i = y
    · by_cases hj : j = x ∨ j = y
      · simp [b, hi, hj] at hij
      · have hz := hp.2.2.2.2 j (not_or.mp hj).1 (not_or.mp hj).2
        rcases hi with rfl | rfl
        · exact hz.1
        · exact hz.2
    · by_cases hj : j = x ∨ j = y <;> simp [b, hi, hj] at hij
  obtain ⟨c, hc⟩ := (Matrix.isIndecomposable_iff_blockTriangular_const
    (α := ℕ) (M 1)).mp hind b hb
  have hc1 : c = 1 := by
    have h := congrFun hc x
    simpa [b] using h.symm
  have hfull : ∀ z, z = x ∨ z = y := by
    intro z
    have h := congrFun hc z
    rw [hc1] at h
    by_contra hz
    simp [b, hz] at h
  have hcard : Fintype.card κ = 2 := by
    have huniv : (Finset.univ : Finset κ) = {x, y} := by
      ext z
      simpa using hfull z
    change Finset.univ.card = 2
    rw [huniv]
    simp [hxy]
  exact ⟨hcard, exists_equiv_of_isNIMRep_fibNim_of_card_eq_two hcard hM hunit⟩

end FibonacciCompression

end

section

open scoped Matrix

open MPSTensor MPOTensor

namespace FibonacciCompression

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {d : ℕ} {χ : Fin 2 → ℕ} {D : κ → ℕ}

/-- Every finite unital Fibonacci-symmetric normal family is a direct sum of regular
two-label families. The physical unit condition at one independent length derives the
unit coefficient matrix, and the resulting number of blocks is even.

Source: GLM23, lines 564--568 and 1991--1993, with the direct-sum correction of
`docs/paper-gaps/glm23_fibonacci_module_rank_scope.tex`. No rank bound, nonemptiness,
symmetry of the coefficients, or indecomposability is assumed. -/
theorem exists_equiv_prod_of_isMPOSymmetricFamily_fibNim
    {O : ∀ a, MPOTensor d (χ a)} (hfus : IsMPOFusionAlgebra O fibNim)
    {A : ∀ x, MPSTensor d (D x)} {M : Fin 2 → κ → κ → ℂ}
    (hsym : IsMPOSymmetricFamily O A M)
    (hA : ∀ x, Kraus.IsNormal (A x)) (hD : ∀ x, 0 < D x)
    {L₀ : ℕ} (hL₀ : 0 < L₀)
    (hli : LinearIndependent ℂ fun x ↦ fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ)
    (hunit : ∀ x, mpo (O 0) L₀ *ᵥ (fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ) =
      fun σ : Fin L₀ → Fin d ↦ mpv (A x) σ) :
    Even (Fintype.card κ) ∧
      ∃ σ : κ ≃ {x // M 1 x x = 0} × Fin 2, ∀ a x y,
        M a x y = if (σ x).1 = (σ y).1 then
          (fibNim a (σ x).2 (σ y).2 : ℂ) else 0 := by
  classical
  obtain ⟨M', hMM', hM'⟩ :=
    exists_isNIMRep_of_isMPOSymmetricFamily hfus hsym hA hD hL₀ hli
  have hunit' : ∀ x y, M' 0 x y = if x = y then 1 else 0 := by
    intro x y
    have hcoeff := Fintype.linearIndependent_iffₛ.1 hli (M 0 x)
      (fun z ↦ if z = x then (1 : ℂ) else 0)
      (by rw [← hsym.mulVec_eq_sum 0 x hL₀]; simpa using hunit x) y
    rw [hMM'] at hcoeff
    by_cases hxy : x = y
    · simpa [hxy] using hcoeff
    · simpa [hxy, Ne.symm hxy] using hcoeff
  obtain ⟨σ, hσ⟩ := exists_equiv_prod_of_isNIMRep_fibNim hM' hunit'
  let e : {x // M' 1 x x = 0} ≃ {x // M 1 x x = 0} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [hMM']; simp
  let σ' := σ.trans (e.prodCongr (Equiv.refl (Fin 2)))
  have hcard : Fintype.card κ =
      Fintype.card {x // M 1 x x = 0} + Fintype.card {x // M 1 x x = 0} := by
    simpa [Fintype.card_prod, Fintype.card_fin, mul_two] using Fintype.card_congr σ'
  refine ⟨⟨_, hcard⟩, σ', ?_⟩
  intro a x y
  change M a x y = if e (σ x).1 = e (σ y).1 then
    (fibNim a (σ x).2 (σ y).2 : ℂ) else 0
  have hcoeff := (hMM' a x y).trans
    (congrArg (fun n : ℕ ↦ (n : ℂ)) (hσ a x y))
  simpa only [Nat.cast_ite, Nat.cast_zero, e.injective.eq_iff] using! hcoeff

end FibonacciCompression

end

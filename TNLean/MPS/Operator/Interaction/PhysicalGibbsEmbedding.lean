/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Simple.CommutingForm
import TNLean.MPS.Operator.PhysicalSector.SitewisePhysicalMatrix
import QICLean.Algebra.Kronecker.FiniteKroneckerProduct
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Generic physical Gibbs embedding

This file develops generic one-site and first-site two-site operators, their
placements on the windows of a ring (`ManyBody.placeAlong` along
`ManyBody.ringWindow`), and the exponential of a sum of commuting one-site
energies.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 999--1016
-/

open scoped Matrix BigOperators ComplexOrder
open ManyBody

noncomputable section

namespace MPOTensor

variable {d N : ℕ}

/-- A one-site matrix in the configuration indexing of the windows of one site.

This wrapper will carry the physical one-site energy in the complement
construction for CPSV16, Definition 4.8, lines 831–847. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def oneSiteOperator (k : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ :=
  fun x y ↦ k (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)

/-- The one-site coordinate operator is matrix reindexing along the unique
identification of `Fin 1 → Fin d` with `Fin d`. -/
theorem oneSiteOperator_eq_reindexAlgEquiv_symm
    (A : Matrix (Fin d) (Fin d) ℂ) :
    oneSiteOperator A =
      (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.funUnique (Fin 1) (Fin d))).symm A := by
  ext x y
  rfl

open scoped Matrix.Norms.Operator in
private theorem exp_oneSiteOperator
    (A : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (oneSiteOperator A) =
      oneSiteOperator (NormedSpace.exp A) := by
  rw [oneSiteOperator_eq_reindexAlgEquiv_symm,
    oneSiteOperator_eq_reindexAlgEquiv_symm]
  symm
  exact NormedSpace.map_exp
    (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.funUnique (Fin 1) (Fin d))).symm
    (LinearMap.continuous_of_finiteDimensional
      (Matrix.reindexAlgEquiv ℂ ℂ
        (Equiv.funUnique (Fin 1) (Fin d))).symm.toLinearMap) A

/-- A two-site operator which acts by `k` on the first site and by the
identity on the second.

This is the fixed two-site form used for the physical Hamiltonian of CPSV16,
Definition 4.8, lines 831–847. The ambient physical-complement construction
is recorded in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def twoSiteFirstOperator (k : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  fun x y ↦
    k (x ⟨0, by omega⟩) (y ⟨0, by omega⟩) *
      (1 : Matrix (Fin d) (Fin d) ℂ)
        (x ⟨1, by omega⟩) (y ⟨1, by omega⟩)

/-- A Hermitian first-site operator remains Hermitian when tensored with the
identity on the second site.

This is the Hermiticity property of the local term in CPSV16,
Definition 4.8, lines 831–847. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem twoSiteFirstOperator_isHermitian
    {k : Matrix (Fin d) (Fin d) ℂ} (hk : k.IsHermitian) :
    (twoSiteFirstOperator k).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, twoSiteFirstOperator, star_mul,
    Matrix.one_apply]
  rw [hk.apply]
  split <;> split <;> simp_all

/-- Placing a two-site operator which acts only on its first site on a ring window is
placing the one-site operator on the window of one site at the same position.

This identifies the periodic translates in CPSV16, Definition 4.8,
lines 831–847, for the physical-complement local term. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem placeAlong_ringWindow_twoSiteFirstOperator
    (hN : 2 ≤ N) (i : Fin N) (k : Matrix (Fin d) (Fin d) ℂ) :
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (twoSiteFirstOperator k) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow (by omega : 1 ≤ N) i)
        (oneSiteOperator k) := by
  ext σ τ
  rw [placeAlong_apply, placeAlong_apply]
  simp only [twoSiteFirstOperator, oneSiteOperator]
  let j : Fin N := MPSTensor.cyclicForwardSite i 1
  have hjOffset : (j.val + N - i.val) % N = 1 := by
    simpa only [j, MPSTensor.cyclicForwardSite] using
      MPSTensor.offset_mod_eq i.isLt (by omega : 1 < N)
  have hAgree :
      (∀ v, (∀ u, ringWindow (by omega : 1 ≤ N) i u ≠ v) → σ v = τ v) ↔
        (∀ v, (∀ u, ringWindow hN i u ≠ v) → σ v = τ v) ∧ τ j = σ j := by
    rw [MPSTensor.forall_ringWindow_ne_imp_iff, MPSTensor.forall_ringWindow_ne_imp_iff]
    constructor
    · intro h
      constructor
      · intro q hq
        exact h q (fun hq' ↦ hq (by omega))
      · exact h j (by omega)
    · rintro ⟨h, hj⟩ q hq
      by_cases hqTwo : (q.val + N - i.val) % N < 2
      · have hqOffset : (q.val + N - i.val) % N = 1 := by omega
        have hqj : q = j := by
          rw [MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i) hqOffset]
          exact Fin.ext (by simp only [j, MPSTensor.cyclicForwardSite])
        rw [hqj]
        exact hj
      · exact h q hqTwo
  rw [MPSTensor.ringWindow_zero, MPSTensor.ringWindow_zero, Matrix.one_apply]
  have h1 : (if σ (ringWindow hN i ⟨1, by omega⟩) = τ (ringWindow hN i ⟨1, by omega⟩)
      then (1 : ℂ) else 0) = if σ j = τ j then 1 else 0 := rfl
  rw [h1]
  by_cases hOne : ∀ v, (∀ u, ringWindow (by omega : 1 ≤ N) i u ≠ v) → σ v = τ v
  · obtain ⟨hTwo, hj⟩ := hAgree.mp hOne
    rw [ite_eq_left hTwo, ite_eq_left hOne, ite_eq_left hj.symm, mul_one]
  · by_cases hTwo : ∀ v, (∀ u, ringWindow hN i u ≠ v) → σ v = τ v
    · have hne : σ j ≠ τ j := by
        intro hj
        exact hOne (hAgree.mpr ⟨hTwo, hj.symm⟩)
      rw [ite_eq_left hTwo, ite_eq_right hOne, ite_eq_right hne, mul_zero]
    · rw [ite_eq_right hTwo, ite_eq_right hOne]

private def rectKroneckerMonoidHom :
    (Fin N → Matrix (Fin d) (Fin d) ℂ) →*
      ChainOperator d N where
  toFun := Matrix.piKronecker
  map_one' := Matrix.piKronecker_one
  map_mul' A B := (Matrix.piKronecker_mul A B).symm

/-- A one-site matrix placed at `i` is the tensor product of that matrix
at `i` and identities at every other site. -/
theorem rectKronecker_mulSingle
    (hN : 1 ≤ N) (i : Fin N) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.piKronecker (Pi.mulSingle i A) =
      placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (oneSiteOperator A) := by
  classical
  ext σ τ
  rw [placeAlong_apply]
  simp only [Matrix.piKronecker_apply, oneSiteOperator]
  rw [MPSTensor.ringWindow_zero]
  by_cases hAgree : ∀ v, (∀ u, ringWindow hN i u ≠ v) → σ v = τ v
  · rw [ite_eq_left hAgree]
    let S : Fin N → Matrix (Fin d) (Fin d) ℂ := Pi.mulSingle i A
    change (∏ n, S n (σ n) (τ n)) = A (σ i) (τ i)
    calc
      (∏ n, S n (σ n) (τ n)) = S i (σ i) (τ i) := by
        apply Finset.prod_eq_single i
        · intro q _ hqi
          rw [show S q = 1 by
            simp only [S, Pi.mulSingle_eq_of_ne hqi],
            Matrix.one_apply, ite_eq_left]
          rw [MPSTensor.forall_ringWindow_ne_imp_iff] at hAgree
          exact (hAgree q (fun hq ↦ hqi (by
            have hqOffset : (q.val + N - i.val) % N = 0 := by omega
            simpa [Nat.mod_eq_of_lt i.isLt] using
              MPSTensor.eq_cyclic_site_of_offset_eq
                (Fin.pos i) hqOffset))).symm
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = A (σ i) (τ i) := by
        rw [show S i = A by simp only [S, Pi.mulSingle_eq_same]]
  · rw [ite_eq_right hAgree]
    rw [MPSTensor.forall_ringWindow_ne_imp_iff] at hAgree
    push Not at hAgree
    obtain ⟨q, hqOutside, hq⟩ := hAgree
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    have hqi : q ≠ i := by
      intro hqi
      subst q
      simp at hqOutside
    rw [Pi.mulSingle_eq_of_ne hqi, Matrix.one_apply, ite_eq_right]
    exact fun h ↦ hq h.symm

/-- Placements of one-site operators on the ring commute at every pair of
positions.

This is the generic disjoint one-site commutation used to realize the local
two-site convention of CPSV16, Definition 4.8, lines 831–847. Its use in the
physical-complement construction is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem commute_placeAlong_ringWindow_oneSiteOperator
    (hN : 1 ≤ N) (A : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin N) :
    Commute
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (oneSiteOperator A))
      (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j) (oneSiteOperator A)) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · refine commute_placeAlong_of_disjoint _
      (disjoint_map_ringWindow_of_not_cyclicWindowsOverlap hN ?_) _ _
    intro hover
    rcases hover with ⟨q, hqi, hqj⟩
    rw [MPSTensor.mem_cyclicWindowSupport_iff hN] at hqi hqj
    have hqiOffset : (q.val + N - i.val) % N = 0 := by omega
    have hqjOffset : (q.val + N - j.val) % N = 0 := by omega
    have hqiEq : q = i := by
      simpa [Nat.mod_eq_of_lt i.isLt] using
        MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos i) hqiOffset
    have hqjEq : q = j := by
      simpa [Nat.mod_eq_of_lt j.isLt] using
        MPSTensor.eq_cyclic_site_of_offset_eq (Fin.pos j) hqjOffset
    exact hij (hqiEq.symm.trans hqjEq)

/-- The product of the one-site placements of a matrix is its tensor power in
configuration coordinates. -/
theorem noncommProd_placeAlong_ringWindow_oneSiteOperator
    (hN : 1 ≤ N) (A : Matrix (Fin d) (Fin d) ℂ) :
    (Finset.univ : Finset (Fin N)).noncommProd
      (fun i => placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (oneSiteOperator A))
      (by
        intro i _ j _ _
        exact commute_placeAlong_ringWindow_oneSiteOperator hN A i j) =
      Matrix.piKronecker (fun _ : Fin N => A) := by
  classical
  let x : Fin N → Matrix (Fin d) (Fin d) ℂ := fun _ => A
  let g : Fin N → (Fin N → Matrix (Fin d) (Fin d) ℂ) :=
    fun i => Pi.mulSingle i (x i)
  have hgcomm :
      ∀ i ∈ (Finset.univ : Finset (Fin N)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)), i ≠ j → Commute (g i) (g j) :=
    fun i _ j _ _ => Pi.mulSingle_apply_commute x i j
  calc
    _ = Finset.univ.noncommProd (fun i => Matrix.piKronecker (g i))
        (fun i hi j hj hij =>
          Commute.map (hgcomm i hi j hj hij) rectKroneckerMonoidHom) :=
      Finset.noncommProd_congr rfl
        (fun i _ => (rectKronecker_mulSingle hN i A).symm) _
    _ = Matrix.piKronecker x := by
      have hmap := Finset.map_noncommProd Finset.univ g hgcomm
        rectKroneckerMonoidHom
      calc
        _ = rectKroneckerMonoidHom
            (Finset.univ.noncommProd g hgcomm) := hmap.symm
        _ = rectKroneckerMonoidHom x := by
          congr 1
          exact Finset.noncommProd_mulSingle x
        _ = Matrix.piKronecker x := rfl
    _ = Matrix.piKronecker (fun _ : Fin N => A) := rfl

/-- The exponential of a sum of identical one-site energies is their
sitewise tensor power. -/
theorem exp_sum_placeAlong_ringWindow_oneSiteOperator
    (hN : 1 ≤ N) (A : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp
        (∑ i : Fin N,
          placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (oneSiteOperator A)) =
      (Matrix.piKronecker fun _ : Fin N ↦ (NormedSpace.exp A)) := by
  let f : Fin N → ChainOperator d N := fun i ↦
    placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i) (oneSiteOperator A)
  have hpair :
      ((Finset.univ : Finset (Fin N)) : Set (Fin N)).Pairwise
        (fun i j ↦ Commute (f i) (f j)) := by
    intro i _ j _ _
    exact commute_placeAlong_ringWindow_oneSiteOperator hN A i j
  change NormedSpace.exp (∑ i ∈ Finset.univ, f i) = _
  rw [Matrix.exp_sum_of_commute Finset.univ f hpair]
  calc
    _ = Finset.univ.noncommProd
        (fun i ↦ placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i)
          (oneSiteOperator (NormedSpace.exp A)))
        (fun i _ j _ _ ↦
          commute_placeAlong_ringWindow_oneSiteOperator hN (NormedSpace.exp A) i j) :=
      Finset.noncommProd_congr rfl (fun i _ ↦ by
        rw [← placeAlong_exp, exp_oneSiteOperator]) _
    _ = (Matrix.piKronecker fun _ : Fin N ↦ (NormedSpace.exp A)) :=
      noncommProd_placeAlong_ringWindow_oneSiteOperator hN _

end MPOTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Normed
import TNLean.MPS.MPDO.TopologicalGibbsHamiltonian

/-!
# Generic physical Gibbs embedding

This file develops generic one-site and first-site two-site operators, their
periodic embeddings, and the exponential of a sum of commuting one-site
energies.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 999--1016
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

variable {d N : ℕ}

/-- A one-site matrix in the configuration indexing used by
`embedLocalOperator`.

This wrapper will carry the physical one-site energy in the complement
construction for CPSV16, Definition 4.8, lines 831–847. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
def oneSiteOperator (k : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ :=
  fun x y ↦ k (x ⟨0, by omega⟩) (y ⟨0, by omega⟩)

private def finOneArrowEquiv (d : ℕ) : (Fin 1 → Fin d) ≃ Fin d where
  toFun x := x ⟨0, by omega⟩
  invFun a := fun _ ↦ a
  left_inv x := by
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

private theorem oneSiteOperator_eq_reindexAlgEquiv_symm
    (A : Matrix (Fin d) (Fin d) ℂ) :
    oneSiteOperator A =
      (Matrix.reindexAlgEquiv ℂ ℂ (finOneArrowEquiv d)).symm A := by
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
    (Matrix.reindexAlgEquiv ℂ ℂ (finOneArrowEquiv d)).symm
    (LinearMap.continuous_of_finiteDimensional
      (Matrix.reindexAlgEquiv ℂ ℂ
        (finOneArrowEquiv d)).symm.toLinearMap) A

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

/-- Embedding a two-site operator which acts only on its first site is the
one-site embedding at the same periodic position.

This identifies the periodic translates in CPSV16, Definition 4.8,
lines 831–847, for the physical-complement local term. See
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem embedLocalOperator_twoSite_first
    (hN : 2 ≤ N) (i : Fin N) (k : Matrix (Fin d) (Fin d) ℂ) :
    embedLocalOperator 2 N hN i (twoSiteFirstOperator k) =
      embedLocalOperator 1 N (by omega) i (oneSiteOperator k) := by
  ext σ τ
  simp only [embedLocalOperator_apply, twoSiteFirstOperator, oneSiteOperator]
  let j : Fin N := MPSTensor.cyclicForwardSite i 1
  have hjOffset : (j.val + N - i.val) % N = 1 := by
    simpa only [j, MPSTensor.cyclicForwardSite] using
      MPSTensor.offset_mod_eq i.isLt (by omega : 1 < N)
  have hAgree :
      AgreesOutsideWindow (d := d) 1 (by omega) i σ τ ↔
        AgreesOutsideWindow (d := d) 2 hN i σ τ ∧ τ j = σ j := by
    rw [agreesOutsideWindow_iff, agreesOutsideWindow_iff]
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
        simpa only [hqj] using hj
      · exact h q hqTwo
  have hσZeroTwo :
      MPSTensor.extractWindow 2 i σ ⟨0, by omega⟩ = σ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  have hτZeroTwo :
      MPSTensor.extractWindow 2 i τ ⟨0, by omega⟩ = τ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  have hσZeroOne :
      MPSTensor.extractWindow 1 i σ ⟨0, by omega⟩ = σ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  have hτZeroOne :
      MPSTensor.extractWindow 1 i τ ⟨0, by omega⟩ = τ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  have hσOneTwo :
      MPSTensor.extractWindow 2 i σ ⟨1, by omega⟩ = σ j := by
    rfl
  have hτOneTwo :
      MPSTensor.extractWindow 2 i τ ⟨1, by omega⟩ = τ j := by
    rfl
  rw [hσZeroTwo, hτZeroTwo, hσZeroOne, hτZeroOne, hσOneTwo, hτOneTwo,
    Matrix.one_apply]
  by_cases hOne : AgreesOutsideWindow (d := d) 1 (by omega) i σ τ
  · obtain ⟨hTwo, hj⟩ := hAgree.mp hOne
    rw [if_pos hTwo, if_pos hOne, if_pos hj.symm, mul_one]
  · by_cases hTwo : AgreesOutsideWindow (d := d) 2 hN i σ τ
    · have hne : σ j ≠ τ j := by
        intro hj
        exact hOne (hAgree.mpr ⟨hTwo, hj.symm⟩)
      rw [if_pos hTwo, if_neg hOne, if_neg hne, mul_zero]
    · rw [if_neg hTwo, if_neg hOne]

/-- Embedding a local zero operator gives the zero chain operator. -/
@[simp]
private theorem embedLocalOperator_zero
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
  embedLocalOperator (d := d) L N hLN i 0 = 0 := by
  ext σ τ
  simp [embedLocalOperator_apply]

/-- Embedding preserves addition of local operators. -/
private theorem embedLocalOperator_add
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (A B : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    embedLocalOperator (d := d) L N hLN i (A + B) =
      embedLocalOperator L N hLN i A + embedLocalOperator L N hLN i B := by
  ext σ τ
  simp only [embedLocalOperator_apply, Matrix.add_apply]
  by_cases h : AgreesOutsideWindow (d := d) L hLN i σ τ <;> simp [h]

/-- Embedding preserves complex scalar multiplication. -/
private theorem embedLocalOperator_smul
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (c : ℂ)
    (A : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    embedLocalOperator (d := d) L N hLN i (c • A) =
      c • embedLocalOperator L N hLN i A := by
  ext σ τ
  simp [embedLocalOperator_apply]

/-- Embedding the local identity gives the chain identity. -/
@[simp]
private theorem embedLocalOperator_one
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    embedLocalOperator (d := d) L N hLN i 1 = 1 := by
  let e := windowComplementEquiv (d := d) L N hLN i
  apply (Matrix.reindex e e).injective
  rw [reindex_embedLocalOperator_windowComplement]
  ext x y
  simp only [Matrix.reindex_apply, Matrix.one_apply, Matrix.kroneckerMap_apply,
    mul_ite, mul_one, mul_zero]
  change (if x.2 = y.2 then if x.1 = y.1 then 1 else 0 else 0) =
    if e.symm x = e.symm y then 1 else 0
  simp only [e.symm.injective.eq_iff]
  by_cases hfst : x.1 = y.1 <;> by_cases hsnd : x.2 = y.2 <;>
    simp_all [Prod.ext_iff]

/-- Embedding into a fixed cyclic window is a complex algebra homomorphism. -/
def embedLocalOperatorAlgHom
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ →ₐ[ℂ]
      ChainOperator d N where
  toFun := embedLocalOperator L N hLN i
  map_one' := embedLocalOperator_one L N hLN i
  map_mul' A B := embedLocalOperator_mul L N hLN i A B
  map_zero' := embedLocalOperator_zero L N hLN i
  map_add' A B := embedLocalOperator_add L N hLN i A B
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      embedLocalOperator_smul, embedLocalOperator_one]

open scoped Matrix.Norms.Operator in
/-- Matrix exponential commutes with embedding into a cyclic window. -/
theorem exp_embedLocalOperator
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (A : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    NormedSpace.exp (embedLocalOperator L N hLN i A) =
      embedLocalOperator L N hLN i (NormedSpace.exp A) := by
  symm
  exact NormedSpace.map_exp
    (embedLocalOperatorAlgHom (d := d) L N hLN i)
    (LinearMap.continuous_of_finiteDimensional
      (embedLocalOperatorAlgHom (d := d) L N hLN i).toLinearMap) A

/-- A heterogeneous tensor product of one matrix at each site. -/
private noncomputable def sitewiseMatrixFamily
    (A : Fin N → Matrix (Fin d) (Fin d) ℂ) : ChainOperator d N :=
  fun σ τ ↦ ∏ n, A n (σ n) (τ n)

private theorem sitewiseMatrixFamily_mul
    (A B : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    sitewiseMatrixFamily A * sitewiseMatrixFamily B =
      sitewiseMatrixFamily fun n ↦ A n * B n := by
  classical
  ext σ τ
  simp only [Matrix.mul_apply, sitewiseMatrixFamily]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.piFinset_univ]
  rw [← Finset.prod_univ_sum
    (fun _ : Fin N ↦ (Finset.univ : Finset (Fin d)))
    (fun n a ↦ A n (σ n) a * B n a (τ n))]

private theorem sitewiseMatrixFamily_one :
    sitewiseMatrixFamily (fun _ : Fin N ↦
      (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  classical
  ext σ τ
  simp only [sitewiseMatrixFamily, Matrix.one_apply]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

private def sitewiseMatrixFamilyMonoidHom :
    (Fin N → Matrix (Fin d) (Fin d) ℂ) →*
      ChainOperator d N where
  toFun := sitewiseMatrixFamily
  map_one' := sitewiseMatrixFamily_one
  map_mul' A B := (sitewiseMatrixFamily_mul A B).symm

private theorem sitewiseMatrixFamily_mulSingle
    (hN : 1 ≤ N) (i : Fin N) (A : Matrix (Fin d) (Fin d) ℂ) :
    sitewiseMatrixFamily (Pi.mulSingle i A) =
      embedLocalOperator 1 N hN i (oneSiteOperator A) := by
  classical
  ext σ τ
  simp only [sitewiseMatrixFamily, embedLocalOperator_apply, oneSiteOperator]
  have hσ :
      MPSTensor.extractWindow 1 i σ ⟨0, by omega⟩ = σ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  have hτ :
      MPSTensor.extractWindow 1 i τ ⟨0, by omega⟩ = τ i := by
    simp [MPSTensor.extractWindow, Nat.mod_eq_of_lt i.isLt]
  rw [hσ, hτ]
  by_cases hAgree : AgreesOutsideWindow (d := d) 1 hN i σ τ
  · rw [if_pos hAgree]
    let S : Fin N → Matrix (Fin d) (Fin d) ℂ := Pi.mulSingle i A
    change (∏ n, S n (σ n) (τ n)) = A (σ i) (τ i)
    calc
      (∏ n, S n (σ n) (τ n)) = S i (σ i) (τ i) := by
        apply Finset.prod_eq_single i
        · intro q _ hqi
          rw [show S q = 1 by
            simp only [S, Pi.mulSingle_eq_of_ne hqi],
            Matrix.one_apply, if_pos]
          rw [agreesOutsideWindow_iff] at hAgree
          exact (hAgree q (fun hq ↦ hqi (by
            have hqOffset : (q.val + N - i.val) % N = 0 := by omega
            simpa [Nat.mod_eq_of_lt i.isLt] using
              MPSTensor.eq_cyclic_site_of_offset_eq
                (Fin.pos i) hqOffset))).symm
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = A (σ i) (τ i) := by
        rw [show S i = A by simp only [S, Pi.mulSingle_eq_same]]
  · rw [if_neg hAgree]
    rw [agreesOutsideWindow_iff] at hAgree
    push Not at hAgree
    obtain ⟨q, hqOutside, hq⟩ := hAgree
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    have hqi : q ≠ i := by
      intro hqi
      subst q
      simp at hqOutside
    rw [Pi.mulSingle_eq_of_ne hqi, Matrix.one_apply, if_neg]
    exact fun h ↦ hq h.symm

/-- Periodic embeddings of one-site operators commute at every pair of
positions.

This is the generic disjoint one-site commutation used to realize the local
two-site convention of CPSV16, Definition 4.8, lines 831–847. Its use in the
physical-complement construction is documented in
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. -/
theorem embedLocalOperator_one_commute
    (hN : 1 ≤ N) (A : Matrix (Fin d) (Fin d) ℂ)
    (i j : Fin N) :
    Commute
      (embedLocalOperator 1 N hN i (oneSiteOperator A))
      (embedLocalOperator 1 N hN j (oneSiteOperator A)) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply embedLocalOperator_commute_of_not_cyclicWindowsOverlap
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

/-- The exponential of a sum of identical one-site energies is their
sitewise tensor power. -/
theorem exp_sum_embedLocalOperator_one
    (hN : 1 ≤ N) (A : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp
        (∑ i : Fin N,
          embedLocalOperator 1 N hN i (oneSiteOperator A)) =
      sitewisePhysicalMatrix (NormedSpace.exp A) N := by
  let f : Fin N → ChainOperator d N := fun i ↦
    embedLocalOperator 1 N hN i (oneSiteOperator A)
  have hpair :
      ((Finset.univ : Finset (Fin N)) : Set (Fin N)).Pairwise
        (fun i j ↦ Commute (f i) (f j)) := by
    intro i _ j _ _
    exact embedLocalOperator_one_commute hN A i j
  let x : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun _ ↦ NormedSpace.exp A
  let g : Fin N → (Fin N → Matrix (Fin d) (Fin d) ℂ) :=
    fun i ↦ Pi.mulSingle i (x i)
  have hgpair :
      ((Finset.univ : Finset (Fin N)) : Set (Fin N)).Pairwise
        (fun i j ↦ Commute (g i) (g j)) := by
    intro i _ j _ _
    exact Pi.mulSingle_apply_commute x i j
  have hgcomm :
      ∀ i ∈ (Finset.univ : Finset (Fin N)),
        ∀ j ∈ (Finset.univ : Finset (Fin N)), i ≠ j →
          Commute (g i) (g j) :=
    fun i hi j hj hij ↦ hgpair hi hj hij
  have hterm (i : Fin N) :
      NormedSpace.exp (f i) = sitewiseMatrixFamily (g i) := by
    calc
      NormedSpace.exp (f i) =
          embedLocalOperator 1 N hN i
            (NormedSpace.exp (oneSiteOperator A)) :=
        exp_embedLocalOperator 1 N hN i (oneSiteOperator A)
      _ = embedLocalOperator 1 N hN i
          (oneSiteOperator (NormedSpace.exp A)) := by
        rw [exp_oneSiteOperator]
      _ = sitewiseMatrixFamily (g i) := by
        exact (sitewiseMatrixFamily_mulSingle hN i (NormedSpace.exp A)).symm
  change NormedSpace.exp (∑ i ∈ Finset.univ, f i) = _
  rw [Matrix.exp_sum_of_commute Finset.univ f hpair]
  calc
    _ = Finset.univ.noncommProd
        (fun i ↦ sitewiseMatrixFamily (g i))
        (fun i hi j hj hij ↦
          Commute.map (hgcomm i hi j hj hij) sitewiseMatrixFamilyMonoidHom) :=
      Finset.noncommProd_congr rfl (fun i _ ↦ hterm i) _
    _ = sitewiseMatrixFamily x := by
      have hmap := Finset.map_noncommProd Finset.univ g hgcomm
        sitewiseMatrixFamilyMonoidHom
      calc
        _ = sitewiseMatrixFamilyMonoidHom
            (Finset.univ.noncommProd g hgcomm) := hmap.symm
        _ = sitewiseMatrixFamilyMonoidHom x := by
          congr 1
          exact Finset.noncommProd_mulSingle x
        _ = sitewiseMatrixFamily x := rfl
    _ = sitewisePhysicalMatrix (NormedSpace.exp A) N := rfl

end MPOTensor

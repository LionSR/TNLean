/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableState
import TNLean.QCA.LocalAlgebra.IntervalCoordinates
import TNLean.MPS.ParentHamiltonian.LocalExpectation.LocalObservableInsertion

/-!
# Local MPS expectations on arbitrary finite integer regions

A finite-region observable can be included in any containing consecutive
interval and evaluated by the local MPS expectation in interval coordinates.
Trace preservation and transfer invariance make this value independent of
the chosen interval and compatible with enlargement of the finite region.
The resulting complex-linear functionals use the existing insertion expectation.

This is the finite-region interpretation of the GVBS expectations in
Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b).
No extension to the completed quasi-local algebra is asserted here.

It also contains the following results.

* `SpinChain.intervalCoordinates_localInclusion_eq_bulkObservable`: interval inclusions as interior
  observable placements.
-/

open scoped Matrix BigOperators

section IntervalObservableCoordinates

/-!
## Interval inclusions as interior observable placements

In consecutive coordinates, the local-algebra inclusion obtained by adjoining
\(b\) sites on the left and \(c\) sites on the right is
\(X\mapsto I_b\otimes X\otimes I_c\). Thus the finite integer-interval
convention agrees with the existing interior observable used in transfer
insertions. Empty intervals and empty added intervals are included.

This is the finite-coordinate identification underlying the local expectations
in Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b).
No completed algebra or infinite-volume state is constructed here.
-/

namespace SpinChain

private theorem interval_complement_eq_iff {d N b c : ℕ}
    (σ τ : Fin ((b + N) + c) → Fin d) :
    (∀ i : Fin ((b + N) + c), ¬ (b ≤ i.val ∧ i.val < b + N) → σ i = τ i) ↔
      (fun i : Fin b => σ (Fin.castAdd c (Fin.castAdd N i))) =
        (fun i : Fin b => τ (Fin.castAdd c (Fin.castAdd N i))) ∧
      (fun i : Fin c => σ (Fin.natAdd (b + N) i)) =
        (fun i : Fin c => τ (Fin.natAdd (b + N) i)) := by
  constructor
  · intro h
    constructor
    · funext i
      exact h _ (by simp only [Fin.val_castAdd]; omega)
    · funext i
      exact h _ (by simp only [Fin.val_natAdd]; omega)
  · rintro ⟨hleft, hright⟩ i hi
    by_cases hb : i.val < b
    · exact congrFun hleft ⟨i.val, hb⟩
    · let j : Fin c := ⟨i.val - (b + N), by omega⟩
      have heq : Fin.natAdd (b + N) j = i := by
        apply Fin.ext
        dsimp [j]
        omega
      simpa only [heq] using congrFun hright j

private theorem bulkObservable_apply {d N b c : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (σ τ : Fin ((b + N) + c) → Fin d) :
    MPSTensor.bulkObservable X b c σ τ =
      X (fun i => σ ⟨b + i.val, by omega⟩) (fun i => τ ⟨b + i.val, by omega⟩) *
        if ∀ i : Fin ((b + N) + c), ¬ (b ≤ i.val ∧ i.val < b + N) → σ i = τ i
        then 1 else 0 := by
  classical
  simp only [MPSTensor.bulkObservable, MPSTensor.appendObservable_apply,
    Matrix.one_apply, interval_complement_eq_iff]
  split_ifs <;> simp_all [Fin.castAdd, Fin.natAdd, Nat.add_comm]

/-- The local-algebra inclusion between consecutive intervals is the interior
observable placement in consecutive coordinates. Source: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.1)--(3.2b), and arXiv:1703.09188,
Appendix, lines 2292--2295. -/
theorem intervalCoordinates_localInclusion_eq_bulkObservable
    (d : ℕ) (a : ℤ) (N b c : ℕ) (X : LocalAlgebra d (finiteChainRegion a N)) :
    intervalCoordinates d (a - b) ((b + N) + c)
      (localInclusion (finiteChainRegion_subset_expanded a N b c) X) =
        MPSTensor.bulkObservable (intervalCoordinates d a N X) b c := by
  ext σ τ
  rw [intervalCoordinates_localInclusion_apply, bulkObservable_apply]

end SpinChain

end IntervalObservableCoordinates

section LocalObservableRegionExpectation

open SpinChain

namespace MPSTensor

variable {d D : ℕ}

private theorem intervalExpectation_expanded (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) (a : ℤ) (N b c : ℕ)
    (X : LocalAlgebra d (finiteChainRegion a N)) :
    observableInsertionExpectation A ρ
      (intervalCoordinates d (a - b) ((b + N) + c)
        (localInclusion (finiteChainRegion_subset_expanded a N b c) X)) =
      observableInsertionExpectation A ρ (intervalCoordinates d a N X) := by
  rw [intervalCoordinates_localInclusion_eq_bulkObservable, bulkObservable,
    observableInsertionExpectation_appendObservable_one A ρ hfix,
    observableInsertionExpectation_one_appendObservable A hTP]

private theorem finiteChainRegion_subset_of_bounds {a a' : ℤ} {N M : ℕ}
    (hleft : a' ≤ a) (hright : a + N ≤ a' + M) :
    finiteChainRegion a N ⊆ finiteChainRegion a' M := by
  intro x hx
  simp only [finiteChainRegion, Finset.mem_Ico] at *
  omega

private theorem intervalExpectation_of_bounds (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) {a a' : ℤ} {N M : ℕ}
    (hleft : a' ≤ a) (hright : a + N ≤ a' + M)
    (X : LocalAlgebra d (finiteChainRegion a N)) :
    observableInsertionExpectation A ρ
      (intervalCoordinates d a' M
        (localInclusion (finiteChainRegion_subset_of_bounds hleft hright) X)) =
      observableInsertionExpectation A ρ (intervalCoordinates d a N X) := by
  obtain ⟨b, ha⟩ : ∃ b : ℕ, a - b = a' := ⟨(a - a').toNat, by omega⟩
  obtain ⟨c, hM⟩ : ∃ c : ℕ, (b + N) + c = M := ⟨M - (b + N), by omega⟩
  subst a'
  subst M
  exact intervalExpectation_expanded A ρ hTP hfix a N b c X

private theorem intervalExpectation_region_independent (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) {Λ : Finset ℤ}
    (a : ℤ) (N : ℕ) (hΛ : Λ ⊆ finiteChainRegion a N)
    (a' : ℤ) (M : ℕ) (hΛ' : Λ ⊆ finiteChainRegion a' M) (X : LocalAlgebra d Λ) :
    observableInsertionExpectation A ρ
      (intervalCoordinates d a N (localInclusion hΛ X)) =
      observableInsertionExpectation A ρ
        (intervalCoordinates d a' M (localInclusion hΛ' X)) := by
  let p := min a a'
  let q := max (a + N) (a' + M)
  let L := (q - p).toNat
  have hLp : p + L = q := by dsimp [p, q, L]; omega
  have hleft : p ≤ a := min_le_left _ _
  have hleft' : p ≤ a' := min_le_right _ _
  have hright : a + N ≤ p + L := by rw [hLp]; exact le_max_left _ _
  have hright' : a' + M ≤ p + L := by rw [hLp]; exact le_max_right _ _
  have h := intervalExpectation_of_bounds A ρ hTP hfix hleft hright (localInclusion hΛ X)
  have h' := intervalExpectation_of_bounds A ρ hTP hfix hleft' hright' (localInclusion hΛ' X)
  simp only [← StarAlgHom.comp_apply, localInclusion_trans] at h h'
  exact h.symm.trans h'

private theorem region_subset_centered_interval (Λ : Finset ℤ) :
    Λ ⊆ finiteChainRegion (-((Λ.sup Int.natAbs : ℕ) : ℤ)) (2 * Λ.sup Int.natAbs + 1) := by
  intro x hx
  have hr := Finset.le_sup (f := Int.natAbs) hx
  have hxpos := Int.le_natAbs (a := x)
  have hxneg := Int.le_natAbs (a := -x)
  simp only [Int.natAbs_neg] at hxneg
  simp only [finiteChainRegion, Finset.mem_Ico]
  omega

/-- The complex-linear local MPS functional on an arbitrary finite region,
obtained by including the observable into a containing consecutive interval.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b). -/
noncomputable def localObservableExpectation (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (Λ : Finset ℤ) : LocalAlgebra d Λ →ₗ[ℂ] ℂ :=
  (observableInsertionExpectationₗ A ρ (2 * Λ.sup Int.natAbs + 1)).comp
    (((intervalCoordinates d (-((Λ.sup Int.natAbs : ℕ) : ℤ))
      (2 * Λ.sup Int.natAbs + 1)).toAlgEquiv.toLinearEquiv.toLinearMap).comp
        (localInclusion (region_subset_centered_interval Λ)).toAlgHom.toLinearMap)

/-- Evaluating a finite-region observable in any containing interval gives the
same local expectation. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), compatibility of local GVBS expectations. -/
theorem localObservableExpectation_eq_of_subset_interval (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) {Λ : Finset ℤ}
    (a : ℤ) (N : ℕ) (hΛ : Λ ⊆ finiteChainRegion a N) (X : LocalAlgebra d Λ) :
    localObservableExpectation A ρ Λ X = observableInsertionExpectation A ρ
      (intervalCoordinates d a N (localInclusion hΛ X)) := by
  exact intervalExpectation_region_independent A ρ hTP hfix
    (-((Λ.sup Int.natAbs : ℕ) : ℤ)) (2 * Λ.sup Int.natAbs + 1)
      (region_subset_centered_interval Λ) a N hΛ X

/-- Local MPS expectations agree after including an observable into a larger
finite region. Source: Nachtergaele, arXiv:cond-mat/9410110,
equations (3.1)--(3.2b), compatibility of local GVBS expectations. -/
theorem localObservableExpectation_localInclusion (A : MPSTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hfix : Kraus.transferMap A ρ = ρ) {Λ Γ : Finset ℤ} (hΛΓ : Λ ⊆ Γ)
    (X : LocalAlgebra d Λ) :
    localObservableExpectation A ρ Γ (localInclusion hΛΓ X) =
      localObservableExpectation A ρ Λ X := by
  rw [localObservableExpectation_eq_of_subset_interval A ρ hTP hfix
    (-((Γ.sup Int.natAbs : ℕ) : ℤ)) (2 * Γ.sup Int.natAbs + 1)
      (hΛΓ.trans (region_subset_centered_interval Γ)) X]
  change observableInsertionExpectation A ρ
    (intervalCoordinates d (-((Γ.sup Int.natAbs : ℕ) : ℤ))
      (2 * Γ.sup Int.natAbs + 1)
        (localInclusion (region_subset_centered_interval Γ) (localInclusion hΛΓ X))) = _
  simp only [← StarAlgHom.comp_apply, localInclusion_trans]

end MPSTensor

end LocalObservableRegionExpectation

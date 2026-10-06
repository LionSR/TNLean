/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.IntervalCoordinates
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion

/-!
# Interval inclusions as interior observable placements

In consecutive coordinates, the local-algebra inclusion obtained by adjoining
\(b\) sites on the left and \(c\) sites on the right is
\(X\mapsto I_b\otimes X\otimes I_c\). Thus the finite integer-interval
convention agrees with the existing interior observable used in transfer
insertions. Empty intervals and empty added intervals are included.

This is the finite-coordinate identification underlying the local expectations
in Nachtergaele, arXiv:cond-mat/9410110, Section 3, equations (3.1)--(3.2b).
No completed algebra or infinite-volume state is constructed here.
-/

open scoped Matrix BigOperators

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
    (d : ℕ) (a : ℤ) (N b c : ℕ) (X : LocalAlgebra d (intervalRegion a N)) :
    intervalCoordinates d (a - b) ((b + N) + c)
      (localInclusion (intervalRegion_subset_expanded a N b c) X) =
        MPSTensor.bulkObservable (intervalCoordinates d a N X) b c := by
  ext σ τ
  rw [intervalCoordinates_localInclusion_apply, bulkObservable_apply]

end SpinChain

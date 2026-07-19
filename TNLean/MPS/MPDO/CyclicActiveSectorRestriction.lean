/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorChainDecomposition

/-!
# Cyclic-active physical sectors

For a physical-sector factorization, a sector is cyclic-active when it lies
on a nonempty closed directed walk of nonzero neighboring operators.  This is
stronger than reflexive reachability: the sector must have an outgoing
nonzero edge followed by a return path.

Every nonzero finite cyclic neighboring product is supported entirely on
cyclic-active sectors.  Consequently, deleting all other sector blocks leaves
the finite cyclic bond products unchanged: every deleted block was already
zero.  This conclusion is purely combinatorial and uses neither saturation of
the area law, zero correlation length, nor injectivity.

## References

* Beigi, arXiv:1105.1019v2, Lemma 2.1 and lines 449--514.
* arXiv:1606.00608, Appendix C.2, equations `formK` and `etarl`, lines
  1434--1450.
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D N : ℕ} {K : MPOTensor d D}

/-- A sector lies on a positive-length closed walk in the directed support of
the neighboring operators.

Equivalently, it has an outgoing nonzero neighboring operator whose target
can return through a possibly empty directed path.  The explicit outgoing
edge excludes the empty reflexive walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514; arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
def IsCyclicActiveSector (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) : Prop :=
  ∃ h : Fin F.sectorCount,
    F.neighboringOperator k h ≠ 0 ∧
      Relation.ReflTransGen
        (fun a b ↦ F.neighboringOperator a b ≠ 0) h k

/-- The subtype of sectors lying on a positive-length closed directed walk.

Source: Beigi, arXiv:1105.1019v2, directed-cycle discussion at lines
449--514. -/
abbrev CyclicActiveSector (F : PhysicalSectorFactorization K) :=
  {k : Fin F.sectorCount // F.IsCyclicActiveSector k}

private theorem reflTransGen_iterate_map
    {V W : Type*} (r : W → W → Prop) (step : V → V) (f : V → W)
    (hstep : ∀ x, r (f x) (f (step x))) (m : ℕ) (x : V) :
    Relation.ReflTransGen r (f x) (f ((step^[m]) x)) := by
  induction m with
  | zero => exact .refl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.tail (hstep _)

private theorem finRotate_pow_card [NeZero N] (n : Fin N) :
    ((finRotate N : Fin N → Fin N)^[N]) n = n := by
  apply Fin.ext
  rw [coe_finRotate_pow]
  simp [Nat.mod_eq_of_lt n.isLt]

/-- If every consecutive edge of a finite cyclic sector word is nonzero,
then every sector in that word is cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, equation following `etarl`, lines
1446--1450. -/
theorem isCyclicActiveSector_of_cyclic_edges
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hedge : ∀ n, F.neighboringOperator (k n) (k (n + 1)) ≠ 0)
    (n : Fin N) :
    F.IsCyclicActiveSector (k n) := by
  refine ⟨k (n + 1), hedge n, ?_⟩
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hreturn :
      ((finRotate N : Fin N → Fin N)^[N - 1]) (finRotate N n) = n := by
    rw [← Function.iterate_succ_apply]
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hNpos] using finRotate_pow_card n
  have hwalk := reflTransGen_iterate_map
    (fun a b ↦ F.neighboringOperator a b ≠ 0) (finRotate N) k
    (fun i ↦ by
      rw [finRotate_apply]
      exact hedge i) (N - 1) (finRotate N n)
  rw [hreturn] at hwalk
  simpa only [finRotate_apply] using hwalk

/-- A nonzero cyclic neighboring product has a nonzero neighboring operator
at every edge of its sector word.

Source: arXiv:1606.00608, Appendix C.2, equation following `etarl`, lines
1446--1450. -/
theorem neighboringOperator_ne_zero_of_cyclicNeighboringProduct_ne_zero
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hprod : F.cyclicNeighboringProduct k ≠ 0) (n : Fin N) :
    F.neighboringOperator (k n) (k (n + 1)) ≠ 0 := by
  intro hn
  apply hprod
  ext x y
  rw [cyclicNeighboringProduct]
  apply Finset.prod_eq_zero (Finset.mem_univ n)
  rw [hn]
  rfl

/-- Every sector occurring in a nonzero cyclic neighboring product is
cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem isCyclicActiveSector_of_cyclicNeighboringProduct_ne_zero
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hprod : F.cyclicNeighboringProduct k ≠ 0) (n : Fin N) :
    F.IsCyclicActiveSector (k n) := by
  apply F.isCyclicActiveSector_of_cyclic_edges k
  exact F.neighboringOperator_ne_zero_of_cyclicNeighboringProduct_ne_zero k hprod

/-- If a finite cyclic sector word contains a sector outside the
cyclic-active support, then its neighboring product is zero.

Thus deleting all non-cyclic-active sector blocks leaves every finite cyclic
bond product unchanged: precisely the deleted blocks vanish.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450; Beigi,
arXiv:1105.1019v2, directed-cycle discussion at lines 449--514. -/
theorem cyclicNeighboringProduct_eq_zero_of_not_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount) (n : Fin N)
    (hn : ¬ F.IsCyclicActiveSector (k n)) :
    F.cyclicNeighboringProduct k = 0 := by
  by_contra hprod
  exact hn (F.isCyclicActiveSector_of_cyclicNeighboringProduct_ne_zero k hprod n)

/-- The finite cyclic neighboring-product family is supported on sector words
whose every value is cyclic-active.

Source: arXiv:1606.00608, Appendix C.2, lines 1441--1450. -/
theorem cyclicNeighboringProduct_eq_zero_of_not_forall_isCyclicActiveSector
    (F : PhysicalSectorFactorization K) [NeZero N]
    (k : Fin N → Fin F.sectorCount)
    (hk : ¬ ∀ n, F.IsCyclicActiveSector (k n)) :
    F.cyclicNeighboringProduct k = 0 := by
  classical
  push Not at hk
  obtain ⟨n, hn⟩ := hk
  exact F.cyclicNeighboringProduct_eq_zero_of_not_isCyclicActiveSector k n hn

end MPOTensor.PhysicalSectorFactorization

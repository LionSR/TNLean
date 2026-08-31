/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.DifferenceProjections

/-!
# Outside-window cancellation for martingale differences

This file formalizes the commutation reduction between equations \(Enpsi\) and
\(Enpsi2\) in the proof of Nachtergaele's Theorem 2.1(i),
arXiv:cond-mat/9410110, lines 1206--1220. For the local ground projection
\(Q_n=G_{n,l}\), the source assumes that \(E_m\) commutes with \(Q_n\) when
\(m<n-l\) or \(n<m\). Mutual orthogonality of the martingale differences then
gives
\[
  E_mQ_nE_n=Q_nE_mE_n=0.
\]
Consequently, the complete resolution sum over \(0\leq m<N\) reduces to the
active interval \(n-l\leq m\leq n\).
-/

open scoped BigOperators InnerProductSpace

namespace FrustrationFree.NestedGroundProjections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Outside the interval \([n-l,n]\), source commutation with the local ground
projection \(Q_n\) and martingale-difference orthogonality imply
\(E_mQ_nE_n=0\).

This is the cancellation in Nachtergaele, arXiv:cond-mat/9410110, lines
1210--1215. -/
theorem martingaleDifference_comp_localProjection_comp_eq_zero
    (G : NestedGroundProjections (E := E)) (Q : E →ₗ[ℂ] E) {m n l : ℕ}
    (hout : m < n - l ∨ n < m)
    (hcomm : (G.martingaleDifference m).comp Q =
      Q.comp (G.martingaleDifference m)) :
    (G.martingaleDifference m).comp
      (Q.comp (G.martingaleDifference n)) = 0 := by
  have hmn : m ≠ n := by omega
  calc
    (G.martingaleDifference m).comp
        (Q.comp (G.martingaleDifference n)) =
      ((G.martingaleDifference m).comp Q).comp
        (G.martingaleDifference n) := by
          rw [LinearMap.comp_assoc]
    _ = (Q.comp (G.martingaleDifference m)).comp
        (G.martingaleDifference n) := by rw [hcomm]
    _ = Q.comp ((G.martingaleDifference m).comp
        (G.martingaleDifference n)) := by rw [LinearMap.comp_assoc]
    _ = 0 := by
      rw [G.martingaleDifference_comp_eq_zero hmn, LinearMap.comp_zero]

/-- The full martingale-resolution sum in \(Enpsi\) reduces to the active
indices \(m\in[n-l,n]\).

The hypothesis is exactly the source commutation condition outside that
interval. The bound \(n<N\) ensures that every active index occurs in the
original sum \(0\leq m<N\). This is the finite-sum reduction used in
Nachtergaele's equation \(Enpsi2\), arXiv:cond-mat/9410110, lines 1206--1220. -/
theorem sum_martingaleDifference_localProjection_eq_sum_Icc
    (G : NestedGroundProjections (E := E)) (Q : E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp Q =
        Q.comp (G.martingaleDifference m)) (v : E) :
    ∑ m ∈ Finset.range N,
        G.martingaleDifference m (Q (G.martingaleDifference n v)) =
      ∑ m ∈ Finset.Icc (n - l) n,
        G.martingaleDifference m (Q (G.martingaleDifference n v)) := by
  symm
  apply Finset.sum_subset
  · intro m hm
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hm).2 hn)
  · intro m _ hm
    have hout : m < n - l ∨ n < m := by
      rw [Finset.mem_Icc] at hm
      omega
    change ((G.martingaleDifference m).comp
      (Q.comp (G.martingaleDifference n))) v = 0
    rw [martingaleDifference_comp_localProjection_comp_eq_zero G Q hout
      (hcomm m hout)]
    rfl

/-- Inner-product form of the active-window reduction from \(Enpsi\) to
\(Enpsi2\):
\[
 \left\langle v,\sum_{m=0}^{N-1}E_mQ_nE_nv\right\rangle
 =\left\langle\sum_{m=n-l}^{n}E_mv,Q_nE_nv\right\rangle.
\]

This uses only the outside-window commutation hypothesis and symmetry of the
martingale differences, exactly as in Nachtergaele,
arXiv:cond-mat/9410110, lines 1206--1220. -/
theorem inner_sum_martingaleDifference_localProjection_eq_inner_sum_Icc
    (G : NestedGroundProjections (E := E)) (Q : E →ₗ[ℂ] E)
    (N n l : ℕ) (hn : n < N)
    (hcomm : ∀ m, m < n - l ∨ n < m →
      (G.martingaleDifference m).comp Q =
        Q.comp (G.martingaleDifference m)) (v : E) :
    inner ℂ v (∑ m ∈ Finset.range N,
        G.martingaleDifference m (Q (G.martingaleDifference n v))) =
      inner ℂ (∑ m ∈ Finset.Icc (n - l) n,
        G.martingaleDifference m v) (Q (G.martingaleDifference n v)) := by
  rw [G.sum_martingaleDifference_localProjection_eq_sum_Icc Q N n l hn hcomm v]
  simp_rw [inner_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro m _
  exact (G.martingaleDifference_isSymmetricProjection m).isSymmetric
    v (Q (G.martingaleDifference n v)) |>.symm

end FrustrationFree.NestedGroundProjections

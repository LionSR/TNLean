/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Periodic.SectorIrreducibility.ProjectionOrtho

/-!
# Global-gauge assembly for the periodic Fundamental Theorem

This module assembles the per-sector corner partial isometries of the periodic
overlap argument into a single global gauge, completing the final algebraic step
of Appendix A of arXiv:1708.00029.

## Setup

Two periodic tensors `A` and `B` carry the cyclic off-diagonal structure of
arXiv:1708.00029, eq:Aoffdiag: there are orthogonal projections `P u` (for `A`)
and `Q v` (for `B`) summing to the identity, with
`A i = ∑ u, P u * A i * P (u + 1)` and `B i = ∑ v, Q v * B i * Q (v + 1)`.  The
overlap argument produces corner partial isometries `U v`, each mapping the
`Q v` corner onto the `P (v - q)` corner (in the notation of eq:Cu, `U_v` is
nonzero only between the respective supports, where it acts like a unitary), and
a per-site proportionality of the form of eq:result with a unit-modulus scalar
`ζ`.

## Main results

* `globalGauge` — the global gauge `∑ u, P u * U (u + q) * Q (u + q)` of
  arXiv:1708.00029, eq:result.
* `globalGauge_eq_sum` — the corner relation collapses the global gauge to
  `∑ v, U v`.
* `repeatedBlocks_of_globalGauge` — the global gauge is unitary and conjugates
  `B` into `A` up to the phase `ζ`, giving a `RepeatedBlocks` relation.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, Appendix A,
  eq:Aoffdiag, eq:Cu, eq:result.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D m : ℕ}

/-- The **global gauge** of arXiv:1708.00029, eq:result.

Given per-sector corner partial isometries `U` matched to the sector
projections `P` (for `A`) and `Q` (for `B`) through the cyclic shift `q`, the
global gauge is `∑ u, P u * U (u + q) * Q (u + q)`.  The per-sector phases of the
paper are absorbed into `U`. -/
def globalGauge (P Q U : Fin m → Matrix (Fin D) (Fin D) ℂ) (q : Fin m) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ u : Fin m, P u * U (u + q) * Q (u + q)

/-- The corner relation `U v = P (v - q) * U v * Q v` collapses each summand of
the global gauge to `U (u + q)`, so the global gauge equals `∑ v, U v`. -/
theorem globalGauge_eq_sum [NeZero m]
    {P Q U : Fin m → Matrix (Fin D) (Fin D) ℂ} {q : Fin m}
    (hU_corner : ∀ v, U v = P (v - q) * U v * Q v) :
    globalGauge P Q U q = ∑ v : Fin m, U v := by
  have hterm : ∀ u : Fin m, P u * U (u + q) * Q (u + q) = U (u + q) := by
    intro u
    have hc := hU_corner (u + q)
    rw [add_sub_cancel_right] at hc
    exact hc.symm
  calc globalGauge P Q U q
      = ∑ u : Fin m, U (u + q) :=
        Finset.sum_congr rfl (fun u _ => hterm u)
    _ = ∑ v : Fin m, U v := Equiv.sum_comp (Equiv.addRight q) U

/-- **Global-gauge assembly** (arXiv:1708.00029, Appendix A, eq:result).

Suppose:

* `P` and `Q` are families of orthogonal projections summing to the identity
  (the cyclic sector projections of `A` and `B`, eq:Aoffdiag);
* `A` and `B` have the cyclic off-diagonal structure `A i = ∑ u, P u A^i P_{u+1}`
  and `B i = ∑ v, Q v B^i Q_{v+1}` (eq:Aoffdiag);
* `U v` is a corner partial isometry from the `Q v` corner onto the `P (v - q)`
  corner: `U v = P (v - q) * U v * Q v`, `(U v)ᴴ * U v = Q v`,
  `U v * (U v)ᴴ = P (v - q)` (eq:Cu);
* the per-site proportionality of eq:result holds with a unit-modulus scalar
  `ζ`:
  `P u A^i P_{u+1} = ζ • (U_{u+q} (Q_{u+q} B^i Q_{u+q+1}) U_{u+q+1}^†)`.

Then `A` and `B` are related by a single unit-modulus gauge phase and an
invertible (in fact unitary) gauge, i.e. `RepeatedBlocks A B`.  The gauge is the
global gauge `∑ u, P u U_{u+q} Q_{u+q}`, which the corner relations show is
unitary, and the per-site proportionality reassembles into the global
conjugation `A^i = ζ • (U_glob B^i U_glob^†)`. -/
theorem repeatedBlocks_of_globalGauge [NeZero m]
    {A B : MPSTensor d D}
    {P Q U : Fin m → Matrix (Fin D) (Fin D) ℂ}
    {q : Fin m} {ζ : ℂ}
    (hP_proj : ∀ u, IsOrthogonalProjection (P u))
    (hP_sum : ∑ u : Fin m, P u = 1)
    (hQ_proj : ∀ v, IsOrthogonalProjection (Q v))
    (hQ_sum : ∑ v : Fin m, Q v = 1)
    (hU_corner : ∀ v, U v = P (v - q) * U v * Q v)
    (hU_isoQ : ∀ v, (U v)ᴴ * U v = Q v)
    (hU_isoP : ∀ v, U v * (U v)ᴴ = P (v - q))
    (hA_cyclic : ∀ i, A i = ∑ u : Fin m, P u * A i * P (u + 1))
    (hB_cyclic : ∀ i, B i = ∑ v : Fin m, Q v * B i * Q (v + 1))
    (hprop : ∀ (u : Fin m) (i : Fin d),
      P u * A i * P (u + 1)
        = ζ • (U (u + q) * (Q (u + q) * B i * Q (u + q + 1)) * (U (u + q + 1))ᴴ))
    (hζ : ‖ζ‖ = 1) :
    RepeatedBlocks A B := by
  classical
  -- Projector facts.
  have hP_idem : ∀ u, P u * P u = P u := fun u => (hP_proj u).2
  have hQ_idem : ∀ v, Q v * Q v = Q v := fun v => (hQ_proj v).2
  have hPortho : Pairwise fun i j : Fin m => P i * P j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one P hP_proj hP_sum
  have hQortho : Pairwise fun i j : Fin m => Q i * Q j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one Q hQ_proj hQ_sum
  -- Corner absorption identities.
  have hUQ : ∀ v, U v * Q v = U v := by
    intro v
    calc U v * Q v
        = (P (v - q) * U v * Q v) * Q v := by rw [← hU_corner v]
      _ = P (v - q) * U v * (Q v * Q v) := by simp only [Matrix.mul_assoc]
      _ = P (v - q) * U v * Q v := by rw [hQ_idem v]
      _ = U v := (hU_corner v).symm
  have hPU : ∀ v, P (v - q) * U v = U v := by
    intro v
    calc P (v - q) * U v
        = P (v - q) * (P (v - q) * U v * Q v) := by rw [← hU_corner v]
      _ = (P (v - q) * P (v - q)) * U v * Q v := by simp only [Matrix.mul_assoc]
      _ = P (v - q) * U v * Q v := by rw [hP_idem (v - q)]
      _ = U v := (hU_corner v).symm
  have hQUh : ∀ v, Q v * (U v)ᴴ = (U v)ᴴ := by
    intro v
    have h := congrArg Matrix.conjTranspose (hUQ v)
    rwa [Matrix.conjTranspose_mul, (hQ_proj v).1.eq] at h
  have hUhP : ∀ v, (U v)ᴴ * P (v - q) = (U v)ᴴ := by
    intro v
    have h := congrArg Matrix.conjTranspose (hPU v)
    rwa [Matrix.conjTranspose_mul, (hP_proj (v - q)).1.eq] at h
  -- Row sums of `U U†` and `U† U` collapse to single diagonal projections.
  have step : ∀ v, ∑ w : Fin m, U v * (U w)ᴴ = P (v - q) := by
    intro v
    have hoff : ∀ w ∈ (Finset.univ : Finset (Fin m)), w ≠ v → U v * (U w)ᴴ = 0 := by
      intro w _ hwv
      calc U v * (U w)ᴴ
          = (U v * Q v) * (Q w * (U w)ᴴ) := by rw [hUQ v, hQUh w]
        _ = U v * (Q v * Q w) * (U w)ᴴ := by simp only [Matrix.mul_assoc]
        _ = U v * 0 * (U w)ᴴ := by rw [hQortho hwv.symm]
        _ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
    rw [Finset.sum_eq_single v hoff (fun hv => absurd (Finset.mem_univ v) hv), hU_isoP v]
  have step' : ∀ v, ∑ w : Fin m, (U v)ᴴ * U w = Q v := by
    intro v
    have hoff : ∀ w ∈ (Finset.univ : Finset (Fin m)), w ≠ v → (U v)ᴴ * U w = 0 := by
      intro w _ hwv
      calc (U v)ᴴ * U w
          = ((U v)ᴴ * P (v - q)) * (P (w - q) * U w) := by rw [hUhP v, hPU w]
        _ = (U v)ᴴ * (P (v - q) * P (w - q)) * U w := by simp only [Matrix.mul_assoc]
        _ = (U v)ᴴ * 0 * U w := by
              rw [hPortho (by simp only [ne_eq, sub_left_inj]; exact hwv.symm)]
        _ = 0 := by rw [Matrix.mul_zero, Matrix.zero_mul]
    rw [Finset.sum_eq_single v hoff (fun hv => absurd (Finset.mem_univ v) hv), hU_isoQ v]
  -- Unitarity of `∑ v, U v`.
  have hSSh : (∑ v : Fin m, U v) * (∑ v : Fin m, U v)ᴴ = 1 := by
    rw [Matrix.conjTranspose_sum]
    calc (∑ v : Fin m, U v) * (∑ w : Fin m, (U w)ᴴ)
        = ∑ v : Fin m, ∑ w : Fin m, U v * (U w)ᴴ := by rw [Finset.sum_mul_sum]
      _ = ∑ v : Fin m, P (v - q) := Finset.sum_congr rfl (fun v _ => step v)
      _ = ∑ u : Fin m, P u := Equiv.sum_comp (Equiv.subRight q) P
      _ = 1 := hP_sum
  have hShS : (∑ v : Fin m, U v)ᴴ * (∑ v : Fin m, U v) = 1 := by
    rw [Matrix.conjTranspose_sum]
    calc (∑ v : Fin m, (U v)ᴴ) * (∑ w : Fin m, U w)
        = ∑ v : Fin m, ∑ w : Fin m, (U v)ᴴ * U w := by rw [Finset.sum_mul_sum]
      _ = ∑ v : Fin m, Q v := Finset.sum_congr rfl (fun v _ => step' v)
      _ = 1 := hQ_sum
  -- Block-structure vanishing for `Q v B^i Q w` away from `w = v + 1`.
  have hQBQ_zero : ∀ (v : Fin m) (i : Fin d) (w : Fin m),
      w ≠ v + 1 → Q v * B i * Q w = 0 := by
    intro v i w hw
    rw [hB_cyclic i, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro t _
    rcases eq_or_ne t v with rfl | htv
    · simp only [Matrix.mul_assoc, hQortho hw.symm, Matrix.mul_zero]
    · simp only [← Matrix.mul_assoc, hQortho htv.symm, Matrix.zero_mul]
  -- The conjugated sum reassembles the per-sector summands.
  have hconj : ∀ i, (∑ v : Fin m, U v) * B i * (∑ v : Fin m, U v)ᴴ
      = ∑ v : Fin m, U v * (Q v * B i * Q (v + 1)) * (U (v + 1))ᴴ := by
    intro i
    rw [Matrix.conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have hsumeq : ∀ w : Fin m,
        U v * B i * (U w)ᴴ = U v * (Q v * B i * Q w) * (U w)ᴴ := by
      intro w
      calc U v * B i * (U w)ᴴ
          = (U v * Q v) * B i * (Q w * (U w)ᴴ) := by rw [hUQ v, hQUh w]
        _ = U v * (Q v * B i * Q w) * (U w)ᴴ := by simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl (fun w _ => hsumeq w)]
    exact Finset.sum_eq_single (v + 1)
      (fun w _ hw => by rw [hQBQ_zero v i w hw]; simp)
      (fun hv => absurd (Finset.mem_univ (v + 1)) hv)
  -- The global gauge equals `∑ v, U v`.
  have hgs : globalGauge P Q U q = ∑ v : Fin m, U v := globalGauge_eq_sum hU_corner
  -- Assemble the `RepeatedBlocks` witness.
  refine ⟨ζ, ⟨globalGauge P Q U q, (globalGauge P Q U q)ᴴ, ?_, ?_⟩, hζ, fun i => ?_⟩
  · rw [hgs]; exact hSSh
  · rw [hgs]; exact hShS
  · change A i = ζ • (globalGauge P Q U q * B i * (globalGauge P Q U q)ᴴ)
    rw [hgs, hconj i, hA_cyclic i,
      Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hprop u i), ← Finset.smul_sum]
    congr 1
    exact Equiv.sum_comp (Equiv.addRight q)
      (fun v => U v * (Q v * B i * Q (v + 1)) * (U (v + 1))ᴴ)

end MPSTensor

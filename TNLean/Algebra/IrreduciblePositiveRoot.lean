/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.MeanErgodicAdjoint
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Channel.Schwarz.Closure

/-!
# Trace preservation for roots of irreducible positive maps

If a positive power of a positive map is irreducible and trace preserving,
the map itself preserves trace. The kernel of the linearization
of the power map consists of trace-annihilating perturbations.

These are reductions for bounded-root selection in arXiv:1708.00029,
Theorem 4.1, converse, lines 812--818. They require an irreducible target,
which can be singular. A direct sum of irreducible blocks need not be
irreducible. Neither result establishes the required Kraus-rank bound;
see `docs/paper-gaps/dccsp17_root_kraus_rank_thm41.tex`.
-/

open scoped Matrix ComplexOrder BigOperators

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ
local notation "End" => Module.End ℂ Mat

private theorem fixed_eq_smul_one [NeZero D]
    (T : End) (hPos : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    (hOne : T 1 = 1) {X : Mat} (hX : T X = X) :
    ∃ c : ℂ, X = c • (1 : Mat) := by
  exact eigenvector_eq_smul_of_irreducible_positive T hPos hIrr
    (r := 1) zero_le_one Matrix.PosDef.one (by simpa using hOne) (by simpa using hX)

/-- Every positive root of an irreducible trace-preserving map is trace
preserving. No invertibility or complete-positivity assumption is needed.
This supplies a normalization reduction for arXiv:1708.00029,
Theorem 4.1, converse; it does not select a bounded-Kraus-rank root. -/
theorem IsPositiveMap.isTracePreservingMap_of_irreducible_pow
    {F : End} (hF : IsPositiveMap F) {p : ℕ} (hp : 0 < p)
    (hTP : IsTracePreservingMap (F ^ p)) (hIrr : IsIrreducibleMap (F ^ p)) :
    IsTracePreservingMap F := by
  classical
  by_cases hD : D = 0
  · subst D
    intro X
    simp [Matrix.trace]
  let : NeZero D := ⟨hD⟩
  let G : End := Matrix.traceAdjointMap F
  have hG : IsPositiveMap G := hF.traceAdjointMap
  have hOne : (G ^ p) 1 = 1 := by
    rw [← Matrix.traceAdjointMap_pow]
    exact isTracePreservingMap_iff_traceAdjointMap_one.mp hTP
  have hIrrG : IsIrreducibleMap (G ^ p) := by
    rw [← Matrix.traceAdjointMap_pow]
    exact hIrr.traceAdjointMap (hF.pow p)
  have hFixed : (G ^ p) (G 1) = G 1 := by
    have h := congrArg (fun T : End => T 1) ((Commute.refl G).pow_left p).eq
    simpa only [Module.End.mul_apply, hOne] using h
  obtain ⟨c, hc⟩ := fixed_eq_smul_one (G ^ p) (hG.pow p) hIrrG hOne hFixed
  have hcNonneg : 0 ≤ c := by
    have hdiag := (hG 1 Matrix.PosSemidef.one).diag_nonneg
      (i := (⟨0, Nat.pos_of_ne_zero hD⟩ : Fin D))
    simpa only [hc, Matrix.smul_apply, Matrix.one_apply, ↓reduceIte,
      smul_eq_mul, mul_one] using hdiag
  obtain ⟨hr, hi⟩ := Complex.nonneg_iff.mp hcNonneg
  have hcReal : (c.re : ℂ) = c := Complex.ext (by simp) (by simpa using hi)
  have hScalar : G 1 = (c.re : ℂ) • (1 : Mat) := by rw [hcReal]; exact hc
  have hIter (n : ℕ) : (G ^ n) 1 = (c.re : ℂ) ^ n • (1 : Mat) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hScalar, smul_smul, pow_succ]
  have hrPowC : (c.re : ℂ) ^ p = 1 := by
    have h := congrArg
      (fun X : Mat => X ⟨0, Nat.pos_of_ne_zero hD⟩ ⟨0, Nat.pos_of_ne_zero hD⟩)
      ((hIter p).symm.trans hOne)
    simpa using h
  have hrPow : c.re ^ p = 1 := by exact_mod_cast hrPowC
  have hrOne : c.re = 1 := (pow_eq_one_iff_of_nonneg hr hp.ne').mp hrPow
  apply isTracePreservingMap_iff_traceAdjointMap_one.mpr
  change G 1 = 1
  simpa only [hrOne, Complex.ofReal_one, one_smul] using hScalar

/-- A perturbation in the kernel of the linearization of a positive root's
power has zero output trace on every input, provided the power is irreducible
and trace preserving. The perturbation need not preserve Hermiticity.
This is a first-order restriction for the root-selection problem in
arXiv:1708.00029, Theorem 4.1; it makes no assertion about exact deformations. -/
theorem IsPositiveMap.trace_eq_zero_of_power_linearization_eq_zero
    {F H : End} (hF : IsPositiveMap F) {p : ℕ} (hp : 0 < p)
    (hTP : IsTracePreservingMap (F ^ p)) (hIrr : IsIrreducibleMap (F ^ p))
    (hH : ∑ k ∈ Finset.range p, F ^ k * H * F ^ (p - 1 - k) = 0) :
    ∀ X : Mat, Matrix.trace (H X) = 0 := by
  classical
  by_cases hD : D = 0
  · subst D
    intro X
    simp [Matrix.trace]
  let : NeZero D := ⟨hD⟩
  have hFtp := hF.isTracePreservingMap_of_irreducible_pow hp hTP hIrr
  let T : End := Matrix.traceAdjointMap F
  let u : Mat := Matrix.traceAdjointMap H 1
  have hTone : T 1 = 1 := isTracePreservingMap_iff_traceAdjointMap_one.mp hFtp
  have hTpowOne (n : ℕ) : (T ^ n) 1 = 1 := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hTone]
  have hTrace (k : ℕ) (X : Mat) : Matrix.trace ((F ^ k) X) = Matrix.trace X :=
    hFtp.pow k X
  have hSum : ∑ k ∈ Finset.range p, (T ^ k) u = 0 := by
    apply (Matrix.trace_mul_right_eq_zero_iff _).mp
    intro X
    rw [Matrix.sum_mul, Matrix.trace_sum]
    calc
      ∑ k ∈ Finset.range p, Matrix.trace ((T ^ k) u * X) =
          ∑ k ∈ Finset.range p, Matrix.trace (H ((F ^ k) X)) := by
        apply Finset.sum_congr rfl
        intro k _
        change Matrix.trace ((Matrix.traceAdjointMap F ^ k)
          (Matrix.traceAdjointMap H 1) * X) = _
        rw [← Matrix.traceAdjointMap_pow, Matrix.trace_traceAdjointMap_mul,
          Matrix.trace_traceAdjointMap_mul, Matrix.one_mul]
      _ = ∑ k ∈ Finset.range p, Matrix.trace (H ((F ^ (p - 1 - k)) X)) :=
        (Finset.sum_range_reflect (fun k => Matrix.trace (H ((F ^ k) X))) p).symm
      _ = Matrix.trace ((∑ k ∈ Finset.range p, F ^ k * H * F ^ (p - 1 - k)) X) := by
        simp only [LinearMap.sum_apply, Matrix.trace_sum, Module.End.mul_apply, hTrace]
      _ = 0 := by rw [hH]; simp
  have hSumNext : ∑ k ∈ Finset.range p, (T ^ (k + 1)) u = 0 := by
    calc
      ∑ k ∈ Finset.range p, (T ^ (k + 1)) u =
          T (∑ k ∈ Finset.range p, (T ^ k) u) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ', Module.End.mul_apply]
      _ = 0 := by rw [hSum, map_zero]
  have hTel : ∑ k ∈ Finset.range p, ((T ^ k) u - (T ^ (k + 1)) u) =
      u - (T ^ p) u := by
    simpa using Finset.sum_range_sub' (fun k => (T ^ k) u) p
  have hFixed : (T ^ p) u = u := by
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [← hTel, Finset.sum_sub_distrib, hSum, hSumNext, sub_self]
  have hIrrT : IsIrreducibleMap (T ^ p) := by
    rw [← Matrix.traceAdjointMap_pow]
    exact hIrr.traceAdjointMap (hF.pow p)
  obtain ⟨c, hc⟩ := fixed_eq_smul_one (T ^ p) (hF.traceAdjointMap.pow p)
    hIrrT (hTpowOne p) hFixed
  have hIter (n : ℕ) : (T ^ n) u = u := by
    rw [hc, map_smul, hTpowOne]
  have hZero : (p : ℂ) • u = 0 := by
    simpa only [hIter, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℂ] using hSum
  have hu : u = 0 := (smul_eq_zero.mp hZero).resolve_left (by exact_mod_cast hp.ne')
  intro X
  have h := Matrix.trace_traceAdjointMap_mul H (1 : Mat) X
  change Matrix.trace (u * X) = Matrix.trace (1 * H X) at h
  simpa [hu] using h.symm

/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.SchmidtNumberCompact
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Entanglement witnesses from a separating hyperplane

Wolf's Chapter 3, Section 3.2 (the paragraph *Detecting entanglement*, Proposition 3.3)
constructs an **entanglement witness** for every bipartite state of Schmidt number
larger than `n`: a Hermitian operator `W` with negative expectation on the given
state but nonnegative expectation on every state of Schmidt number at most `n`.
The construction separates the given state from the compact convex set `S_n` of
trace-one states of Schmidt number at most `n` by a hyperplane, and reads the witness
off the separating functional.

This file supplies the capstone of that argument: the separation, the representation
of the separating functional as a trace form, and the witness it produces.

## The separating-hyperplane construction

The two geometric inputs are already in place: `S_n` is convex
(`Matrix.convex_setOf_hasSchmidtNumberLE_trace_one`) and compact
(`Matrix.isCompact_setOf_hasSchmidtNumberLE_trace_one`).  A trace-one Hermitian
state ρ of Schmidt number exceeding `n` lies outside `S_n`, so the geometric
Hahn–Banach theorem produces a continuous real-linear functional `f` and a constant
`c` with `f ρ < c` and `c < f σ` for every `σ ∈ S_n`.

Every real-linear functional on the matrix space is a **trace form**: it equals
`X ↦ Re tr(X H)` for some matrix `H`.  This is the existence half of the Riesz
representation for the nondegenerate real bilinear pairing
`(X, H) ↦ Re tr(X H)`, whose nondegeneracy is `Re tr(H Hᴴ) = ‖H‖²_F`.  Replacing `H`
by its Hermitian part `H₀ = (H + Hᴴ)/2` keeps the value on Hermitian inputs and makes
`H₀` Hermitian.

The witness is `W = H₀ − c • 1`.  Its expectation `Re tr(W ρ)` is `f ρ − c < 0`,
while on a unit Schmidt-rank-≤`n` vector ψ the projector `|ψ⟩⟨ψ|` lies in `S_n`, so
its expectation is `f σ − c > 0`; scaling back to a general such ψ keeps the
expectation nonnegative.

## Main results

* `Matrix.exists_isHermitian_trace_form_re`: every real-linear functional on the
  matrix space is a trace form `X ↦ Re tr(X H)` with `H` Hermitian — the Riesz
  representation underlying the witness construction.
* `Matrix.exists_isHermitian_witness`: **an entanglement witness exists for every
  trace-one Hermitian state of Schmidt number larger than `n`** (Wolf §3.2,
  Proposition 3.3, the only-if direction).
* `Matrix.not_hasSchmidtNumberLE_of_exists_witness`: the converse — a state detected by a
  Schmidt-`n` witness has Schmidt number larger than `n` (no density-matrix hypotheses
  needed).
* `Matrix.not_hasSchmidtNumberLE_iff_exists_witness`: **Wolf §3.2, Proposition 3.3** as an
  iff, for a trace-one Hermitian state: Schmidt number larger than `n` is equivalent to
  detection by an entanglement witness for `S_n`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, the *Detecting entanglement* paragraph, Proposition 3.3][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

-- The Frobenius norm equips the matrix space with a finite-dimensional real normed
-- structure whose topology agrees with the entrywise-convergence topology used for the
-- merged compactness input; it supplies the `NormedSpace ℝ`/`FiniteDimensional ℝ`/
-- `LocallyConvexSpace ℝ` instances the separation theorem requires.
open scoped Matrix.Norms.Frobenius

namespace Matrix

variable {N : Type*} [Fintype N]

/-! ## The trace bilinear form and its nondegeneracy -/

/-- The real bilinear trace pairing `(X, H) ↦ Re tr(X H)` on the matrix space,
packaged as a real-bilinear map.  It is symmetric in the sense `Re tr(X H) = Re tr(H X)`
and nondegenerate, with `Re tr(H Hᴴ) = ‖H‖²_F`. -/
noncomputable def traceFormReal : Matrix N N ℂ →ₗ[ℝ] Matrix N N ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X H => ((X * H).trace).re)
    (fun X₁ X₂ H => by rw [add_mul, trace_add, Complex.add_re])
    (fun c X H => by
      rw [smul_mul_assoc, trace_smul, Complex.smul_re, smul_eq_mul])
    (fun X H₁ H₂ => by rw [mul_add, trace_add, Complex.add_re])
    (fun c X H => by
      rw [mul_smul_comm, trace_smul, Complex.smul_re, smul_eq_mul])

@[simp]
theorem traceFormReal_apply (X H : Matrix N N ℂ) :
    traceFormReal X H = ((X * H).trace).re := rfl

/-- The trace bilinear form on the diagonal pair `(H, Hᴴ)` is the squared Frobenius
norm of `H`: `Re tr(H Hᴴ) = ‖H‖²_F = ∑ |H i j|²`.  In particular it is positive
unless `H = 0`, the nondegeneracy underlying the trace-form representation. -/
theorem traceFormReal_self_conjTranspose_eq_zero_iff (H : Matrix N N ℂ) :
    traceFormReal H Hᴴ = 0 ↔ H = 0 := by
  constructor
  · intro h
    -- `tr(H Hᴴ)` is a nonnegative real, and its real part vanishes, so it is zero.
    have hpos : (H * Hᴴ).PosSemidef := posSemidef_self_mul_conjTranspose H
    have hnn : (0 : ℂ) ≤ (H * Hᴴ).trace := hpos.trace_nonneg
    have htrace : (H * Hᴴ).trace = 0 := by
      refine Complex.ext h ?_
      exact (RCLike.nonneg_iff (K := ℂ).mp hnn).2
    exact (trace_mul_conjTranspose_self_eq_zero_iff).1 htrace
  · intro h; subst h; simp

/-! ## The trace-form representation of a real-linear functional -/

/-- The representing map `H ↦ (X ↦ Re tr(X H))` sending a matrix to the trace form it
defines.  It is the flip of the real bilinear trace pairing. -/
noncomputable def traceFormRep : Matrix N N ℂ →ₗ[ℝ] (Matrix N N ℂ →ₗ[ℝ] ℝ) :=
  (traceFormReal (N := N)).flip

@[simp]
theorem traceFormRep_apply (H X : Matrix N N ℂ) :
    traceFormRep H X = ((X * H).trace).re := rfl

/-- The trace-form representation map is injective: a matrix `H` whose trace form
`X ↦ Re tr(X H)` vanishes identically is zero.  Evaluating on `X = Hᴴ` gives
`Re tr(Hᴴ H) = ‖H‖²_F = 0`, forcing `H = 0`. -/
theorem traceFormRep_injective : Function.Injective (traceFormRep (N := N)) := by
  rw [injective_iff_map_eq_zero]
  intro H hH
  -- Read off the diagonal value `Re tr(Hᴴ H) = ‖H‖²_F`.
  have hval : traceFormRep H Hᴴ = 0 := by rw [hH]; rfl
  rw [traceFormRep_apply, trace_mul_comm] at hval
  exact (traceFormReal_self_conjTranspose_eq_zero_iff H).1 hval

/-- **Every real-linear functional on the matrix space is a trace form.**  For each
real-linear functional `g : Matrix N N ℂ →ₗ[ℝ] ℝ` there is a matrix `H` with
`g X = Re tr(X H)` for all `X`.

This is the existence half of the Riesz representation for the nondegenerate real
bilinear pairing `(X, H) ↦ Re tr(X H)`: the representing map `H ↦ (X ↦ Re tr(X H))`
is an injective real-linear map between the matrix space and its real dual, which have
equal finite dimension, hence is surjective. -/
theorem exists_trace_form_re (g : Matrix N N ℂ →ₗ[ℝ] ℝ) :
    ∃ H : Matrix N N ℂ, ∀ X, g X = ((X * H).trace).re := by
  -- The representing map is injective between two real spaces of equal finite dimension,
  -- hence surjective; `g` is in its range.
  have hdim :
      Module.finrank ℝ (Matrix N N ℂ) = Module.finrank ℝ (Matrix N N ℂ →ₗ[ℝ] ℝ) :=
    (Subspace.dual_finrank_eq (K := ℝ) (V := Matrix N N ℂ)).symm
  have hsurj : Function.Surjective (traceFormRep (N := N)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 traceFormRep_injective
  obtain ⟨H, hH⟩ := hsurj g
  exact ⟨H, fun X => by rw [← hH]; rfl⟩

/-- **Every real-linear functional is the trace form of a Hermitian matrix.**  Given
`g : Matrix N N ℂ →ₗ[ℝ] ℝ`, there is a Hermitian `H₀` with `g X = Re tr(X H₀)` for
every Hermitian `X`.

The trace-form representation `g X = Re tr(X H)` of `exists_trace_form_re` holds with
some `H`; replacing `H` by its Hermitian part `H₀ = (H + Hᴴ)/2` keeps the value on
Hermitian inputs, because `tr(X Hᴴ) = conj tr(X H)` when `X` is Hermitian, so the two
trace forms have equal real part there. -/
theorem exists_isHermitian_trace_form_re (g : Matrix N N ℂ →ₗ[ℝ] ℝ) :
    ∃ H₀ : Matrix N N ℂ, H₀.IsHermitian ∧
      ∀ X : Matrix N N ℂ, X.IsHermitian → g X = ((X * H₀).trace).re := by
  obtain ⟨H, hH⟩ := exists_trace_form_re g
  refine ⟨((2⁻¹ : ℝ) : ℂ) • (H + Hᴴ), ?_, ?_⟩
  · -- The Hermitian part is Hermitian: a self-adjoint real scalar times a Hermitian sum.
    refine IsHermitian.smul ?_ ?_
    · rw [IsHermitian, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    · rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  · intro X hX
    rw [hH X]
    -- On Hermitian `X`, `tr(X Hᴴ) = conj tr(X H)`, so `Re tr(X Hᴴ) = Re tr(X H)`.
    have hconj : (X * Hᴴ).trace = star ((X * H).trace) := by
      rw [← trace_conjTranspose, conjTranspose_mul, hX, trace_mul_comm]
    have hre : ((X * Hᴴ).trace).re = ((X * H).trace).re := by
      rw [hconj, Complex.star_def, Complex.conj_re]
    -- Expand the Hermitian-part trace form and use `Re tr(X Hᴴ) = Re tr(X H)`.
    have hexpand : (X * (((2⁻¹ : ℝ) : ℂ) • (H + Hᴴ))).trace
        = ((2⁻¹ : ℝ) : ℂ) * ((X * H).trace + (X * Hᴴ).trace) := by
      rw [mul_smul_comm, trace_smul, mul_add, trace_add, smul_eq_mul]
    have hrhs : ((X * (((2⁻¹ : ℝ) : ℂ) • (H + Hᴴ))).trace).re = ((X * H).trace).re := by
      rw [hexpand, Complex.re_ofReal_mul, Complex.add_re, hre]
      ring
    rw [hrhs]

end Matrix

/-! ## The separating-hyperplane witness -/

namespace Matrix

variable {d d' : ℕ}

open scoped ComplexOrder

/-- The trace of a pure-state projector `|ψ⟩⟨ψ|` is the squared Euclidean norm of ψ,
which is real, so its real part recovers `ψ ⬝ᵥ star ψ`. -/
private theorem re_trace_vecMulVec (ψ : Fin d × Fin d' → ℂ) :
    ((vecMulVec ψ (star ψ)).trace).re = (ψ ⬝ᵥ star ψ).re := by
  rw [trace_vecMulVec]

/-- **An entanglement witness exists for every trace-one Hermitian state of Schmidt
number larger than `n`** (Wolf §3.2, Proposition 3.3, only-if direction).

A trace-one Hermitian bipartite state ρ that is not of Schmidt number at most `n`
admits a Hermitian operator `W` whose expectation on ρ is negative and whose
expectation on every pure state of Schmidt rank at most `n` is nonnegative.

The set `S_n` of trace-one states of Schmidt number at most `n` is compact and convex;
ρ lies outside it, so the geometric Hahn–Banach theorem separates `{ρ}` from `S_n` by a
continuous real-linear functional `f` and a constant `c` with `f ρ < c < f σ` for every
`σ ∈ S_n`.  Representing `f` as the trace form of a Hermitian `H₀` and setting
`W = H₀ − c • 1` makes `Re tr(W ρ) = f ρ − c < 0`, while for a unit Schmidt-rank-≤`n`
vector the projector lies in `S_n` and gives a nonnegative expectation; a general such
vector scales this by its squared norm. -/
theorem exists_isHermitian_witness (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρH : ρ.IsHermitian) (hρtr : ρ.trace = 1) (hρ : ¬ HasSchmidtNumberLE n ρ) :
    ∃ W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ, W.IsHermitian ∧
      (W * ρ).trace.re < 0 ∧
      ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE n ψ →
        0 ≤ (W * Matrix.vecMulVec ψ (star ψ)).trace.re := by
  classical
  -- The Frobenius normed structure makes the matrix space a real locally convex space,
  -- the ambient hypothesis of the geometric Hahn–Banach separation theorem.
  haveI : LocallyConvexSpace ℝ (Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :=
    NormedSpace.toLocallyConvexSpace (E := Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ)
  -- ρ is separated from the compact convex set `S_n` by a hyperplane.
  set Sn : Set (Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :=
    {σ | HasSchmidtNumberLE n σ ∧ σ.trace = 1} with hSn
  have hconv : Convex ℝ Sn := convex_setOf_hasSchmidtNumberLE_trace_one n
  have hcomp : IsCompact Sn := isCompact_setOf_hasSchmidtNumberLE_trace_one n
  have hρnotmem : ρ ∉ Sn := by
    rw [hSn]; rintro ⟨hmem, _⟩; exact hρ hmem
  -- Separate the closed convex `{ρ}` from the compact convex `S_n`.
  obtain ⟨f, u, v, hfρ, huv, hfSn⟩ :=
    geometric_hahn_banach_closed_compact (convex_singleton ρ) isClosed_singleton hconv hcomp
      (by rw [Set.disjoint_singleton_left]; exact hρnotmem)
  -- A constant strictly between the two sides.
  set c : ℝ := (u + v) / 2 with hc
  have hfρc : f ρ < c := by
    have := hfρ ρ rfl; rw [hc]; linarith
  have hcSn : ∀ σ ∈ Sn, c < f σ := fun σ hσ => by
    have := hfSn σ hσ; rw [hc]; linarith
  -- Represent the separating functional as the trace form of a Hermitian matrix.
  obtain ⟨H₀, hH₀herm, hH₀rep₀⟩ :=
    exists_isHermitian_trace_form_re (N := Fin d × Fin d') f.toLinearMap
  have hH₀rep : ∀ X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ, X.IsHermitian →
      f X = ((X * H₀).trace).re := fun X hX => by
    have := hH₀rep₀ X hX; rwa [ContinuousLinearMap.coe_coe] at this
  -- The witness.
  refine ⟨H₀ - (c : ℂ) • 1, ?_, ?_, ?_⟩
  · -- `W` is Hermitian: a difference of Hermitian matrices.
    refine hH₀herm.sub ?_
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  · -- `Re tr(W ρ) = f ρ − c < 0`.
    have hWρ : ((H₀ - (c : ℂ) • 1) * ρ).trace.re = (f ρ) - c := by
      rw [sub_mul, trace_sub, Complex.sub_re, smul_mul_assoc, one_mul, trace_smul,
        smul_eq_mul, Complex.re_ofReal_mul, hρtr, Complex.one_re, mul_one,
        trace_mul_comm, ← hH₀rep ρ hρH]
    rw [hWρ]; linarith
  · -- For each Schmidt-rank-≤`n` vector ψ the expectation is nonnegative.
    intro ψ hψ
    -- The expectation, scaled out as a value on the projector.
    have hWψ : ((H₀ - (c : ℂ) • 1) * vecMulVec ψ (star ψ)).trace.re
        = (f (vecMulVec ψ (star ψ))) - c * (ψ ⬝ᵥ star ψ).re := by
      rw [sub_mul, trace_sub, Complex.sub_re, smul_mul_assoc, one_mul, trace_smul,
        smul_eq_mul, Complex.re_ofReal_mul, re_trace_vecMulVec,
        trace_mul_comm,
        ← hH₀rep (vecMulVec ψ (star ψ)) (posSemidef_vecMulVec_self_star ψ).isHermitian]
    rw [hWψ]
    -- The squared norm `s = ‖ψ‖²` is nonnegative.
    set s : ℝ := (ψ ⬝ᵥ star ψ).re with hs
    have hs_nonneg : 0 ≤ s := by
      rw [hs, ← re_trace_vecMulVec]
      exact (RCLike.nonneg_iff (K := ℂ).mp
        (posSemidef_vecMulVec_self_star ψ).trace_nonneg).1
    -- Split on whether ψ vanishes.
    by_cases hψ0 : ψ = 0
    · subst hψ0
      simp only [hs, star_zero, dotProduct_zero, Complex.zero_re, mul_zero, sub_zero,
        vecMulVec_zero]
      simp
    · -- Normalize ψ to a unit vector whose projector lies in `S_n`.
      obtain ⟨φ, hφnorm, hφrank, hφeq⟩ :=
        exists_unit_smul_euclideanProj_eq hψ0 hψ
      -- The trace identity for the squared norm.
      have hsval :
          ((‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin d × Fin d'))‖ : ℝ) ^ 2 : ℝ)
            = s := by
        have h := ofReal_normSq_eq_dotProduct_star ψ
        rw [hs, ← h, Complex.ofReal_re]
      -- The normalized projector is a state of `S_n`.
      have hP : euclideanProj φ ∈ Sn := by
        rw [hSn]
        refine ⟨hasSchmidtNumberLE_vecMulVec hφrank, ?_⟩
        rw [trace_euclideanProj, hφnorm]; norm_num
      have hfP : c < f (euclideanProj φ) := hcSn _ hP
      -- `|ψ⟩⟨ψ| = s • (euclideanProj φ)`, so `f` and the norm-factor relate the two.
      have hproj_eq : vecMulVec ψ (star ψ) = (s : ℝ) • euclideanProj φ := by
        rw [← hsval]; exact hφeq.symm
      have hfψ : f (vecMulVec ψ (star ψ)) = s * f (euclideanProj φ) := by
        rw [hproj_eq, map_smul, smul_eq_mul]
      rw [hfψ]
      -- `s * f(P) - c * s = s * (f(P) - c) ≥ 0`.
      have : s * f (euclideanProj φ) - c * s = s * (f (euclideanProj φ) - c) := by ring
      rw [this]
      exact mul_nonneg hs_nonneg (by linarith)

/-- **A state detected by a Schmidt-`n` witness is not of Schmidt number at most `n`**
(Wolf §3.2, Proposition 3.3, if direction).

If a Hermitian operator `W` has negative expectation on ρ but nonnegative expectation on
every pure state of Schmidt rank at most `n`, then ρ is not of Schmidt number at most `n`.
This direction needs no density-matrix hypotheses on ρ: if ρ were a sum
`∑ i, |ψ_i⟩⟨ψ_i|` of pure projectors of Schmidt rank at most `n`, the linearity of the
trace would make `Re tr(W ρ)` the sum of the nonnegative numbers `Re tr(W |ψ_i⟩⟨ψ_i|)`,
contradicting its negativity. -/
theorem not_hasSchmidtNumberLE_of_exists_witness (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hW : ∃ W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ, W.IsHermitian ∧
      (W * ρ).trace.re < 0 ∧
      ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE n ψ →
        0 ≤ (W * Matrix.vecMulVec ψ (star ψ)).trace.re) :
    ¬ HasSchmidtNumberLE n ρ := by
  obtain ⟨W, _, hneg, hpos⟩ := hW
  rintro ⟨ι, _, ψ, hψ, rfl⟩
  -- Push the witness multiplication and the trace through the finite sum.
  have hsum : (W * ∑ i, vecMulVec (ψ i) (star (ψ i))).trace.re
      = ∑ i, (W * vecMulVec (ψ i) (star (ψ i))).trace.re := by
    rw [Finset.mul_sum, trace_sum, Complex.re_sum]
  -- Each summand is nonnegative, so the total is nonnegative, contradicting `hneg`.
  rw [hsum] at hneg
  have : 0 ≤ ∑ i, (W * vecMulVec (ψ i) (star (ψ i))).trace.re :=
    Finset.sum_nonneg fun i _ => hpos (ψ i) (hψ i)
  linarith

/-- **Wolf's entanglement-witness criterion** (Wolf §3.2, Proposition 3.3).  A trace-one
Hermitian bipartite state ρ has Schmidt number larger than `n` if and only if there is a
Hermitian operator `W` whose expectation on ρ is negative while its expectation on every
pure state of Schmidt rank at most `n` is nonnegative.

The forward implication is the separating-hyperplane construction
`exists_isHermitian_witness`; the converse `not_hasSchmidtNumberLE_of_exists_witness`
needs no density-matrix hypotheses on ρ and holds by the linearity of the trace. -/
theorem not_hasSchmidtNumberLE_iff_exists_witness (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρH : ρ.IsHermitian) (hρtr : ρ.trace = 1) :
    ¬ HasSchmidtNumberLE n ρ ↔
      ∃ W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ, W.IsHermitian ∧
        (W * ρ).trace.re < 0 ∧
        ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE n ψ →
          0 ≤ (W * Matrix.vecMulVec ψ (star ψ)).trace.re :=
  ⟨fun hρ => exists_isHermitian_witness n hρH hρtr hρ,
   not_hasSchmidtNumberLE_of_exists_witness n⟩

end Matrix

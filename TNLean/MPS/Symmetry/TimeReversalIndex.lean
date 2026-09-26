/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryEntrywiseConjugation
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Symmetry.GaugeUniqueness

/-!
# Time-reversal and reflection indices of normal MPS; the Kramers obstruction

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
`Papers/2011.12127/TN-Review-main.tex` lines 1085–1086 (eq. `eq:XAX=B`), lines
1116–1117 (time reversal and the Kramers obstruction) and line 1120 (reflection):
for a normal tensor with `Āⁱ = e^{iφ} X† Aⁱ X`, applying the symmetry twice gives
`Aⁱ = (X X̄)† Aⁱ (X X̄)`, so `X X̄ = ±1`, a topological index; for the Wigner time
reversal `Aⁱ ↦ ∑ⱼ (σ_y)ᵢⱼ Āʲ` the same computation gives `Aⁱ = -Aⁱ` up to gauge,
so no normal tensor carries that symmetry.  Reflection acts by transposition,
`(Aⁱ)ᵀ = e^{iφ} X† Aⁱ X`, with the same index.

**Formalized here.**
* Eq. `eq:XAX=B` for normal tensors: `X⁻¹ Aⁱ X = c Y⁻¹ Aⁱ Y` forces `c = 1` and
  `X ∝ Y`.
* The time-reversal index: for a normal tensor, a physical matrix `P` with
  `P P̄ = 1` (the on-site part of time reversal, `P = 1` for pure time reversal)
  and a unitary gauge `X` with `∑ⱼ Pᵢⱼ Āʲ = ζ X† Aⁱ X`, `X X̄ = 1` or `X X̄ = -1`,
  and the sign does not depend on the choice of the unitary gauge.
* The reflection index: the same conclusions for `(Aⁱ)ᵀ = ζ X† Aⁱ X`.
* The Kramers obstruction: if `P P̄ = -1` (as for `σ_y`), no normal tensor of
  positive bond dimension satisfies `∑ⱼ Pᵢⱼ Āʲ = ζ X⁻¹ Aⁱ X` with `X` invertible;
  for injective tensors this excludes equality of the matrix product vectors with
  those of the time-reversed tensor.

The source derives the gauge relations from the fundamental theorem for
symmetric states; the index statements here start from the gauge relations.

## Main results

* `MPSTensor.gauge_phase_unique_of_isNormal`
* `MPSTensor.mul_map_star_eq_one_or_neg_one_of_timeReversal_gauge`
* `MPSTensor.mul_map_star_eq_of_timeReversal_gauges`
* `MPSTensor.mul_map_star_eq_one_or_neg_one_of_reflection_gauge`
* `MPSTensor.mul_map_star_eq_of_reflection_gauges`
* `MPSTensor.not_timeReversal_gauge_of_mul_map_star_eq_neg_one`
* `MPSTensor.not_wignerTimeReversal_gauge`
* `MPSTensor.not_sameMPV_wignerTimeReversal_of_isInjective`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-! ### Gauge-phase uniqueness for normal tensors -/

/-- A letterwise gauge-phase relation propagates to words, with the phase raised
to the word length. -/
theorem evalWord_gauge_phase {A : MPSTensor d D} {X Y : GL (Fin D) ℂ} {c : ℂ}
    (h : ∀ i, ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X =
      c • (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * Y)) :
    ∀ w : List (Fin d),
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * Kraus.evalWord A w * X =
        c ^ w.length •
          (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * Kraus.evalWord A w * Y)
  | [] => by simp [Kraus.evalWord]
  | i :: w => by
      have hw := evalWord_gauge_phase h w
      have hsplit : ∀ Z : GL (Fin D) ℂ,
          ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * (A i * Kraus.evalWord A w) * Z =
            (((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * Z) *
              (((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * Kraus.evalWord A w * Z) := by
        intro Z
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
      simp only [Kraus.evalWord, List.length_cons]
      rw [hsplit, hsplit, h i, hw, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ,
        mul_comm c]

/-- A normal tensor of positive bond dimension has a nonzero letter: otherwise every
word of positive length vanishes and no word space is the full matrix algebra. -/
theorem exists_apply_ne_zero_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) : ∃ i, A i ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hNpos, hN⟩ := hA
  have hB : Kraus.IsInjective (blockTensor A N) :=
    (isNBlkInjective_iff_blockTensor_isInjective A N).1 hN
  have hBzero : ∀ I, blockTensor A N I = 0 := by
    intro I
    have hlen := Kraus.length_wordOfBlock d N I
    change Kraus.evalWord A (Kraus.wordOfBlock d N I) = 0
    cases hw : Kraus.wordOfBlock d N I with
    | nil => rw [hw] at hlen; simp at hlen; omega
    | cons i w => simp [Kraus.evalWord, hcon i]
  have htop := hB.span_eq_top
  have hbot : Submodule.span ℂ (Set.range (blockTensor A N)) = ⊥ :=
    (Submodule.span_eq_bot).2 (fun x ⟨I, hI⟩ => hI ▸ hBzero I)
  rw [hbot] at htop
  have : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) :=
    htop ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot ℂ).1 this)

/-- **Gauge-phase uniqueness for normal tensors.**
Source: arXiv:2011.12127, §III.A, eq. `eq:XAX=B`
(`Papers/2011.12127/TN-Review-main.tex` lines 1085–1086): for a normal tensor,
`X⁻¹ Aⁱ X = e^{iχ} Y⁻¹ Aⁱ Y` for all `i` forces `e^{iχ} = 1` and `X ∝ Y`.

Blocking to an injective length gives `X ∝ Y` from `gauge_phase_unique`; the
single-letter relation then reads `Y⁻¹ Aⁱ Y = c Y⁻¹ Aⁱ Y`, and some letter is
nonzero, so `c = 1`. -/
theorem gauge_phase_unique_of_isNormal [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {X Y : GL (Fin D) ℂ} {c : ℂ}
    (h : ∀ i, ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X =
      c • (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * Y)) :
    c = 1 ∧ ∃ u : Units ℂ,
      (X : Matrix (Fin D) (Fin D) ℂ) = (u : ℂ) • (Y : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  obtain ⟨N, hNpos, hN⟩ := hA
  have hB : Kraus.IsInjective (blockTensor A N) :=
    (isNBlkInjective_iff_blockTensor_isInjective A N).1 hN
  have hBrel : ∀ I, ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * blockTensor A N I * X =
      c ^ N • (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * blockTensor A N I * Y) := by
    intro I
    have := evalWord_gauge_phase h (Kraus.wordOfBlock d N I)
    rwa [Kraus.length_wordOfBlock] at this
  obtain ⟨-, u, hu⟩ := gauge_phase_unique hB hBrel
  refine ⟨?_, u, hu⟩
  -- With `X = u Y`, the letter relation reads `Y⁻¹ Aⁱ Y = c Y⁻¹ Aⁱ Y`.
  have hXinv : ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      ((u⁻¹ : Units ℂ) : ℂ) • ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    have h1 : (((u⁻¹ : Units ℂ) : ℂ) • ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
        (X : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      rw [hu, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul,
        Units.inv_mul]
    calc ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
        = ((((u⁻¹ : Units ℂ) : ℂ) • ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
            (X : Matrix (Fin D) (Fin D) ℂ)) * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ) := by
          rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  obtain ⟨i, hi0⟩ := exists_apply_ne_zero_of_isNormal ⟨N, hNpos, hN⟩
  have hi := h i
  rw [hXinv, hu, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Units.mul_inv, one_smul] at hi
  by_contra hc
  have h1 : ((1 - c) • (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * Y)) = 0 := by
    rw [sub_smul, one_smul, ← hi, sub_self]
  have h2 := (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr (Ne.symm hc))
  have h3 := congrArg (fun M => (Y : Matrix (Fin D) (Fin D) ℂ) * M *
    ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) h2
  exact hi0 (by simpa [Matrix.mul_assoc] using h3)

/-! ### The involution index `X X̄ = ±1` -/

/-- A unitary matrix as an element of the general linear group. -/
private def unitaryGL (X : Matrix.unitaryGroup (Fin D) ℂ) : GL (Fin D) ℂ :=
  ⟨X, star X, Matrix.mem_unitaryGroup_iff.mp X.2, Matrix.mem_unitaryGroup_iff'.mp X.2⟩

/-- Core of the index lemmas: if applying a symmetry twice returns
`Aⁱ = c (X X̄)† Aⁱ (X X̄)` for a unitary `X` and a normal tensor `A`, then
`X X̄ = ±1`. -/
theorem mul_map_star_eq_one_or_neg_one_of_twice [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) (X : Matrix.unitaryGroup (Fin D) ℂ) {c : ℂ}
    (h : ∀ i, A i = c • (((X : Matrix (Fin D) (Fin D) ℂ) *
      (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ))ᴴ * A i *
        ((X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)))) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ∨
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1 := by
  let Xb : Matrix.unitaryGroup (Fin D) ℂ := Matrix.UnitaryGroup.map_star X
  let W : Matrix.unitaryGroup (Fin D) ℂ := X * Xb
  have hW : ((W : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := rfl
  obtain ⟨-, u, hu⟩ := gauge_phase_unique_of_isNormal hA (X := 1) (Y := unitaryGL W) (c := c)
    (fun i => by simpa [unitaryGL, hW, Matrix.star_eq_conjTranspose] using h i)
  -- `1 = u W`, so `W = u⁻¹ · 1`.
  have hWs : (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      ((u⁻¹ : Units ℂ) : ℂ) • 1 := by
    have h1 : ((u⁻¹ : Units ℂ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) =
        ((u⁻¹ : Units ℂ) : ℂ) • ((u : ℂ) • (W : Matrix (Fin D) (Fin D) ℂ)) := by
      simpa [unitaryGL] using congrArg (((u⁻¹ : Units ℂ) : ℂ) • ·) hu
    rw [smul_smul, Units.inv_mul, one_smul] at h1
    rw [← hW, h1]
  have := Matrix.scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one X _ hWs
  rcases this with h1 | h1
  · left; rw [hWs, h1, one_smul]
  · right; rw [hWs, h1, neg_one_smul]

/-- Two unitary matrices that differ by a scalar have the same involution index
`X X̄`: the scalar has unit modulus and cancels against its conjugate. -/
theorem mul_map_star_eq_of_eq_smul (X Y : Matrix.unitaryGroup (Fin D) ℂ) [NeZero D] {u : ℂ}
    (h : (X : Matrix (Fin D) (Fin D) ℂ) = u • (Y : Matrix (Fin D) (Fin D) ℂ)) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      (Y : Matrix (Fin D) (Fin D) ℂ) * (Y : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := by
  have hXX := Matrix.mem_unitaryGroup_iff.mp X.2
  have hYY := Matrix.mem_unitaryGroup_iff.mp Y.2
  have hu : u * starRingEnd ℂ u = 1 := by
    rw [h, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Matrix.star_eq_conjTranspose, hYY] at hXX
    have h0 := congrFun (congrFun hXX 0) 0
    simpa [Matrix.one_apply] using h0
  rw [h, Matrix.map_smul', Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  · simp [hu]
  · intro a b; simp

private lemma map_conj_smul_mul_mul (a : ℂ) (M N P : Matrix (Fin D) (Fin D) ℂ) :
    (a • (M * N * P)).map (starRingEnd ℂ) = starRingEnd ℂ a •
      (M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) * P.map (starRingEnd ℂ)) := by
  ext; simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]

private lemma conjTranspose_mul_map_star (M : Matrix (Fin D) (Fin D) ℂ) :
    (M * M.map (starRingEnd ℂ))ᴴ = (Mᴴ).map (starRingEnd ℂ) * Mᴴ := by
  rw [Matrix.conjTranspose_mul]; congr 1

/-- Applying the antiunitary twist `Bⁱ ↦ ∑ⱼ Pᵢⱼ B̄ʲ` twice is the linear twist by `P P̄`. -/
private lemma antiunitaryTwist_twice (A : MPSTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (i : Fin d) :
    ∑ j : Fin d, P i j • (∑ k : Fin d, P j k • (A k).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      ∑ k : Fin d, (P * P.map (starRingEnd ℂ)) i k • A k := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    map_mul, Complex.conj_conj, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The antiunitary twist of a transformed family: if `Bʲ = ζ M Aʲ N`, then
`∑ⱼ Pᵢⱼ B̄ʲ = ζ̄ M̄ (∑ⱼ Pᵢⱼ Āʲ) N̄`. -/
private lemma antiunitaryTwist_smul_mul_mul (A : MPSTensor d D) (P : Matrix (Fin d) (Fin d) ℂ)
    (M N : Matrix (Fin D) (Fin D) ℂ) (ζ : ℂ) (i : Fin d) :
    ∑ j : Fin d, P i j • (ζ • (M * A j * N)).map (starRingEnd ℂ) =
      starRingEnd ℂ ζ • (M.map (starRingEnd ℂ) *
        (∑ j : Fin d, P i j • (A j).map (starRingEnd ℂ)) * N.map (starRingEnd ℂ)) := by
  simp only [map_conj_smul_mul_mul, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]

/-- **Time-reversal index.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1116–1117 and 1120): time reversal acts on an MPS tensor as
`Aⁱ ↦ ∑ⱼ Pᵢⱼ Āʲ`, with `Ā` the entrywise conjugate and `P` its on-site part
(`P = 1` for pure time reversal), and for a normal tensor with
`∑ⱼ Pᵢⱼ Āʲ = e^{iφ} X† Aⁱ X` "this is only possible for `X X̄ = ±1`".  Here
`P P̄ = 1`, so that time reversal squares to the identity on the site, and `X` is
unitary. -/
theorem mul_map_star_eq_one_or_neg_one_of_timeReversal_gauge [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P.map (starRingEnd ℂ) = 1) (X : Matrix.unitaryGroup (Fin D) ℂ) {ζ : ℂ}
    (h : ∀ i, ∑ j : Fin d, P i j • (A j).map (starRingEnd ℂ) =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X)) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ∨
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1 := by
  refine mul_map_star_eq_one_or_neg_one_of_twice hA X (c := starRingEnd ℂ ζ * ζ) fun i => ?_
  have h1 := antiunitaryTwist_twice A P i
  rw [hP] at h1
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h1
  calc A i = ∑ j : Fin d, P i j • (∑ k : Fin d, P j k • (A k).map (starRingEnd ℂ)).map
        (starRingEnd ℂ) := h1.symm
    _ = ∑ j : Fin d, P i j • (ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A j * X)).map
        (starRingEnd ℂ) := Finset.sum_congr rfl fun j _ => by rw [h j]
    _ = starRingEnd ℂ ζ • (((X : Matrix (Fin D) (Fin D) ℂ)ᴴ).map (starRingEnd ℂ) *
        (ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X)) *
          (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ)) := by
        rw [antiunitaryTwist_smul_mul_mul, h i]
    _ = _ := by
        rw [conjTranspose_mul_map_star]
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]

/-- **The time-reversal and reflection indices do not depend on the gauge.**
Two unitary gauges related to the same normal tensor by `ζ X† Aⁱ X = ζ' X'† Aⁱ X'`,
with `ζ ≠ 0`, have the same involution index `X X̄ = X' X̄'`.  Source:
arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` line 1117), where
`±1` is called a topological index. -/
theorem mul_map_star_eq_of_gauges [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsNormal A)
    (X X' : Matrix.unitaryGroup (Fin D) ℂ) {ζ ζ' : ℂ} (hζ : ζ ≠ 0)
    (h : ∀ i, ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X) =
      ζ' • ((X' : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X')) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      (X' : Matrix (Fin D) (Fin D) ℂ) * (X' : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := by
  obtain ⟨-, u, hu⟩ := gauge_phase_unique_of_isNormal hA (X := unitaryGL X)
    (Y := unitaryGL X') (c := ζ⁻¹ * ζ') (fun i => by
      have hi := congrArg (ζ⁻¹ • ·) (h i)
      simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at hi
      simpa [unitaryGL, Matrix.star_eq_conjTranspose] using hi)
  exact mul_map_star_eq_of_eq_smul X X' (u := u) (by simpa [unitaryGL] using hu)

/-- **Reflection index.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1120): reflection acts on an MPS tensor by transposition, and for a normal
tensor with `(Aⁱ)ᵀ = e^{iφ} X† Aⁱ X` the argument of the time-reversal case gives
`X X̄ = ±1`.  Here `X` is unitary. -/
theorem mul_map_star_eq_one_or_neg_one_of_reflection_gauge [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) (X : Matrix.unitaryGroup (Fin D) ℂ) {ζ : ℂ}
    (h : ∀ i, (A i)ᵀ = ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X)) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = 1 ∨
      (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = -1 := by
  refine mul_map_star_eq_one_or_neg_one_of_twice hA X (c := ζ * ζ) fun i => ?_
  have e : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      (ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * M * (X : Matrix (Fin D) (Fin D) ℂ)))ᵀ =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᵀ * Mᵀ * ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)ᵀ) := by
    intro M
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  calc A i = ((A i)ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
    _ = (ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (X : Matrix (Fin D) (Fin D) ℂ)))ᵀ := by
        rw [h i]
    _ = ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᵀ * (A i)ᵀ * ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)ᵀ) := e _
    _ = ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᵀ * (ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X)) *
          ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)ᵀ) := by rw [h i]
    _ = _ := by
      rw [conjTranspose_mul_map_star]
      have h1 : ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ).map (starRingEnd ℂ) =
          (X : Matrix (Fin D) (Fin D) ℂ)ᵀ := by ext; simp
      have h2 : ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ)ᵀ =
          (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := by ext; simp
      rw [h1, h2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]

/-- A normal tensor of positive bond dimension admits no vanishing gauge phase:
`Āⁱ = 0 · X† Aⁱ X` (or `(Aⁱ)ᵀ = 0`) would make every letter zero. -/
private lemma ne_zero_of_map_eq_smul [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsNormal A)
    (f : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ) (hf : ∀ M, f M = 0 → M = 0)
    {X : Matrix (Fin D) (Fin D) ℂ} {ζ : ℂ} (h : ∀ i, f (A i) = ζ • (Xᴴ * A i * X)) : ζ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := exists_apply_ne_zero_of_isNormal hA
  exact hi (hf _ (by simpa using h i))

/-- **The time-reversal index does not depend on the unitary gauge.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1117): "`±1` is a topological index". -/
theorem mul_map_star_eq_of_timeReversal_gauges [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P.map (starRingEnd ℂ) = 1) (X X' : Matrix.unitaryGroup (Fin D) ℂ) {ζ ζ' : ℂ}
    (h : ∀ i, ∑ j : Fin d, P i j • (A j).map (starRingEnd ℂ) =
      ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X))
    (h' : ∀ i, ∑ j : Fin d, P i j • (A j).map (starRingEnd ℂ) =
      ζ' • ((X' : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X')) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      (X' : Matrix (Fin D) (Fin D) ℂ) * (X' : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := by
  refine mul_map_star_eq_of_gauges hA X X' ?_ (fun i => (h i).symm.trans (h' i))
  rintro rfl
  obtain ⟨i, hi⟩ := exists_apply_ne_zero_of_isNormal hA
  apply hi
  have h1 := antiunitaryTwist_twice A P i
  rw [hP] at h1
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h1
  rw [← h1]
  simp [h]

/-- **The reflection index does not depend on the unitary gauge.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1117–1120). -/
theorem mul_map_star_eq_of_reflection_gauges [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) (X X' : Matrix.unitaryGroup (Fin D) ℂ) {ζ ζ' : ℂ}
    (h : ∀ i, (A i)ᵀ = ζ • ((X : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X))
    (h' : ∀ i, (A i)ᵀ = ζ' • ((X' : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * X')) :
    (X : Matrix (Fin D) (Fin D) ℂ) * (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      (X' : Matrix (Fin D) (Fin D) ℂ) * (X' : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) :=
  mul_map_star_eq_of_gauges hA X X'
    (ne_zero_of_map_eq_smul hA (fun M => Mᵀ) (fun M hM => by
      rw [← Matrix.transpose_transpose M, hM, Matrix.transpose_zero]) h)
    (fun i => (h i).symm.trans (h' i))

/-! ### The Kramers obstruction -/

/-- **Kramers obstruction for a physical time reversal squaring to `-1`.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1117) and §III.C, paragraph "Kramers theorem and Lieb-Schultz-Mattis"
(line 1218): if time reversal acts as `Aⁱ ↦ ∑ⱼ Pᵢⱼ Āʲ` with `P P̄ = -1`, applying it
twice gives `-Aⁱ = |ζ|² (X X̄)⁻¹ Aⁱ (X X̄)`, which eq. `eq:XAX=B` rules out.  So no
normal tensor of positive bond dimension admits a gauge `X` and a scalar `ζ` with
`∑ⱼ Pᵢⱼ Āʲ = ζ X⁻¹ Aⁱ X`. -/
theorem not_timeReversal_gauge_of_mul_map_star_eq_neg_one [NeZero D] {A : MPSTensor d D}
    (hA : Kraus.IsNormal A) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P * P.map (starRingEnd ℂ) = -1) (X : GL (Fin D) ℂ) (ζ : ℂ)
    (h : ∀ i, ∑ j : Fin d, P i j • (A j).map (starRingEnd ℂ) =
      ζ • (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X)) : False := by
  let Xb : GL (Fin D) ℂ := Matrix.GeneralLinearGroup.map (starRingEnd ℂ) X
  have hXb : (Xb : Matrix (Fin D) (Fin D) ℂ) = (X : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) :=
    rfl
  have hXbinv : ((Xb⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) := by
    simp only [Xb, ← Matrix.GeneralLinearGroup.map_inv]; rfl
  have htwice : ∀ i, A i = (-(starRingEnd ℂ ζ * ζ)) •
      ((((X * Xb)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (X * Xb : GL (Fin D) ℂ)) := by
    intro i
    have h1 := antiunitaryTwist_twice A P i
    rw [hP] at h1
    simp only [Matrix.neg_apply, Matrix.one_apply, neg_smul, ite_smul, one_smul, zero_smul,
      Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
    simp_rw [h] at h1
    rw [antiunitaryTwist_smul_mul_mul, h i, ← hXbinv, ← hXb] at h1
    calc A i = -(-A i) := (neg_neg _).symm
      _ = -(starRingEnd ℂ ζ • (((Xb⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
            (ζ • (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X)) * Xb)) := by
          rw [h1]
      _ = _ := by
          simp only [mul_inv_rev, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
            Matrix.mul_assoc, neg_smul]
  obtain ⟨hc, -⟩ := gauge_phase_unique_of_isNormal hA (X := 1) (Y := X * Xb)
    (c := -(starRingEnd ℂ ζ * ζ)) (fun i => by simpa using htwice i)
  have hre := congrArg Complex.re hc
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re,
    Complex.one_re] at hre
  nlinarith [sq_nonneg ‖ζ‖]

/-- The Pauli matrix `σ_y = !![0, -i; i, 0]`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- `σ_y σ̄_y = -1`: the Wigner time reversal of a spin `1/2` squares to `-1`. -/
theorem pauliY_mul_map_star : pauliY * pauliY.map (starRingEnd ℂ) = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pauliY, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Kramers obstruction for spin `1/2`.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1117): with time reversal `Aⁱ ↦ ∑ⱼ (σ_y)ᵢⱼ Āʲ`, as in Wigner's treatment of
spin `1/2`, no normal tensor of positive bond dimension is time-reversal symmetric:
there is no gauge `X` and scalar `ζ` with `∑ⱼ (σ_y)ᵢⱼ Āʲ = ζ X⁻¹ Aⁱ X`. -/
theorem not_wignerTimeReversal_gauge [NeZero D] {A : MPSTensor 2 D} (hA : Kraus.IsNormal A)
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (h : ∀ i, ∑ j : Fin 2, pauliY i j • (A j).map (starRingEnd ℂ) =
      ζ • (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X)) : False :=
  not_timeReversal_gauge_of_mul_map_star_eq_neg_one hA pauliY_mul_map_star X ζ h

/-- **No injective spin-`1/2` MPS is invariant under the Wigner time reversal.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1117): the ground state of a system with this symmetry cannot be an injective
MPS.  Invariance is equality of the matrix product vectors of `A` and of its
time-reversed tensor `∑ⱼ (σ_y)ᵢⱼ Āʲ`; the fundamental theorem for injective
tensors turns it into a gauge relation. -/
theorem not_sameMPV_wignerTimeReversal_of_isInjective [NeZero D] {A : MPSTensor 2 D}
    (hA : Kraus.IsInjective A) :
    ¬ SameMPV A (fun i => ∑ j : Fin 2, pauliY i j • (A j).map (starRingEnd ℂ)) := by
  intro hsame
  obtain ⟨X, hX⟩ := (sameMPV_iff_gaugeEquiv_of_injective hA).1 hsame
  exact not_wignerTimeReversal_gauge hA.isNormal X⁻¹ 1 (fun i => by simpa using hX i)

end MPSTensor

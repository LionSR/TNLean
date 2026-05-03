/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Stinespring
import TNLean.Channel.Semigroup.CPClosure
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# POVMs, instruments, and the Naimark dilation (Wolf Chapter 2, Theorem 2.6 / Neumark)

This file defines positive operator-valued measures (POVMs) on `M_D(ℂ)`,
quantum instruments, and proves the **Naimark extension theorem**: every
finite-outcome POVM can be realised as a projective measurement on a
larger (dilated) Hilbert space via an isometry.

## Main definitions

* `POVM D n` — a family of `n` positive-semidefinite `D × D` operators
  summing to the identity (resolution of identity).
* `POVM.naimarkKraus` — a Kraus-type square root `M i` with `E i = (M i)ᴴ * M i`,
  obtained from `CStarAlgebra.nonneg_iff_eq_star_mul_self`.
* `POVM.naimarkIsometry` — the isometry `V : ℂ^D → ℂ^D ⊗ ℂ^n` built from
  the Kraus square roots via the Stinespring pattern.
* `POVM.naimarkProjection i` — the orthogonal projector
  `P_i = 1_D ⊗ |i⟩⟨i|` on the dilated space.
* `Instrument D n` — a family of CP maps whose sum is trace-preserving.

## Main results

* `POVM.naimarkIsometry_isometry` — `Vᴴ * V = 𝟙`.
* `POVM.naimarkProjection_sum_eq_one` — `∑ᵢ P_i = 𝟙` on the dilation.
* `POVM.naimarkProjection_mul_self` — `P_i * P_i = P_i`.
* `POVM.naimarkProjection_hermitian` — `P_iᴴ = P_i`.
* `POVM.naimarkProjection_orthogonal` — `P_i * P_j = 0` for `i ≠ j`.
* `POVM.naimark_recovers_povm` — `Vᴴ * P_i * V = E_i` (main Naimark identity).
* `POVM.exists_naimark_dilation` — the existential form of Wolf Theorem 2.6.
* `POVM.ofPSDResolutionOfIdentity` — converse direction: every isometry together
  with a PSD resolution of identity on the dilated space yields a POVM via
  `E_i := Vᴴ P_i V`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.6
  (Neumark's theorem)][Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder ComplexOrder TNMatrixCFC
open Matrix Finset BigOperators

variable {D n : ℕ}

/-! ### Positive operator-valued measures -/

/-- A **POVM** with `n` outcomes on `M_D(ℂ)`:
a family of positive-semidefinite operators summing to the identity. -/
structure POVM (D n : ℕ) where
  /-- The `n` positive-semidefinite effect operators. -/
  ops : Fin n → Matrix (Fin D) (Fin D) ℂ
  /-- Each effect operator is positive semidefinite. -/
  posSemidef : ∀ i, (ops i).PosSemidef
  /-- Resolution of the identity: the effects sum to `𝟙`. -/
  sum_eq_one : ∑ i, ops i = (1 : Matrix (Fin D) (Fin D) ℂ)

namespace POVM

variable (E : POVM D n)

/-- The Kraus-type square root of each POVM effect: an operator `M i`
satisfying `E i = (M i)ᴴ * M i`, chosen by `CStarAlgebra.nonneg_iff_eq_star_mul_self`. -/
noncomputable def naimarkKraus (i : Fin n) : Matrix (Fin D) (Fin D) ℂ :=
  Classical.choose
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (E.posSemidef i).nonneg)

/-- Defining property of `naimarkKraus`: `E i = (M i)ᴴ * M i`. -/
theorem naimarkKraus_spec (i : Fin n) :
    E.ops i = (E.naimarkKraus i)ᴴ * E.naimarkKraus i := by
  have h := Classical.choose_spec
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (E.posSemidef i).nonneg)
  simpa [naimarkKraus, Matrix.star_eq_conjTranspose] using h

/-- `∑ᵢ (M i)ᴴ * M i = 𝟙` — the normalization condition on the Kraus square roots,
equivalent to the resolution of the identity for the POVM. -/
theorem sum_naimarkKraus_conjTranspose_mul :
    ∑ i, (E.naimarkKraus i)ᴴ * E.naimarkKraus i =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
  have : ∑ i, (E.naimarkKraus i)ᴴ * E.naimarkKraus i = ∑ i, E.ops i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (E.naimarkKraus_spec i).symm
  rw [this, E.sum_eq_one]

/-! ### Naimark isometry -/

/-- The **Naimark isometry** `V : ℂ^D → ℂ^D ⊗ ℂ^n` attached to the POVM,
built from the Kraus square roots via the Stinespring pattern:
`V (k, i) j = (M i)_{k, j}`. -/
noncomputable def naimarkIsometry :
    Matrix (Fin D × Fin n) (Fin D) ℂ :=
  stinespringV E.naimarkKraus

/-- `Vᴴ * V = 𝟙`: the Naimark isometry is indeed an isometry. -/
theorem naimarkIsometry_isometry :
    (E.naimarkIsometry)ᴴ * E.naimarkIsometry =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [naimarkIsometry, stinespringV_conjTranspose_mul]
  exact E.sum_naimarkKraus_conjTranspose_mul

/-! ### Naimark projective measurement -/

/-- The `i`-th **Naimark projector** on the dilated space
`ℂ^D ⊗ ℂ^n`: `P_i = 𝟙_D ⊗ |i⟩⟨i|`, defined entrywise by
`P_i ((a, b), (c, d)) = δ_{a, c} · δ_{b, i} · δ_{d, i}`. -/
noncomputable def naimarkProjection (i : Fin n) :
    Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ :=
  fun (p : Fin D × Fin n) (q : Fin D × Fin n) =>
    if p.1 = q.1 ∧ p.2 = i ∧ q.2 = i then 1 else 0

@[simp]
theorem naimarkProjection_apply (i : Fin n)
    (a c : Fin D) (b d : Fin n) :
    naimarkProjection (D := D) i (a, b) (c, d) =
      if a = c ∧ b = i ∧ d = i then 1 else 0 := rfl

/-- Naimark projectors are Hermitian. -/
theorem naimarkProjection_hermitian (i : Fin n) :
    (naimarkProjection (D := D) i)ᴴ = naimarkProjection i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.conjTranspose_apply, naimarkProjection_apply]
  by_cases hca : c = a
  · by_cases hdi : d = i
    · by_cases hbi : b = i
      · subst hca hdi hbi; simp
      · simp [hdi, hbi]
    · by_cases hbi : b = i
      · simp [hdi, hbi]
      · simp [hdi, hbi]
  · have hac : a ≠ c := fun h => hca h.symm
    simp [hca, hac]

/-- Naimark projectors are idempotent: `P_i * P_i = P_i`. -/
theorem naimarkProjection_mul_self (i : Fin n) :
    naimarkProjection (D := D) i * naimarkProjection i =
      naimarkProjection i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, naimarkProjection_apply, Fintype.sum_prod_type]
  by_cases hbi : b = i
  · by_cases hdi : d = i
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single i]
        · by_cases hac : a = c
          · subst hac; simp [hbi, hdi]
          · simp [hac, hbi, hdi]
        · intro b' _ hb'i
          simp [hb'i]
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro a' _ ha'a
        refine Finset.sum_eq_zero ?_
        intro b' _
        simp [Ne.symm ha'a]
      · intro h; exact absurd (Finset.mem_univ a) h
    · have hfalse : ¬(a = c ∧ b = i ∧ d = i) := fun ⟨_, _, h⟩ => hdi h
      rw [if_neg hfalse]
      refine Finset.sum_eq_zero fun a' _ => ?_
      refine Finset.sum_eq_zero fun b' _ => ?_
      by_cases hb'i : b' = i
      · simp [hb'i, hdi]
      · simp [hb'i]
  · have hfalse : ¬(a = c ∧ b = i ∧ d = i) := fun ⟨_, h, _⟩ => hbi h
    rw [if_neg hfalse]
    refine Finset.sum_eq_zero fun a' _ => ?_
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [hbi]

/-- Distinct Naimark projectors are orthogonal: `P_i * P_j = 0` if `i ≠ j`. -/
theorem naimarkProjection_orthogonal (i j : Fin n) (hij : i ≠ j) :
    naimarkProjection (D := D) i * naimarkProjection j = 0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, naimarkProjection_apply, Fintype.sum_prod_type,
    Matrix.zero_apply]
  refine Finset.sum_eq_zero ?_
  intro a' _
  refine Finset.sum_eq_zero ?_
  intro b' _
  -- Either the first factor vanishes (b' ≠ i) or the second vanishes (b' ≠ j);
  -- these two conditions can never both fail because i ≠ j.
  by_cases hb'i : b' = i
  · have hb'j : b' ≠ j := hb'i ▸ hij
    simp [hb'j]
  · simp [hb'i]

/-- The Naimark projectors sum to the identity: `∑ᵢ P_i = 𝟙`. -/
theorem naimarkProjection_sum_eq_one :
    ∑ i : Fin n, naimarkProjection (D := D) i =
      (1 : Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [Matrix.sum_apply]
  simp only [naimarkProjection_apply]
  by_cases hbd : b = d
  · subst hbd
    by_cases hac : a = c
    · subst hac
      rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb
        simp [Ne.symm hjb]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · rw [Matrix.one_apply_ne (by simp [hac])]
      refine Finset.sum_eq_zero ?_
      intro j _
      simp [hac]
  · rw [Matrix.one_apply_ne (by simp [hbd])]
    refine Finset.sum_eq_zero ?_
    intro j _
    by_cases hbj : b = j
    · by_cases hdj : d = j
      · exact absurd (hbj.trans hdj.symm) hbd
      · simp [hbj, hdj]
    · simp [hbj]

/-! ### Naimark theorem: `Vᴴ * P_i * V = E_i` -/

/-- **Wolf Theorem 2.6 (Naimark / Neumark)**: every POVM `{E_i}` on `ℂ^D` arises
as `E_i = Vᴴ * P_i * V` for an isometry `V : ℂ^D → ℂ^D ⊗ ℂ^n` and a projective
measurement `{P_i}` on the dilated space. -/
theorem naimark_recovers_povm (i : Fin n) :
    (E.naimarkIsometry)ᴴ * naimarkProjection (D := D) i *
        E.naimarkIsometry = E.ops i := by
  rw [E.naimarkKraus_spec i]
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    naimarkIsometry, stinespringV_apply,
    naimarkProjection_apply, Fintype.sum_prod_type]
  -- LHS: ∑ q1, ∑ q2, (∑ p1, ∑ p2, star(K p2 p1 k) *
  --                                  [p1=q1 ∧ p2=i ∧ q2=i]) * K q2 q1 l
  -- RHS: ∑ a, star(K i a k) * K i a l
  refine Finset.sum_congr rfl ?_
  intro q1 _
  rw [Finset.sum_eq_single i]
  · -- q2 = i: peel inner p1 = q1, then p2 = i.
    rw [Finset.sum_eq_single q1]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro p2 _ hp2; simp [hp2]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro p1 _ hp1
      refine Finset.sum_eq_zero fun p2 _ => ?_
      simp [hp1]
    · intro h; exact absurd (Finset.mem_univ q1) h
  · -- q2 ≠ i: the inner sum is 0, so the product with `K q2 q1 l` is 0.
    intro q2 _ hq2
    have hinner : (∑ p1 : Fin D, ∑ p2 : Fin n,
        star (E.naimarkKraus p2 p1 k) *
          (if p1 = q1 ∧ p2 = i ∧ q2 = i then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun p1 _ => ?_
      refine Finset.sum_eq_zero fun p2 _ => ?_
      rw [if_neg (fun h => hq2 h.2.2)]
      ring
    rw [hinner, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Existential form of Wolf Theorem 2.6**: Naimark dilation exists for every POVM.
The witnesses `(P i)` form a full projective measurement on the dilation: each is
self-adjoint and idempotent, pairwise orthogonal, and they sum to the identity. -/
theorem exists_naimark_dilation :
    ∃ (r : ℕ) (V : Matrix (Fin D × Fin r) (Fin D) ℂ)
      (P : Fin n → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Vᴴ * V = 1 ∧
      (∀ i, P i * P i = P i) ∧
      (∀ i, (P i)ᴴ = P i) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i = 1) ∧
      (∀ i, Vᴴ * P i * V = E.ops i) :=
  ⟨n, E.naimarkIsometry, naimarkProjection, E.naimarkIsometry_isometry,
    naimarkProjection_mul_self, naimarkProjection_hermitian,
    naimarkProjection_orthogonal,
    naimarkProjection_sum_eq_one, E.naimark_recovers_povm⟩

end POVM

/-! ### Converse: PSD resolutions of identity on a dilation give POVMs -/

namespace POVM

/-- **Converse of Naimark (PSD resolution of identity)**: given an isometry
`V : ℂ^D → ℂ^d'` and a family of positive semidefinite operators `{P_i}` on the
dilated space summing to the identity, the pulled-back operators
`E_i := Vᴴ * P_i * V` form a POVM. A projective measurement on the dilation is
a special case (see `POVM.naimark_recovers_povm` for the canonical Naimark
instance); the statement here requires only the PSD/sum-to-one structure that
the proof actually uses. -/
noncomputable def ofPSDResolutionOfIdentity {D n d' : ℕ}
    (V : Matrix (Fin d') (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (P : Fin n → Matrix (Fin d') (Fin d') ℂ)
    (hPsum : ∑ i, P i = 1)
    (hPpos : ∀ i, (P i).PosSemidef) :
    POVM D n where
  ops i := Vᴴ * P i * V
  posSemidef i := by
    -- Vᴴ * (P i) * V = Vᴴ * (P i) * (Vᴴᴴ); apply PSD-sandwich with B := Vᴴ.
    have := (hPpos i).mul_mul_conjTranspose_same (B := Vᴴ)
    simpa [Matrix.mul_assoc] using this
  sum_eq_one := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hPsum, Matrix.mul_one]
    exact hV

end POVM

/-! ### Quantum instruments -/

/-- A **quantum instrument** with `n` outcomes: a family of completely positive
maps whose sum is a quantum channel (trace-preserving). The `i`-th component
implements the (unnormalised) post-measurement update for outcome `i`. -/
structure Instrument (D n : ℕ) where
  /-- The `n` completely-positive component maps. -/
  maps : Fin n → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- Each component map is completely positive. -/
  cp : ∀ i, IsCPMap (maps i)
  /-- The sum of the component maps is trace-preserving. -/
  tp : IsTracePreservingMap (∑ i, maps i)

namespace Instrument

variable (I : Instrument D n)

/-- The overall quantum channel `∑ᵢ Φᵢ` obtained by averaging over outcomes. -/
noncomputable def total :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, I.maps i

/-- The average map of an instrument is a quantum channel (CPTP). -/
theorem total_isChannel : IsChannel I.total := by
  refine ⟨?_, I.tp⟩
  exact Finset.isCPMap_sum (n := Fin D) Finset.univ I.maps (fun i _ => I.cp i)

/-- The (unnormalised) **post-measurement state update** after outcome `i`:
`ρ ↦ Φ_i(ρ)`. The physical normalised state is `Φ_i(ρ) / tr(Φ_i(ρ))`
(see `Instrument.probability` and `Instrument.posteriorState`). -/
noncomputable def update (i : Fin n) (rho : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  I.maps i rho

/-- The probability of observing outcome `i` in state `ρ`: `tr(Φ_i(ρ))`. -/
noncomputable def probability (i : Fin n) (rho : Matrix (Fin D) (Fin D) ℂ) :
    ℂ :=
  Matrix.trace (I.maps i rho)

/-- **Conservation of probability**: for any state `ρ`, the outcome probabilities
sum to `tr(ρ)`. -/
theorem sum_probability (rho : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i, I.probability i rho = Matrix.trace rho := by
  simp only [probability, ← Matrix.trace_sum]
  have : (∑ i, I.maps i) rho = ∑ i, I.maps i rho := by
    simp [Finset.sum_apply]
  rw [← this, I.tp rho]

/-- Outcome probabilities are non-negative real numbers (in `ℂ` with
`ComplexOrder`): for any PSD state `ρ`, `0 ≤ I.probability i rho`. -/
theorem probability_nonneg (i : Fin n) {rho : Matrix (Fin D) (Fin D) ℂ}
    (hrho : rho.PosSemidef) : 0 ≤ I.probability i rho :=
  ((I.cp i).isPositiveMap rho hrho).trace_nonneg

/-- The physical **post-measurement state** after outcome `i`: the component
update normalised by the outcome probability. Only meaningful when the
probability is nonzero. -/
noncomputable def posteriorState (i : Fin n)
    (rho : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  (I.probability i rho)⁻¹ • I.maps i rho

end Instrument

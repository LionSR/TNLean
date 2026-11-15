/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.QuadraticCanonicalOBCWindow
import TNLean.MPS.CanonicalForm.QuadraticSolutionRephasing
import TNLean.Wielandt.Inequality.Bounds

/-!
# The corrected quadratic reconstruction converse

Theorem 8 of PGVWC07 forms the quadratic system (S) over the window of `D⁴`
open-boundary canonical matrices after the onset `L₀` of condition C1, and
asserts that every solution is related to the canonical tensor by a unitary.
The corrected converse proved here holds for every solution of the system
over the canonical window: the solution tensor `B` and the unital block
`λ⁻¹ A` of the canonical tensor satisfy `λ⁻¹ A_i = ξ U B_i U†` for a unitary
`U` and a unit-modulus scalar `ξ`. The solution is not assumed canonical,
injective, or to represent the state.

## The endpoint argument

In the physical cut bases the window matrices are `P_j⁻¹ (A_i ⊗ 1) P_{j+1}`
with invertible `P_0, …, P_m`, `m = D⁴`. For a solution with gauges `Y_j`,
`Z_j` put `G_j = Y_j P_j⁻¹` and `K_j = P_{j+1} Z_j`; the system becomes
`B_i ⊗ 1 = G_j (A_i ⊗ 1) K_j` with `G_{j+1} K_j = 1` at the internal cuts.
Only the endpoint gauges `G_0` and `K_{m-1}` are unconstrained. If the words
of a length `1 ≤ ℓ ≤ m - 2` in `A` span the matrix algebra, then
`Σ_w c_w A_w = 1` gives `X ⊗ 1 = G_1 K_ℓ = G_0 K_{ℓ-1}` for
`X = Σ_w c_w B_w`, so `G_0` is invertible. The matrices `G_0⁻¹, K_0, …,
K_{m-1}` are nonzero and form a complete chain over the `D⁴ + 1` cuts, and
the chain-combination and slice-extraction lemmas give a nonzero intertwiner.
The unitarity argument for unital tensors under condition C1 finishes the
proof. For `D ≥ 2` a spanning length at most `D⁴ - D²` is supplied by the
quantum Wielandt inequality; for `D = 1` the endpoint gauge is a nonzero
scalar.

The weight `λ` of the single canonical block (Theorem 4 of the source) is a
datum of the canonical tensor that the system does not see: the
normalization equation fixes the scale of every solution tensor. When the
solution tensor represents the same nonzero state, the weight is one and the
phase is an `N`th root of unity; that case, for an arbitrary window, is the
same-state converse at the end of this file.

**Scope restriction (same-state solutions):** the theorems whose names end in
`_of_same_state` take an arbitrary window and assume that the solution tensor
represents the prescribed state. Over the canonical window this hypothesis is
unnecessary by `exists_unitary_phase`. See
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex` and
`docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex`.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 8 and proof, lines 1154--1176,
with the complete-cut uniqueness argument of Theorem 7, lines 1002--1108.

## Main declarations

* `MPSTensor.exists_isNBlkInjective_le_of_canonical` - a spanning length at
  most `D⁴ - 2` from the quantum Wielandt inequality.
* `MPSTensor.isUnit_gauge_zero_of_isNBlkInjective`,
  `MPSTensor.exists_intertwiner_of_gauged` - the endpoint invertibility and
  the complete chain of intertwiners for the gauged system.
* `MPSTensor.exists_intertwiner_of_physicalCutWindow` - a nonzero intertwiner
  for every solution over a physical cut window.
* `MPSTensor.QuadraticReconstructionSolution.exists_unitary_phase` - the
  corrected converse of Theorem 8 for every solution over the canonical window.
* `MPSTensor.QuadraticReconstructionSolution.exists_rephased_solution_exact_gauge`
  - the rephased solution, its state, and the root-of-unity criterion.
-/

open Matrix MPSPreparation OBCChainTensor
open scoped BigOperators ComplexOrder Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-! ## A spanning length within the window -/

/-- A family whose letters span a space of dimension at most one has word
spans of dimension at most one at every length: every word is a multiple of a
power of one matrix. This is the reason a primitive family on a bond space of
dimension at least two has Kraus rank at least two. -/
theorem finrank_wordSpan_le_one_of_krausRank_le_one (K : MPSTensor d D)
    (hK : krausRank K ≤ 1) (n : ℕ) :
    Module.finrank ℂ (Kraus.wordSpan K n) ≤ 1 := by
  have hprin : ∀ S : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ),
      Module.finrank ℂ S ≤ 1 → ∃ x, S = Submodule.span ℂ {x} := fun S hS ↦
    ((Submodule.finrank_le_one_iff_isPrincipal S).mp hS).principal
  have hsing : ∀ x : Matrix (Fin D) (Fin D) ℂ,
      Module.finrank ℂ (Submodule.span ℂ {x}) ≤ 1 := fun x ↦
    (Submodule.finrank_le_one_iff_isPrincipal _).mpr ⟨⟨x, rfl⟩⟩
  obtain ⟨y, hy⟩ := hprin (Kraus.wordSpan K 1) hK
  induction n with
  | zero =>
    rw [Kraus.wordSpan_zero]
    exact hsing 1
  | succ n ih =>
    obtain ⟨x, hx⟩ := hprin _ ih
    rw [Kraus.wordSpan_succ, hx, hy, Submodule.span_mul_span, Set.singleton_mul_singleton]
    exact hsing _

/-- **A spanning length inside the reconstruction window.** For a canonical
tensor satisfying condition C1 on a bond space of dimension `D ≥ 2`, the words
of some length `1 ≤ ℓ ≤ D⁴ - 2` span the full matrix algebra. The unital block
`λ⁻¹ A` is a unital family, its adjoint family is trace preserving and normal,
its letters span a space of dimension `k ≥ 2`, and the quantum Wielandt
inequality bounds the least spanning length by
`(D² - k + 1) D² ≤ D⁴ - D²`.
Source: PGVWC07, condition C1, MPSarchive.tex lines 907--908; Wolf,
Theorem 6.9; arXiv:0909.5347, Theorem 1. -/
theorem exists_isNBlkInjective_le_of_canonical [NeZero D] {A : MPSTensor d D}
    (hA : IsPGVWC07CanonicalForm A) {L : ℕ} (hC1 : Kraus.IsNBlkInjective A L)
    (hD : 2 ≤ D) :
    ∃ ℓ, 0 < ℓ ∧ ℓ + 2 ≤ D ^ 4 ∧ Kraus.IsNBlkInjective A ℓ := by
  classical
  obtain ⟨Cd⟩ := hA
  obtain ⟨lam, hlam, -, hsum⟩ := Cd.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  let K : MPSTensor d D := fun i ↦ ((lam : ℂ)⁻¹ • A i)ᴴ
  have hNorm : ∑ i, (K i)ᴴ * K i = 1 := by
    simpa only [K, Matrix.conjTranspose_conjTranspose] using
      sum_inv_smul_mul_conjTranspose_eq_one hlam hsum
  have hKinj (n : ℕ) : Kraus.IsNBlkInjective K n ↔ Kraus.IsNBlkInjective A n :=
    (Kraus.isNBlkInjective_conjTranspose_iff (fun i ↦ (lam : ℂ)⁻¹ • A i) n).trans
      (isNBlkInjective_smul_iff (inv_ne_zero hlam0) A n)
  have hL : Kraus.IsNBlkInjective K (L + 1) :=
    (hKinj _).mpr (isNBlkInjective_of_le_of_canonical ⟨Cd⟩ hC1 (Nat.le_succ L))
  have hnormal : Kraus.IsNormal K := ⟨L + 1, Nat.succ_pos L, hL⟩
  have hq := iIndex_le_general_of_isPrimitivePaper K hNorm (isPrimitivePaper_of_isNormal K hnormal)
  have hmem : 0 < iIndex K ∧ Kraus.wordSpan K (iIndex K) = ⊤ :=
    Nat.sInf_mem (s := {n : ℕ | 0 < n ∧ Kraus.wordSpan K n = ⊤}) ⟨L + 1, Nat.succ_pos L, hL⟩
  have hrank : 2 ≤ krausRank K := by
    by_contra hlt
    have h1 := finrank_wordSpan_le_one_of_krausRank_le_one K (by omega) (iIndex K)
    rw [hmem.2, finrank_top, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self,
      mul_one] at h1
    nlinarith
  refine ⟨iIndex K, hmem.1, ?_, (hKinj _).mp hmem.2⟩
  have hD2 : 4 ≤ D ^ 2 := by nlinarith
  have hstep : (D ^ 2 - krausRank K + 1) * D ^ 2 ≤ (D ^ 2 - 1) * D ^ 2 :=
    Nat.mul_le_mul_right _ (by omega)
  have hfin : (D ^ 2 - 1) * D ^ 2 + 2 ≤ D ^ 4 := by
    obtain ⟨t, ht⟩ : ∃ t, D ^ 2 = t + 4 := ⟨D ^ 2 - 4, by omega⟩
    have h4 : D ^ 4 = D ^ 2 * D ^ 2 := by ring
    have h3 : t + 4 - 1 = t + 3 := by omega
    rw [h4, ht, h3]
    nlinarith
  omega

/-! ## Endpoint invertibility for the gauged system -/

private theorem mul_kronecker_one (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (X * Y) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * (Y ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

private theorem sum_kronecker_one {ι : Type*} (s : Finset ι)
    (X : ι → Matrix (Fin D) (Fin D) ℂ) :
    (∑ σ ∈ s, X σ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      ∑ σ ∈ s, X σ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_kronecker, ih]

/-- **Words in the gauged system telescope.** If `B_i ⊗ 1 = G_j (A_i ⊗ 1) K_j`
at the sites `j < m` and `G_{j+1} K_j = 1` at the internal cuts, then a word
`i w` placed at the sites `p, …, p + |w|` inside the window satisfies
`B_{iw} ⊗ 1 = G_p (A_{iw} ⊗ 1) K_{p+|w|}`.
Source: the endpoint argument recorded in
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`, for the system of
PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem evalWord_cons_kronecker_eq_of_gauged {a b : MPSTensor d D} {m : ℕ}
    {G K : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hsys : ∀ j < m, ∀ i, b i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      G j * (a i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * K j)
    (hinv : ∀ j, j + 1 < m → G (j + 1) * K j = 1)
    (w : List (Fin d)) (i : Fin d) (p : ℕ) (hp : p + w.length < m) :
    Kraus.evalWord b (i :: w) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      G p * (Kraus.evalWord a (i :: w) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
        K (p + w.length) := by
  induction w generalizing i p with
  | nil => simpa using hsys p (by simpa using hp) i
  | cons i' w ih =>
    have hlen : p + (i' :: w).length = p + 1 + w.length := by
      simp only [List.length_cons]
      omega
    rw [hlen] at hp ⊢
    have hKG : K p * G (p + 1) = 1 := mul_eq_one_comm.mp (hinv p (by omega))
    rw [Kraus.evalWord_cons, Kraus.evalWord_cons a, mul_kronecker_one, mul_kronecker_one,
      hsys p (by omega) i, ih i' (p + 1) hp]
    calc G p * (a i ⊗ₖ 1) * K p * (G (p + 1) *
          (Kraus.evalWord a (i' :: w) ⊗ₖ 1) * K (p + 1 + w.length))
        = G p * (a i ⊗ₖ 1) * (K p * G (p + 1)) *
            (Kraus.evalWord a (i' :: w) ⊗ₖ 1) * K (p + 1 + w.length) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hKG, Matrix.mul_one]
          simp only [Matrix.mul_assoc]

/-- **Endpoint invertibility.** In the gauged system
`B_i ⊗ 1 = G_j (A_i ⊗ 1) K_j` (`j < m`) with `G_{j+1} K_j = 1` at the internal
cuts, suppose that the words of some length `1 ≤ ℓ ≤ m - 2` in `A` span the
matrix algebra. Writing `Σ_w c_w A_w = 1` and `X = Σ_w c_w B_w`, placing the
words at the sites `1, …, ℓ` and `0, …, ℓ - 1` gives
`X ⊗ 1 = G_1 K_ℓ = G_0 K_{ℓ-1}`. The first product is invertible, so the
endpoint gauge `G_0` is invertible.
Source: the endpoint argument recorded in
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`, for the system of
PGVWC07, MPSarchive.tex lines 1139--1152. -/
theorem isUnit_gauge_zero_of_isNBlkInjective {a b : MPSTensor d D} {m ℓ : ℕ}
    {G K : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hsys : ∀ j < m, ∀ i, b i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      G j * (a i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * K j)
    (hinv : ∀ j, j + 1 < m → G (j + 1) * K j = 1)
    (hℓ : 0 < ℓ) (hℓm : ℓ + 2 ≤ m) (hspan : Kraus.IsNBlkInjective a ℓ) :
    IsUnit (G 0) := by
  classical
  have h1 : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ Submodule.span ℂ
      (Set.range fun σ : Fin ℓ → Fin d ↦ Kraus.evalWord a (List.ofFn σ)) := by
    rw [hspan.span_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h1
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  let X : Matrix (Fin D) (Fin D) ℂ := ∑ σ, c σ • Kraus.evalWord b (List.ofFn σ)
  have hX : ∀ p, p + ℓ' < m → X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) = G p * K (p + ℓ') := by
    intro p hp
    have hterm : ∀ σ : Fin (ℓ' + 1) → Fin d,
        Kraus.evalWord b (List.ofFn σ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
          G p * (Kraus.evalWord a (List.ofFn σ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
            K (p + ℓ') := by
      intro σ
      rw [List.ofFn_succ]
      simpa only [List.length_ofFn] using evalWord_cons_kronecker_eq_of_gauged hsys hinv
        (List.ofFn fun k ↦ σ k.succ) (σ 0) p (by simpa only [List.length_ofFn] using hp)
    calc X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)
        = ∑ σ, G p * ((c σ • Kraus.evalWord a (List.ofFn σ)) ⊗ₖ
            (1 : Matrix (Fin D) (Fin D) ℂ)) * K (p + ℓ') := by
          rw [sum_kronecker_one]
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          rw [Matrix.smul_kronecker, hterm σ, Matrix.smul_kronecker, Matrix.mul_smul,
            Matrix.smul_mul]
      _ = G p * K (p + ℓ') := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, ← sum_kronecker_one, hc,
            Matrix.one_kronecker_one, Matrix.mul_one]
  have hG1 : IsUnit (G 1) := IsUnit.of_mul_eq_one _ (hinv 0 (by omega))
  have hK : IsUnit (K (1 + ℓ')) := IsUnit.of_mul_eq_one_right _ (hinv (1 + ℓ') (by omega))
  have hunit : IsUnit (G 0 * K (0 + ℓ') * 1) := by
    rw [Matrix.mul_one, ← hX 0 (by omega), hX 1 (by omega)]
    exact hG1.mul hK
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hunit)

/-- **The complete chain of intertwiners for the gauged system.** In the
gauged system `B_i ⊗ 1 = G_j (A_i ⊗ 1) K_j` over the `D⁴` window sites, with
`G_{j+1} K_j = 1` at the internal cuts, an invertible endpoint gauge `G_0` and
a nonzero letter of `B`, the matrices `G_0⁻¹, K_0, …, K_{D⁴-1}` are nonzero and
satisfy `W_k (B_i ⊗ 1) = (A_i ⊗ 1) W_{k+1}` at all `D⁴ + 1` cuts. Hence there
are a nonzero `R` and a scalar `x ≠ 0` with `R B_i = x⁻¹ A_i R`.
Source: PGVWC07, MPSarchive.tex lines 1080--1095 and 1167--1176, with the
complete cut family of
`docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex`. -/
theorem exists_intertwiner_of_gauged {a b : MPSTensor d D}
    {G K : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hsys : ∀ j < D ^ 4, ∀ i, b i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      G j * (a i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * K j)
    (hinv : ∀ j, j + 1 < D ^ 4 → G (j + 1) * K j = 1)
    (hG0 : IsUnit (G 0)) (hb : ∃ i, b i ≠ 0) :
    ∃ (R : Matrix (Fin D) (Fin D) ℂ) (x : ℂ), R ≠ 0 ∧ x ≠ 0 ∧
      ∀ i, R * b i = x⁻¹ • (a i * R) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hb
  have : Nonempty (Fin D) := by
    by_contra h
    exact hi₀ (Matrix.ext fun p _ ↦ (h ⟨p⟩).elim)
  have hdet : IsUnit (G 0).det := (Matrix.isUnit_iff_isUnit_det _).mp hG0
  have hKne : ∀ j < D ^ 4, K j ≠ 0 := by
    intro j hj hK
    apply hi₀
    have h := hsys j hj i₀
    rw [hK, Matrix.mul_zero] at h
    ext p q
    simpa [Matrix.kroneckerMap_apply] using congrFun (congrFun h (p, p)) (q, p)
  let W : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
    fun k ↦ if k = 0 then (G 0)⁻¹ else K (k - 1)
  refine exists_intertwiner_of_kronecker_chain W (fun j hj ↦ ?_) (fun j hj i ↦ ?_)
  · rcases j with _ | j
    · intro h0
      have h := Matrix.mul_nonsing_inv (G 0) hdet
      simp only [W, ite_eq_left rfl] at h0
      rw [h0, Matrix.mul_zero] at h
      exact zero_ne_one h
    · simpa only [W, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel] using hKne j (by omega)
  · rcases j with _ | j
    · simp only [W, ite_eq_left rfl, ite_eq_right (Nat.succ_ne_zero 0), Nat.sub_self]
      rw [hsys 0 hj i]
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    · simp only [W, ite_eq_right (Nat.succ_ne_zero j), ite_eq_right (Nat.succ_ne_zero (j + 1)),
        Nat.add_sub_cancel]
      have hKG : K j * G (j + 1) = 1 := mul_eq_one_comm.mp (hinv j hj)
      rw [hsys (j + 1) hj i]
      simp only [← Matrix.mul_assoc, hKG, Matrix.one_mul]

/-- A nonzero `1 × 1` matrix has invertible amplification. -/
private theorem isUnit_kronecker_one_of_bondDim_eq_one (hD : D = 1)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ≠ 0) :
    IsUnit (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
  subst hD
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one,
    Matrix.det_unique, Fintype.card_fin, pow_one, isUnit_iff_ne_zero]
  intro h0
  apply hX
  ext a b
  rw [Subsingleton.elim a default, Subsingleton.elim b default]
  exact h0

/-- **A nonzero intertwiner for every solution over a physical cut window.**
Let `A` be a canonical tensor satisfying condition C1 at `L`, let
`2 L + D⁴ < N`, and let the window be the physical slicing maps in any bases
of the actual cut spaces of the length-`N` state. Every solution of system
(S) over this window has a nonzero `R` and a scalar `x ≠ 0` with
`R B_i = x⁻¹ A_i R`. The endpoint gauge is invertible by
`isUnit_gauge_zero_of_isNBlkInjective` when `D ≥ 2`, and because it is a
nonzero scalar when `D = 1`.
Source: PGVWC07, Theorem 8 and proof, MPSarchive.tex lines 1139--1176. -/
theorem exists_intertwiner_of_physicalCutWindow [NeZero D] {A : MPSTensor d D}
    {L N : ℕ} (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L)
    (hN : 2 * L + D ^ 4 < N) {ψ : (Fin N → Fin d) → ℂ} (hψ : ψ = mpv A)
    (C : (j : Fin (D ^ 4 + 1)) → Module.Basis (Fin D × Fin D) ℂ
      (cutColumnSpace ψ (L + j.val)))
    {H : Fin (D ^ 4) → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hH : H = quadraticPhysicalCutWindow ψ C) (s : QuadraticReconstructionSolution H) :
    ∃ (R : Matrix (Fin D) (Fin D) ℂ) (x : ℂ), R ≠ 0 ∧ x ≠ 0 ∧
      ∀ i, R * s.tensor i = x⁻¹ • (A i * R) := by
  classical
  subst hH hψ
  have hcut (j : Fin (D ^ 4 + 1)) : L + j.val ≤ N := by have := j.isLt; omega
  have hleft (j : Fin (D ^ 4 + 1)) : Kraus.IsNBlkInjective A (L + j.val) :=
    isNBlkInjective_of_le_of_canonical hA hC1 (by omega)
  have hright (j : Fin (D ^ 4 + 1)) : Kraus.IsNBlkInjective A (N - (L + j.val)) := by
    have := j.isLt
    exact isNBlkInjective_of_le_of_canonical hA hC1 (by omega)
  obtain ⟨P, P', hPP', hloc⟩ := exists_physicalCutWindow_invertible_gauges hcut hleft hright C
  have hP'P (k : Fin (D ^ 4 + 1)) : P' k * P k = 1 := mul_eq_one_comm.mp (hPP' k)
  have hwin (j : Fin (D ^ 4)) (i : Fin d) : quadraticPhysicalCutWindow (mpv A) C j i =
      P' j.castSucc * (A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * P j.succ := by
    rw [← hloc j i]
    calc quadraticPhysicalCutWindow (mpv A) C j i
        = (P' j.castSucc * P j.castSucc) * quadraticPhysicalCutWindow (mpv A) C j i *
            (P' j.succ * P j.succ) := by rw [hP'P, hP'P, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  let G : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j ↦
    if h : j < D ^ 4 then s.leftGauge ⟨j, h⟩ * P' (Fin.castSucc ⟨j, h⟩) else 0
  let K : ℕ → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun j ↦
    if h : j < D ^ 4 then P (Fin.succ ⟨j, h⟩) * s.rightGauge ⟨j, h⟩ else 0
  have hsys : ∀ j < D ^ 4, ∀ i, s.tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) =
      G j * (A i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * K j := by
    intro j hj i
    simp only [G, K, dite_eq_left hj]
    rw [s.kronecker_eq i ⟨j, hj⟩, hwin]
    simp only [Matrix.mul_assoc]
  have hinv : ∀ j, j + 1 < D ^ 4 → G (j + 1) * K j = 1 := by
    intro j hj
    have hj' : j < D ^ 4 := by omega
    simp only [G, K, dite_eq_left hj, dite_eq_left hj']
    have hidx : (Fin.castSucc ⟨j + 1, hj⟩ : Fin (D ^ 4 + 1)) = Fin.succ ⟨j, hj'⟩ := Fin.ext rfl
    rw [hidx]
    calc s.leftGauge ⟨j + 1, hj⟩ * P' (Fin.succ ⟨j, hj'⟩) *
          (P (Fin.succ ⟨j, hj'⟩) * s.rightGauge ⟨j, hj'⟩)
        = s.leftGauge ⟨j + 1, hj⟩ * (P' (Fin.succ ⟨j, hj'⟩) * P (Fin.succ ⟨j, hj'⟩)) *
            s.rightGauge ⟨j, hj'⟩ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hP'P, Matrix.mul_one]
          exact s.leftGauge_mul_rightGauge ⟨j, hj'⟩ hj
  have hb : ∃ i, s.tensor i ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := s.sum_mul_conjTranspose
    simp only [h, Matrix.zero_mul, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hG0 : IsUnit (G 0) := by
    rcases (show D = 1 ∨ 2 ≤ D by have := NeZero.pos D; omega) with hD | hD
    · obtain ⟨i, hi⟩ := hb
      have h := hsys 0 (pow_pos (NeZero.pos D) 4) i
      have hu := isUnit_kronecker_one_of_bondDim_eq_one hD hi
      rw [h] at hu
      exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
    · obtain ⟨ℓ, hℓ, hℓm, hspan⟩ := exists_isNBlkInjective_le_of_canonical hA hC1 hD
      exact isUnit_gauge_zero_of_isNBlkInjective hsys hinv hℓ hℓm hspan
  exact exists_intertwiner_of_gauged hsys hinv hG0 hb

end MPSTensor

namespace MPSTensor.QuadraticReconstructionSolution

variable {d D m : ℕ}
    {H : Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}

/-- **The corrected converse of PGVWC07 Theorem 8 for every solution.** Let
`A` be a translation-invariant canonical tensor satisfying condition C1 at
`L₀`, let `N > 2 L₀ + D⁴`, and let `B` be an open-boundary representation of
the same length-`N` vector satisfying the source canonical equations. For
every solution `s` of system (S) over the canonical window, the canonical
form has a single block of some weight `λ ∈ (0, 1]`, and there are a unitary
`U` and a scalar `ξ` with `|ξ| = 1` and `A_i = λ ξ U s_i U†`; equivalently
the unital block `λ⁻¹ A` is `ξ U s_i U†`. The solution is not assumed
canonical, injective, or to represent the state.

The printed conclusion `A_i = U B_i U†` omits the phase `ξ`, which the
phase symmetry of the system forces, and is stated for the canonical tensor
normalized by `Σ_i A_i A_i† = 1`, which is the unital block here.
Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 8, MPSarchive.tex lines
1154--1176, and the canonical form of Theorem 4, lines 742--763; the phase
correction and the endpoint argument are in
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`. -/
theorem exists_unitary_phase {A : MPSTensor d D} {L₀ N Q : ℕ}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L₀)
    (hN : 2 * L₀ + D ^ 4 < N) (hletter : ∃ i, A i ≠ 0) (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A)
    (s : QuadraticReconstructionSolution
      (quadraticCanonicalOBCWindow hletter hC1 hN B Λ hzero hstep hfaithful hrow hcoeff)) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ ∑ i, A i * (A i)ᴴ = ((lam : ℂ) ^ 2) • 1 ∧
      ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧
        ∀ i, A i = ((lam : ℂ) * ξ) • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  have : NeZero D := ⟨fun hD ↦ by
    subst hD
    obtain ⟨i, hi⟩ := hletter
    exact hi (Subsingleton.elim _ _)⟩
  obtain ⟨R, x, hR, hx, hrel⟩ := exists_intertwiner_of_physicalCutWindow hA hC1 hN hcoeff
    (prescribedOBCWindowCutBases hletter hC1 hN
      (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff) hcoeff)
    (quadraticPrescribedOBCWindow_eq_physicalCutWindow hletter hC1 hN
      (canonicalOBCWithSquaredBound B Λ hzero hstep hfaithful hrow hcoeff) hcoeff) s
  obtain ⟨Cd⟩ := hA
  obtain ⟨lam, hlam, hle, hsum⟩ := Cd.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  let A₁ : MPSTensor d D := fun i ↦ (lam : ℂ)⁻¹ • A i
  have hA₁ : ∑ i, A₁ i * (A₁ i)ᴴ = 1 := sum_inv_smul_mul_conjTranspose_eq_one hlam hsum
  have hC1₁ : Kraus.IsNBlkInjective A₁ L₀ := isNBlkInjective_smul _ (inv_ne_zero hlam0) hC1
  have hy : x * (lam : ℂ)⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hlam0)
  have hrel₁ : ∀ i, R * s.tensor i = (x * (lam : ℂ)⁻¹)⁻¹ • (A₁ i * R) := by
    intro i
    rw [hrel i, Matrix.smul_mul, smul_smul, mul_inv, inv_inv, mul_assoc,
      mul_inv_cancel₀ hlam0, mul_one]
  obtain ⟨U, hnorm, hconj⟩ := exists_unitaryConj_of_intertwines_of_isNBlkInjective hA₁
    s.sum_mul_conjTranspose hC1₁ hR hy hrel₁
  refine ⟨lam, hlam, hle, hsum, U, x * (lam : ℂ)⁻¹, hnorm, fun i ↦ ?_⟩
  have h := hconj i
  calc A i = (lam : ℂ) • A₁ i := by
        simp only [A₁, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    _ = _ := by rw [h, smul_smul]

/-- **The rephased solution for every solution of system (S).** In the setting
of `exists_unitary_phase`, write `λ` for the weight of the canonical block and
`A¹ = λ⁻¹ A` for the unital block. The explicitly rephased solution `ξ s` of
the same system represents the same length-`N` state as `A¹` and is exactly
unitarily conjugate to it; the solution tensor `s` itself represents that
state if and only if `ξ ^ N = 1`.
Source: PGVWC07, Theorem 8, MPSarchive.tex lines 1154--1176, with the
corrected conclusion of
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`. -/
theorem exists_rephased_solution_exact_gauge {A : MPSTensor d D} {L₀ N Q : ℕ}
    (hA : IsPGVWC07CanonicalForm A) (hC1 : Kraus.IsNBlkInjective A L₀)
    (hN : 2 * L₀ + D ^ 4 < N) (hletter : ∃ i, A i ≠ 0) (B : OBCChainTensor d Q N)
    (Λ : (k : Fin (N + 1)) → Matrix (Fin (B.bondDim k)) (Fin (B.bondDim k)) ℂ)
    (hzero : Λ 0 = 1)
    (hstep : ∀ p : Fin N, ∑ i, (B.tensor p i)ᴴ * Λ p.castSucc * B.tensor p i = Λ p.succ)
    (hfaithful : ∀ k, (Λ k).PosDef)
    (hrow : ∀ p : Fin N, ∑ i, B.tensor p i * (B.tensor p i)ᴴ = 1)
    (hcoeff : B.coeff = mpv A)
    (s : QuadraticReconstructionSolution
      (quadraticCanonicalOBCWindow hletter hC1 hN B Λ hzero hstep hfaithful hrow hcoeff)) :
    ∃ (lam : ℝ) (ξ : ℂ) (hξ : ‖ξ‖ = 1), 0 < lam ∧ lam ≤ 1 ∧
      ∑ i, A i * (A i)ᴴ = ((lam : ℂ) ^ 2) • 1 ∧
      (∀ σ : Fin N → Fin d,
        mpv (fun i ↦ (lam : ℂ)⁻¹ • A i) σ = mpv (s.rephase ξ hξ).tensor σ) ∧
      ((∀ σ : Fin N → Fin d, mpv (fun i ↦ (lam : ℂ)⁻¹ • A i) σ = mpv s.tensor σ) ↔
        ξ ^ N = 1) ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∀ i, (lam : ℂ)⁻¹ • A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨lam, hlam, hle, hsum, U, ξ, hξ, hconj⟩ :=
    s.exists_unitary_phase hA hC1 hN hletter B Λ hzero hstep hfaithful hrow hcoeff
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξ
    exact zero_ne_one hξ
  have hconj₁ : ∀ i, (lam : ℂ)⁻¹ • A i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    intro i
    rw [hconj i, smul_smul, ← mul_assoc, inv_mul_cancel₀ hlam0, one_mul]
  have hmpv : ∀ σ : Fin N → Fin d,
      mpv (fun i ↦ (lam : ℂ)⁻¹ • A i) σ = ξ ^ N * mpv s.tensor σ :=
    mpv_eq_pow_mul_mpv_of_unitaryConj hξ0 U hconj₁
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0 := by
    by_contra h
    push Not at h
    exact coeff_ne_zero_of_faithful_density B Λ hzero hstep hfaithful (hcoeff.trans (funext h))
  have hσ₀' : mpv (fun i ↦ (lam : ℂ)⁻¹ • A i) σ₀ ≠ 0 := by
    rw [mpv_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hσ₀
  refine ⟨lam, ξ, hξ, hlam, hle, hsum, fun σ ↦ ?_, ⟨fun h ↦ ?_, fun h σ ↦ ?_⟩, U, fun i ↦ ?_⟩
  · rw [hmpv, rephase_tensor, mpv_smul]
  · have h0 := hmpv σ₀
    rw [h σ₀] at h0
    have hs : mpv s.tensor σ₀ ≠ 0 := by rwa [← h σ₀]
    exact ((mul_eq_right₀ hs).mp h0.symm)
  · rw [hmpv, h, one_mul]
  · rw [hconj₁ i, rephase_tensor]
    simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- The actual same-state solution tensor is unitarily conjugate to the
canonical tensor up to an Nth-root phase. The solution's normalization is
used; no canonical or injectivity hypothesis on the solution tensor is added.
Both endpoint cuts are derived from the actual fixed-length equality and
condition C1 in the displayed size regime.
Source: the corrected PGVWC07 Theorem 8 converse, lines 1154--1176;
finite-ring phase and cut corrections in the module's cited paper-gap notes. -/
theorem exists_unitary_phase_of_same_state (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    (∑ i, A i * (A i)ᴴ = 1) ∧
      ∃ (U : Matrix.unitaryGroup (Fin D) ℂ) (ξ : ℂ), ‖ξ‖ = 1 ∧ ξ ^ N = 1 ∧
        ∀ i, A i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hnonzero
  let : NeZero D := ⟨fun hD ↦ hσ₀ (by subst hD; simp [mpv, coeff, Matrix.trace])⟩
  obtain ⟨C⟩ := hA
  obtain ⟨lam, hlam, _, hsum⟩ := C.exists_weight_sum_mul_conjTranspose_eq_of_isNBlkInjective hC1
  have hcandidate : ∑ i, s.tensor i * (s.tensor i)ᴴ = ((1 : ℝ) : ℂ) ^ 2 • 1 := by
    simpa only [Complex.ofReal_one, one_pow, one_smul] using s.sum_mul_conjTranspose
  obtain ⟨hlameq, U, ξ, hξ, hξN, hconj⟩ := pgvwc07_uniqueness_of_weighted
    hlam (by norm_num : (0 : ℝ) < 1) hsum hcandidate hC1 hN hstate ⟨σ₀, hσ₀⟩
  refine ⟨?_, U, ξ, hξ, hξN, hconj⟩
  simpa only [hlameq, Complex.ofReal_one, one_pow, one_smul] using hsum

/-- The corrected converse as the existing unit-modulus gauge-phase
predicate, with the same explicit nonzero fixed-length state condition.
Source: corrected PGVWC07 Theorem 8, lines 1154--1176. -/
theorem unitGaugePhaseEquiv_of_same_state (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    UnitGaugePhaseEquiv s.tensor A := by
  obtain ⟨_, U, ξ, hξ, _, hconj⟩ :=
    s.exists_unitary_phase_of_same_state hA hC1 hN hstate hnonzero
  refine ⟨Unitary.toUnits U, ξ, ?_, fun i ↦ ?_⟩
  · rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    norm_num
  · change A i = ξ • ((U : Matrix (Fin D) (Fin D) ℂ) * s.tensor i *
      star (U : Matrix (Fin D) (Fin D) ℂ))
    simpa only [Matrix.star_eq_conjTranspose] using hconj i

/-- The explicitly rephased tensor remains a solution of the very same
quadratic system and represents the same length-N state. It is exactly
gauge equivalent, through an actual unitary, to the canonical tensor.
Source: corrected PGVWC07 Theorem 8, lines 1154--1176, and
`docs/paper-gaps/pgvwc07_quadratic_reconstruction_phase.tex`. -/
theorem exists_rephased_solution_exact_gauge_of_same_state
    (s : QuadraticReconstructionSolution H)
    {A : MPSTensor d D} {L₀ N : ℕ} (hA : IsPGVWC07CanonicalForm A)
    (hC1 : Kraus.IsNBlkInjective A L₀) (hN : 2 * L₀ + D ^ 4 < N)
    (hstate : ∀ σ : Fin N → Fin d, mpv A σ = mpv s.tensor σ)
    (hnonzero : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ (ξ : ℂ) (hξ : ‖ξ‖ = 1), ξ ^ N = 1 ∧
      (∀ σ : Fin N → Fin d, mpv (s.rephase ξ hξ).tensor σ = mpv s.tensor σ) ∧
      GaugeEquiv (s.rephase ξ hξ).tensor A ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∀ i, A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨_, U, ξ, hξ, hξN, hconj⟩ :=
    s.exists_unitary_phase_of_same_state hA hC1 hN hstate hnonzero
  have hhat : ∀ i, A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
    intro i
    rw [hconj i]
    simp only [rephase_tensor, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨ξ, hξ, hξN, s.mpv_rephase ξ hξ hξN, ?_, U, hhat⟩
  refine ⟨Unitary.toUnits U, fun i ↦ ?_⟩
  change A i = (U : Matrix (Fin D) (Fin D) ℂ) * (s.rephase ξ hξ).tensor i *
    star (U : Matrix (Fin D) (Fin D) ℂ)
  simpa only [Matrix.star_eq_conjTranspose] using hhat i

end MPSTensor.QuadraticReconstructionSolution

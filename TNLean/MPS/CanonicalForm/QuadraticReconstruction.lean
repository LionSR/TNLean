/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QICLean.MPS.Defs

/-!
# Quadratic reconstruction system for the translation-invariant canonical form

This file formalizes the quadratic system of equations from Pérez-García,
Verstraete, Wolf, and Cirac (PGVWC07, arXiv:quant-ph/0608197), Section
"Obtaining the canonical form", together with the two lemmas that drive the
uniqueness part of its reconstruction theorem.

PGVWC07 stores a translation-invariant state whose successive reduced density
operators have rank at most `D ^ 2` as an open-boundary matrix product state
with `D ^ 2 × D ^ 2` matrices `A i j` on a window of sites, and reconstructs a
translation-invariant `D`-tensor `B` by solving the system (S) of quadratic
equations displayed at MPSarchive.tex lines 1139-1152:

* `B i ⊗ 1 = Y j * A j i * Z (j + 1)` for all physical indices `i` and window
  sites `j`;
* `Y (j + 1) * Z (j + 1) = 1` at every internal cut represented by the
  window;
* `∑ i, B i * (B i)ᴴ = 1`.

The reconstruction theorem (MPSarchive.tex lines 1154-1165) asserts that the
system is solvable whenever the state admits a translation-invariant
representation with condition C1, and that any solution is unitarily conjugate
to the canonical one. Its proof reduces, as in the uniqueness theorem
`thm-uniq`, to two lemmas formalized below: the chain-combination lemma
`lem-same-matr` (lines 1022-1049) and the Kronecker intertwiner lemma
`lem-horn` (lines 1053-1058).

## Main declarations

* `MPSTensor.QuadraticReconstructionSolution` - a solution of the PGVWC07
  system (S) over a supplied window of open-boundary matrices.
* `pgvwc07ChainCoeff`, `pgvwc07_chainCoeff_combination_spec` - the coefficient
  sequence and conclusion of PGVWC07 Lemma `lem-same-matr`.
* `Matrix.kronecker_one_intertwines_iff_kroneckerSlice_intertwines`,
  `Matrix.exists_nonzero_intertwiner_of_kronecker_one_intertwines` - PGVWC07
  Lemma `lem-horn` in multiplicity-slice form, and the nonzero-intertwiner
  consequence used at lines 1094-1095.
* `MPSTensor.QuadraticReconstructionSolution.chainIntertwiner`,
  `MPSTensor.QuadraticReconstructionSolution.chainIntertwiner_mul_kronecker` -
  the internal chain of intertwiners comparing two solutions of system (S),
  the first step of the reconstruction proof (lines 1167-1176).
-/

open scoped Matrix Kronecker

/-! ## The chain-combination lemma `lem-same-matr` -/

/-- The coefficient sequence of PGVWC07, Lemma `lem-same-matr`
(arXiv:quant-ph/0608197, MPSarchive.tex lines 1022-1049). With the source's
one-based data `λ_1, …, λ_{n-1}` written zero-based as `lam 0, …, lam (n - 1)`,
the value at `j` is the source coefficient
`μ_{j+1} = λ_1 x^{j+1} + λ_2 x^{j} + ⋯ + λ_{j+1} x`. -/
def pgvwc07ChainCoeff (lam : ℕ → ℂ) (x : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (j + 1), lam k * x ^ (j + 1 - k)

/-- The recurrence `μ_{j+1} = x (λ_{j+1} + μ_j)` satisfied by the coefficients
of PGVWC07 Lemma `lem-same-matr` (MPSarchive.tex lines 1032-1037). -/
theorem pgvwc07ChainCoeff_succ (lam : ℕ → ℂ) (x : ℂ) (j : ℕ) :
    pgvwc07ChainCoeff lam x (j + 1) = x * (lam (j + 1) + pgvwc07ChainCoeff lam x j) := by
  unfold pgvwc07ChainCoeff
  rw [Finset.sum_range_succ]
  have hstep : ∀ k ∈ Finset.range (j + 1),
      lam k * x ^ (j + 1 + 1 - k) = x * (lam k * x ^ (j + 1 - k)) := by
    intro k hk
    have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : j + 1 + 1 - k = (j + 1 - k) + 1 := by omega
    rw [hpow, pow_succ]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hone : j + 1 + 1 - (j + 1) = 1 := by omega
  rw [hone, pow_one]
  ring

/-- **PGVWC07, Lemma `lem-same-matr`** (arXiv:quant-ph/0608197, MPSarchive.tex
lines 1022-1049), zero-based. Let `T`, `S` be linear maps on the same spaces
and `Y 0, …, Y n` vectors such that `T (Y k) = S (Y (k + 1))` for `k < n`, the
vectors `Y 0, …, Y (n - 1)` are linearly independent, and
`Y n = ∑ k < n, lam k • Y k`. For any solution `x ≠ 0` of the polynomial
equation `∑ k < n, lam k * x ^ (n - k) = 1`, the combination
`∑ k < n, μ k • Y k` with the coefficients `μ` of `pgvwc07ChainCoeff` is
nonzero and satisfies `T Y = x⁻¹ • S Y`. -/
theorem pgvwc07_chainCoeff_combination_spec
    {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (T S : M →ₗ[ℂ] M') {n : ℕ} (Y : ℕ → M) (lam : ℕ → ℂ) {x : ℂ}
    (hchain : ∀ k < n, T (Y k) = S (Y (k + 1)))
    (hindep : LinearIndependent ℂ fun k : Fin n ↦ Y k)
    (hdep : Y n = ∑ k ∈ Finset.range n, lam k • Y k)
    (hx : x ≠ 0)
    (hxeq : ∑ k ∈ Finset.range n, lam k * x ^ (n - k) = 1) :
    (∑ k ∈ Finset.range n, pgvwc07ChainCoeff lam x k • Y k) ≠ 0 ∧
      T (∑ k ∈ Finset.range n, pgvwc07ChainCoeff lam x k • Y k) =
        x⁻¹ • S (∑ k ∈ Finset.range n, pgvwc07ChainCoeff lam x k • Y k) := by
  classical
  rcases n with - | m
  · exact absurd hxeq (by simp)
  have hlast : pgvwc07ChainCoeff lam x m = 1 := hxeq
  constructor
  · intro h0
    have hfin : ∑ k : Fin (m + 1), pgvwc07ChainCoeff lam x (k : ℕ) • Y (k : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range fun k ↦ pgvwc07ChainCoeff lam x k • Y k]
      exact h0
    have hzero :=
      Fintype.linearIndependent_iff.mp hindep (fun k : Fin (m + 1) ↦ pgvwc07ChainCoeff lam x k)
        hfin ⟨m, Nat.lt_succ_self m⟩
    rw [show (((⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) : ℕ)) = m from rfl, hlast] at hzero
    exact one_ne_zero hzero
  · have step1 : T (∑ k ∈ Finset.range (m + 1), pgvwc07ChainCoeff lam x k • Y k) =
        S (∑ k ∈ Finset.range (m + 1), pgvwc07ChainCoeff lam x k • Y (k + 1)) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [map_smul, map_smul, hchain k (Finset.mem_range.mp hk)]
    have hshift : (∑ k ∈ Finset.range m, pgvwc07ChainCoeff lam x k • Y (k + 1)) =
        ∑ j ∈ Finset.range (m + 1),
          (if j = 0 then 0 else pgvwc07ChainCoeff lam x (j - 1)) • Y j := by
      rw [Finset.sum_range_succ']
      simp
    have step2 : (∑ k ∈ Finset.range (m + 1), pgvwc07ChainCoeff lam x k • Y (k + 1)) =
        x⁻¹ • ∑ k ∈ Finset.range (m + 1), pgvwc07ChainCoeff lam x k • Y k := by
      rw [Finset.sum_range_succ, hlast, one_smul, hdep, hshift, ← Finset.sum_add_distrib,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← add_smul, smul_smul]
      congr 1
      rcases j with - | j'
      · have h0 : pgvwc07ChainCoeff lam x 0 = lam 0 * x := by
          simp [pgvwc07ChainCoeff]
        rw [ite_eq_left rfl, zero_add, h0, mul_comm (lam 0) x, inv_mul_cancel_left₀ hx]
      · rw [ite_eq_right (Nat.succ_ne_zero j'), Nat.succ_sub_one, pgvwc07ChainCoeff_succ,
          inv_mul_cancel_left₀ hx]
        ring
    rw [step1, step2, map_smul]

/-! ## The Kronecker intertwiner lemma `lem-horn` -/

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
variable {R : Type*} [CommRing R]

/-- The multiplicity slice of a matrix on a doubled index: the `(a, b)` slice
of `W` is the matrix of entries `W (p, a) (q, b)`. This realizes the tensor
factorization `M_{nm} = M_n ⊗ M_m` used in PGVWC07, Lemma `lem-horn`
(arXiv:quant-ph/0608197, MPSarchive.tex lines 1053-1058). -/
def kroneckerSlice (W : Matrix (n × m) (n × m) R) (a b : m) : Matrix n n R :=
  fun p q ↦ W (p, a) (q, b)

/-- **PGVWC07, Lemma `lem-horn`** (arXiv:quant-ph/0608197, MPSarchive.tex
lines 1053-1058) in multiplicity-slice form: `W` solves the amplified matrix
equation `W (C ⊗ 1) = (B ⊗ 1) W` if and only if every multiplicity slice of
`W` solves the unamplified equation `X C = B X`. The source phrases this as
the solution space of the amplified equation being `S ⊗ M_n` for `S` the
solution space of `X C = B X`; the slice decomposition realizes exactly that
tensor factorization. -/
theorem kronecker_one_intertwines_iff_kroneckerSlice_intertwines
    (B C : Matrix n n R) (W : Matrix (n × m) (n × m) R) :
    W * (C ⊗ₖ (1 : Matrix m m R)) = (B ⊗ₖ (1 : Matrix m m R)) * W ↔
      ∀ a b, kroneckerSlice W a b * C = B * kroneckerSlice W a b := by
  constructor
  · intro h a b
    ext p q
    have h' := congrFun (congrFun h (p, a)) (q, b)
    simpa [kroneckerSlice, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm] using h'
  · intro h
    ext ⟨p, a⟩ ⟨q, b⟩
    have h' := congrFun (congrFun (h a b) p) q
    simpa [kroneckerSlice, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type, mul_comm] using h'

/-- The consequence of PGVWC07 Lemma `lem-horn` used in the uniqueness and
reconstruction proofs (arXiv:quant-ph/0608197, MPSarchive.tex lines 1094-1095): a
nonzero simultaneous solution `W` of the amplified equations
`W (C i ⊗ 1) = (B i ⊗ 1) W` yields a nonzero matrix `X` with `X * C i = B i * X`
for every `i`. -/
theorem exists_nonzero_intertwiner_of_kronecker_one_intertwines
    {ι : Type*} (B C : ι → Matrix n n R) (W : Matrix (n × m) (n × m) R)
    (hW : W ≠ 0)
    (h : ∀ i, W * (C i ⊗ₖ (1 : Matrix m m R)) = (B i ⊗ₖ (1 : Matrix m m R)) * W) :
    ∃ X : Matrix n n R, X ≠ 0 ∧ ∀ i, X * C i = B i * X := by
  have hslice : ∃ a b, kroneckerSlice W a b ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hW ?_
    ext ⟨p, a⟩ ⟨q, b⟩
    have := congrFun (congrFun (hall a b) p) q
    simpa [kroneckerSlice] using this
  obtain ⟨a, b, hab⟩ := hslice
  exact ⟨kroneckerSlice W a b, hab, fun i ↦
    (kronecker_one_intertwines_iff_kroneckerSlice_intertwines (B i) (C i) W).mp (h i) a b⟩

end Matrix

/-! ## The quadratic system (S) -/

namespace MPSTensor

variable {d D m : ℕ}

/-- **PGVWC07 system (S)** (arXiv:quant-ph/0608197, MPSarchive.tex lines
1139-1152). Over a supplied window `A` of open-boundary matrices on the
doubled bond space (in the source, the `D ^ 2 × D ^ 2` matrices
`A i (L₀ + 1), …, A i (L₀ + D ^ 4)` of the unique open-boundary canonical
form, so that the window length is `D ^ 4`), a solution consists of matrices
`Y j`, `Z (j + 1)` on the doubled bond space and a translation-invariant
tensor `B` of bond dimension `D` satisfying the quadratic equations

* `B i ⊗ 1 = Y j * A j i * Z (j + 1)` for all `i`, `j`;
* `Y (j + 1) * Z (j + 1) = 1` at every internal cut represented by the
  window;
* `∑ i, B i * (B i)ᴴ = 1`.

Here `leftGauge j` is the source unknown `Y (L₀ + 1 + j)`, while
`rightGauge j` is the source unknown `Z (L₀ + 2 + j)`, both indexed from
`j = 0`. Thus `leftGauge (j + 1) * rightGauge j = 1` is the source equation
`Y (L₀ + 2 + j) * Z (L₀ + 2 + j) = 1`. -/
structure QuadraticReconstructionSolution
    (A : Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) where
  /-- The row unknowns `Y j` of system (S), zero-based over the window. -/
  leftGauge : Fin m → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ
  /-- The column unknowns `Z (j + 1)` of system (S), zero-based over the
  window: `rightGauge j` is the source unknown `Z (L₀ + 2 + j)` attached to
  the right of window site `L₀ + 1 + j`. -/
  rightGauge : Fin m → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ
  /-- The translation-invariant tensor unknowns `B i` of system (S). -/
  tensor : MPSTensor d D
  /-- The quadratic equations `B i ⊗ 1 = Y j * A j i * Z (j + 1)` of system
  (S), MPSarchive.tex lines 1147-1149. -/
  kronecker_eq : ∀ (i : Fin d) (j : Fin m),
    tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ) = leftGauge j * A j i * rightGauge j
  /-- The internal inversion equations `Y (j + 1) * Z (j + 1) = 1` of
  system (S), MPSarchive.tex line 1150. In the zero-based stored variables this
  is `leftGauge (j + 1) * rightGauge j = 1`. -/
  leftGauge_mul_rightGauge : ∀ (j : Fin m) (h : (j : ℕ) + 1 < m),
    leftGauge ⟨(j : ℕ) + 1, h⟩ * rightGauge j = 1
  /-- The normalization equation `∑ i, B i * (B i)ᴴ = 1` of system (S),
  MPSarchive.tex line 1151. -/
  sum_mul_conjTranspose : ∑ i, tensor i * (tensor i)ᴴ = 1

namespace QuadraticReconstructionSolution

variable {A : Fin m → Fin d → Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}

/-- In a solution of system (S), each row unknown paired by an inversion
equation is invertible. This is the invertibility of the `Y j` used implicitly
in the reconstruction argument of PGVWC07 (arXiv:quant-ph/0608197,
MPSarchive.tex lines 1142-1152). -/
theorem isUnit_leftGauge (s : QuadraticReconstructionSolution A)
    {j : Fin m} (h : (j : ℕ) + 1 < m) :
    IsUnit (s.leftGauge ⟨(j : ℕ) + 1, h⟩) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (s.leftGauge_mul_rightGauge j h))

/-- In a solution of system (S), each column unknown paired by an inversion
equation is invertible. This is the invertibility of the `Z j` used implicitly
in the reconstruction argument of PGVWC07 (arXiv:quant-ph/0608197,
MPSarchive.tex lines 1142-1152). -/
theorem isUnit_rightGauge (s : QuadraticReconstructionSolution A)
    {j : Fin m} (h : (j : ℕ) + 1 < m) :
    IsUnit (s.rightGauge j) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (s.leftGauge_mul_rightGauge j h))

/-- The intertwiner comparing two solutions of system (S) at a window site:
with row unknowns `Y`, `Y'` and column unknowns `Z`, `Z'` of the two solutions,
the matrix at the internal cut after site `j` is
`W (j + 1) = Y' (j + 1) * Z (j + 1)`, which equals
`Y' (j + 1) * (Y (j + 1))⁻¹` by the inversion equations. For a window of
`m` sites this definition gives exactly `m - 1` internal intertwiners. This is
the internal part of the chain used in the reconstruction proof of PGVWC07
(arXiv:quant-ph/0608197, MPSarchive.tex lines 1167-1176), by comparison with
the uniqueness proof at lines 1080-1086.

**Local fix (`docs/paper-gaps/pgvwc07_intertwiner_chain_off_by_one.tex`):**
The internal chain alone has only `m - 1` intertwiners and does not force a
linear dependence. For the source window `m = D ^ 4`, the dimension argument
requires `D ^ 4 + 1` cut intertwiners. The two endpoint cuts are deliberately
not invented here; they must come from a future open-boundary gauge comparison. -/
def chainIntertwiner (s t : QuadraticReconstructionSolution A) (j : ℕ) (h : j + 1 < m) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  t.leftGauge ⟨j + 1, h⟩ * s.rightGauge ⟨j, Nat.lt_of_succ_lt h⟩

/-- Each chain intertwiner comparing two solutions of system (S) is invertible,
as the product of a row unknown and a column unknown that are each paired by an
inversion equation. This is the invertibility of the matrices `W_k` in the
reconstruction proof of PGVWC07 (arXiv:quant-ph/0608197, MPSarchive.tex lines
1167-1176). -/
theorem isUnit_chainIntertwiner (s t : QuadraticReconstructionSolution A)
    {j : ℕ} (h : j + 1 < m) :
    IsUnit (chainIntertwiner s t j h) :=
  (t.isUnit_leftGauge (j := ⟨j, Nat.lt_of_succ_lt h⟩) h).mul
    (s.isUnit_rightGauge (j := ⟨j, Nat.lt_of_succ_lt h⟩) h)

/-- **Chain relation between two solutions of system (S)** (PGVWC07,
arXiv:quant-ph/0608197, MPSarchive.tex lines 1167-1176): the invertible
intertwiners `W` of `chainIntertwiner` satisfy
`W (j + 1) * (B i ⊗ 1) = (C i ⊗ 1) * W (j + 2)` for the tensors `B`, `C` of
the two solutions, at every window site where both inversion equations are
available. For a window of `m` sites, this theorem supplies exactly `m - 2`
adjacent relations among the `m - 1` internal intertwiners. It does not supply
the endpoint relations or the dependence hypothesis of `lem-same-matr`. The
source writes the corresponding relation as
`W_k (C_i ⊗ 1) = (B_i ⊗ 1) W_{k+1}` at lines 1080-1086. -/
theorem chainIntertwiner_mul_kronecker (s t : QuadraticReconstructionSolution A)
    (i : Fin d) {j : ℕ} (h1 : j + 1 < m) (h2 : j + 2 < m) :
    chainIntertwiner s t j h1 * (s.tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
      (t.tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * chainIntertwiner s t (j + 1) h2 := by
  have hs := s.kronecker_eq i ⟨j + 1, h1⟩
  have ht := t.kronecker_eq i ⟨j + 1, h1⟩
  have hsflip : s.rightGauge ⟨j, Nat.lt_of_succ_lt h1⟩ * s.leftGauge ⟨j + 1, h1⟩ = 1 :=
    mul_eq_one_comm.mp (s.leftGauge_mul_rightGauge ⟨j, Nat.lt_of_succ_lt h1⟩ h1)
  have htflip : t.rightGauge ⟨j + 1, h1⟩ * t.leftGauge ⟨j + 1 + 1, h2⟩ = 1 :=
    mul_eq_one_comm.mp (t.leftGauge_mul_rightGauge ⟨j + 1, h1⟩ h2)
  have hcancel : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      s.rightGauge ⟨j, Nat.lt_of_succ_lt h1⟩ * (s.leftGauge ⟨j + 1, h1⟩ * X) = X := fun X ↦ by
    rw [← Matrix.mul_assoc, hsflip, Matrix.one_mul]
  have tcancel : ∀ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
      t.rightGauge ⟨j + 1, h1⟩ * (t.leftGauge ⟨j + 1 + 1, h2⟩ * X) = X := fun X ↦ by
    rw [← Matrix.mul_assoc, htflip, Matrix.one_mul]
  change t.leftGauge ⟨j + 1, h1⟩ * s.rightGauge ⟨j, Nat.lt_of_succ_lt h1⟩ *
      (s.tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) =
    (t.tensor i ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
      (t.leftGauge ⟨j + 1 + 1, h2⟩ * s.rightGauge ⟨j + 1, h1⟩)
  rw [hs, ht]
  simp only [Matrix.mul_assoc]
  rw [hcancel, tcancel]

end QuadraticReconstructionSolution

end MPSTensor

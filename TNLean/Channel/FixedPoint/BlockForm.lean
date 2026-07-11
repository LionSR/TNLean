/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Algebra.StarSubalgebraBlockForm

/-!
# Unitary block form of the fixed-point algebra of a Kraus map

This file instantiates the full block form of a star-subalgebra of complex matrices
(`StarSubalgebra.exists_unitary_conj_blockDiagonal_iff`) with the fixed-point algebras of
*Quantum Channels & Operations* (Wolf 2012), Chapter 6. For a trace-preserving Kraus map
whose Schrödinger picture has a positive definite fixed point, the set of fixed points of
the Heisenberg-picture map is a unital star-subalgebra (Theorem 6.12 of *Quantum
Channels & Operations*, Wolf 2012), so there is a unitary $U$ with
$$\{X \mid T^{*}(X) = X\}
  \;=\; U \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes M_{d_k}(\mathbb{C})\Bigr)
  U^{\dagger},$$
the block representation of Equation (1.39) of *Quantum Channels & Operations*
(Wolf 2012),
written with the Kronecker factors in the
order identity-times-matrix. The positive definite fixed point removes the zero block:
this is the unital case of the block form invoked by Theorem 6.14 there. The general case of
Theorem 6.14, where the Schrödinger-picture fixed-point space carries a zero block and
each
summand is weighted by a density operator $\rho_k$, is not asserted here.

## Main results

* `Kraus.adjointFixedPoints_blockDiagonal_iff` -- for a trace-preserving Kraus map with a
  positive definite Schrödinger-picture fixed point, a matrix is a fixed point of the
  Heisenberg-picture map exactly when a fixed unitary conjugates it to block-diagonal
  form with blocks $\mathbf{1}_{m_k} \otimes B_k$.
* `Kraus.fixedPoints_blockDiagonal_iff` -- the same statement for the fixed points of a
  unital Kraus map whose adjoint has a positive definite fixed point.
-/

open scoped Matrix ComplexOrder Kronecker

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Unitary block form of the Heisenberg-picture fixed points.** Let $T$ be a
trace-preserving Kraus map on $M_{D}(\mathbb{C})$ with a positive definite fixed point
$\rho$. Then there are $n \in \mathbb{N}$, positive dimensions $d_k$ and multiplicities
$m_k$ with $\sum_k d_k m_k = D$, and a unitary $U$ such that a matrix $X$ satisfies
$T^{*}(X) = X$ exactly when
$$U^{\dagger} X U \;=\; \bigoplus_{k} \mathbf{1}_{m_k} \otimes B_k$$
for some matrices $B_k \in M_{d_k}(\mathbb{C})$: up to reordering the two Kronecker
factors of each block,
$$\{X \mid T^{*}(X) = X\}
  \;=\; U \Bigl(\bigoplus_{k} \mathbf{1}_{m_k} \otimes M_{d_k}(\mathbb{C})\Bigr)
  U^{\dagger}.$$
The fixed points of the unital map $T^{*}$ form a star-subalgebra because $T$ has a
positive definite fixed point (Theorem 6.12 of *Quantum Channels & Operations*, Wolf 2012,
in the Kraus case of the Schwarz hypothesis), and every star-subalgebra takes the block
form of Equation (1.39) there; the
positive definiteness of $\rho$ removes the zero block, so this is the unital case of the
block representation invoked by Theorem 6.14 of *Quantum Channels & Operations*
(Wolf 2012).
The density-weighted form of Theorem 6.14 for the Schrödinger-picture fixed points is not
asserted here. -/
theorem adjointFixedPoints_blockDiagonal_iff
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : map K ρ = ρ) :
    ∃ (n : ℕ) (dims mult : Fin n → ℕ)
      (e : ((k : Fin n) × (Fin (mult k) × Fin (dims k))) ≃ Fin D) (U : Mat),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (∀ k, 0 < dims k) ∧ (∀ k, 0 < mult k) ∧
        ∀ X : Mat, adjointMap K X = X ↔
          ∃ B : ∀ k, Matrix (Fin (dims k)) (Fin (dims k)) ℂ,
            star U * X * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) := by
  obtain ⟨n, dims, mult, e, U, hU, hdims, hmult, hiff⟩ :=
    (adjointFixedPointsStarSubalgebra (d := d) (D := D) K h_tp hρ
      hρ_fix).exists_unitary_conj_blockDiagonal_iff
  refine ⟨n, dims, mult, e, U, hU, hdims, hmult, fun X => Iff.trans ?_ (hiff X)⟩
  exact ((mem_adjointFixedPointsStarSubalgebra K h_tp hρ hρ_fix X).trans
    (mem_adjointFixedPoints K X)).symm

/-- **Unitary block form of the fixed points of a unital Kraus map.** Let $E$ be a unital
Kraus map on $M_{D}(\mathbb{C})$ whose adjoint has a positive definite fixed point $\rho$.
Then there are $n \in \mathbb{N}$, positive dimensions $d_k$ and multiplicities $m_k$ with
$\sum_k d_k m_k = D$, and a unitary $U$ such that a matrix $X$ satisfies $E(X) = X$
exactly when
$$U^{\dagger} X U \;=\; \bigoplus_{k} \mathbf{1}_{m_k} \otimes B_k$$
for some matrices $B_k \in M_{d_k}(\mathbb{C})$. This is
`Kraus.adjointFixedPoints_blockDiagonal_iff` with the roles of the map and its adjoint
exchanged: the fixed points of the unital map $E$ form a star-subalgebra (Theorem 6.12
of *Quantum Channels & Operations*, Wolf 2012, in the Kraus case of the Schwarz
hypothesis), and the positive definite fixed point of the
adjoint removes the zero block from the block representation of Equation (1.39) there,
the
unital case invoked by Theorem 6.14 of *Quantum Channels & Operations* (Wolf 2012). -/
theorem fixedPoints_blockDiagonal_iff
    (K : Fin d → Mat) (h_unital : IsUnital K) {ρ : Mat}
    (hρ : ρ.PosDef) (hρ_fix : adjointMap K ρ = ρ) :
    ∃ (n : ℕ) (dims mult : Fin n → ℕ)
      (e : ((k : Fin n) × (Fin (mult k) × Fin (dims k))) ≃ Fin D) (U : Mat),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (∀ k, 0 < dims k) ∧ (∀ k, 0 < mult k) ∧
        ∀ X : Mat, map K X = X ↔
          ∃ B : ∀ k, Matrix (Fin (dims k)) (Fin (dims k)) ℂ,
            star U * X * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (mult k)) (Fin (mult k)) ℂ) ⊗ₖ B k) := by
  obtain ⟨n, dims, mult, e, U, hU, hdims, hmult, hiff⟩ :=
    (fixedPointsStarSubalgebra (d := d) (D := D) K h_unital hρ
      hρ_fix).exists_unitary_conj_blockDiagonal_iff
  refine ⟨n, dims, mult, e, U, hU, hdims, hmult, fun X => Iff.trans ?_ (hiff X)⟩
  exact ((mem_fixedPointsStarSubalgebra K h_unital hρ hρ_fix X).trans
    (mem_fixedPoints K X)).symm

end Kraus

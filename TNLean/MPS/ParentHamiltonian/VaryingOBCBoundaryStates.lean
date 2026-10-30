/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.VaryingOBCProjectorKernel

/-!
# Actual open-chain boundary states lie in the parent kernel

Splitting a physical word splits its ordered rectangular matrix product on the
actual intermediate bond. For a fixed prefix and suffix, cyclicity of the
rectangular trace therefore gives a two-site boundary matrix. The actual
projector kernel characterization then proves annihilation by the open parent
Hamiltonian. This direction requires neither injectivity nor row normalization.

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem 9 and equation unique-OBC,
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 1195–1220.
-/

open scoped Matrix

namespace Matrix

variable {d : ℕ}

/-- Concatenation splits the actual rectangular product at its intermediate
bond. Source: PGVWC07, Theorem 9 proof, equation unique-OBC, lines 1213–1220. -/
theorem obc_rectangularEval_append (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {m n : ℕ} (u : Fin m → Fin d) (v : Fin n → Fin d) :
    Kraus.rectangularEval b (fun k : Fin (m + n) ↦ A k.val) (Fin.append u v) =
      Kraus.rectangularEval b (fun k : Fin m ↦ A k.val) u *
        Kraus.rectangularEval (fun k ↦ b (m + k))
          (fun k : Fin n ↦ A (m + k.val)) v := by
  induction n with
  | zero =>
    rw [Fin.append_right_nil u v rfl]
    simp only [Kraus.rectangularEval, Matrix.mul_one]
    rfl
  | succ n ih =>
    have hleft := obc_rectangularEval_snoc b A
      (Fin.append u (Fin.init v)) (v (Fin.last n))
    have hright := obc_rectangularEval_snoc (fun k ↦ b (m + k))
      (fun k ↦ A (m + k)) (Fin.init v) (v (Fin.last n))
    rw [← Fin.append_snoc, Fin.snoc_init_self] at hleft
    rw [Fin.snoc_init_self] at hright
    rw [hright, ← Matrix.mul_assoc, ← ih]
    exact hleft

/-- The full physical vector associated with an actual rectangular chain and
an arbitrary endpoint boundary matrix. Source: PGVWC07, equation unique-OBC
and its full-chain conclusion, lines 1213–1237. -/
noncomputable def obcBoundaryState (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ)
    (Z : Matrix (Fin (b N)) (Fin (b 0)) ℂ) :
    EuclideanSpace ℂ (Fin N → Fin d) :=
  (WithLp.linearEquiv 2 ℂ ((Fin N → Fin d) → ℂ)).symm
    (fun w ↦ Matrix.trace (Z * Kraus.rectangularEval b (fun k : Fin N ↦ A k.val) w))

/-- Fixing the outside configurations gives the explicit pair boundary
\(X=P_{\mathrm{suffix}}ZP_{\mathrm{prefix}}\) on the actual virtual spaces.
Source: PGVWC07, equation unique-OBC, lines 1213–1220. -/
theorem obcBoundaryState_pair_section (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ)
    {N p q : ℕ} (h : p + 2 + q = N)
    (Z : Matrix (Fin (b N)) (Fin (b 0)) ℂ)
    (u : Fin p → Fin d) (v : Fin q → Fin d) :
    ∃ X : Matrix (Fin (b (p + 2))) (Fin (b p)) ℂ,
      ∀ σ : Fin 2 → Fin d,
        obcPairSection h u v (obcBoundaryState b A N Z) σ =
          Matrix.trace (X * A p (σ 0) * A (p + 1) (σ 1)) := by
  subst N
  let P := Kraus.rectangularEval b (fun k : Fin p ↦ A k.val) u
  let Q := Kraus.rectangularEval (fun k ↦ b (p + 2 + k))
    (fun k : Fin q ↦ A (p + 2 + k.val)) v
  refine ⟨Q * Z * P, fun σ ↦ ?_⟩
  change Matrix.trace (Z * Kraus.rectangularEval b
    (fun k : Fin (p + 2 + q) ↦ A k.val) (Fin.append (Fin.append u σ) v)) = _
  rw [obc_rectangularEval_append, obc_rectangularEval_append]
  have hpair : Kraus.rectangularEval (fun k ↦ b (p + k))
      (fun k : Fin 2 ↦ A (p + k.val)) σ = A p (σ 0) * A (p + 1) (σ 1) := by
    simp [Kraus.rectangularEval]
  rw [hpair]
  change Matrix.trace (Z * ((P * (A p (σ 0) * A (p + 1) (σ 1))) * Q)) = _
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- Every actual full-chain boundary state is annihilated by the actual open
parent Hamiltonian. No spanning or canonical normalization hypothesis is used.
Source: PGVWC07, Theorem 9 and equation unique-OBC, lines 1201–1220. -/
theorem obcParentHamiltonian_apply_obcBoundaryState (b : ℕ → ℕ)
    (A : ∀ k, Fin d → Matrix (Fin (b k)) (Fin (b (k + 1))) ℂ) (N : ℕ)
    (Z : Matrix (Fin (b N)) (Fin (b 0)) ℂ) :
    obcParentHamiltonian b A N (obcBoundaryState b A N Z) = 0 := by
  apply (obcParentHamiltonian_apply_eq_zero_iff b A N _).mpr
  intro p q h u v
  apply (obcPairProjector_apply_eq_zero_iff b A p _).mpr
  exact obcBoundaryState_pair_section b A h Z u v

end Matrix

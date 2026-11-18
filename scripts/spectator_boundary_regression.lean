/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorSiteExpectation

/-!
# Zero-dimensional spectator expectation boundaries

Additional regressions for the Option-site implementation. The companion
`spectator_site_expectation_regression.lean` already checks a nonmaximally entangled
input, non-Hermitian spectator factors and an empty spectator. Here we check all-q
blockwise equality and support, zero local dimension, and empty physical sites.
In the last case q = 0 does not make the matrix index empty: the spectator survives.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator

namespace SpectatorBoundaryRegression

-- Matrix-level block equality, with no positivity, Hermiticity or nonemptiness.
theorem blockwise {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (a b : Aux) :
    (spectatorSiteExpectation q K B).submatrix (fun σ => (σ, a)) (fun τ => (τ, b)) =
      ManyBody.regionExpectation K (B.submatrix (fun σ => (σ, a)) (fun τ => (τ, b))) := by
  ext σ τ
  exact spectatorSiteExpectation_apply K B σ τ a b

-- Each output block belongs to the canonical retained physical algebra.
theorem block_supported {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (a b : Aux) :
    (spectatorSiteExpectation q K B).submatrix (fun σ => (σ, a)) (fun τ => (τ, b)) ∈
      ManyBody.supportedOperators (fun _ : ι => Fin q) K := by
  rw [blockwise]
  exact ManyBody.regionExpectation_mem_supportedOperators _ _

-- When there are no physical sites, every matrix is fixed, even when q = 0.
theorem empty_sites {q : ℕ} {Aux : Type*}
    (B : Matrix ((Fin 0 → Fin q) × Aux) ((Fin 0 → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q (∅ : Finset (Fin 0)) B = B := by
  have h : (∅ : Finset (Fin 0)) = Finset.univ := by ext i; exact Fin.elim0 i
  rw [h, spectatorSiteExpectation_univ]

-- Nonempty physical sites at q = 0 instead give an empty matrix index.
theorem zero_dimension {Aux : Type*}
    (K : Finset Unit) (B : Matrix ((Unit → Fin 0) × Aux) ((Unit → Fin 0) × Aux) ℂ) :
    spectatorSiteExpectation 0 K B = B := by
  ext ⟨σ, _⟩
  exact Fin.elim0 (σ ())

-- A nonzero off-diagonal spectator survives when both q and the site count are zero.
example :
    spectatorSiteExpectation 0 (∅ : Finset (Fin 0))
      ((1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ) ⊗ₖ
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) =
      (1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ) ⊗ₖ !![0, 1; 0, 0] :=
  empty_sites _

-- This surviving entry is 1, so the empty-site check is not vacuous.
example :
    spectatorSiteExpectation 0 (∅ : Finset (Fin 0))
      ((1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ) ⊗ₖ
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      (Fin.elim0, 0) (Fin.elim0, 1) = 1 := by
  rw [empty_sites]
  simp [Matrix.kroneckerMap_apply]

-- The norm API also permits q = 0 and an empty spectator simultaneously.
example (B : Matrix ((Fin 0 → Fin 0) × Fin 0) ((Fin 0 → Fin 0) × Fin 0) ℂ) :
    ‖spectatorSiteExpectation 0 (∅ : Finset (Fin 0)) B‖ ≤ ‖B‖ :=
  norm_spectatorSiteExpectation_le _ _

end SpectatorBoundaryRegression

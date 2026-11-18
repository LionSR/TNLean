/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SpectatorOscillationSupport

/-!
# Arbitrary spectator labels and finite Option coordinates

The algebraic API accepts an infinite spectator without
adding a second expectation definition. Norm results keep finite spectators.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix QuantumCircuit
open scoped Kronecker

namespace SpectatorArbitraryAuxRegression

-- Neither spectator finiteness nor decidable equality is assumed.
example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (A : Matrix (ι → Fin q) (ι → Fin q) ℂ) (S : Matrix Aux Aux ℂ) :
    spectatorSiteExpectation q K (A ⊗ₖ S) = ManyBody.regionExpectation K A ⊗ₖ S :=
  spectatorSiteExpectation_kronecker K A S

-- In particular, the API accepts the infinite index type Nat, for every q.
example {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (S : Matrix ℕ ℕ ℂ) :
    spectatorSiteExpectation q K ((1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S) =
      (1 : Matrix (ι → Fin q) (ι → Fin q) ℂ) ⊗ₖ S :=
  spectatorSiteExpectation_one_kronecker K S

example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q Finset.univ B = B :=
  spectatorSiteExpectation_univ B

example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q K B = B ↔
      ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin q) K :=
  spectatorSiteExpectation_eq_self_iff K B

-- With finite Aux, the same definition has the Option-site coordinate formula.
example {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Aux] [DecidableEq Aux] (K : Finset ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorSiteExpectation q K B =
      reindex (spectatorConfigEquiv q ι Aux) (spectatorConfigEquiv q ι Aux)
        (ManyBody.regionExpectation (Finset.insertNone K)
          (reindex (spectatorConfigEquiv q ι Aux).symm (spectatorConfigEquiv q ι Aux).symm B)) :=
  spectatorSiteExpectation_eq_reindex K B

end SpectatorArbitraryAuxRegression

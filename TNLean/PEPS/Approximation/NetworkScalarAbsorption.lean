/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork

/-! # Absorbing a scalar into one party tensor

Multiplying one local tensor multiplies the network contraction by the same
scalar, without changing the links or their dimensions.
Source: polynomial-PEPS, `04-compression.tex`, lines 573–579.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
namespace TNLean.PEPS.DependentBondNetwork
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
variable [DecidableEq Edge] {Phys : Vertex → Type}
variable (tail head : Edge → Vertex) (D : Edge → Type) [∀ e, Fintype (D e)]

/-- A scalar can be placed in any existing vertex tensor.
Source: polynomial-PEPS, `04-compression.tex`, lines 573–579. -/
theorem network_mul_at_vertex
    (A : (v : Vertex) → LocalConfig tail head D v → Phys v → ℂ)
    (B : (e : Edge) → Matrix (D e) (D e) ℂ)
    (σ : (v : Vertex) → Phys v) (p : Vertex) (s : ℂ) :
    network tail head D (fun q η x => (if q = p then s else 1) * A q η x) B σ =
      s * network tail head D A B σ := by
  classical
  simp only [network, Finset.prod_mul_distrib, Fintype.prod_ite_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  exact mul_left_comm (bondWeight D B β) s _

end TNLean.PEPS.DependentBondNetwork

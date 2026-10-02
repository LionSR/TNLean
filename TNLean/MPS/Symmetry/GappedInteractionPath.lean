/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding
import TNLean.Algebra.FinKronecker
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Interval.Set.Instances

/-!
# Symmetric gapped interaction paths on a common physical space

Schuch–Pérez-García–Cirac, arXiv:1010.3732, Sections II.C.1–2,
`sec:phases-definition-no-sym` and `sec:def-sym-phases`, define a path
by bounded local interactions, continuity, a uniform spectral gap, and
symmetry of every finite-chain Hamiltonian. These conditions do not refer
to virtual cocycles.

The definition here describes the path after the endpoint systems have
been blocked and embedded into a common physical space with a fixed
unitary representation. It does not perform those endpoint embeddings or
assert the classification theorem. Nearest-neighbor rings have at least
two sites; no convention for embedding two distinct sites into a one-site
ring is needed.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- The translation-invariant nearest-neighbor Hamiltonian of a two-site
interaction on a periodic chain. Source: arXiv:1010.3732,
`sec:phases-definition-no-sym`, lines 407–427. -/
noncomputable def interactionHamiltonian {d N : ℕ}
    (h : MPOTensor.ChainOperator d 2) (hN : 2 ≤ N) :
    MPOTensor.ChainOperator d N :=
  ∑ i : Fin N, MPOTensor.embedLocalOperator 2 N hN i h

/-- A common-space symmetric gapped path between two nearest-neighbor
interactions. This is the path required after blocking and embedding in
arXiv:1010.3732, `sec:def-sym-phases`, lines 439–453. The gap is measured
above the entire ground eigenspace; it does not assume a unique ground
state or zero ground energy. -/
structure SymmetricGappedInteractionPath {G : Type} [Group G] {d : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (h₀ h₁ : MPOTensor.ChainOperator d 2) where
  /-- The two-site interaction along the path; source lines 413–420. -/
  interaction : ℝ → MPOTensor.ChainOperator d 2
  /-- The initial interaction is the prescribed endpoint; source line 421. -/
  interaction_zero : interaction 0 = h₀
  /-- The final interaction is the prescribed endpoint; source line 421. -/
  interaction_one : interaction 1 = h₁
  /-- Interactions are Hermitian Hamiltonians; source lines 407–420. -/
  hermitian : ∀ γ ∈ Set.Icc (0 : ℝ) 1, (interaction γ).IsHermitian
  /-- The interaction strength is bounded in operator norm; source line 422. -/
  norm_le_one : ∀ γ ∈ Set.Icc (0 : ℝ) 1, ‖interaction γ‖ ≤ 1
  /-- Continuity of the local interaction; source line 423. -/
  continuous : ContinuousOn interaction (Set.Icc (0 : ℝ) 1)
  /-- One positive lower gap bound works for every parameter and chain
  length. The real number `E` is the least spectral value, and all other
  spectral values are at least `E + δ`; source lines 424–426. -/
  gap : ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ Set.Icc (0 : ℝ) 1,
    ∀ (N : ℕ) (hN : 2 ≤ N), ∃ E : ℝ,
      (E : ℂ) ∈ spectrum ℂ (interactionHamiltonian (interaction γ) hN) ∧
      ∀ z ∈ spectrum ℂ (interactionHamiltonian (interaction γ) hN),
        E ≤ z.re ∧ (z.re = E ∨ E + δ ≤ z.re)
  /-- The full periodic Hamiltonian commutes with the on-site symmetry
  on every chain. This does not impose the stronger condition that each
  chosen local term separately commutes; source lines 439–453. -/
  symmetric : ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∀ g : G,
    ∀ (N : ℕ) (hN : 2 ≤ N),
      Commute (interactionHamiltonian (interaction γ) hN)
        (Matrix.finKronecker fun _ : Fin N => (U g : Matrix (Fin d) (Fin d) ℂ))

/-- Reversing the parameter of a symmetric gapped interaction path exchanges
its endpoints and preserves the same uniform gap. This is the symmetry of
the path condition in arXiv:1010.3732, `sec:def-sym-phases`. -/
def SymmetricGappedInteractionPath.reverse {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁) :
    SymmetricGappedInteractionPath U h₁ h₀ where
  interaction γ := P.interaction (1 - γ)
  interaction_zero := by simpa using P.interaction_one
  interaction_one := by simpa using P.interaction_zero
  hermitian γ hγ := P.hermitian _
    (Set.Icc.one_sub_mem hγ)
  norm_le_one γ hγ := P.norm_le_one _
    (Set.Icc.one_sub_mem hγ)
  continuous := P.continuous.comp
    (continuous_const.sub continuous_id).continuousOn
    (fun _ hγ => (Set.Icc.one_sub_mem hγ))
  gap := by
    obtain ⟨δ, hδ, hgap⟩ := P.gap
    exact ⟨δ, hδ, fun γ hγ => hgap (1 - γ)
      (Set.Icc.one_sub_mem hγ)⟩
  symmetric γ hγ := P.symmetric _
    (Set.Icc.one_sub_mem hγ)

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.LiebRobinson
import TNLean.MPS.AreaLaw.Hastings.PrintedAreaLaw

/-!
# Hastings' factorization and entropy bound at a constructed length

The velocity `V = 40 * (chainLRVelocity R J - 1)` is independent of the gap,
chain length and local dimension. For `J ≥ 0` it is a fixed multiple of `J`.
Together with length eighty it gives a Lieb–Robinson bound with numerical
prefactor four and arbitrary finite second support. Define
`Xi = max (2*V/Delta) 80`; then `Xi` is at least twice the length `zeta`
of the positive endpoint factorization. This one choice absorbs both its
square-root loss and the factor of two in the fixed-length entropy iteration.
The factorization constant is cubic in `Xi`, and the entropy has the printed
shape with `xi' = 6*Xi` and a numerical constant for nearest neighbours.

**Local fix (length convention):** The time-cone statement uses length in
`exp(-d/xi_C)`, as documented in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`. For zero interaction
bound the multiplication-cone statement remains valid without division
by the zero velocity. The fixed-length arithmetic correction is retained in
`docs/paper-gaps/hastings07_doubling_constants.tex`.

Source: Hastings, arXiv:0705.2024v4, eqs. `lrb`, `smd`, lines 96–142,
and Lemma 1 with the note added, lines 246–267 and 912–1003.
-/

open scoped Matrix.Norms.L2Operator ComplexOrder
namespace TNLean.MPS.AreaLaw

/-- An interaction-proportional velocity for Hastings, arXiv:0705.2024v4, eq. `lrb`. -/
noncomputable def hastingsLRVelocity (R : ℕ) (J : ℝ) : ℝ :=
  40 * (chainLRVelocity R J - 1)

/-- The length `max(2V/Delta, 80)` from the constructed Lieb–Robinson pair.
Hastings, arXiv:0705.2024v4, lines 139–142. -/
noncomputable def hastingsLRLength (R : ℕ) (J Δ : ℝ) : ℝ :=
  max (2 * hastingsLRVelocity R J / Δ) 80

/-- A gap-independent physical velocity and numerical length give the
Lieb–Robinson estimate of Hastings, arXiv:0705.2024v4, lines 96–112. -/
theorem ChainHamiltonian.norm_heisenberg_commutator_le_hastings_cone
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (X Y : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A X)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val)
    (t : ℝ) (hcone : hastingsLRVelocity R J * |t| ≤ d) :
    ‖QuantumCircuit.heisenbergEvolution h.operator t A * B -
      B * QuantumCircuit.heisenbergEvolution h.operator t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ * Real.exp (-((d : ℝ) / 80)) := by
  refine (h.norm_heisenberg_commutator_le_numeric X Y hA hB d hd t).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  dsimp only [hastingsLRVelocity] at hcone
  nlinarith only [hcone, Nat.cast_nonneg (α := ℝ) d]

/-- Positive factorization at a length from an explicit admissible
Lieb–Robinson pair. Hastings, arXiv:0705.2024v4, Lemma 1 and note added. -/
theorem exists_projectorFactorization_posSemidef_sourceLength (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∀ c l : ℕ, ∃ OB OL OR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
        OB.PosSemidef ∧
        Hastings.IsFactorizationAt Ω c l (K * hastingsLRLength R J Δ ^ 3 *
          Real.exp (-(l / (6 * hastingsLRLength R J Δ)))) OB OL OR := by
  obtain ⟨K, hK, hbound⟩ := exists_projectorFactorization_posSemidef_endpoint R
  refine ⟨K, hK, fun {J Δ} hJ hΔ {L q} _ h E₀ Ω hgs c l ↦ ?_⟩
  obtain ⟨OB, OL, OR, hOB, hF⟩ := hbound hJ hΔ h hgs c l
  refine ⟨OB, OL, OR, hOB, hF.mono ?_⟩
  have hsize : 2 * lemmaOneEndpointLength R J Δ ≤ hastingsLRLength R J Δ :=
    two_mul_lemmaOneEndpointLength_le_sourceLength R hJ hΔ
  have hζ : 0 < lemmaOneEndpointLength R J Δ :=
    (lemmaOneEndpointLength_eq R J Δ).symm ▸
      mul_pos (by norm_num : (0 : ℝ) < 5 / 4) (lemmaOneLength_pos R (J / Δ) 1)
  have hζΞ : lemmaOneEndpointLength R J Δ ≤ hastingsLRLength R J Δ := by
    linarith only [hsize, hζ]
  have hΞ : 0 < hastingsLRLength R J Δ := hζ.trans_le hζΞ
  rw [show 2 * (6 * lemmaOneEndpointLength R J Δ) =
    6 * (2 * lemmaOneEndpointLength R J Δ) by ring]
  gcongr

/-- A constructed length of the form used in Hastings, arXiv:0705.2024v4,
lines 139–142, gives the printed entropy-bound shape. -/
theorem Hastings.exists_regionEntropy_prefix_le_sourceLength (R : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {J Δ : ℝ}, 0 ≤ J → 0 < Δ →
      ∀ {L q : ℕ} [NeZero q] (h : ChainHamiltonian L q R J) {E₀ : ℝ}
      {Ω : EuclideanSpace ℂ (Fin L → Fin q)}, Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∀ i : ℕ,
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 i) Ω ≤
          c₀ * (6 * hastingsLRLength R J Δ) * Real.log (6 * hastingsLRLength R J Δ) *
            Real.log q * (2 : ℝ) ^ ((6 * hastingsLRLength R J Δ) * Real.log q) := by
  obtain ⟨c₀, hc₀, hbound⟩ := Hastings.exists_regionEntropy_prefix_le_printed R
  exact ⟨c₀, hc₀, fun {J Δ} hJ hΔ {L q} _ h E₀ Ω hgs i ↦
    hbound hJ hΔ h hgs (hastingsLRLength R J Δ)
      (two_mul_lemmaOneEndpointLength_le_sourceLength R hJ hΔ) i⟩

end TNLean.MPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolSweepFrames
import TNLean.MPS.AreaLaw.LogarithmicSeparation
import Mathlib.Data.Nat.Dist

/-!
# Information estimates for the births and the first direct death

The two births of a sweep stage and the direct death at stage zero use
their actual before-birth or after-death environments. These regions are
separated from their targets by at least the chosen width. The physical
logarithmic-separation theorem then gives information at most L⁻⁶⁰ for
the original ground state. The constants are chosen before the chain,
Hamiltonian, vector, stage and width. No information estimate is assumed.

**Scope restriction (contiguous chains):** The sites are `Fin L`. The
finite-domain distinction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (half-open lattice bands):** The targets use the existing
half-open convention, recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Sources: the one-dimensional note, Part II, `con:sweep`, lines 330–343,
and `prop:sweep`, proof, lines 365–374; Part II, `lem:logsep`, lines
472–488. The information exponent is 24, as in the source's logarithmic
width choice.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice

variable {L w : ℕ}

/-- Exact separations for the two births and the exceptional first death.
The third environment is evaluated after that death.
Source: Part II, `prop:sweep`, proof, lines 365–374. -/
theorem birth_death_separation (hw : 1 ≤ w) (k : Fin (stageCount L w)) :
    (∀ x ∈ remainderBirthTarget L w k,
      ∀ y ∈ (stageFrame L w k.castSucc).birthEnv (.inl k.castSucc),
        w ≤ Nat.dist x.val y.val) ∧
      (∀ x ∈ blockBirthTarget L w k,
        ∀ y ∈ (afterRemainderBirth L w k).birthEnv (.inl k.castSucc),
          w ≤ Nat.dist x.val y.val) ∧
      (k.val = 0 → ∀ x ∈ leftBandTarget L w k,
        ∀ y ∈ (afterLeftTransfer L w k).birthEnv (.inr k),
          w ≤ Nat.dist x.val y.val) := by
  obtain ⟨hE₁, hE₂⟩ := birth_environments k
  have hb : (k.val + 1) * (20 * w) = k.val * (20 * w) + 20 * w := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hE₁] at hy
    simp only [remainderBirthTarget, mem_interval] at hx
    simp only [mem_interval] at hy
    have hdist := Nat.dist_tri_left' x.val y.val
    omega
  · intro x hx y hy
    rw [hE₂] at hy
    simp only [blockBirthTarget, mem_interval] at hx
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [mem_interval] at hy
      have hdist := Nat.dist_tri_left' x.val y.val
      omega
    · simp only [remainderBirthTarget, mem_interval] at hy
      have hdist := Nat.dist_tri_left x.val y.val
      omega
  · intro hk x hx y hy
    rw [first_left_death_environment k hk] at hy
    simp only [leftBandTarget, mem_interval, hk, zero_mul, zero_add] at hx
    simp only [mem_interval] at hy
    have hdist := Nat.dist_tri_left x.val y.val
    omega

/-- The original ground state's information bounds for the actual two birth
targets and first-stage death follow from physical logarithmic separation.
The constants precede every chain, state, width and stage.
Source: Part II, `lem:logsep`, lines 472–488, and Part II, `prop:sweep`,
proof, lines 365–374. -/
theorem birth_death_information_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (D₂₄ : ℝ) (L₀ : ℕ), 0 < D₂₄ ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainHamiltonian L q R J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∀ (w : ℕ), 1 ≤ w →
        D₂₄ * Real.log (L : ℝ) ≤ (w : ℝ) →
      ∀ k : Fin (stageCount L w),
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (remainderBirthTarget L w k)
          ((stageFrame L w k.castSucc).birthEnv (.inl k.castSucc)) ≤
            (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (blockBirthTarget L w k)
          ((afterRemainderBirth L w k).birthEnv (.inl k.castSucc)) ≤
            (L : ℝ) ^ (-24 : ℤ)) ∧
        (k.val = 0 → FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (leftBandTarget L w k)
          ((afterLeftTransfer L w k).birthEnv (.inr k)) ≤
            (L : ℝ) ^ (-24 : ℤ)) := by
  classical
  obtain ⟨D₂₄, L₀, hD, hL₀, hlogsep⟩ :=
    ChainHamiltonian.mutualInformation_le_of_logarithmic_separation
      q hq R J Δ hΔ 24 (by norm_num) 1 le_rfl
  refine ⟨D₂₄, L₀, hD, hL₀, ?_⟩
  intro L hL h Ω E₀ hgs w hw hwidth k
  obtain ⟨hd₁, hd₂, hd₃⟩ := birth_death_separation hw k
  have hinterval (b c : ℕ) (E : Finset (Fin L))
      (hd : ∀ x ∈ interval L b c, ∀ y ∈ E, w ≤ Nat.dist x.val y.val) :
      FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
        (interval L b c) E ≤ (L : ℝ) ^ (-24 : ℤ) := by
    have hT : ∃ (n : ℕ) (a z : Fin n → ℕ), n ≤ 1 ∧
        interval L b c = Finset.univ.biUnion (fun i ↦ interval L (a i) (z i)) :=
      ⟨1, fun _ ↦ b, fun _ ↦ c, le_rfl, by simp⟩
    have hi := hlogsep L hL h Ω E₀ hgs (interval L b c) E hT
      (fun x hx y hy ↦ hwidth.trans (by exact_mod_cast hd x hx y hy))
    have hexponent : -(24 : ℝ) = ((-24 : ℤ) : ℝ) := by norm_num
    rw [hexponent, Real.rpow_intCast] at hi
    exact hi
  refine ⟨?_, ?_, ?_⟩
  · exact hinterval _ _ _ hd₁
  · exact hinterval _ _ _ hd₂
  · intro hk
    exact hinterval _ _ _ (hd₃ hk)

end TNLean.MPS.AreaLaw.ChainSweep

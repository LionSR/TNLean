/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledPowerRank
import TNLean.MPS.AreaLaw.ViableSet.CutDecomposition
import TNLean.MPS.AreaLaw.ViableSet.ErrorReduction

/-!
# Sampled left factors for viable-set error reduction

For positive nearest-neighbour contractions with a unit gapped ground vector,
choose an accuracy `0 < δ ≤ 1`. The physical sampler is used at
`Q = 8 / δ` and `η = δ / 8`, so its actual sampled operator is within `δ / 4`
of the ground projection. Its simultaneous spatial rank bound constructs a
cut decomposition with at most `r = ℓ * q^(2u)` terms. Every left factor retains
rank at most `r` at each internal cut.

The resulting family `{A_j s}` improves any half-viable input family to error
`δ`. Its cardinality is at most `a * s` with `a ≤ r`, and its MPS bond is at
most `r * max 1 b`. The sample is chosen before the cut and the input family;
at each cut, the factors are chosen before all possible input families.
Neither a successful sample nor a suitable decomposition is assumed.

**Scope restriction (specified ground energy):** `E0` is an input to the
normalization, word length and sample count, chosen before the sampled family.
The count retains `exp (2 * E0 * log (8 / δ) / Δ)`. This is an existence theorem
for specified ground energy, not a construction uniform in an unknown ground
energy or a polynomial bound with energy-independent degree. The source-version
boundary is recorded in `docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
Selection of the word length and relative-error sample budget without an exact
energy input remains separate. The overall scalar itself is immaterial after
normalizing the output vectors, as the published Methods observes.

The normalization uses the proved overlap-loss factor `4` by sampling to error
`δ / 4`; the correction to the printed witness-normalization step is recorded
in `docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, Claim `c:errorreduction`,
lines 580--592 of `algo53.tex`, and the published Methods, Proposition 1,
p. 6, https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf,
DOI 10.1038/nphys3345.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- The sampled normalized power constructs a left-factor family that improves every
half-viable input family at a chosen cut. Ground energy is specified before sampling.
LVV13, Claim c:errorreduction, lines 580--592; published Methods, Proposition 1, p. 6. -/
theorem exists_sampled_nn_errorReduction
    {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i.val (i.val + 2)))
    (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {p : ℕ} (hp : 0 < p) (hpD : 2 * (q : ℝ) ^ L < (4 : ℝ) ^ p) :
    let n := Fintype.card (Fin (L - 1)) + 1
    let Q := 8 / δ
    let η := δ / 8
    let m := ⌈((n : ℝ) - E0) / Δ * Real.log Q⌉₊
    let C := (1 - E0 / n)⁻¹
    let ℓ := ⌈16 * (p : ℝ) ^ 2 * (n : ℝ) ^ 2 *
      Real.exp (2 * E0 * Real.log Q / Δ) / η ^ 2⌉₊ + 1
    let u := ⌈((m : ℝ) / n + Real.log (2 * (n : ℝ) * ℓ)) / Real.log 2⌉₊
    let r := ℓ * q ^ (2 * u)
    0 < ℓ ∧ ∃ σ : Fin ℓ → Fin m → Option (Fin (L - 1)),
      let K := (ℓ : ℂ)⁻¹ • ∑ b,
        (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
      ‖K - ((C : ℂ) • (1 - (Fintype.card (Fin (L - 1)) + 1 : ℂ)⁻¹ • ∑ i, h i)) ^ m‖ < η ∧
      ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < δ / 4 ∧
      (∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u) ∧
      (∀ k : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) ≤ r) ∧
      ∀ i : ℕ, i ≤ L → ∃ (a : ℕ) (A : Fin a → LeftBlockMatrix L q i)
        (B : Fin a → RightBlockMatrix L q i),
        a ≤ r ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
          ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ r) ∧
        ∀ (s b : ℕ) (S : Finset (LeftBlockVector L q i)),
          IsViableMPS Ω s b (1 / 2) S →
          IsViableMPS Ω (a * s) (r * max 1 b) δ (errorReductionSet Finset.univ A S) := by
  classical
  intro n Q η m C ℓ u r
  have hQ : 1 ≤ Q := (le_div_iff₀ hδ).mpr (by linarith only [hδ1])
  have hη : 0 < η := div_pos hδ (by norm_num)
  have hsum : η + 1 / Q = δ / 4 := by
    dsimp only [η, Q]
    field_simp
    ring
  obtain ⟨hℓ, σ, hA, hProj, hcounts, hrank⟩ :=
    exists_sampled_nn_power_approximation_with_rank hq h hs hpos hu hΩ hHΩ hgap hΔ hQ hη hp hpD
  let K := (ℓ : ℂ)⁻¹ • ∑ b,
    (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
  have hProj' : ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < δ / 4 := by
    rwa [hsum] at hProj
  refine ⟨hℓ, σ, hA, hProj', hcounts, hrank, fun i hi ↦ ?_⟩
  obtain ⟨a, A, B, ha, hdec, hleft⟩ := exists_cutDecomposition_of_operatorSchmidtRank_le
    hi _ hrank
  refine ⟨a, A, B, ha, hdec, hleft, fun s b S hS ↦ ?_⟩
  have hred := hS.errorReduction_of_norm_sub_groundProjection_le
    (J := Finset.univ) hi hΩ hdec
    (fun j _ k hk hki ↦ hleft j k hk hki) hProj'.le (by linarith only [hδ1])
  have hcard : (Finset.univ : Finset (Fin a)).card = a := by simp
  simpa only [hcard, show 4 * (δ / 4) = δ by ring] using hred

end TNLean.MPS.AreaLaw

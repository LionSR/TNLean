/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledErrorReduction
import QICLean.Analysis.PositiveGapUniqueness
import QICLean.Analysis.OptimizedPureStateTraceError

/-!
# One sampled left-factor family for the entire ground line

Assume that the actual energy `E0` has a normalized ground vector satisfying
the positive lower-gap inequality. A reference vector is chosen internally.
The existing uniqueness theorem identifies every other normalized vector at
energy `E0` with a scalar multiple of this vector, and the scalar has norm one.
Their rank-one ground projections are therefore equal.

The sample is chosen before every normalized ground vector, every spatial cut,
and every viable input family. At a cut, its left and right factors are likewise
chosen before every normalized ground vector and viable input family. The same
sampled operator and the same factors give all the approximation, rank, size,
MPS bond and viability conclusions.

**Scope restriction (specified ground energy):** the energy `E0` is fixed before
the normalized-power parameters and the sample are selected. The positive
sample count retains `exp (2 * E0 * log (8 / δ) / Δ)`. Independence from the
choice of normalized ground vector does not remove this energy dependence or
provide word-length and sample-budget choices uniform in an unknown energy.
An overall scalar is immaterial after normalizing vectors; the budget issue
is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, Claim `c:errorreduction`,
lines 580--592 of `algo53.tex`, and the published Methods, Proposition 1,
p. 6, https://people.eecs.berkeley.edu/~vazirani/pubs/1dalg.pdf,
DOI 10.1038/nphys3345. The existence of one normalized vector with positive
rank-one lower gap is the unique-ground-state hypothesis, expressed without
choosing a representative in the conclusion.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- One sampled normalized power and its cut factors reduce viable-set error for
all unit vectors in the ground line simultaneously. No ground representative is
specified before the existential sample. LVV13, Claim c:errorreduction; published
Methods, Proposition 1, p. 6, with the specified-energy scope above. -/
theorem exists_sampled_nn_errorReduction_forall_ground_vectors
    {L q : ℕ} (hq : 1 ≤ q)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (h i) (interval L i.val (i.val + 2)))
    (hpos : ∀ i, (h i).PosSemidef) (hu : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ}
    (hground : ∃ Ω : EuclideanSpace ℂ (Fin L → Fin q), ‖Ω‖ = 1 ∧
      (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω ∧
      ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
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
      (∀ b a, WordMultiplicity.countsFinsupp (σ b) a < u) ∧
      (∀ k : ℕ, operatorSchmidtRank
        (Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L k) K) ≤ r) ∧
      (∀ Ω : EuclideanSpace ℂ (Fin L → Fin q), ‖Ω‖ = 1 →
        (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω →
        ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < δ / 4) ∧
      ∀ i : ℕ, i ≤ L → ∃ (a : ℕ) (A : Fin a → LeftBlockMatrix L q i)
        (B : Fin a → RightBlockMatrix L q i),
        a ≤ r ∧ Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i) K =
          ∑ j, A j ⊗ₖ B j ∧
        (∀ j k, 0 < k → k < i → operatorSchmidtRank
          (Entropy.cutOperator (n := fun _ : Fin i ↦ q) (leftBlock i k)
            ((A j).submatrix leftConfigOfFin leftConfigOfFin)) ≤ r) ∧
        ∀ Ω : EuclideanSpace ℂ (Fin L → Fin q), ‖Ω‖ = 1 →
          (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω →
          ∀ (s b : ℕ) (S : Finset (LeftBlockVector L q i)),
          IsViableMPS Ω s b (1 / 2) S →
          IsViableMPS Ω (a * s) (r * max 1 b) δ (errorReductionSet Finset.univ A S) := by
  classical
  intro n Q η m C ℓ u r
  obtain ⟨Ω₀, hΩ₀, heig₀, hgap₀⟩ := hground
  obtain ⟨hℓ, σ, hA, hProj, hcounts, hrank, hfac⟩ := exists_sampled_nn_errorReduction
    hq h hs hpos hu hΩ₀ heig₀ hgap₀ hΔ hδ hδ1 hp hpD
  let K := (ℓ : ℂ)⁻¹ • ∑ b,
    (C : ℂ) ^ m • (List.ofFn fun j ↦ 1 - (σ b j).elim 0 h).prod
  have hprojEq (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
      (heig : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω) :
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) =
        vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)) := by
    have hcol := hgap₀.eq_inner_smul_of_gap hΔ hΩ₀ heig
    let c := ⟪Ω₀, Ω⟫_ℂ
    have hc : ‖c‖ = 1 := by
      have hn := congrArg norm hcol
      simpa only [norm_smul, hΩ, hΩ₀, mul_one] using hn.symm
    calc
      _ = vecMulVec (c • WithLp.ofLp Ω₀) (star (c • WithLp.ofLp Ω₀)) :=
        congrArg (fun v : EuclideanSpace ℂ (Fin L → Fin q) ↦
          vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v))) hcol
      _ = (‖c‖ ^ 2 : ℝ) • vecMulVec (WithLp.ofLp Ω₀) (star (WithLp.ofLp Ω₀)) :=
        vecMulVec_ofLp_smul_self Ω₀ c
      _ = _ := by rw [hc, one_pow, one_smul]
  have hProjAll (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
      (heig : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω) :
      ‖K - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ < δ / 4 := by
    rw [hprojEq Ω hΩ heig]
    exact hProj
  refine ⟨hℓ, σ, hA, hcounts, hrank, hProjAll, fun i hi ↦ ?_⟩
  obtain ⟨a, A, B, ha, hdec, hleft, _⟩ := hfac i hi
  refine ⟨a, A, B, ha, hdec, hleft, fun Ω hΩ heig s b S hS ↦ ?_⟩
  have hred := hS.errorReduction_of_norm_sub_groundProjection_le
    (J := Finset.univ) hi hΩ hdec
    (fun j _ k hk hki ↦ hleft j k hk hki) (hProjAll Ω hΩ heig).le
    (by linarith only [hδ1])
  have hcard : (Finset.univ : Finset (Fin a)).card = a := by simp
  simpa only [hcard, show 4 * (δ / 4) = δ by ring] using hred

end TNLean.MPS.AreaLaw

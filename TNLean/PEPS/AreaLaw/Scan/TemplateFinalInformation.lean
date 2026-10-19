/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TemplateScanner
import TNLean.PEPS.AreaLaw.Scan.SourceRoundedInformation
import TNLean.PEPS.AreaLaw.Scan.TemplateSourceEntropy
import TNLean.PEPS.AreaLaw.LatticeCounts
import Mathlib.Data.Fintype.EquivFin

/-!
# Original-template information from the uniform safe-box estimate

Construct the actual physical scanner and discharge its graph, depth,
anchor, multiplicity, volume, row and clearance premises. The sole remaining
analytic input beyond the physical gapped-ground-state model is the genuine
uniform safe-box estimate at the specified final exponent. The original
state and literal template regions appear in the conclusion.

This theorem does not derive the improved safe-box exponent and does not
claim an unconditional Proposition 9.6 or the full area law. It leaves the
already accepted cut/volume packaging theorem unchanged.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58, 571--590 and 808--944, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof reused.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

open _root_.TNLean.PEPS.AreaLaw.Geometry

private theorem template_target_volume {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl) :
    (T.points.card : ℝ) ≤ 9 * (n : ℝ) ^ 2 := by
  have hp : (1 : ℝ) ≤ T.pieceCount := by exact_mod_cast T.pieceCount_pos
  have hm : (1 : ℝ) ≤ Ctpl * T.pieceCount := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ Ctpl by linarith))
      (sub_nonneg.mpr hp)]
  have hs : (s₀ : ℝ) ≤ n := by
    have h := (le_mul_of_one_le_left (by positivity : (0 : ℝ) ≤ s₀ + 1) hm).trans
      T.scale
    linarith
  have hcard : (T.points.card : ℝ) ≤ 9 * (n : ℝ) * s₀ := by
    exact_mod_cast template_card_le T (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 9 * n)]

private theorem template_scanner_clearance
    {Ctpl D₀ : ℝ} {n s₀ L m D r₀ K : ℕ} (T : Template Ctpl n s₀)
    {Z : Finset (ℤ × ℤ)} (hsep : T.IsSeparated D₀ Z) (hD₀ : 1 ≤ D₀)
    (hL : L ≤ s₀) (hr : 2 * r₀ ≤ D) (hDm : 4 * D ≤ m)
    (hK : 1 ≤ K) (hKL : 8 * K * m ≤ L) :
    ∀ t ∈ T.points, ∀ z ∈ Z,
      ((2 * L + 10 * r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  have hmL : 8 * m ≤ L := by
    have h := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 8 hK)
    omega
  have hrL : 5 * r₀ ≤ L := by omega
  have hbudget : 2 * L + 10 * r₀ ≤ 4 * s₀ := by omega
  have hbudgetR : ((2 * L + 10 * r₀ : ℕ) : ℝ) ≤ 4 * (s₀ : ℝ) := by
    exact_mod_cast hbudget
  have hDmul := mul_le_mul_of_nonneg_right hD₀ (Nat.cast_nonneg s₀)
  intro t ht z hz
  have hclear := hsep t ht z hz
  have hresult : ((2 * L + 10 * r₀ : ℕ) : ℝ) <
      max |(t.1 : ℝ) - z.1| |(t.2 : ℝ) - z.2| := by
    nlinarith
  unfold ambientSupDistance
  exact_mod_cast hresult

/-- The anchor multiplicity `2 ^ (2 R (R + 1))` of the final template scanner: the number of
subsets of an `R`-ball containing a fixed site (`08-scanner.tex`, lines 32--58). -/
def collarMultiplicity (R : ℕ) : ℕ :=
  2 ^ ((1 + 2 * R * (R + 1)) - 1)

/-- The explicit collar information coefficient `C_m` of Proposition 9.6 at the safe-box constant
`Cbox`: the final-scale source information coefficient at target-volume constant `9` and
source-entropy coefficient `templateSourceEntropyConstant q ε_box Cbox`, where
`g = Δ / positiveNormalization 1 (Δ / 2) J` (`08-scanner.tex`, lines 808--944). -/
noncomputable def collarConstant (q : ℕ) (J Δ Cbox : ℝ) : ℝ :=
  CollarScan.sourceFinalInformationConstant q
    (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J) 9
    (templateSourceEntropyConstant q (Exponents.boxError : ℝ) Cbox)

/-- The collar information coefficient is positive. -/
theorem collarConstant_pos {q : ℕ} (hq : 1 ≤ q) (J Δ Cbox : ℝ) : 0 < collarConstant q J Δ Cbox :=
  CollarScan.sourceFinalInformationConstant_pos hq _ (by norm_num)
    (templateSourceEntropyConstant_nonneg _ _ _)

/-- The explicit collar size threshold `N₁` of Proposition 9.6 at the safe-box constant `Cbox`:
the rounded-scale source information threshold at target-volume constant `9`, charge constant
`3 μ`, multiplicity `μ = collarMultiplicity R`, rate `P = 1` and source-entropy coefficient
`templateSourceEntropyConstant q ε_box Cbox`. The truncation constant `Ctr` and the transport
constants `ct, Cent, eent, Cen, een` are its remaining inputs (`08-scanner.tex`,
lines 808--944). -/
noncomputable def collarThreshold (q R : ℕ) (J Δ Cbox Ctr ct Cent eent Cen een : ℝ) : ℕ :=
  CollarScan.sourceRoundedInformationThreshold q R
    (Δ / SpectralFilter.positiveNormalization 1 (Δ / 2) J) 9
    (3 * (collarMultiplicity R : ℝ)) (collarMultiplicity R) 1
    (templateSourceEntropyConstant q (Exponents.boxError : ℝ) Cbox) Ctr ct Cent eent Cen een

/-- The collar size threshold is at least two. -/
theorem two_le_collarThreshold (q R : ℕ) (J Δ Cbox Ctr ct Cent eent Cen een : ℝ) :
    2 ≤ collarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een :=
  CollarScan.two_le_sourceRoundedInformationThreshold _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Both final information powers for every separated template in the original gapped ground
state, as in `exists_template_final_mutualInformation_of_boxEntropy_of_threshold_le`, at the named
truncation constant `latticeTruncationRadiusConstant R J Δ 10` (target-volume constant `9`) and at
any transport constants with `0 < ct` satisfying the finite-family transport bound.
Source: `08-scanner.tex`, lines 808--944. -/
theorem template_final_mutualInformation_of_boxEntropy_explicit
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD₀ : 1 ≤ D₀)
    {J Δ Ctpl Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hCtpl : 24 ≤ Ctpl) (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ)))
    {ct Cent eent Cen een : ℝ} (hct : 0 < ct)
    (htransport : CollarScan.FiniteFamilyTransportBound ct Cent eent Cen een) :
      ∀ n s₀ : ℕ, collarThreshold q R J Δ Cbox (latticeTruncationRadiusConstant R J Δ 10) ct Cent
          eent Cen een ≤ n →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Template Ctpl n s₀),
            T.IsSeparated D₀ (boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ ≤ s₀ →
            let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
            let X := A.filter fun x ↦ x.val ∈ T.points
            let S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T.points L
            let β := fun _ : Site Λ ↦ Fin q
            2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                collarConstant q J Δ Cbox * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
              2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                collarConstant q J Δ Cbox *
                  (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  classical
  let : NeZero q := ⟨by omega⟩
  let μ : ℕ := collarMultiplicity R
  let C₁ : ℝ := 3 * (μ : ℝ)
  have hC₁ : 0 < C₁ := by dsimp [C₁, μ, collarMultiplicity]; positivity
  set Ctr := latticeTruncationRadiusConstant R J Δ 10 with hCtrDef
  have hCtr : 0 < Ctr := latticeTruncationRadiusConstant_pos R hΔ (by norm_num)
  have hsource :=
    CollarScan.sourceTarget_finalScale_mutualInformation_of_rounded_scales_explicit
      hq R hJ hΔ (by norm_num : (0 : ℝ) ≤ 9) hC₁ μ le_rfl 1
      (by norm_num [Exponents.scannerNu]) hct htransport (Ctr := Ctr)
      (by norm_num [hCtrDef])
  have hentropy := template_final_source_entropy_bounds_of_boxEntropy q R D₀ hq hD₀ hCbox hbox
  have hbound := hsource _ (templateSourceEntropyConstant_nonneg q (Exponents.boxError : ℝ) Cbox)
  intro n s₀ hn Λ h E₀ Ω hgs A T hsep hL
  let : LinearOrder (AdmissibleSupport Λ R) :=
    LinearOrder.lift' (Fintype.equivFin (AdmissibleSupport Λ R))
      (Fintype.equivFin (AdmissibleSupport Λ R)).injective
  let S := finalTemplateScanner T.nonempty A R n Ctr C₁
  let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
  have hnS : collarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een ≤ n := hn
  have hnG : finalScannerAdmissibilityThreshold Ctr ≤ n := by
    unfold collarThreshold CollarScan.sourceRoundedInformationThreshold at hn
    exact (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := (two_le_collarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hLpos : 1 ≤ L := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow hnR
      (by norm_num [Exponents.scannerEll] : 0 ≤ 1 - (Exponents.scannerEll : ℝ)))
  have hscales := finalScanner_admissibility_of_threshold_le hCtr.le hnG
  change 2 * S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧ 4 * S.D ≤ S.m ∧
    1 ≤ S.K ∧ 8 * S.K * S.m ≤ L at hscales
  have hanchor : ∀ i, S.anchor i ∈ i.val := fun i ↦ i.property.1.choose_spec
  have hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ :=
    fun x ↦ card_anchor_fiber_le S.anchor hanchor x
  have hrows : ∀ r : ℕ, 1 ≤ r → r ≤ L →
      (ambientDilation T.points r \ ambientDilation T.points (r - 1)).card ≤ n := by
    intro r hr hrL
    exact template_layer_card_le T hCtpl r hr (hrL.trans hL)
  have hclear : ∀ t ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z :=
    template_scanner_clearance T hsep (by exact_mod_cast hD₀) hL
      hscales.1 hscales.2.2.1 hscales.2.2.2.1 hscales.2.2.2.2
  obtain ⟨htarget, hprefix⟩ := hentropy Λ h E₀ Ω hgs S T hCtpl hsep rfl L hLpos hL
  have hinfo := hbound Λ T.points T.nonempty h S E₀ Ω hgs rfl hanchor hnS
    rfl rfl rfl rfl rfl (template_target_volume T hCtpl) rfl
    hrows hmult hclear htarget hprefix
  have htrunc (r : ℕ) : S.truncationSet r =
      A.filter fun x ↦ x.val ∈ ambientDilation T.points r :=
    finalTemplateScanner_truncationSet T.nonempty A R n Ctr C₁ r
  dsimp only at hinfo
  rw [htrunc] at hinfo
  simpa only [S, finalTemplateScanner, collarConstant] using hinfo

/-- The literal uniform safe-box estimate at the improved exponent implies both final
information powers for every separated template in the original gapped ground state, with the
explicit coefficient `collarConstant q J Δ Cbox` at every `n` from the explicit threshold
`collarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een` on. The truncation constant `Ctr` and the
transport constants `ct, Cent, eent, Cen, een` remain existential and precede the entire physical
instance. Source: `08-scanner.tex`, lines 808--944. -/
theorem exists_template_final_mutualInformation_of_boxEntropy_of_threshold_le
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD₀ : 1 ≤ D₀)
    {J Δ Ctpl Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hCtpl : 24 ≤ Ctpl) (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ n s₀ : ℕ, collarThreshold q R J Δ Cbox Ctr ct Cent eent Cen een ≤ n →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Template Ctpl n s₀),
            T.IsSeparated D₀ (boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ ≤ s₀ →
            let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
            let X := A.filter fun x ↦ x.val ∈ T.points
            let S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T.points L
            let β := fun _ : Site Λ ↦ Fin q
            2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                collarConstant q J Δ Cbox * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
              2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                collarConstant q J Δ Cbox *
                  (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨ct, Cent, eent, Cen, een, hct, htransport⟩ :=
    CollarScan.exists_finiteFamilyTransportBound
  exact ⟨_, ct, Cent, eent, Cen, een,
    latticeTruncationRadiusConstant_pos R hΔ (by norm_num : (0 : ℝ) ≤ 10), hct,
    template_final_mutualInformation_of_boxEntropy_explicit q R D₀ hq hD₀ hJ hΔ hCtpl hCbox hbox
      hct htransport⟩

/-- The literal uniform safe-box estimate at the improved exponent implies
both final information powers for every separated template in the original
gapped ground state. The scanner, support anchors and all geometric inputs
are constructed or derived; none is an additional hypothesis. Constants and
thresholds precede the entire physical instance. The fixed-exponent safe-box
estimate remains an explicit analytic premise. Source: `08-scanner.tex`,
lines 808--944. -/
theorem exists_template_final_mutualInformation_of_boxEntropy
    (q R D₀ : ℕ) (hq : 1 ≤ q) (hD₀ : 1 ≤ D₀)
    {J Δ Ctpl Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hCtpl : 24 ≤ Ctpl) (hCbox : 0 ≤ Cbox)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤
      Cbox * (r : ℝ) ^ (1 + (Exponents.boxError : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n s₀ : ℕ, N ≤ n →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (T : Template Ctpl n s₀),
            T.IsSeparated D₀ (boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ ≤ s₀ →
            let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
            let X := A.filter fun x ↦ x.val ∈ T.points
            let S₀ := A.filter fun x ↦ x.val ∈ ambientDilation T.points L
            let β := fun _ : Site Λ ↦ Fin q
            2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                C * (n : ℝ) ^ (62497 / 62500 : ℝ) ∧
              2 * FiniteProduct.mutualInformation β Ω X S₀ᶜ ≤
                C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, -, -, hall⟩ :=
    exists_template_final_mutualInformation_of_boxEntropy_of_threshold_le q R D₀ hq hD₀ hJ hΔ hCtpl
      hCbox hbox
  exact ⟨_, collarConstant_pos hq J Δ Cbox, _, two_le_collarThreshold q R J Δ Cbox Ctr ct Cent
    eent Cen een, hall⟩

end TNLean.PEPS.AreaLaw.Scan

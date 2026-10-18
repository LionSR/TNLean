/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryBirthTemplates
import TNLean.PEPS.AreaLaw.Geometry.BeltReplacementTemplates
import TNLean.PEPS.AreaLaw.Geometry.DescendantCutClearance
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLength
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthRank
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyExplicitThresholds

/-!
# Templates for remembered birth regions

Every nondummy remembered birth region with a lattice point admits a template
whose point set is its full ambient lattice sample. The prescribed primary,
belt and replacement scales satisfy both endpoint clearance conditions after
uniform choices of the stopping scale and lower layer index.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `10-geometry.tex`, lines 709–750, with creation
at lines 393–417 and retention at lines 565–568.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The lower-layer threshold of the birth templates: the largest of
`fineScaleIndexThreshold S_*`, `descendantCutClearanceThreshold D₀ C_B` and
`primaryScaleLimitThreshold C_P (1/4)`. Auxiliary to the explicit constant of
Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`, rows 37–38 and 74).
Source: area-law Section 11, `10-geometry.tex`, lines 742–750 and 756–774. -/
noncomputable def birthTemplateLayerThreshold (D₀ CP CB Sstar : ℝ) : ℕ :=
  max (fineScaleIndexThreshold Sstar)
    (max (descendantCutClearanceThreshold D₀ CB) (primaryScaleLimitThreshold CP (1 / 4)))

/-- **Templates for remembered birth regions, with explicit constants.** With
`C_P = primaryScannerConstant C_tpl` and `C_B = beltScannerConstant C_tpl`, every
stopping scale `S_* ≥ repairMarginThreshold (1/128)`, every layer width
`C₀ > 4 D₀` and every lower layer index
`k₀ ≥ birthTemplateLayerThreshold D₀ C_P C_B S_*`, every nondummy remembered
birth region with a lattice point has a template whose point set is its full
lattice sample, with both endpoint clearances.
Source: area-law Section 11, `10-geometry.tex`, lines 709–750, with the
replacement instructions of lines 393–417 and retention of lines 565–568. -/
theorem repairStage_birth_templates_of_le (Ctpl : ℝ) (hCtpl : 1 ≤ Ctpl) (D₀ : ℝ)
    {Sstar : ℝ} (hS : repairMarginThreshold (1 / 128) ≤ Sstar) (C : ℕ) (hWidth : 4 * D₀ < C)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ) (hC : 2 ≤ C)
    (h₀ : 50000000 ≤ k₀)
    (hK : birthTemplateLayerThreshold D₀ (primaryScannerConstant Ctpl)
      (beltScannerConstant Ctpl) Sstar ≤ k₀) (N : ℕ) :
    let D := repairStage o Λ A C k₀ hC h₀ Sstar N
    ∀ x : D.regionIndex, x ≠ D.dummy →
      ∀ w : ℤ × ℤ, integerPoint w ∈ D.birth x →
        let rank := repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N x
        let u := repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N x
        let n : ℕ := if rank = 0 then
          ⌈primaryScannerConstant Ctpl * u ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
        else ⌈beltScannerConstant Ctpl * u⌉₊
        ∃ s₀ : ℕ, ∃ T : Template Ctpl n s₀,
          (s₀ : ℝ) = (if rank ≤ 1 then u else 2 * u) ∧
            (∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ D.birth x) ∧
            T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
            ∀ y ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
              2 * (n : ℝ) ^ (Exponents.beta : ℝ) <
                (Scan.ambientSupDistance y z : ℝ) := by
  classical
  set CP := primaryScannerConstant Ctpl
  set CB := beltScannerConstant Ctpl
  have hPrimary := primaryScannerConstant_spec Ctpl
  have hCB16 : 16 * Ctpl ≤ CB := by simp only [CB, beltScannerConstant]; linarith
  have hStop : 1 ≤ Sstar := (one_le_repairMarginThreshold _).trans hS
  have hKD := descendant_birthTemplate_cutClearance_of_le hS C D₀ CB
  have hKB := initialBelt_birthTemplate_cutClearance_of_le (D₀ := D₀) (CB := CB)
  set KP : ℕ := primaryScaleLimitThreshold CP (1 / 4)
  have hKP (k : ℕ) (hk : KP ≤ k) :=
    primaryScaleLimits_of_primaryScaleLimitThreshold_le CP
      (show (0 : ℝ) < 1 / 4 by norm_num) hk
  have hKD₀ : max (fineScaleIndexThreshold Sstar) (descendantCutClearanceThreshold D₀ CB) ≤
      k₀ := max_le (le_of_max_le_left hK) (le_of_max_le_left (le_of_max_le_right hK))
  have hKB₀ : descendantCutClearanceThreshold D₀ CB ≤ k₀ :=
    le_of_max_le_left (le_of_max_le_right hK)
  have hKP₀ : KP ≤ k₀ := le_of_max_le_right (le_of_max_le_right hK)
  induction N with
  | zero =>
    let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose hchoice
    let hb := Classical.choose_spec hchoice
    let b := Classical.choose hb
    dsimp only
    intro x hx w hw
    rcases x with u | (p | B)
    · exact (hx (congrArg Sum.inl (Subsingleton.elim u ()))).elim
    · rcases p with ⟨k, J⟩
      have hrank : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar 0
          (Sum.inr (Sum.inl ⟨k, J⟩)) = 0 := rfl
      have hlength : repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar 0
          (Sum.inr (Sum.inl ⟨k, J⟩)) = (2 : ℝ) ^ k.val := rfl
      simp only [hrank, hlength, show (0 : ℕ) ≤ 1 by omega, ite_true]
      have hmem : integerPoint w ∈ primaryBirthRegion o k.val (fineScaleIndex k.val)
          (pitchScaleIndex k.val) (boundaryEndpoints Λ A) C
          (a k.val).val (b k.val).val J.val := hw
      rw [primaryBirthRegion_eq_iUnion_primaryFragment] at hmem
      obtain ⟨z, hz, -⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨hscale, hdiam⟩ := hPrimary o k.val (fineScaleIndex k.val)
        (boundaryEndpoints Λ A) C (a k.val).val (b k.val).val J.val
      let T := primaryBirthTemplate o k.val (fineScaleIndex k.val) (pitchScaleIndex k.val)
        (boundaryEndpoints Λ A) C (a k.val).val (b k.val).val J.val ⟨z, hz⟩ hscale hdiam
      have hpoints : ∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈
          primaryBirthRegion o k.val (fineScaleIndex k.val) (pitchScaleIndex k.val)
            (boundaryEndpoints Λ A) C (a k.val).val (b k.val).val J.val := by
        intro y
        have heq := congrArg (y ∈ ·) (primaryBirthTemplate_points o k.val
          (fineScaleIndex k.val) (pitchScaleIndex k.val) (boundaryEndpoints Λ A) C
          (a k.val).val (b k.val).val J.val ⟨z, hz⟩ hscale hdiam)
        simpa only [Finset.mem_coe, Set.mem_preimage] using (Iff.of_eq heq)
      refine ⟨2 ^ k.val, T, by simp, hpoints, ?_, ?_⟩
      · exact primaryBirthTemplate_isSeparated o k.val (fineScaleIndex k.val)
          (pitchScaleIndex k.val) (boundaryEndpoints Λ A) C hWidth
          (a k.val).val (b k.val).val J.val ⟨z, hz⟩ hscale hdiam
      · intro y hy v hv
        have hd := dyadicLayer_dist_lower o k.val (boundaryEndpoints Λ A) C
          (integerPoint y) (closure_mono Set.inter_subset_left ((hpoints y).mp hy)) v hv
        have hbeta := (hKP k.val (hKP₀.trans k.property)).2.2
        have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
        have hpos : (0 : ℝ) < 2 ^ k.val := by positivity
        have hmargin : 2 * (primaryScannerScale CP k.val : ℝ) ^
            (Exponents.beta : ℝ) < (C : ℝ) * 2 ^ k.val := by nlinarith
        have hdist : dist (integerPoint y) (integerPoint v) =
            (Scan.ambientSupDistance y v : ℝ) := by
          simp [integerPoint, Prod.dist_eq, Real.dist_eq, Scan.ambientSupDistance]
        rw [hdist] at hd
        exact hmargin.trans_le hd
    · have hrank : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar 0
          (Sum.inr (Sum.inr B)) = 1 := rfl
      have hlength : repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar 0
          (Sum.inr (Sum.inr B)) = (2 : ℝ) ^ fineScaleIndex B.1.val := rfl
      simp only [hrank, hlength, show (1 : ℕ) ≤ 1 by omega,
        show (1 : ℕ) ≠ 0 by omega, ite_true, ite_false]
      obtain ⟨T, -, hpoints⟩ := initialBelt_exists_template Ctpl CB hCtpl hCB16 o k₀
        (boundaryEndpoints Λ A) C a b hC h₀ (Sum.inr (Sum.inr B)) B rfl w hw
      have hcut := (hKB o k₀ (boundaryEndpoints Λ A) C a b hC h₀ hKB₀
        (Sum.inr (Sum.inr B)) B rfl).2 T
      refine ⟨2 ^ fineScaleIndex B.1.val, T, by simp, hpoints,
        hcut (fun t ht ↦ (hpoints t).mp ht) ?_ le_rfl⟩
      push_cast
      have hnonneg : (0 : ℝ) ≤ 2 ^ fineScaleIndex B.1.val := by positivity
      linarith
  | succ N ih =>
    dsimp only
    intro x hx w hw
    rcases x with x | q
    · exact ih x (fun h ↦ hx (congrArg Sum.inl h)) w hw
    · have hparent : repairRegionParent o Λ A C k₀ hC h₀ Sstar N (Sum.inr q) =
          some q.2.1.val := rfl
      have hrank : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (N + 1) (Sum.inr q) =
          N + 2 := rfl
      have hlength : repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar
          (N + 1) (Sum.inr q) =
          repairHalfSide ((repairStage o Λ A C k₀ hC h₀ Sstar N).scale q.2.1.val) := rfl
      simp only [hrank, hlength, show N + 2 ≠ 0 by omega,
        show ¬N + 2 ≤ 1 by omega, ite_false]
      obtain ⟨s₀, hs₀, T, -, hpoints⟩ :=
        repairReplacement_exists_template o Λ A C k₀ hC h₀ Sstar hStop Ctpl CB hCtpl le_rfl N
          (Sum.inr q) q.2.1.val hparent w hw
      obtain ⟨k, hk, hu, hfar, hcut⟩ :=
        hKD o Λ A k₀ hC h₀ hKD₀ N (Sum.inr q) q.2.1.val hparent
      exact ⟨s₀, T, hs₀, hpoints,
        hcut T (fun t ht ↦ (hpoints t).mp ht) hs₀.le le_rfl⟩

/-- Uniform templates for the full ambient lattice samples of actual remembered
birth regions. The primary and belt coefficients are chosen before the endpoint
constant and all geometric data. At every generation the primitive size is the
remembered characteristic length for primaries and initial belts, and twice
that length for replacements. Both endpoint clearances hold after uniform
stopping-scale and lower-layer choices. The primary part of the lower-layer
choice is the explicit layer `primaryScaleLimitThreshold C_P (1 / 4)`; all
constants are explicit in `repairStage_birth_templates_of_le`.

Auxiliary to area-law Section 11, `10-geometry.tex`, lines 709–750, with the
replacement instructions of lines 393–417 and retention of lines 565–568.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/
theorem exists_uniform_repairStage_birth_templates (Ctpl : ℝ) (hCtpl : 1 ≤ Ctpl) :
    ∃ CP CB : ℝ, 1 ≤ CP ∧ 0 < CB ∧
      ∀ D₀ : ℝ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
        ∀ Sstar : ℝ, T₀ ≤ Sstar →
          ∀ C : ℕ, 4 * D₀ < (C : ℝ) → ∃ K : ℕ,
            ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
              (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
                ∀ N : ℕ,
                  let D := repairStage o Λ A C k₀ hC h₀ Sstar N
                  ∀ x : D.regionIndex, x ≠ D.dummy →
                    ∀ w : ℤ × ℤ, integerPoint w ∈ D.birth x →
                      let rank := repairStageBirthRank o Λ A C k₀ hC h₀ Sstar N x
                      let u := repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar N x
                      let n : ℕ := if rank = 0 then
                        ⌈CP * u ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ else ⌈CB * u⌉₊
                      ∃ s₀ : ℕ, ∃ T : Template Ctpl n s₀,
                        (s₀ : ℝ) = (if rank ≤ 1 then u else 2 * u) ∧
                          (∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ D.birth x) ∧
                          T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
                          ∀ y ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
                            2 * (n : ℝ) ^ (Exponents.beta : ℝ) <
                              (Scan.ambientSupDistance y z : ℝ) :=
  ⟨_, _, one_le_primaryScannerConstant Ctpl, beltScannerConstant_pos hCtpl, fun D₀ ↦
    ⟨_, one_le_repairMarginThreshold _, fun _ hS C hWidth ↦
      ⟨_, repairStage_birth_templates_of_le Ctpl hCtpl D₀ hS C hWidth⟩⟩⟩

end TNLean.PEPS.AreaLaw.Geometry

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem
import TNLean.PEPS.AreaLaw.Geometry.PrimaryBirthSeparation
import TNLean.PEPS.AreaLaw.Geometry.RepairActualBirthTemplates
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLengthLowerBound
import TNLean.PEPS.AreaLaw.Geometry.RepairOrderedBirthSeparation
import TNLean.PEPS.AreaLaw.Geometry.RepairOrderedPartition
import TNLean.PEPS.AreaLaw.Geometry.RepairRankZeroAncestry
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedErrorSum
import TNLean.PEPS.AreaLaw.Geometry.RepairUniformExceptionalSites

/-!
# Two families with separated birth templates

The geometric construction gives a finite ordered partition of every cut
with positive edge boundary into an exceptional set and two labelled families
of nonempty pieces. Each piece lies in the full lattice sample of its
remembered birth region. The templates have the prescribed lower scale,
dilation bound, endpoint clearance and clearance from earlier pieces of the
same label. Their inverse hundredth powers have a uniform boundary bound.
All constants are chosen before the finite domain and cut.

The construction first uses a positive template constant at least as large
as the specified one. Decreasing that constant changes only the template
scale inequality; all polygons, lattice points and size parameters are kept.
Thus the parameterized assertion is valid for every real template constant.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Proposition 11.2 (`prop:two-families`), `10-geometry.tex`,
lines 98–140, with the construction and final estimates at lines 709–798.
The template definition is Definition 9.3 (`scanner:template`),
`08-scanner.tex`, lines 536–564.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- **Proposition 11.2** (`prop:two-families`). The ordered two-family
construction satisfies all template, clearance and summability requirements
for every fixed pair of template parameters. The repair metric hypotheses,
large-scale conditions and common empty generation are derived within the
construction, rather than supplied as additional hypotheses.

Source: area-law Proposition 11.2, `10-geometry.tex`, lines 98–140;
scanner scales and final construction, lines 709–798; Definition 9.3,
`08-scanner.tex`, `scanner:template`, lines 536–564.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem twoFamilyDecomposition (D₀ Ctpl : ℝ) : TwoFamilyDecomposition D₀ Ctpl := by
  classical
  obtain ⟨CP, CB, hCP, hCB, hTemplates⟩ :=
    Geometry.exists_uniform_repairStage_birth_templates (max Ctpl 1) (le_max_right _ _)
  obtain ⟨Ttpl, hTtpl, hTemplates⟩ := hTemplates D₀
  obtain ⟨c₁, hc₁, Tsep, hSeparation⟩ := Geometry.exists_birthSeparation
  obtain ⟨Tmetric, hMetric⟩ := Geometry.exists_repairMetricHypotheses
    (a₀ := (1 : ℝ) / 4) (by norm_num) le_rfl
  intro nstar hnstar
  obtain ⟨UF, hUF⟩ := Filter.eventually_atTop.mp
    (Geometry.eventually_fine_clearance hc₁ hCB.le)
  obtain ⟨UB, hUB⟩ := Filter.eventually_atTop.mp
    (Geometry.eventually_beltReplacementScaleLimit CB (show (0 : ℝ) < 1 by norm_num))
  let U : ℝ := max UF (max UB (max 2 ((nstar : ℝ) / CB)))
  let Sstar : ℝ := max Ttpl (max Tsep (max Tmetric (max U 2)))
  have hStops : Ttpl ≤ Sstar ∧ Tsep ≤ Sstar ∧ Tmetric ≤ Sstar ∧
      U ≤ Sstar ∧ 2 ≤ Sstar := by
    dsimp only [Sstar]
    exact ⟨le_max_left _ _, le_max_of_le_right (le_max_left _ _),
      le_max_of_le_right (le_max_of_le_right (le_max_left _ _)),
      le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))),
      le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))⟩
  obtain ⟨KP, hKP⟩ := Filter.eventually_atTop.mp
    (Geometry.eventually_primaryScaleLimits CP (show (0 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨KN, hKN⟩ := Filter.eventually_atTop.mp
    (Geometry.le_primaryScannerScale (lt_of_lt_of_le one_pos hCP) nstar)
  obtain ⟨C, hCgt⟩ := exists_nat_gt (max (4 * D₀) (2 : ℝ))
  have hC : 2 ≤ C := by exact_mod_cast (le_max_right (4 * D₀) 2).trans hCgt.le
  have hWidth : 4 * D₀ < (C : ℝ) := (le_max_left _ _).trans_lt hCgt
  obtain ⟨KT, hKT⟩ := hTemplates Sstar hStops.1 C hWidth
  obtain ⟨KS, hKS⟩ := hSeparation Sstar hStops.2.1 C
  obtain ⟨KM, hKM⟩ := hMetric Sstar hStops.2.2.1 C
  obtain ⟨KU, hKU⟩ := Geometry.exists_uniform_repairStage_positive_rank_length_lower_bound U
  let k₀ : ℕ := max 50000000 (max KT (max KS (max KM (max KU (max KP KN)))))
  have hk₀ : 50000000 ≤ k₀ ∧ KT ≤ k₀ ∧ KS ≤ k₀ ∧ KM ≤ k₀ ∧
      KU ≤ k₀ ∧ KP ≤ k₀ ∧ KN ≤ k₀ := by
    dsimp only [k₀]
    omega
  rcases hk₀ with ⟨h₀, hKT₀, hKS₀, hKM₀, hKU₀, hKP₀, hKN₀⟩
  have hStop : 1 < Sstar := one_lt_two.trans_le hStops.2.2.2.2
  obtain ⟨L, hL, hResidual⟩ := Geometry.exists_uniform_repairStageExceptionalSites_bound
    C k₀ hC h₀ hStop
  obtain ⟨E, hE, hError⟩ := Geometry.exists_uniform_repairStage_retained_error_sum_bound
    (lt_of_lt_of_le one_pos hCP) hStop
  refine ⟨max L (E * (2 * (C : ℝ) + 1) ^ 2), ?_⟩
  intro Λ A hboundary
  have h := hKM Geometry.dyadicOrigin Λ A k₀ hC h₀ hKM₀
  obtain ⟨N, hN, hRes⟩ := hResidual Geometry.dyadicOrigin Λ A (1 / 4) h
  obtain ⟨N, rfl⟩ : ∃ m, N = 0 + m := ⟨N, (Nat.zero_add N).symm⟩
  let : IsEmpty
      (Geometry.repairStage Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N)).markIndex := hN
  obtain ⟨P, e, hpiece, hfamily, hresidual, hmono⟩ :=
    h.exists_orderedTwoFamilyPartition_of_isEmpty hStop.le hboundary (0 + N)
  let D := Geometry.repairStage Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N)
  let I : Type := D.RetainedRegionIndex Λ A
  let rank : I → ℕ := fun i ↦
    Geometry.repairStageBirthRank Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N) i.val
  let u : I → ℝ := fun i ↦
    Geometry.repairStageCharacteristicLength
      Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N) i.val
  let nI : I → ℕ := fun i ↦ if rank i = 0 then
    ⌈CP * (u i) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ else ⌈CB * u i⌉₊
  let : Finite I :=
    (Geometry.finite_and_card_repairStage_retainedRegionIndex_le
      Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N)).1
  let : Fintype I := Fintype.ofFinite I
  have hTemplate (i : I) : ∃ s₀ : ℕ, ∃ T : Geometry.Template (max Ctpl 1) (nI i) s₀,
      (s₀ : ℝ) = (if rank i ≤ 1 then u i else 2 * u i) ∧
        (∀ y : ℤ × ℤ, y ∈ T.points ↔ Geometry.integerPoint y ∈ D.birth i.val) ∧
        T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) ∧
        ∀ y ∈ T.points, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
          2 * (nI i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance y z : ℝ) := by
    obtain ⟨w, hw⟩ := i.property.2
    have hb : Geometry.integerPoint w.val ∈ D.birth i.val :=
      Geometry.repairStage_current_subset_birth Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N)
        i.val (Finset.mem_filter.mp hw).2
    exact hKT Geometry.dyadicOrigin Λ A k₀ hC h₀ hKT₀ (0 + N) i.val i.property.1 w.val hb
  choose sI TI hsI hpoints hsep hcut using hTemplate
  let hchoice := (Classical.choose_spec Geometry.exists_uniform_separated_initial_marks).2
    Geometry.dyadicOrigin Λ A C k₀ hC h₀
  let a := Classical.choose hchoice
  let b := Classical.choose (Classical.choose_spec hchoice)
  have hOrigins := Geometry.existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero
    Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar N
  have hDistance (v w : ℤ × ℤ) :
      dist (Geometry.integerPoint v) (Geometry.integerPoint w) =
        (Scan.ambientSupDistance v w : ℝ) := by
    simp [Geometry.integerPoint, Prod.dist_eq, Real.dist_eq, Scan.ambientSupDistance]
  have hOrdered : ∀ i : Fin P.pieceCount, ∀ t ∈ (TI (e i)).points,
      ∀ x ∈ P.earlierSameFamily i,
        2 * (nI (e i) : ℝ) ^ (Exponents.beta : ℝ) <
          (Scan.ambientSupDistance t x.val : ℝ) := by
    intro i t ht x hx
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_filter.mp hj with ⟨-, hji, hcolor⟩
    have hxCurrent : Geometry.integerPoint x.val ∈ D.current (e j).val := by
      rw [hpiece j] at hx
      exact (Finset.mem_filter.mp hx).2
    have htBirth := (hpoints (e i) t).mp ht
    have hRanks : rank (e j) ≤ rank (e i) := hmono hji.le
    have hDistinct : (e j).val ≠ (e i).val := by
      intro he
      exact (ne_of_lt hji) (e.injective (Subtype.ext he))
    have hColor : D.color (e j).val = D.color (e i).val :=
      (hfamily j).symm.trans (hcolor.trans (hfamily i))
    by_cases hrank : rank (e i) = 0
    · have hrankj : rank (e j) = 0 := Nat.eq_zero_of_le_zero (hRanks.trans_eq hrank)
      obtain ⟨p, hp, -⟩ := hOrigins (e i).val hrank (e i).property.1
      obtain ⟨q, hq, -⟩ := hOrigins (e j).val hrankj (e j).property.1
      have hu := Geometry.repairStageCharacteristicLength_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl p))
      have hbp := Geometry.repairStage_birth_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl p))
      have hbq := Geometry.repairStage_birth_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl q))
      have hcp := Geometry.repairStage_color_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl p))
      have hcq := Geometry.repairStage_color_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl q))
      rw [hp] at hu hbp hcp
      rw [hq] at hbq hcq
      change u (e i) = (2 : ℝ) ^ p.1.val at hu
      change D.birth (e i).val = Geometry.primaryBirthRegion Geometry.dyadicOrigin p.1.val
        (Geometry.fineScaleIndex p.1.val) (Geometry.pitchScaleIndex p.1.val)
        (Geometry.boundaryEndpoints Λ A) C (a p.1.val).val (b p.1.val).val p.2.val at hbp
      change D.birth (e j).val = Geometry.primaryBirthRegion Geometry.dyadicOrigin q.1.val
        (Geometry.fineScaleIndex q.1.val) (Geometry.pitchScaleIndex q.1.val)
        (Geometry.boundaryEndpoints Λ A) C (a q.1.val).val (b q.1.val).val q.2.val at hbq
      change D.color (e i).val = Fin.ofNat 2 p.1.val at hcp
      change D.color (e j).val = Fin.ofNat 2 q.1.val at hcq
      have hpar : p.1.val % 2 = q.1.val % 2 := by
        exact congrArg Fin.val (hcp.symm.trans (hColor.symm.trans hcq))
      have hPair : (p.1.val, p.2.val) ≠ (q.1.val, q.2.val) := by
        intro he
        have hpq : p = q := Sigma.subtype_ext
          (Subtype.ext (congrArg Prod.fst he)) (congrArg Prod.snd he)
        subst q
        exact hDistinct (hq.symm.trans hp)
      have hn : nI (e i) = Geometry.primaryScannerScale CP p.1.val := by
        dsimp only [nI]
        rw [ite_eq_left hrank, hu]
        rfl
      have hlimits := hKP p.1.val (hKP₀.trans p.1.property)
      have hstrict : 2 * (nI (e i) : ℝ) ^ (Exponents.beta : ℝ) <
          min ((2 : ℝ) ^ Geometry.fineScaleIndex p.1.val) ((2 : ℝ) ^ p.1.val / 2) := by
        rw [hn]
        apply lt_min
        · nlinarith [hlimits.2.1, pow_pos (by norm_num : (0 : ℝ) < 2)
            (Geometry.fineScaleIndex p.1.val)]
        · nlinarith [hlimits.2.2, pow_pos (by norm_num : (0 : ℝ) < 2) p.1.val]
      have hxBirth := Geometry.repairStage_current_subset_birth
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N) (e j).val hxCurrent
      rw [hbp] at htBirth
      rw [hbq] at hxBirth
      have hd := Geometry.primaryBirthRegion_dist_separation_of_same_parity
        Geometry.dyadicOrigin p.1.val q.1.val (Geometry.boundaryEndpoints Λ A) C
        (fun k ↦ (a k).val) (fun k ↦ (b k).val) p.2.val q.2.val hC hpar hPair
        (Geometry.integerPoint t) (Geometry.integerPoint x.val) htBirth hxBirth
      exact hstrict.trans_le (hd.trans_eq (hDistance t x.val))
    · have hpositive : 0 < rank (e i) := Nat.pos_of_ne_zero hrank
      have huU : U ≤ u (e i) := hKU Geometry.dyadicOrigin Λ A C k₀ hC h₀ hKU₀
        Sstar hStops.2.2.2.1 (0 + N) (e i).val hpositive
      have hclear := hUF (u (e i)) ((le_max_left UF _).trans huU)
      have hxFinal : Geometry.integerPoint x.val ∈ Geometry.repairFinalRegion
          Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N) (e j).val := by
        rw [Geometry.repairFinalRegion_eq_current_of_isEmpty]
        exact hxCurrent
      obtain ⟨hinitial, hrepair⟩ := hKS Geometry.dyadicOrigin Λ A k₀ hC h₀ hKS₀
      have hd := Geometry.repairStage_birth_separation_of_rank_le
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar hinitial hrepair (0 + N)
        (e i).val (e j).val hpositive hDistinct (e j).property.1 hRanks hColor
        (Geometry.integerPoint t) htBirth (Geometry.integerPoint x.val) hxFinal
      change c₁ * u (e i) ^ (Exponents.rho : ℝ) ≤
        dist (Geometry.integerPoint t) (Geometry.integerPoint x.val) at hd
      rw [show nI (e i) = ⌈CB * u (e i)⌉₊ from ite_eq_right hrank]
      exact hclear.trans_le (hd.trans_eq (hDistance t x.val))
  have hSizes (i : I) :
      ⌊(nI i : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ ≤ sI i ∧ nstar ≤ nI i := by
    by_cases hrank : rank i = 0
    · obtain ⟨p, hp, -⟩ := hOrigins i.val hrank i.property.1
      have hu := Geometry.repairStageCharacteristicLength_oldInclusion
        Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar 0 N (.inr (.inl p))
      rw [hp] at hu
      change u i = (2 : ℝ) ^ p.1.val at hu
      have hs := hsI i
      rw [ite_eq_left (show rank i ≤ 1 by omega)] at hs
      have hn : nI i = Geometry.primaryScannerScale CP p.1.val := by
        dsimp only [nI]
        rw [ite_eq_left hrank, hu]
        rfl
      rw [hn]
      refine ⟨?_, hKN p.1.val (hKN₀.trans p.1.property)⟩
      have hfloor := (hKP p.1.val (hKP₀.trans p.1.property)).1
      have hreal :
          (⌊(Geometry.primaryScannerScale CP p.1.val : ℝ) ^
            (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ sI i := by
        rw [hs, hu]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p.1.val]
      exact_mod_cast hreal
    · have huU : U ≤ u i := hKU Geometry.dyadicOrigin Λ A C k₀ hC h₀ hKU₀
        Sstar hStops.2.2.2.1 (0 + N) i.val (Nat.pos_of_ne_zero hrank)
      have hUBU : UB ≤ U := le_max_of_le_right (le_max_left _ _)
      have hTwoU : 2 ≤ U := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
      have hDivU : (nstar : ℝ) / CB ≤ U :=
        le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
      have hfloor :
          (⌊(⌈CB * u i⌉₊ : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ u i := by
        simpa only [one_mul] using hUB (u i) (hUBU.trans huU)
      have huS : u i ≤ (sI i : ℝ) := by
        rw [hsI i]
        split_ifs <;> linarith [hTwoU.trans huU]
      have hminimum : (nstar : ℝ) ≤ (⌈CB * u i⌉₊ : ℝ) := by
        have hmul : (nstar : ℝ) ≤ CB * u i := by
          simpa only [mul_comm] using (div_le_iff₀ hCB).mp (hDivU.trans huU)
        exact hmul.trans (Nat.le_ceil _)
      rw [show nI i = ⌈CB * u i⌉₊ from ite_eq_right hrank]
      exact ⟨by exact_mod_cast hfloor.trans huS, by exact_mod_cast hminimum⟩
  let T : ∀ i : I, Geometry.Template Ctpl (nI i) (sI i) := fun i ↦
    { n_pos := (TI i).n_pos
      s₀_pos := (TI i).s₀_pos
      pieceCount := (TI i).pieceCount
      pieceCount_pos := (TI i).pieceCount_pos
      polygon := (TI i).polygon
      sample := (TI i).sample
      mem_sample := (TI i).mem_sample
      piece_diameter := (TI i).piece_diameter
      points := (TI i).points
      nonempty := (TI i).nonempty
      cover := (TI i).cover
      scale := (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Ctpl 1)
          (Nat.cast_nonneg (TI i).pieceCount)) (by positivity)).trans (TI i).scale
      diameter := (TI i).diameter }
  refine ⟨P, (fun i ↦ nI (e i)), (fun i ↦ sI (e i)), (fun i ↦ T (e i)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hresidual]
    exact hRes.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Nat.cast_nonneg (edgeBoundary Λ A).card))
  · intro i
    rw [hpiece i]
    exact (e i).property.2
  · intro i x hx
    rw [hpiece i] at hx
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩
    exact (hpoints (e i) x.val).mpr (Geometry.repairStage_current_subset_birth
      Geometry.dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N) (e i).val
      (Finset.mem_filter.mp hx).2)
  · exact fun i ↦ hsep (e i)
  · exact fun i ↦ (hSizes (e i)).1
  · exact fun i ↦ (hSizes (e i)).2
  · exact fun i ↦ hcut (e i)
  · exact hOrdered
  · have hsum := hError CB hCB Geometry.dyadicOrigin Λ A C k₀ hC h₀ (1 / 4) h (0 + N)
    change (∑ᶠ i : I, ((nI i : ℝ) ^ 100)⁻¹) ≤
      E * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card at hsum
    rw [finsum_eq_sum_of_fintype] at hsum
    calc
      _ = ∑ i : I, ((nI i : ℝ) ^ 100)⁻¹ :=
        e.sum_comp (fun i : I ↦ ((nI i : ℝ) ^ 100)⁻¹)
      _ ≤ E * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := hsum
      _ ≤ max L (E * (2 * (C : ℝ) + 1) ^ 2) * (edgeBoundary Λ A).card :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)

end TNLean.PEPS.AreaLaw

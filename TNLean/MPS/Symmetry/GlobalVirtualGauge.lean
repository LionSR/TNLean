/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.LocalVirtualGauge
import TNLean.MPS.Symmetry.CocycleCoboundary
import TNLean.MPS.Symmetry.InvertibleProjectivePathInvariance
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Piecewise

/-!
# Continuous virtual gauges on the parameter interval

Local continuous bond gauges of one-site injective tensor families can be
joined along a finite subdivision of the unit interval. Gauge uniqueness
allows adjacent choices to be rescaled by one nonzero constant to agree at
the common endpoint.

**Scope restriction (fixed bond dimension and exact tensor symmetry):**
The tensors have one fixed positive bond dimension and remain one-site
injective. The symmetry application preserves the periodic vectors exactly.
The construction does not handle changes of the minimal bond dimension or
deduce a tensor path from an arbitrary Hamiltonian path. These remaining
parts of the separation argument of arXiv:1010.3732, Section II.F.2 and
Appendix C, are recorded in
`docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- An invertible intertwiner between tensor letters gives a bond gauge.
Source context: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem gauge_covariance_of_invertible_intertwiner
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (hdet : X.det ≠ 0)
    (hX : ∀ i, B i * X = X * A i) :
    ∀ i, B i =
      (Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet)⁻¹ : GL (Fin D) ℂ) := by
  let Y := Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet
  change ∀ i, B i * (Y : Matrix (Fin D) (Fin D) ℂ) = Y * A i at hX
  intro i
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M *
    ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) (hX i)
  simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using h

/-- Invertible intertwiners of an injective tensor differ by a nonzero
scalar. Source context: arXiv:1010.3732, Section II.F.2, lines 1000–1018. -/
theorem exists_units_smul_of_invertible_intertwiners
    (A B : MPSTensor d D) (hA : Kraus.IsInjective A)
    (X Z : Matrix (Fin D) (Fin D) ℂ) (hXdet : X.det ≠ 0) (hZdet : Z.det ≠ 0)
    (hX : ∀ i, B i * X = X * A i) (hZ : ∀ i, B i * Z = Z * A i) :
    ∃ c : Units ℂ, Z = (c : ℂ) • X := by
  obtain ⟨c, hc⟩ := gauge_unique_up_to_scalar hA
    (gauge_covariance_of_invertible_intertwiner A B X hXdet hX)
    (gauge_covariance_of_invertible_intertwiner A B Z hZdet hZ)
  exact ⟨c, hc⟩

/-- Continuous pointwise gauge-equivalent injective tensor families on the
unit interval have a continuous invertible bond gauge with a prescribed
initial value. No finiteness assumption on a symmetry group is needed for
this lifting of one family. Source: arXiv:1010.3732, Section II.F.2,
lines 1000–1018. -/
theorem exists_continuous_gauge_on_unitInterval
    (hD : 0 < D) (A B : unitInterval → MPSTensor d D)
    (hA : Continuous A) (hB : Continuous B)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (hGauge : ∀ t, GaugeEquiv (A t) (B t)) (X₀ : GL (Fin D) ℂ)
    (hbase : ∀ i, B 0 i = X₀ * A 0 i * X₀⁻¹) :
    ∃ X : unitInterval → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ (∀ t, (X t).det ≠ 0) ∧
      (∀ t i, B t i * X t = X t * A t i) ∧ X 0 = X₀ := by
  classical
  choose Y hY using hGauge
  choose F hF hFbase hFdet hFInt using fun z =>
    exists_continuous_local_gauge_of_gaugeEquiv hD A B hA hB hInj
      (fun t => ⟨Y t, hY t⟩) z (Y z) (hY z)
  let U : unitInterval → Set unitInterval := fun z => {s | (F z s).det ≠ 0}
  have hUopen (z : unitInterval) : IsOpen (U z) :=
    (isOpen_ne : IsOpen {c : ℂ | c ≠ 0}).preimage (hF z).matrix_det
  have hUcover : Set.univ ⊆ ⋃ z, U z := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z, (hFdet z).self_of_nhds⟩
  obtain ⟨t, ht0, htmono, ⟨n_max, hmax⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hUopen hUcover
  have hprefix : ∀ n, ∃ X : unitInterval → Matrix (Fin D) (Fin D) ℂ,
      ContinuousOn X (Set.Icc 0 (t n)) ∧
      (∀ s ∈ Set.Icc 0 (t n), (X s).det ≠ 0) ∧
      (∀ s ∈ Set.Icc 0 (t n), ∀ i, B s i * X s = X s * A s i) ∧ X 0 = X₀ := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => (X₀ : Matrix (Fin D) (Fin D) ℂ), continuous_const.continuousOn,
        ?_, ?_, rfl⟩
      · exact fun _ _ => X₀.det_ne_zero
      · intro s hs i
        have hsEq : s = 0 := le_antisymm (ht0 ▸ hs.2) hs.1
        simp only [hsEq, hbase i, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    | succ n ih =>
      obtain ⟨X, hcont, hdet, hInt, hzero⟩ := ih
      obtain ⟨z, hsub⟩ := hsub n
      have htn : t n ∈ Set.Icc 0 (t n) := ⟨bot_le, le_rfl⟩
      obtain ⟨c, hmatch⟩ := exists_units_smul_of_invertible_intertwiners
        (A (t n)) (B (t n)) (hInj (t n)) (F z (t n)) (X (t n))
        (hsub ⟨le_rfl, htmono n.le_succ⟩) (hdet _ htn)
        (hFInt z (t n)) (hInt _ htn)
      have hnewcont : ContinuousOn
          (fun s => if s ≤ t n then X s else (c : ℂ) • F z s)
          (Set.Icc 0 (t (n + 1))) := by
        apply ContinuousOn.if
        · intro s hs
          have hsEq : s = t n := Set.mem_singleton_iff.mp (frontier_Iic_subset (t n) hs.2)
          simpa only [hsEq] using hmatch
        · apply hcont.mono
          intro s hs
          rw [closure_le_eq continuous_id' continuous_const] at hs
          exact ⟨hs.1.1, hs.2⟩
        · exact ((continuous_const : Continuous fun _ : unitInterval => (c : ℂ)).smul
            (hF z)).continuousOn
      refine ⟨_, hnewcont, ?_, ?_, ?_⟩
      · intro s hs
        split_ifs with hle
        · exact hdet s ⟨hs.1, hle⟩
        · rw [Matrix.det_smul]
          exact mul_ne_zero (pow_ne_zero _ c.ne_zero)
            (hsub ⟨le_of_not_ge hle, hs.2⟩)
      · intro s hs i
        split_ifs with hle
        · exact hInt s ⟨hs.1, hle⟩ i
        · simpa only [Matrix.mul_smul, Matrix.smul_mul] using
            congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => (c : ℂ) • M) (hFInt z s i)
      · simpa only [ite_eq_left (show (0 : unitInterval) ≤ t n from bot_le)] using hzero
  obtain ⟨X, hcont, hdet, hInt, hzero⟩ := hprefix n_max
  have hfull : Set.Icc 0 (t n_max) = Set.univ := by
    rw [hmax n_max le_rfl]
    exact Set.eq_univ_of_forall fun s => ⟨bot_le, le_top⟩
  exact ⟨X, continuousOn_univ.mp (hfull ▸ hcont),
    fun s => hdet s (hfull.symm ▸ Set.mem_univ s),
    fun s => hInt s (hfull.symm ▸ Set.mem_univ s), hzero⟩

/-- Exact on-site symmetry of a continuous one-site injective tensor family
on the unit interval gives continuous everywhere invertible virtual gauges,
separately for every group element. Source: arXiv:1010.3732,
Section II.F.2, lines 1000–1018, at fixed positive bond dimension. -/
theorem exists_continuous_virtualGauge_of_isOnSiteSymmetric
    {G : Type} [Group G] (hD : 0 < D)
    (A : unitInterval → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ t, IsOnSiteSymmetric (A t) U) :
    ∃ X : unitInterval → G → Matrix (Fin D) (Fin D) ℂ,
      (∀ g, Continuous fun t => X t g) ∧ (∀ t g, (X t g).det ≠ 0) ∧
      ∀ t g i, twistedTensor (A t) U g i * X t g = X t g * A t i := by
  have hGauge (t : unitInterval) (g : G) :
      GaugeEquiv (A t) (twistedTensor (A t) U g) :=
    gaugeEquiv_twistedTensor_of_injective (A t) (hInj t) U (hSym t) g
  have hB (g : G) : Continuous fun t => twistedTensor (A t) U g := by
    unfold twistedTensor
    exact continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (continuous_const : Continuous fun _ : unitInterval => U g i j).smul
        ((continuous_apply j).comp hA)
  have hlocal (g : G) : ∃ X : unitInterval → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ (∀ t, (X t).det ≠ 0) ∧
      ∀ t i, twistedTensor (A t) U g i * X t = X t * A t i := by
    obtain ⟨X₀, hbase⟩ := hGauge 0 g
    obtain ⟨X, hcont, hdet, hInt, _⟩ := exists_continuous_gauge_on_unitInterval
      hD A (fun t => twistedTensor (A t) U g) hA (hB g) hInj
      (fun t => hGauge t g) X₀ hbase
    exact ⟨X, hcont, hdet, hInt⟩
  choose X hcont hdet hInt using hlocal
  exact ⟨fun t g => X g t, hcont, fun t g => hdet g t, fun t g => hInt g t⟩

open TNLean.Algebra

/-- A continuous one-site injective tensor family with exact on-site
symmetry admits virtual projective representations whose matrices and
factor systems are continuous in the interval parameter. Source:
arXiv:1010.3732, Section II.F.2, lines 1000–1029, at fixed positive
bond dimension. -/
theorem exists_continuous_projectiveRepresentation_of_isOnSiteSymmetric
    {G : Type} [Group G] (hD : 0 < D)
    (A : unitInterval → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ t, IsOnSiteSymmetric (A t) U) :
    ∃ ω : unitInterval → ScalarCocycle G,
    ∃ ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t),
      (∀ g, Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ)) ∧
      (∀ g h, Continuous fun t => (ω t g h : ℂ)) ∧
      ∀ t g i, twistedTensor (A t) U g i =
        ((ρ t).X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A t i *
          ((((ρ t).X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  obtain ⟨X, hcont, hdet, hInt⟩ :=
    exists_continuous_virtualGauge_of_isOnSiteSymmetric hD A hA hInj U hSym
  let Y (t : unitInterval) (g : G) : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (X t g) (hdet t g)
  have hCov (t : unitInterval) (g : G) (i : Fin d) :
      twistedTensor (A t) U g i = (Y t g : Matrix (Fin D) (Fin D) ℂ) * A t i *
        (((Y t g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    gauge_covariance_of_invertible_intertwiner (A t) (twistedTensor (A t) U g)
      (X t g) (hdet t g) (hInt t g) i
  choose ω ρ hρ hCov using fun t =>
    exists_projectiveRepresentation_of_virtual_covariance (A t) (hInj t) U (Y t) (hCov t)
  have hV (g : G) : Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) := by
    simpa only [hρ, Y, Matrix.GeneralLinearGroup.val_mkOfDetNeZero] using hcont (g⁻¹)
  exact ⟨ω, ρ, hV, continuous_projectiveFactor_of_invertibleMatrixPath hD
    (fun t g => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ)) ω hV
    (fun t g => ((ρ t).X g).det_ne_zero) (fun t => (ρ t).map_mul), hCov⟩

/-- The virtual cohomology class is constant along a continuous family of
one-site injective tensors of fixed positive bond dimension with exact
on-site symmetry. The endpoint representations are arbitrary choices;
no continuous virtual family is assumed. Source: arXiv:1010.3732,
Section II.F.2, lines 1000–1063. -/
theorem cohomologousTo_of_continuous_isOnSiteSymmetric_tensorPath
    {G : Type} [Group G] (hD : 0 < D)
    (A : unitInterval → MPSTensor d D) (hA : Continuous A)
    (hInj : ∀ t, Kraus.IsInjective (A t))
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSym : ∀ t, IsOnSiteSymmetric (A t) U)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (hρ₀ : ∀ g i, twistedTensor (A 0) U g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A 0 i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₁ : ∀ g i, twistedTensor (A 1) U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A 1 i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ω₁.CohomologousTo ω₀ := by
  obtain ⟨ω, ρ, hcont, _, hCov⟩ :=
    exists_continuous_projectiveRepresentation_of_isOnSiteSymmetric hD A hA hInj U hSym
  have hpath : (ω 1).CohomologousTo (ω 0) :=
    invertible_projectivePath_factor_endpoints_cohomologous hD
      (fun t g => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ)) ω hcont
      (fun t g => ((ρ t).X g).det_ne_zero) (fun t => (ρ t).map_mul)
  exact (cohomologousTo_of_isInjective (A 1) (hInj 1) U hD (hCov 1) hρ₁).trans
    (hpath.trans (cohomologousTo_of_isInjective (A 0) (hInj 0) U hD hρ₀ (hCov 0)))

end MPSTensor

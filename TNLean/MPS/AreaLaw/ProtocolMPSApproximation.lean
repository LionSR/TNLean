/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolUniformPreparation
import TNLean.MPS.AreaLaw.CompressedBlockColumn
import TNLean.MPS.AreaLaw.ProtocolPolynomialMPS
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators

/-!
# Physical matrix product state approximation by the chain-sweep protocol

The physical assumptions construct one uniform family containing every
admissible sufficiently large Hamiltonian and ground vector. Compression
selects one actual nonzero product-basis column before all cuts. Its
normalization, inverse main-coordinate image and matrix product
representation refer to the same vector throughout. The remaining finite
lengths have exact matrix product representations and are absorbed into the
same uniform polynomial prefactor.

**Scope restriction (contiguous chains):** The sites are Fin L, exactly the
chain in Theorem B. See
`docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (retired auxiliary registers):** Only main registers are physical;
all auxiliary copies remain private at their actual owners. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Source: the one-dimensional note, Part 0, `thm:B`, lines 229–238, and Part II,
proof of `thm:B`, lines 574–615. The crossing bound is at most 1280,
and hence satisfies the printed upper bound 1600 used in the bond estimate.
-/

noncomputable section

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.PEPS.PairEffect TNLean.PEPS.EncodedFrame

/-- The protocol's density error permits column extraction and the source's
final phase error for every L≥2. Source: Part II, `thm:B`, lines 587–593. -/
private theorem protocol_error_bounds {L : ℕ} (hL : 2 ≤ L) :
    (L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ) < 1 ∧
      2 * ((L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ)) ≤ 1 / (L : ℝ) := by
  let x : ℝ := L
  have hx2 : 2 ≤ x := by
    change (2 : ℝ) ≤ (L : ℝ)
    exact_mod_cast hL
  have hx0 : 0 < x := by linarith
  have h6 : (52 : ℝ) ≤ x ^ (6 : ℕ) := by
    calc
      52 ≤ (2 : ℝ) ^ (6 : ℕ) := by norm_num
      _ ≤ x ^ (6 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have h5 : (32 : ℝ) ≤ x ^ (5 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ x ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have h4 : (4 : ℝ) ≤ x ^ (4 : ℕ) := by
    calc
      4 ≤ (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ x ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
  have hη : 52 / x ^ (11 : ℕ) ≤ 1 / x ^ (5 : ℕ) := by
    apply (div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx0 _)).2
    calc
      52 * x ^ (5 : ℕ) ≤ x ^ (6 : ℕ) * x ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right h6 (pow_nonneg hx0.le _)
      _ = 1 * x ^ (11 : ℕ) := by ring
  have hε : 1 / x ^ (5 : ℕ) + 52 / x ^ (11 : ℕ) ≤ 2 / x ^ (5 : ℕ) := by
    simp only [div_eq_mul_inv, one_mul] at hη ⊢
    linarith
  have hε2 : 2 * (1 / x ^ (5 : ℕ) + 52 / x ^ (11 : ℕ)) ≤ 4 / x ^ (5 : ℕ) := by
    simp only [div_eq_mul_inv, one_mul] at hη ⊢
    linarith
  have hsmall : 2 / x ^ (5 : ℕ) < 1 :=
    (div_lt_one (pow_pos hx0 _)).2 (by linarith)
  have hfinal : 4 / x ^ (5 : ℕ) ≤ 1 / x := by
    apply (div_le_div_iff₀ (pow_pos hx0 _) hx0).2
    simpa only [one_mul, pow_succ] using mul_le_mul_of_nonneg_right h4 hx0.le
  have hrpow : x ^ (-5 : ℝ) = 1 / x ^ (5 : ℕ) := by
    simpa only [Real.rpow_ofNat, one_div] using Real.rpow_neg hx0.le (5 : ℝ)
  have hzpow : x ^ (-11 : ℤ) = 1 / x ^ (11 : ℕ) := by
    simp only [zpow_neg, zpow_ofNat, one_div]
  change x ^ (-5 : ℝ) + 52 * x ^ (-11 : ℤ) < 1 ∧
    2 * (x ^ (-5 : ℝ) + 52 * x ^ (-11 : ℤ)) ≤ 1 / x
  rw [hrpow, hzpow]
  simpa only [mul_one_div] using ⟨hε.trans_lt hsmall, hε2.trans hfinal⟩

/-- The literal inverse main-coordinate map preserves the phase-error norm.
Source: Part II, `thm:B`, block-to-site passage at lines 605–615. -/
private theorem norm_mainPullback_sub (L w q : ℕ)
    (u : EuclideanSpace ℂ
      ((p : Party L w) → Fin (physicalDimension L w q p)))
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (c : ℂ) :
    ‖WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω‖ =
      ‖u - c • LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (mainConfigurationEquiv L w q) Ω‖ := by
  let E := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (mainConfigurationEquiv L w q)
  have hvector :
      E (WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω) =
        u - c • E Ω := by
    rw [map_sub, map_smul]
    congr 1
    ext x
    change u ((mainConfigurationEquiv L w q)
      ((mainConfigurationEquiv L w q).symm x)) = u x
    rw [Equiv.apply_symm_apply]
  calc
    _ = ‖E (WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x)) - c • Ω)‖ :=
      (E.norm_map _).symm
    _ = _ := congrArg norm hvector

/-- All states on chains of length at most N have an exact representation
with bond at most q^N. Source: Part II, `thm:B`, finite lengths at lines 575–578. -/
private theorem exact_isOpenMPS_of_length_le {L q N : ℕ}
    (hq : 1 ≤ q) (hLN : L ≤ N) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) :
    IsOpenMPS L q (q ^ N) (fun x ↦ Ω x) := by
  classical
  apply isOpenMPS_of_internal_cutMatrix_rank_le
  intro k _ _
  calc
    (cutMatrix Ω k).rank ≤
        Fintype.card ((v : {v : Fin L // v ∈ leftBlock L k}) → Fin q) :=
      Matrix.rank_le_card_height _
    _ = q ^ Fintype.card {v : Fin L // v ∈ leftBlock L k} := by simp
    _ ≤ q ^ N := Nat.pow_le_pow_right (by omega : 0 < q)
      ((Fintype.card_subtype_le _).trans (by simpa using hLN))

/-- Theorem B by the physical chain-sweep protocol. The polynomial constants
are chosen before the length, Hamiltonian and ground state. The approximant
is a unit, nonzero open-boundary MPS, with the source's phase error.
Source: the one-dimensional note, Part 0, `thm:B`, lines 229–238;
Part II, proof of `thm:B`, lines 574–615. -/
theorem exists_protocol_isOpenMPS_norm_sub_phase_le
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (C : ℝ) (n : ℕ), 0 < C ∧ 0 < n ∧
      ∀ (L : ℕ), 2 ≤ L →
        ∀ (h : ChainHamiltonian L q R J)
          (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
          Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
            ∃ (B : ℕ) (Φ : EuclideanSpace ℂ (Fin L → Fin q)),
              ‖Φ‖ = 1 ∧ Φ ≠ 0 ∧ IsOpenMPS L q B (fun x ↦ Φ x) ∧
                (B : ℝ) ≤ C * (L : ℝ) ^ n ∧
                ∃ θ : ℝ, ‖Φ - Complex.exp (θ * Complex.I) • Ω‖ ≤ 1 / (L : ℝ) := by
  classical
  obtain ⟨D, K, s, L₀, hL₀, hD, _hK, hfamily⟩ :=
    exists_uniform_preparation_family q hq R J Δ hΔ
  let ι := {a : Σ L : ℕ, ChainHamiltonian L q R J ×
      EuclideanSpace ℂ (Fin L → Fin q) × ℝ //
    L₀ ≤ a.1 ∧ Matrix.IsGappedGroundState a.2.1.operator a.2.2.2 a.2.2.1 Δ}
  let length := fun i : ι ↦ i.val.1
  let width := fun i : ι ↦ ⌈D * Real.log (length i : ℝ)⌉₊
  let ground := fun i : ι ↦ i.val.2.2.1
  let hLpos := fun i : ι ↦ Nat.lt_of_lt_of_le (by omega : 0 < L₀) i.property.1
  obtain ⟨hx, circuits, hsize, hcount, hphysical, harity, hlifetime,
      hmonomial, hexpansion, htarget, hdensity, hgate, _houter, hwidths⟩ := hfamily
  let C₀ := fun i : ι ↦
    preparationConstruction (w := width i) (ground i) (hLpos i) (hx i) (circuits i)
  let target := fun i : ι ↦ LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (mainConfigurationEquiv (length i) (width i) q) (ground i)
  obtain ⟨Cp, α, hCp, hα, hnetwork⟩ := exists_uniform_sampled_block_column
    (fun i : ι ↦ (length i : ℝ)) hsize length width C₀
    3 40 1600 (by decide) (by decide)
    1 s 1 0 0 2 K 1 1 hcount hphysical harity hlifetime hmonomial hexpansion
    target htarget (fun i : ι ↦ 52 * (length i : ℝ) ^ (-11 : ℤ))
    hdensity hgate 5 (by norm_num)
  let n := max 1 (⌈40 * D * Real.log (q : ℝ)⌉₊ + 1600 * α)
  let Clarge := (q : ℝ) ^ 40 * (Cp + 1) ^ 1600
  let Cfinal := max Clarge ((q : ℝ) ^ L₀)
  have hClarge : 0 < Clarge :=
    mul_pos (pow_pos (by exact_mod_cast (show 0 < q by omega)) _)
      (pow_pos (by linarith) _)
  have hCfinal : 0 < Cfinal := hClarge.trans_le (le_max_left _ _)
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨Cfinal, n, hCfinal, hn, ?_⟩
  intro L hL h Ω E₀ hgs
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  by_cases hlarge : L₀ ≤ L
  · let i : ι := ⟨⟨L, h, Ω, E₀⟩, hlarge, hgs⟩
    let w := ⌈D * Real.log (L : ℝ)⌉₊
    have herrors := protocol_error_bounds hL
    obtain ⟨Gate, hGateFinite, hGateDecidable, participants, root, hroot,
        Label, hLabelFinite, k, c, T, _hσ, _hσρ, _hρlow, _hρhigh,
        _halphabetReal, _hdegree, _hcommonGate, _hcongestion, _halphabetNat,
        hcolumn⟩ := hnetwork i
    let := hGateFinite
    let := hGateDecidable
    let := hLabelFinite
    obtain ⟨z, ψ, _hnetworkCoefficient, _hactualColumn, _hψ,
        hunit, ⟨θ, hphase⟩, hranks⟩ := hcolumn herrors.1
    let u : EuclideanSpace ℂ
        ((p : Party L w) → Fin (physicalDimension L w q p)) :=
      ((‖ψ‖ : ℂ)⁻¹) • ψ
    let Φ : EuclideanSpace ℂ (Fin L → Fin q) :=
      WithLp.toLp 2 (fun x ↦ u (mainConfigurationEquiv L w q x))
    let B := q ^ (40 * w) * (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ 1600
    have hmargin : 60 * w ≤ L := by
      have hm := (hwidths i).2
      change 3 * (20 * w) ≤ L at hm
      omega
    have hprefix (r : ℕ) (_hr : 0 < r) (_hrm : r ≤ stageCount L w) :
        (TNLean.PEPS.WholeGroup.flattening (fun y ↦ u y)
          (Finset.univ.filter fun p : Party L w ↦ partyLevel p < r)).rank ≤
            (max 1 ⌈Cp * (L : ℝ) ^ α⌉₊) ^ 1600 := by
      simpa only [u, C₀, preparationConstruction, length, width, i] using! (hranks r).2.2.2
    obtain ⟨hΦnorm, _hΦcuts, hΦmps, _hn, hB⟩ :=
      isOpenMPS_of_polynomial_partyPrefix_bounds 1600 hq hD hCp hα hL
        (show w = ⌈D * Real.log (L : ℝ)⌉₊ from rfl) hmargin u hunit hprefix
    have hΦne : Φ ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hΦnorm]
      exact one_ne_zero
    refine ⟨B, Φ, hΦnorm, hΦne, hΦmps, ?_, θ, ?_⟩
    · exact hB.trans (mul_le_mul_of_nonneg_right (le_max_left Clarge _)
        (pow_nonneg (by positivity : (0 : ℝ) ≤ L) n))
    · calc
        _ = ‖u - Complex.exp (θ * Complex.I) •
            LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (mainConfigurationEquiv L w q) Ω‖ :=
          norm_mainPullback_sub L w q u Ω (Complex.exp (θ * Complex.I))
        _ ≤ 2 * ((L : ℝ) ^ (-5 : ℝ) + 52 * (L : ℝ) ^ (-11 : ℤ)) := hphase
        _ ≤ 1 / (L : ℝ) := herrors.2
  · have hsmall : L ≤ L₀ := by omega
    have hmps := exact_isOpenMPS_of_length_le hq hsmall Ω
    have hΩne : Ω ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hgs.1]
      exact one_ne_zero
    refine ⟨q ^ L₀, Ω, hgs.1, hΩne, hmps, ?_, 0, ?_⟩
    · calc
        ((q ^ L₀ : ℕ) : ℝ) = (q : ℝ) ^ L₀ := by simp only [Nat.cast_pow]
        _ ≤ Cfinal := le_max_right _ _
        _ ≤ Cfinal * (L : ℝ) ^ n :=
          le_mul_of_one_le_right hCfinal.le (one_le_pow₀ hLreal)
    · simp

end TNLean.MPS.AreaLaw.ChainSweep

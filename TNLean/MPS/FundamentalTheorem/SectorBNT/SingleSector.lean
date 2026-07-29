/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.SectorBNT.Basic

/-!
# Single-sector BNT canonical forms

This file presents a tensor as a sector decomposition with one basis block, one copy, and
unit weight. It proves that the presentation is a BNT canonical form under the standard
irreducibility, left-canonicality, and self-overlap hypotheses. A normal tensor admits such
a presentation after its pure trace-preserving Perron gauge.

## Main results

* `singleSectorDecomposition`: the one-sector, one-copy decomposition of a tensor.
* `isBNTCanonicalForm_singleSectorDecomposition`: the corresponding BNT canonical form.
* `IsNormalTensor.exists_gaugeEquiv_singleSectorDecomposition`: a normal tensor has a
  gauge-equivalent single-sector BNT presentation.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Section 2.3,
  lines 217--301.
-/

open Filter Topology

namespace MPSTensor

variable {d D : ℕ}

/-- The sector decomposition with one basis block, one copy, and unit weight. -/
@[reducible]
noncomputable def singleSectorDecomposition (A : MPSTensor d D) :
    SectorDecomposition d where
  basisCount := 1
  basisDim := fun _ => D
  basis := fun _ => A
  sectors :=
    { copies := fun _ => 1
      copies_pos := fun _ => Nat.one_pos
      weight := fun _ _ => 1
      weight_ne_zero := fun _ _ => one_ne_zero }

/-- An irreducible left-canonical tensor with normalized self-overlap gives a
single-sector BNT canonical form.

This is the one-block specialization of the BNT canonical form in
arXiv:1606.00608, Section 2.3, lines 217--301. -/
theorem isBNTCanonicalForm_singleSectorDecomposition [NeZero D]
    {A : MPSTensor d D}
    (hIrr : IsIrreducibleTensor A)
    (hLeft : IsLeftCanonical A)
    (hSelf : Tendsto (fun N : ℕ => mpvOverlap (d := d) A A N) atTop (𝓝 1)) :
    IsBNTCanonicalForm (singleSectorDecomposition A) where
  basis_dim_pos := fun _ => NeZero.pos D
  basis_irreducible := fun _ => hIrr
  basis_left_canonical := fun _ => hLeft
  basis_normalized_self_overlap := fun _ => hSelf
  bnt_data := by
    classical
    obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 (hSelf.eventually_ne one_ne_zero))
    refine ⟨N₀, fun N hN => ?_⟩
    apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
    intro hState
    apply hN₀ N (Nat.le_of_lt hN)
    have hCoeff : ∀ σ : Fin N → Fin d, mpv A σ = 0 := by
      intro σ
      have hApply := congrArg (fun x => x σ) hState
      simpa using hApply
    simp only [mpvOverlap, hCoeff, zero_mul, Finset.sum_const_zero]
  basis_distinct := fun j k hjk _ =>
    absurd (Subsingleton.elim j k) hjk
  weight_norm_le_one := by
    intro _ _
    change ‖(1 : ℂ)‖ ≤ 1
    simp
  weight_unit_exists := by
    refine ⟨0, 0, ?_⟩
    change ‖(1 : ℂ)‖ = 1
    simp

/-- A normal tensor is gauge equivalent to a single-sector BNT canonical form.

The gauge is the pure trace-preserving Perron gauge from arXiv:1606.00608,
Appendix A, lines 1093--1117. -/
theorem IsNormalTensor.exists_gaugeEquiv_singleSectorDecomposition
    {A : MPSTensor d D} (hA : IsNormalTensor A) :
    ∃ B : MPSTensor d D,
      GaugeEquiv A B ∧
      IsBNTCanonicalForm (singleSectorDecomposition B) ∧
      SameMPV₂Pos A (singleSectorDecomposition B).toTensor := by
  letI : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨σ, _hσ, _hσfix, hLeft, hGauge, hPrim, hIrr⟩ := hA.exists_tpGauge
  let B := tpGauge (d := d) (D := D) A σ
  have hSelf :
      Tendsto (fun N : ℕ => mpvOverlap (d := d) B B N) atTop (𝓝 1) :=
    overlap_tendsto_one_of_peripheralPrimitive_of_irreducible B hIrr hLeft hPrim
  have hBNT : IsBNTCanonicalForm (singleSectorDecomposition B) :=
    isBNTCanonicalForm_singleSectorDecomposition hIrr hLeft hSelf
  refine ⟨B, hGauge, hBNT, ?_⟩
  intro N _hN τ
  calc
    mpv A τ = mpv B τ := GaugeEquiv.sameMPV hGauge N τ
    _ = mpv (singleSectorDecomposition B).toTensor τ := by
      rw [(singleSectorDecomposition B).mpv_toTensor_eq_sum_coeff]
      simp [singleSectorDecomposition, SectorDecomposition.coeff, SectorWeightData.coeff]

end MPSTensor

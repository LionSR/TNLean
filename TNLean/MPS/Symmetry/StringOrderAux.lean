/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.StringOrderDefs
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Irreducible.Adjoint
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Irreducible.Similarity
import TNLean.Channel.Irreducible.TraceAdjoint
import TNLean.Channel.KrausRepresentation
import TNLean.Spectral.SpectralGapNT

/-!
# String order: trace-preserving gauge reduction and auxiliary proofs

This file provides the trace-preserving gauge setup and auxiliary proofs
supporting the main string-order equivalence theorems in
`TNLean.MPS.Symmetry.StringOrder`.

## Contents

* `TwistedTPGaugeSetup` — bundled TP-gauge data for the spectral radius bound
* `transferMap_tpGauge_eq_similarityMap` — similarity transform of the transfer map
* `virtualUnitary_of_gaugePhaseEquiv_twisted` — normalization of a gauge-phase
  intertwiner to a unitary
* `boundaryState_invariant_of_virtualUnitary` — boundary-state invariance `V† Λ V = Λ`

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447 (PRL 2008)
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

set_option maxHeartbeats 800000 in
-- Expanding `tpGauge`, `transferMap`, and CFC adjoint identities is kernel-expensive.
/-- The transfer map of a TP-gauged tensor is the similarity transform of the
original transfer map by the positive square root of the adjoint fixed point. -/
lemma transferMap_tpGauge_eq_similarityMap
    (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef) :
    transferMap (tpGauge (d := d) (D := D) A σ) =
      similarityMap (D := D) (CFC.sqrt σ)⁻¹ (transferMap A) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : IsUnit S.det := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) σ
  have hS_inv_inv : S⁻¹⁻¹ = S := Matrix.nonsing_inv_nonsing_inv S hS_det
  have hS_inv_herm : (S⁻¹)ᴴ = (Sᴴ)⁻¹ := Matrix.conjTranspose_nonsing_inv S
  have hS_inv_herm' : (S⁻¹)ᴴ = S⁻¹ := by simpa [hS_herm] using hS_inv_herm
  ext X i j
  have hcalc :
      transferMap (tpGauge (d := d) (D := D) A σ) X =
        similarityMap (D := D) S⁻¹ (transferMap A) X := by
    calc
      transferMap (tpGauge (d := d) (D := D) A σ) X
          = ∑ i : Fin d, (S * A i * S⁻¹) * X * (S * A i * S⁻¹)ᴴ := by
              simp [transferMap_apply, tpGauge, S]
              rfl
      _ = ∑ i : Fin d, S * (A i * (S⁻¹ * X * S⁻¹ * (A i)ᴴ)) * S := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_nonsing_inv]
            simp [Matrix.mul_assoc, hS_herm]
      _ = S * (∑ i : Fin d, A i * (S⁻¹ * X * S⁻¹ * (A i)ᴴ)) * S := by
            rw [Matrix.sum_mul_mul]
      _ = similarityMap (D := D) S⁻¹ (transferMap A) X := by
            simp [similarityMap, transferMap_apply, S, hS_inv_inv, hS_inv_herm',
              Matrix.mul_assoc]
  exact congrFun (congrFun hcalc i) j

/-- TP gauging preserves irreducibility when the original transfer map is
irreducible. -/
lemma isIrreducibleTensor_tpGauge_of_isIrreducibleMap [NeZero D]
    (A : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A)) :
    IsIrreducibleTensor (d := d) (D := D) (tpGauge (d := d) (D := D) A σ) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : S.det ≠ 0 := by
    exact (isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ).ne_zero
  have hIrrSim :
      IsIrreducibleMap (similarityMap (D := D) S⁻¹ (transferMap A)) := by
    refine isIrreducibleMap_similarity (D := D) ?_ hIrr
    simpa [S, Matrix.det_nonsing_inv] using inv_ne_zero hS_det
  have hEq :
      transferMap (tpGauge (d := d) (D := D) A σ) =
        similarityMap (D := D) S⁻¹ (transferMap A) := by
    simpa [S] using transferMap_tpGauge_eq_similarityMap (A := A) (σ := σ) hσ
  have hIrr' : IsIrreducibleMap
      (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) := by
    simpa [hEq] using hIrrSim
  exact isIrreducibleTensor_of_isIrreducibleMap _ hIrr'

/-- Gauge equivalence on the left and right transports a gauge-phase
equivalence back to the original tensors. -/
lemma gaugePhaseEquiv_of_gaugeEquiv_left_right
    {A A' B B' : MPSTensor d D}
    (hAA' : GaugeEquiv A A')
    (hA'B' : GaugePhaseEquiv A' B')
    (hBB' : GaugeEquiv B B') :
    GaugePhaseEquiv A B := by
  obtain ⟨X, hX⟩ := hAA'
  obtain ⟨Y, ζ, hζ, hY⟩ := hA'B'
  obtain ⟨Z, hZ⟩ := hBB'
  refine ⟨Z⁻¹ * Y * X, ζ, hζ, ?_⟩
  intro i
  have hB' : B' i = Z * B i * Z⁻¹ := hZ i
  calc
    B i = Z⁻¹ * B' i * Z := by
      rw [hB']
      simp [Matrix.mul_assoc]
    _ = Z⁻¹ * (ζ • (Y * A' i * Y⁻¹)) * Z := by rw [hY i]
    _ = ζ • (Z⁻¹ * (Y * A' i * Y⁻¹) * Z) := by
          simp [Matrix.mul_assoc]
    _ = ζ • (Z⁻¹ * (Y * (X * A i * X⁻¹) * Y⁻¹) * Z) := by rw [hX i]
    _ = ζ • (((Z⁻¹ * Y * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((((Z⁻¹ * Y * X : GL (Fin D) ℂ)⁻¹ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ))) := by
          simp [Matrix.mul_assoc, mul_inv_rev]

/-- Bundled TP-gauge data for a twisted MPS tensor, used to reduce the spectral radius
bound to the TP-normalized setting in the string-order proofs. -/
structure TwistedTPGaugeSetup [NeZero D]
    (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ) where
  B : MPSTensor d D
  hB_def : B = twistedMixedCompanion A u
  hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ, transferMap B X = transferMap A X
  σ : Matrix (Fin D) (Fin D) ℂ
  hσ_pd : σ.PosDef
  hσ_fixB : transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ = σ
  S : Matrix (Fin D) (Fin D) ℂ
  hS_def : S = CFC.sqrt σ
  hS_herm : Sᴴ = S
  hS_mul_inv : S * S⁻¹ = 1
  hS_inv_mul : S⁻¹ * S = 1
  hS_hMul_inv : Sᴴ * (Sᴴ)⁻¹ = 1
  hS_inv_herm : (S⁻¹)ᴴ = S⁻¹
  A' : MPSTensor d D
  hA'_def : A' = tpGauge (d := d) (D := D) A σ
  B' : MPSTensor d D
  hB'_def : B' = tpGauge (d := d) (D := D) B σ
  hA'TP : ∑ i : Fin d, (A' i)ᴴ * A' i = 1
  hB'TP : ∑ i : Fin d, (B' i)ᴴ * B' i = 1
  hIrrA' : IsIrreducibleTensor (d := d) (D := D) A'
  hIrrB' : IsIrreducibleTensor (d := d) (D := D) B'

/-- Constructs a `TwistedTPGaugeSetup` from an injective, normalized MPS tensor and
a unitary twist matrix `u`. -/
noncomputable def twistedTPGaugeSetup [NeZero D]
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1) :
    TwistedTPGaugeSetup (d := d) (D := D) A u := by
  classical
  let B : MPSTensor d D := twistedMixedCompanion A u
  have hB_eq : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      transferMap B X = transferMap A X := by
    intro X
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu X
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hEqBA : transferMap B = transferMap A := LinearMap.ext hB_eq
  have hIrrB : IsIrreducibleMap (transferMap (d := d) (D := D) B) := by
    simpa [hEqBA] using hIrrA
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap A hIrrA
  have hIrrAdj : IsIrreducibleMap (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor A hIrrTensor
  have hAadjNorm : ∑ i : Fin d, (((fun i => (A i)ᴴ) i)ᴴ) * ((fun i => (A i)ᴴ) i) = 1 := by
    simpa using
      kraus_sum_mul_conjTranspose_of_unital A (transferMap A)
        (fun X => by simp [transferMap_apply]) hNorm
  have hChAdj : IsChannel (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    transferMap_isChannel (A := fun i => (A i)ᴴ) hAadjNorm
  let hσ_exists :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := transferMap (d := d) (D := D) fun i => (A i)ᴴ) hChAdj hIrrAdj (NeZero.pos D)
  let σ := Classical.choose hσ_exists
  have hσ_spec := Classical.choose_spec hσ_exists
  have hσ_pd : σ.PosDef := hσ_spec.2.1
  have hσ_fixA : transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ = σ := hσ_spec.2.2.1
  have hσ_fixB : transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ = σ := by
    calc
      transferMap (d := d) (D := D) (fun i => (B i)ᴴ) σ
          = transferMap (d := d) (D := D) (fun i => (A i)ᴴ) σ := by
              simpa [B, transferMap_apply, Matrix.mul_assoc] using
                kraus_dual_eq_of_map_eq B A
                  (fun X => by simpa [transferMap_apply] using hB_eq X) σ
      _ = σ := hσ_fixA
  let S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_herm : Sᴴ = S := by
    simpa [S] using conjTranspose_cfc_sqrt (D := D) σ
  have hS_det : IsUnit (Matrix.det S) := by
    simpa [S] using isUnit_det_cfc_sqrt_of_posDef (D := D) σ hσ_pd
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hS_inv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hS_detT : IsUnit (Matrix.det Sᴴ) := by
    simpa [Matrix.det_conjTranspose] using IsUnit.star hS_det
  have hS_hMul_inv : Sᴴ * (Sᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Sᴴ hS_detT
  have hS_inv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    simpa [hS_herm] using Matrix.conjTranspose_nonsing_inv S
  let A' := tpGauge (d := d) (D := D) A σ
  let B' := tpGauge (d := d) (D := D) B σ
  have hA'TP : ∑ i : Fin d, (A' i)ᴴ * A' i = 1 := by
    simpa [A'] using
      tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := A) (ρ := σ) hσ_pd hσ_fixA
  have hB'TP : ∑ i : Fin d, (B' i)ᴴ * B' i = 1 := by
    simpa [B'] using
      tpGauge_isTP_of_transferMap_conjTranspose_fixedPoint (A := B) (ρ := σ) hσ_pd hσ_fixB
  have hIrrA' : IsIrreducibleTensor (d := d) (D := D) A' := by
    simpa [A'] using isIrreducibleTensor_tpGauge_of_isIrreducibleMap
      (A := A) (σ := σ) hσ_pd hIrrA
  have hIrrB' : IsIrreducibleTensor (d := d) (D := D) B' := by
    simpa [B'] using isIrreducibleTensor_tpGauge_of_isIrreducibleMap
      (A := B) (σ := σ) hσ_pd hIrrB
  exact
    { B := B
      hB_def := rfl
      hB_eq := hB_eq
      σ := σ
      hσ_pd := hσ_pd
      hσ_fixB := hσ_fixB
      S := S
      hS_def := rfl
      hS_herm := hS_herm
      hS_mul_inv := hS_mul_inv
      hS_inv_mul := hS_inv_mul
      hS_hMul_inv := hS_hMul_inv
      hS_inv_herm := hS_inv_herm
      A' := A'
      hA'_def := rfl
      B' := B'
      hB'_def := rfl
      hA'TP := hA'TP
      hB'TP := hB'TP
      hIrrA' := hIrrA'
      hIrrB' := hIrrB' }

/-- An eigenvalue of the twisted transfer map is also an eigenvalue of the mixed
transfer map in the TP-gauge picture. -/
theorem twistedTPGaugeSetup_hasEigenvalue [NeZero D]
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (setup : TwistedTPGaugeSetup (d := d) (D := D) A u)
    (ev : ℂ) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V ≠ 0)
    (hEig : twistedTransferMap A u V = ev • V) :
    Module.End.HasEigenvalue (mixedTransferMap setup.A' setup.B') ev := by
  have hEigMixed : mixedTransferMap A setup.B V = ev • V := by
    simpa [setup.hB_def, twistedTransferMap_eq_mixedTransfer] using hEig
  have hEigGauge :
      mixedTransferMap setup.A' setup.B' (setup.S * V * setup.Sᴴ) =
        ev • (setup.S * V * setup.Sᴴ) := by
    have hTerm :
        ∀ i : Fin d,
          setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ =
            setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
      intro i
      have hAeq : setup.A' i = setup.S * A i * setup.S⁻¹ := by
        rw [setup.hA'_def, tpGauge, setup.hS_def]
        rfl
      have hBstar :
          (setup.B' i)ᴴ = setup.S⁻¹ * (setup.B i)ᴴ * setup.S := by
        calc
          (setup.B' i)ᴴ
              = ((setup.S * setup.B i * setup.S⁻¹ : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
                  rw [setup.hB'_def, tpGauge, setup.hS_def]
                  rfl
          _ = (setup.S⁻¹)ᴴ * (setup.B i)ᴴ * setup.Sᴴ := by
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = setup.S⁻¹ * (setup.B i)ᴴ * setup.S := by
                simp [setup.hS_herm, setup.hS_inv_herm]
      calc
        setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ
            = (setup.S * A i * setup.S⁻¹) * (setup.S * V * setup.S) *
                (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                  rw [hAeq, hBstar, setup.hS_herm]
        _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.S := by
              calc
                (setup.S * A i * setup.S⁻¹) * (setup.S * V * setup.S) *
                    (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                    = setup.S * A i * (setup.S⁻¹ * (setup.S * V * setup.S)) *
                        (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                        simp [Matrix.mul_assoc]
                _ = setup.S * A i * (V * setup.S) *
                      (setup.S⁻¹ * (setup.B i)ᴴ * setup.S) := by
                      have hSV :
                          setup.S⁻¹ * (setup.S * V * setup.S) = V * setup.S := by
                        calc
                          setup.S⁻¹ * (setup.S * V * setup.S)
                              = (setup.S⁻¹ * setup.S) * V * setup.S := by
                                  simp [Matrix.mul_assoc]
                          _ = V * setup.S := by simp [setup.hS_inv_mul]
                      rw [hSV]
                _ = setup.S * A i * (V * (setup.B i)ᴴ * setup.S) := by
                      calc
                        setup.S * A i * (V * setup.S) *
                            (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                            = setup.S * A i *
                                ((V * setup.S) * (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)) := by
                                simp [Matrix.mul_assoc]
                        _ = setup.S * A i * (V * (setup.B i)ᴴ * setup.S) := by
                              congr 1
                              calc
                                (V * setup.S) * (setup.S⁻¹ * (setup.B i)ᴴ * setup.S)
                                    = V * (setup.S * setup.S⁻¹) * (setup.B i)ᴴ * setup.S := by
                                        simp [Matrix.mul_assoc]
                                _ = V * (setup.B i)ᴴ * setup.S := by
                                      simp [setup.hS_mul_inv, Matrix.mul_assoc]
                _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.S := by
                      simp [Matrix.mul_assoc]
        _ = setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
              simp [setup.hS_herm]
    calc
      mixedTransferMap setup.A' setup.B' (setup.S * V * setup.Sᴴ)
          = ∑ i : Fin d,
              setup.A' i * (setup.S * V * setup.Sᴴ) * (setup.B' i)ᴴ := by
                  simp [mixedTransferMap_apply]
      _ = ∑ i : Fin d, setup.S * (A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
            simp [hTerm]
      _ = setup.S * (∑ i : Fin d, A i * V * (setup.B i)ᴴ) * setup.Sᴴ := by
            simpa using
              (Matrix.sum_mul_mul
                (L := setup.S) (M := fun i : Fin d => A i * V * (setup.B i)ᴴ) (R := setup.Sᴴ))
      _ = ev • (setup.S * V * setup.Sᴴ) := by
            simpa [mixedTransferMap_apply, Matrix.mul_assoc] using
              congrArg (fun M => setup.S * M * setup.Sᴴ) hEigMixed
  have hGauge_ne : setup.S * V * setup.Sᴴ ≠ 0 := by
    intro hZero
    apply hV
    have h' : setup.S⁻¹ * (setup.S * V * setup.Sᴴ) * (setup.Sᴴ)⁻¹ = 0 := by
      simp [hZero]
    have h'' : setup.S⁻¹ * (setup.S * V) = 0 := by
      simpa [Matrix.mul_assoc, setup.hS_hMul_inv] using h'
    have h''' : (setup.S⁻¹ * setup.S) * V = 0 := by
      simpa [Matrix.mul_assoc] using h''
    simpa [setup.hS_inv_mul] using h'''
  rw [Module.End.hasEigenvalue_iff]
  intro hBot
  have hMem :
      setup.S * V * setup.Sᴴ ∈ Module.End.eigenspace
        (mixedTransferMap setup.A' setup.B') ev :=
    Module.End.mem_eigenspace_iff.mpr hEigGauge
  have : setup.S * V * setup.Sᴴ ∈ (⊥ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
    simpa [hBot] using hMem
  exact hGauge_ne (Submodule.mem_bot ℂ |>.mp this)

/-- If the twisted companion family is gauge-phase equivalent to `A`, the gauge
matrix can be normalized to a unitary and converted into the phased virtual
symmetry relation from the string-order paper. -/
theorem virtualUnitary_of_gaugePhaseEquiv_twisted
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (hNorm : transferMap A 1 = 1)
    (hGauge : GaugePhaseEquiv A (twistedMixedCompanion A u)) :
    ∃ V : Matrix (Fin D) (Fin D) ℂ, ∃ μ : ℂ,
      V * Vᴴ = 1 ∧ Vᴴ * V = 1 ∧ ‖μ‖ = 1 ∧
      ∀ i : Fin d,
        ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ) := by
  classical
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    refine ⟨1, 1, by simp, by simp, by simp, ?_⟩
    intro i
    ext a
    exact Fin.elim0 a
  haveI : NeZero D := ⟨hD⟩
  let B : MPSTensor d D := twistedMixedCompanion A u
  obtain ⟨Xgl, ζ, hζ, hX⟩ := hGauge
  let X : Matrix (Fin D) (Fin D) ℂ := (Xgl : Matrix (Fin D) (Fin D) ℂ)
  let Xin : Matrix (Fin D) (Fin D) ℂ := ((Xgl⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hX_mul_inv : X * Xin = 1 := by
    simp [X, Xin]
  have hX_inv_mul : Xin * X = 1 := by
    simp [X, Xin]
  have hB_eq : ∀ Y : Matrix (Fin D) (Fin D) ℂ, transferMap B Y = transferMap A Y := by
    intro Y
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu Y
  let Q : Matrix (Fin D) (Fin D) ℂ := X * Xᴴ
  have hQ_psd : Q.PosSemidef := by
    simpa [Q] using Matrix.posSemidef_self_mul_conjTranspose X
  let C : MPSTensor d D := fun i => X * A i * Xin
  have hB_C : B = fun i => ζ • C i := by
    funext i
    simpa [B, C, X, Xin] using hX i
  have hXinQ : Xin * Q * Xinᴴ = 1 := by
    calc
      Xin * Q * Xinᴴ = (Xin * X) * Xᴴ * Xinᴴ := by
        simp [Q, Matrix.mul_assoc]
      _ = Xᴴ * Xinᴴ := by
        simp [hX_inv_mul]
      _ = (Xin * X)ᴴ := by
        simp [Matrix.conjTranspose_mul]
      _ = 1 := by
        simp [hX_inv_mul]
  have hQ_eigC : transferMap C Q = Q := by
    calc
      transferMap C Q = X * transferMap A (Xin * Q * Xinᴴ) * Xᴴ := by
        simpa [C, X, Xin, Matrix.mul_assoc] using transferMap_gauge_conj A Xgl Q
      _ = X * transferMap A 1 * Xᴴ := by rw [hXinQ]
      _ = Q := by simp [Q, hNorm]
  have hQ_eigB : transferMap B Q = (Complex.normSq ζ : ℂ) • Q := by
    calc
      transferMap B Q = transferMap (fun i => ζ • C i) Q := by
        simp [hB_C]
      _ = ∑ i : Fin d, (ζ • C i) * Q * (ζ • C i)ᴴ := by
            simp [transferMap_apply]
      _ = ∑ i : Fin d, (Complex.normSq ζ : ℂ) • (C i * Q * (C i)ᴴ) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [Matrix.conjTranspose_smul, smul_smul,
              Complex.normSq_eq_conj_mul_self, mul_comm]
      _ = (Complex.normSq ζ : ℂ) • ∑ i : Fin d, C i * Q * (C i)ᴴ := by
            simp [Finset.smul_sum]
      _ = (Complex.normSq ζ : ℂ) • transferMap C Q := by
            simp [transferMap_apply]
      _ = (Complex.normSq ζ : ℂ) • Q := by rw [hQ_eigC]
  have hQ_eigA : transferMap A Q = (Complex.normSq ζ : ℂ) • Q := by
    rw [← hB_eq Q]
    exact hQ_eigB
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hXh_inv_mul : Xᴴ * Xinᴴ = 1 := by
      calc
        Xᴴ * Xinᴴ = (Xin * X)ᴴ := by
          simp [Matrix.conjTranspose_mul]
        _ = 1 := by
          simp [hX_inv_mul]
    have : X = 0 := by
      calc
        X = X * 1 := by simp
        _ = X * (Xᴴ * Xinᴴ) := by rw [hXh_inv_mul]
        _ = (X * Xᴴ) * Xinᴴ := by simp [Matrix.mul_assoc]
        _ = 0 := by simp [Q, hQ0]
    have hX_ne : X ≠ 0 := by
      intro hX0
      have hbad := hX_mul_inv
      simp [X, Xin, hX0] at hbad
    exact hX_ne this
  have hζ_sq_eq_one : Complex.normSq ζ = 1 := by
    have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
      injective_implies_irreducibleCP A hA
    have hCPA : IsCPMap (transferMap (d := d) (D := D) A) :=
      transferMap_isCPMap A
    have hone_psd : (1 : Matrix (Fin D) (Fin D) ℂ).PosSemidef := by
      simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
    have hone_eig : transferMap A 1 = ((1 : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
      simpa using hNorm
    exact
      eigenvalue_unique_of_irreducible_cp
        (E := transferMap (d := d) (D := D) A) hCPA hIrrA
        (1 : Matrix (Fin D) (Fin D) ℂ) Q 1 (Complex.normSq ζ)
        hone_psd one_ne_zero (by norm_num) hQ_psd hQ_ne
        (Complex.normSq_pos.2 hζ) hone_eig hQ_eigA |>.symm
  have hQ_fix : transferMap A Q = Q := by
    simpa [hζ_sq_eq_one] using hQ_eigA
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hone_psd : (1 : Matrix (Fin D) (Fin D) ℂ).PosSemidef := by
    simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ)).posSemidef
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := A) hIrrA
      (1 : Matrix (Fin D) (Fin D) ℂ) Q hone_psd one_ne_zero hQ_psd hNorm hQ_fix with
    ⟨c, hQ_scalar⟩
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    apply hQ_ne
    simp [hQ_scalar, hc0]
  have hc_nonneg : 0 ≤ c := by
    have hscalar_psd : (c • (1 : Matrix (Fin D) (Fin D) ℂ)).PosSemidef := by
      simpa [hQ_scalar] using hQ_psd
    have hdiag_psd : (Matrix.diagonal (fun _ : Fin D => c)).PosSemidef := by
      simpa [Matrix.smul_one_eq_diagonal] using hscalar_psd
    have hdiag_nonneg := (Matrix.posSemidef_diagonal_iff).1 hdiag_psd
    exact hdiag_nonneg ⟨0, NeZero.pos D⟩
  have hc_eq_real : c = (c.re : ℂ) := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hc_nonneg).2.symm)
  have hcre_nonneg : 0 ≤ c.re := (Complex.nonneg_iff.mp hc_nonneg).1
  have hcre_ne0 : c.re ≠ 0 := by
    intro h0
    apply hc_ne0
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = 0 := by simp [h0]
  have hcre_pos : 0 < c.re := lt_of_le_of_ne hcre_nonneg (Ne.symm hcre_ne0)
  set a : ℂ := (Real.sqrt c.re : ℂ)
  have ha_ne0 : a ≠ 0 := by
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.mpr hcre_pos)
  have hc_eq_sq : c = a * a := by
    calc
      c = (c.re : ℂ) := hc_eq_real
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by
            simp [Real.sq_sqrt hcre_nonneg]
      _ = a * a := by
            rw [pow_two]
            simp [a]
  have hstar_a : star a = a := by
    simp [a]
  have hstar_a_inv : star a⁻¹ = a⁻¹ := by
    simp [a]
  let U : Matrix (Fin D) (Fin D) ℂ := a⁻¹ • X
  have hU_unitary_left : U * Uᴴ = 1 := by
    calc
      U * Uᴴ = (star a⁻¹ * a⁻¹) • (X * Xᴴ) := by
            simp [U, Matrix.conjTranspose_smul, smul_smul]
      _ = (a⁻¹ * a⁻¹) • Q := by
            rw [hstar_a_inv]
      _ = ((a⁻¹ * a⁻¹) * c) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
            rw [hQ_scalar]
            simp [smul_smul, mul_comm]
      _ = 1 := by
            have hscalar : ((a⁻¹ * a⁻¹) * c : ℂ) = 1 := by
              calc
                (a⁻¹ * a⁻¹) * c = (a⁻¹ * a⁻¹) * (a * a) := by rw [hc_eq_sq]
                _ = 1 := by field_simp [ha_ne0]
            simp [hscalar]
  have hU_unitary_right : Uᴴ * U = 1 := mul_eq_one_comm.mp hU_unitary_left
  have hX_eq : X = a • U := by
    simp [U, ha_ne0]
  have hXinv_eq : Xin = a⁻¹ • Uᴴ := by
    have hXin' : X⁻¹ = a⁻¹ • Uᴴ := by
      apply Matrix.inv_eq_right_inv
      calc
        X * (a⁻¹ • Uᴴ) = (a • U) * (a⁻¹ • Uᴴ) := by rw [hX_eq]
        _ = (a * a⁻¹) • (U * Uᴴ) := by
              simpa [Matrix.mul_assoc] using smul_mul_smul_comm a U a⁻¹ Uᴴ
        _ = 1 := by simp [ha_ne0, hU_unitary_left]
    simpa [X, Xin] using hXin'
  refine ⟨Uᴴ, ζ⁻¹, ?_, ?_, ?_, ?_⟩
  · simpa using hU_unitary_right
  · simpa using hU_unitary_left
  · have hζ_norm : ‖ζ‖ = 1 := by
      have hsq : ‖ζ‖ ^ 2 = 1 := by
        simpa [Complex.normSq_eq_norm_sq] using hζ_sq_eq_one
      nlinarith [norm_nonneg ζ]
    simp [norm_inv, hζ_norm]
  · intro i
    have hBi : ∀ j : Fin d, B j = ζ • (U * A j * Uᴴ) := by
      intro j
      calc
        B j = ζ • (X * A j * Xin) := hX j
        _ = ζ • ((a • U) * A j * (a⁻¹ • Uᴴ)) := by rw [hX_eq, hXinv_eq]
        _ = ζ • (U * A j * Uᴴ) := by
              congr 1
              calc
                (a • U) * A j * (a⁻¹ • Uᴴ)
                    = (a • (U * A j)) * (a⁻¹ • Uᴴ) := by
                        simp [Matrix.mul_assoc]
                _ = (a * a⁻¹) • ((U * A j) * Uᴴ) := by
                      simpa [Matrix.mul_assoc] using
                        smul_mul_smul_comm a (U * A j) a⁻¹ Uᴴ
                _ = (a * a⁻¹) • (U * A j * Uᴴ) := by
                      simp [Matrix.mul_assoc]
                _ = U * A j * Uᴴ := by simp [ha_ne0]
    have hsum :
        ∑ j : Fin d, u i j • B j = A i := by
      have hcoeff :
          ∀ n' : Fin d,
            ∑ j : Fin d, u i j * (starRingEnd ℂ) (u n' j) = if i = n' then 1 else 0 := by
        intro n'
        have hentry := congrFun (congrFun hu i) n'
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hentry
      calc
        ∑ j : Fin d, u i j • B j
            = ∑ j : Fin d, ∑ n' : Fin d, (u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
                refine Finset.sum_congr rfl ?_
                intro j _
                have hBj :
                    B j = ∑ n' : Fin d, (starRingEnd ℂ) (u n' j) • A n' := by
                  simp [B, twistedMixedCompanion]
                rw [hBj]
                simpa [smul_smul, mul_assoc] using
                  (Finset.smul_sum (s := Finset.univ)
                    (f := fun n' : Fin d => (starRingEnd ℂ) (u n' j) • A n')
                    (r := u i j))
        _ = ∑ n' : Fin d, ∑ j : Fin d, (u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
              rw [Finset.sum_comm]
        _ = ∑ n' : Fin d, (∑ j : Fin d, u i j * (starRingEnd ℂ) (u n' j)) • A n' := by
              refine Finset.sum_congr rfl ?_
              intro n' _
              simpa using
                (Finset.sum_smul (s := Finset.univ)
                  (f := fun j : Fin d => u i j * (starRingEnd ℂ) (u n' j))
                  (x := A n')).symm
        _ = ∑ n' : Fin d, (if i = n' then 1 else 0) • A n' := by
              simp [hcoeff]
        _ = A i := by
              simp
    have htransport : Uᴴ * A i * U = ζ • (∑ j : Fin d, u i j • A j) := by
      have hsum_virtual : A i = ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ) := by
        calc
          A i = ∑ j : Fin d, u i j • B j := hsum.symm
          _ = ∑ j : Fin d, u i j • (ζ • (U * A j * Uᴴ)) := by
                simp [hBi]
          _ = ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ) := by
                simp [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, mul_comm,
                  smul_smul, Matrix.mul_assoc]
      have hconj := congrArg (fun M => Uᴴ * M * U) hsum_virtual
      calc
        Uᴴ * A i * U = Uᴴ * (ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ)) * U := by
              simpa [Matrix.mul_assoc] using hconj
        _ = ζ • (∑ j : Fin d, u i j • A j) := by
              calc
                Uᴴ * (ζ • (U * (∑ j : Fin d, u i j • A j) * Uᴴ)) * U
                    = ζ • (Uᴴ * ((U * (∑ j : Fin d, u i j • A j) * Uᴴ) * U)) := by
                        simp [Matrix.mul_assoc]
                _ = ζ • ((Uᴴ * U) * (∑ j : Fin d, u i j • A j) * (Uᴴ * U)) := by
                        simp [Matrix.mul_assoc]
                _ = ζ • (∑ j : Fin d, u i j • A j) := by
                        simp [hU_unitary_right]
    calc
      ∑ j : Fin d, u i j • A j = ζ⁻¹ • (ζ • (∑ j : Fin d, u i j • A j)) := by
            simp [hζ, smul_smul]
      _ = ζ⁻¹ • (Uᴴ * A i * U) := by
            rw [htransport]
      _ = ζ⁻¹ • (Uᴴ * A i * Uᴴᴴ) := by
            simp

/-- A phased virtual symmetry immediately produces a peripheral eigenvector of the
twisted transfer map. -/
theorem twistedTransfer_eigen_of_virtualUnitary
    (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ)
    (hNorm : transferMap A 1 = 1)
    (hV : V * Vᴴ = 1)
    (hC1μ : ∀ i : Fin d,
      ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ)) :
    twistedTransferMap A u V = μ • V := by
  have hV' : Vᴴ * V = 1 := by
    simpa using (mul_eq_one_comm.mp hV)
  calc
    twistedTransferMap A u V
        = ∑ i : Fin d, (∑ j : Fin d, u i j • A j) * V * (A i)ᴴ := by
            rw [twistedTransferMap_apply, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            simp [Finset.sum_mul, Matrix.mul_assoc]
    _ = ∑ i : Fin d, (μ • (V * A i * Vᴴ)) * V * (A i)ᴴ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hC1μ i]
    _ = μ • ∑ i : Fin d, V * A i * (A i)ᴴ := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            (μ • (V * A i * Vᴴ)) * V * (A i)ᴴ
                = μ • (((V * A i * Vᴴ) * V) * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
            _ = μ • ((V * A i * (Vᴴ * V)) * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
            _ = μ • ((V * A i) * (A i)ᴴ) := by
                    simp [hV', Matrix.mul_assoc]
            _ = μ • (V * A i * (A i)ᴴ) := by
                    simp [Matrix.mul_assoc]
    _ = μ • (V * ∑ i : Fin d, A i * (A i)ᴴ) := by
          simp [Matrix.mul_assoc, Matrix.mul_sum]
    _ = μ • (V * transferMap A 1) := by
          simp [transferMap_apply]
    _ = μ • V := by
          simp [hNorm]

/-- A phased virtual symmetry preserving the twisted transfer data also preserves
the stationary boundary state `Λ`, provided `Λ` is the unique fixed point of the
adjoint transfer channel. This is the paper's `V† Λ V = Λ` conclusion from
Lemma 1. -/
theorem boundaryState_invariant_of_virtualUnitary
    (A : MPSTensor d D)
    (hA : IsInjective A)
    (u : Matrix (Fin d) (Fin d) ℂ)
    (hu : u * uᴴ = 1)
    (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (V : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ)
    (hV : V * Vᴴ = 1) (hV' : Vᴴ * V = 1) (hμ : ‖μ‖ = 1)
    (hC1μ : ∀ i : Fin d,
      ∑ j : Fin d, u i j • A j = μ • (V * A i * Vᴴ)) :
    Vᴴ * Λ * V = Λ := by
  rcases eq_or_ne D 0 with hD | hD
  · subst hD
    simp at hΛtr
  haveI : NeZero D := ⟨hD⟩
  let B : MPSTensor d D := twistedMixedCompanion A u
  have hμ_ne : μ ≠ 0 := by
    intro hμ0
    have : ‖μ‖ = 0 := by simp [hμ0]
    rw [hμ] at this
    norm_num at this
  have hμ_sq : star μ * μ = 1 := by
    have hsq : ‖μ‖ * ‖μ‖ = 1 := by
      nlinarith [hμ]
    have hsqR : Complex.normSq μ = 1 := by
      simpa [Complex.normSq_eq_norm_sq, sq] using hsq
    have hsq' : (Complex.normSq μ : ℂ) = 1 := by
      exact_mod_cast hsqR
    rw [Complex.normSq_eq_conj_mul_self] at hsq'
    simpa using hsq'
  have huc : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hcoeff :
      ∀ k j : Fin d,
        ∑ i : Fin d, (starRingEnd ℂ) (u i k) * u i j = if k = j then 1 else 0 := by
    intro k j
    have hentry := congrFun (congrFun huc k) j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hentry
  have hA_from_B :
      ∀ k : Fin d, A k = μ • (V * B k * Vᴴ) := by
    intro k
    calc
      A k = ∑ j : Fin d, (if k = j then 1 else 0) • A j := by simp
      _ = ∑ j : Fin d, (∑ i : Fin d, (starRingEnd ℂ) (u i k) * u i j) • A j := by
            simp [hcoeff]
      _ = ∑ j : Fin d, ∑ i : Fin d, ((starRingEnd ℂ) (u i k) * u i j) • A j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_smul]
      _ = ∑ i : Fin d, ∑ j : Fin d, ((starRingEnd ℂ) (u i k) * u i j) • A j := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin d, (starRingEnd ℂ) (u i k) • (∑ j : Fin d, u i j • A j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp [smul_smul]
      _ = ∑ i : Fin d, (starRingEnd ℂ) (u i k) • (μ • (V * A i * Vᴴ)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hC1μ i]
      _ = μ • (V * B k * Vᴴ) := by
            simp [B, twistedMixedCompanion, smul_smul, mul_assoc,
              Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, mul_comm]
  have hB_eq :
      ∀ X : Matrix (Fin D) (Fin D) ℂ, transferMap B X = transferMap A X := by
    intro X
    simpa [B] using transferMap_twistedMixedCompanion_eq (A := A) (u := u) hu X
  have hBfix : transferMap (fun i => (B i)ᴴ) Λ = Λ := by
    calc
      transferMap (fun i => (B i)ᴴ) Λ
          = transferMap (fun i => (A i)ᴴ) Λ := by
              simpa [transferMap_apply, Matrix.mul_assoc] using
                kraus_dual_eq_of_map_eq B A
                  (fun X => by simpa [transferMap_apply] using hB_eq X) Λ
      _ = Λ := hΛfix
  let ρ : Matrix (Fin D) (Fin D) ℂ := V * Λ * Vᴴ
  have hρ_psd : ρ.PosSemidef := by
    simpa [ρ, Matrix.mul_assoc] using hΛpos.posSemidef.mul_mul_conjTranspose_same (B := V)
  have hρ_fix : transferMap (fun i => (A i)ᴴ) ρ = ρ := by
    calc
      transferMap (fun i => (A i)ᴴ) ρ
          = ∑ i : Fin d, (A i)ᴴ * ρ * A i := by
              simp [transferMap_apply]
      _ = ∑ i : Fin d, V * ((B i)ᴴ * Λ * B i) * Vᴴ := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              (A i)ᴴ * ρ * A i
                  = ((μ • (V * B i * Vᴴ))ᴴ) * ρ * (μ • (V * B i * Vᴴ)) := by
                      rw [hA_from_B i]
              _ = (star μ * μ) • (((V * B i * Vᴴ)ᴴ) * ρ * (V * B i * Vᴴ)) := by
                    simp [Matrix.conjTranspose_smul, smul_smul, Matrix.mul_assoc, mul_comm]
              _ = (star μ * μ) • (V * ((B i)ᴴ * Λ * B i) * Vᴴ) := by
                    congr 1
                    calc
                      ((V * B i * Vᴴ)ᴴ) * ρ * (V * B i * Vᴴ)
                          = (V * (B i)ᴴ * Vᴴ) * (V * Λ * Vᴴ) * (V * B i * Vᴴ) := by
                              simp [ρ, Matrix.conjTranspose_mul, Matrix.mul_assoc]
                      _ = V * (B i)ᴴ * (Vᴴ * V) * Λ * (Vᴴ * V) * B i * Vᴴ := by
                            simp [Matrix.mul_assoc]
                      _ = V * (B i)ᴴ * Λ * B i * Vᴴ := by simp [hV', Matrix.mul_assoc]
                      _ = V * ((B i)ᴴ * Λ * B i) * Vᴴ := by simp [Matrix.mul_assoc]
              _ = V * ((B i)ᴴ * Λ * B i) * Vᴴ := by
                    rw [hμ_sq, one_smul]
      _ = V * (∑ i : Fin d, (B i)ᴴ * Λ * B i) * Vᴴ := by
            simpa using
              (Matrix.sum_mul_mul
                (L := V) (M := fun i : Fin d => (B i)ᴴ * Λ * B i) (R := Vᴴ))
      _ = V * transferMap (fun i => (B i)ᴴ) Λ * Vᴴ := by
            simp [transferMap_apply]
      _ = ρ := by simp [ρ, hBfix, Matrix.mul_assoc]
  have hρ_tr : Matrix.trace ρ = 1 := by
    calc
      Matrix.trace ρ = Matrix.trace (V * Λ * Vᴴ) := rfl
      _ = Matrix.trace (Vᴴ * (V * Λ)) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle V Λ Vᴴ
      _ = Matrix.trace ((Vᴴ * V) * Λ) := by simp [Matrix.mul_assoc]
      _ = 1 := by simpa [hV'] using hΛtr
  have hρ_ne : ρ ≠ 0 := by
    intro hρ0
    simp [hρ0] at hρ_tr
  have hIrrA : IsIrreducibleMap (transferMap (d := d) (D := D) A) :=
    injective_implies_irreducibleCP A hA
  have hIrrTensor : IsIrreducibleTensor (d := d) (D := D) A :=
    isIrreducibleTensor_of_isIrreducibleMap A hIrrA
  have hIrrAdj :
      IsIrreducibleMap (transferMap (d := d) (D := D) fun i => (A i)ᴴ) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor A hIrrTensor
  have hΛ_ne : Λ ≠ 0 := by
    intro hΛ0
    simp [hΛ0] at hΛtr
  rcases posSemidef_fixedPoint_unique_of_irreducible (A := fun i => (A i)ᴴ) hIrrAdj
      Λ ρ hΛpos.posSemidef hΛ_ne hρ_psd hΛfix hρ_fix with ⟨c, hρ_scalar⟩
  have hc : c = 1 := by
    rw [hρ_scalar, Matrix.trace_smul, hΛtr] at hρ_tr
    simpa using hρ_tr
  have hρ_eq : ρ = Λ := by simpa [hc] using hρ_scalar
  calc
    Vᴴ * Λ * V = Vᴴ * ρ * V := by
      simpa [Matrix.mul_assoc] using congrArg (fun M => Vᴴ * M * V) hρ_eq.symm
    _ = Vᴴ * (V * (Λ * (Vᴴ * V))) := by simp [ρ, Matrix.mul_assoc]
    _ = Vᴴ * (V * Λ) := by simp [hV']
    _ = (Vᴴ * V) * Λ := by simp [Matrix.mul_assoc]
    _ = Λ := by simp [hV']

end MPSTensor

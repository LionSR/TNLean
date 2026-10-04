/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StationarySupportedDensityPhaseInvariance
import QICLean.Analysis.SupportCompression
import QICLean.Channel.Irreducible.FromSpectral
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.KoashiImoto.MeanErgodicProjection
import Mathlib.Tactic.Abel

/-!
# Irreducibility of a faithful stationary support compression

Compression to the entire support of a stationary density makes the compressed
density positive definite. If the ambient trace-one stationary matrix is
unique, the compressed trace-one stationary matrix is unique as well. When the
compressed tensor is unital, the adjoint channel criterion for irreducibility
then applies. Irreducibility passes from the adjoint channel to the primal
transfer map.

The fixed-point criterion and stationary support invariance follow Wolf,
Theorem 6.3 and Lemma 6.4. This is an auxiliary preparation result for
arXiv:1010.3732, Appendix C, lines 2653–2717; it does not identify the compressed
periodic rays with those of the ambient tensor.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix ComplexOrder
open Matrix

/-- A unital support compression of a uniquely stationary ambient tensor is
irreducible. Its compressed stationary density is faithful because the
compression uses the entire support. -/
theorem MPSTensor.isIrreducibleMap_of_unital_support_compression
    {d k D : ℕ} [NeZero D] (B : MPSTensor d k) (A : MPSTensor d D)
    (K : Matrix (Fin k) (Fin D) ℂ) (hK : K.IsIsometry)
    (hA : ∀ i, A i = Kᴴ * B i * K) (hUnital : Kraus.IsUnital A)
    (σ : Matrix (Fin k) (Fin k) ℂ) (hσ : σ.PosSemidef)
    (hsupport : K * Kᴴ = hσ.supportProj)
    (hfix : Kraus.adjointMap B σ = σ) (htrace : σ.trace = 1)
    (huniq : ∀ Z : Matrix (Fin k) (Fin k) ℂ,
      Kraus.adjointMap B Z = Z → Z.trace = 1 → Z = σ) :
    IsIrreducibleMap (Kraus.mapLM A) := by
  let ρ := Kᴴ * σ * K
  obtain ⟨hρfix, hρtr, hρunique⟩ :=
    MPSTensor.stationaryMatrix_compression_unique B A K hK hA σ hσ hsupport
      hfix htrace huniq
  have hρpd : ρ.PosDef := by
    simpa only [Matrix.conjTranspose_conjTranspose, ρ] using
      hσ.compression_on_support_posDef
        (V := Kᴴ) (by
          simpa only [Matrix.conjTranspose_conjTranspose] using
            (show Kᴴ * K = 1 from hK))
        (by simpa only [Matrix.conjTranspose_conjTranspose] using hsupport)
  have hTP : Kraus.IsTP (fun i => (A i)ᴴ) := by
    simpa only [Kraus.IsTP, Kraus.IsUnital, Matrix.conjTranspose_conjTranspose] using hUnital
  have hAdj : Kraus.mapLM (fun i => (A i)ᴴ) = Kraus.adjointMapLM A := by
    ext X
    simp only [Kraus.mapLM_apply, Kraus.map_apply,
      Matrix.conjTranspose_conjTranspose, Kraus.adjointMapLM_apply, Kraus.adjointMap_apply]
  have hIrr : IsIrreducibleMap (Kraus.adjointMapLM A) := by
    rw [← hAdj]
    apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique _
      (Kraus.isChannel_mapLM _ hTP) ρ hρpd (by rw [hAdj]; exact hρfix)
    intro Z _ hZ
    have hNorm : Kraus.adjointMap A (Z + (1 - Z.trace) • ρ) =
        Z + (1 - Z.trace) • ρ := by
      change Kraus.adjointMapLM A (Z + (1 - Z.trace) • ρ) = _
      rw [map_add, map_smul]
      change Kraus.adjointMap A Z + (1 - Z.trace) • Kraus.adjointMap A ρ = _
      rw [hρfix]
      simpa only [Kraus.mapLM_apply, Matrix.conjTranspose_conjTranspose,
        Kraus.map_apply, Kraus.adjointMap_apply] using congrArg
          (fun X => X + (1 - Z.trace) • ρ) hZ
    have hTr : (Z + (1 - Z.trace) • ρ).trace = 1 := by
      rw [Matrix.trace_add, Matrix.trace_smul, hρtr]
      ring
    have h := hρunique _ hNorm hTr
    refine ⟨Z.trace, ?_⟩
    calc Z = (Z + (1 - Z.trace) • ρ) - (1 - Z.trace) • ρ :=
          (add_sub_cancel_right _ _).symm
      _ = ρ - (1 - Z.trace) • ρ := congrArg (fun X => X - (1 - Z.trace) • ρ) h
      _ = Z.trace • ρ := by rw [sub_smul, one_smul]; abel
  apply (isIrreducibleMap_traceAdjointMap_iff (Kraus.isPositiveMap_mapLM A)).mp
  simpa only [Kraus.traceAdjointMap_mapLM] using hIrr

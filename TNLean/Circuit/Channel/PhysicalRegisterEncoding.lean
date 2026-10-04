/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.NativeRegisterWires
import QICLean.Channel.LocalizedKrausCPTP

/-!
# Physical register encodings with an explicit untouched reference

The complement of the data wires consists of the physical ports and scratch registers.
It is retained as an arbitrary reference, rather than assumed initially uncorrelated
with the input. Native encoding and decoding maps are transported through the sitewise
digit equivalence and the exact data/complement split. Retractions and channel
intertwining survive this transport on all operators.

The coordinate equivalences describe where the data reside; they are not asserted to
be extra free gates. Physical gate costs are certified separately by the port protocol.
-/

open Matrix

namespace QuantumCircuit.PortRegisters

noncomputable section

variable {N k d : ℕ} {α β : Type*}

/-- The full configuration of wires outside the data registers. -/
abbrev DataReference (N k d : ℕ) :=
  {w : Fin (N * (1 + k + k)) // w ∉ Set.range (allData N k)} → Fin d

/-- Encode a native input into the physical data registers, retaining the complementary
port/scratch configuration as an arbitrary identity reference. -/
def physicalEncoding
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ) :
    Matrix (α × DataReference N k d) (α × DataReference N k d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ :=
  (registerMatrixSplit (allData N k)).symm.toLinearMap ∘ₗ
    tensorMapIdLM ((nativeMatrixEquiv N k d).toLinearMap ∘ₗ E)

/-- Decode the physical data registers while retaining the same complementary reference. -/
def physicalDecoding
    (D : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ →ₗ[ℂ] Matrix α α ℂ) :
    Matrix (Fin (N * (1 + k + k)) → Fin d) (Fin (N * (1 + k + k)) → Fin d) ℂ →ₗ[ℂ]
      Matrix (α × DataReference N k d) (α × DataReference N k d) ℂ :=
  tensorMapIdLM (D ∘ₗ (nativeMatrixEquiv N k d).symm.toLinearMap) ∘ₗ
    (registerMatrixSplit (allData N k)).toLinearMap

/-- A CPTP native encoding remains CPTP with the explicit complementary reference. -/
theorem physicalEncoding_isKrausCPTP [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ}
    (hE : IsKrausCPTP E) : IsKrausCPTP (physicalEncoding E) := by
  have hG : IsKrausCPTP (nativeMatrixEquiv N k d).toLinearMap :=
    equivReindexMap_isKrausCPTP (groupedConfigurations N k d).symm
  have hS : IsKrausCPTP (registerMatrixSplit (d := d) (allData N k)).symm.toLinearMap :=
    equivReindexMap_isKrausCPTP (registerConfigurationSplit (d := d) (allData N k)).symm
  exact isKrausCPTP_comp (tensorMapIdLM_isKrausCPTP (isKrausCPTP_comp hE hG)) hS

/-- A completed CPTP native decoder remains CPTP on the entire physical operator space. -/
theorem physicalDecoding_isKrausCPTP [Fintype α] [DecidableEq α]
    {D : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hD : IsKrausCPTP D) : IsKrausCPTP (physicalDecoding D) := by
  have hG : IsKrausCPTP (nativeMatrixEquiv N k d).symm.toLinearMap :=
    equivReindexMap_isKrausCPTP (groupedConfigurations N k d)
  have hS : IsKrausCPTP (registerMatrixSplit (d := d) (allData N k)).toLinearMap :=
    equivReindexMap_isKrausCPTP (registerConfigurationSplit (d := d) (allData N k))
  exact isKrausCPTP_comp hS (tensorMapIdLM_isKrausCPTP (isKrausCPTP_comp hG hD))

/-- Native decoding/encoding retractions remain exact with arbitrary port/scratch
correlations in the physical representation. -/
theorem physicalDecoding_encoding
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ)
    (D : Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ →ₗ[ℂ] Matrix α α ℂ)
    (hDE : D ∘ₗ E = LinearMap.id) :
    physicalDecoding D ∘ₗ physicalEncoding E = LinearMap.id := by
  let G := nativeMatrixEquiv N k d
  let S := registerMatrixSplit (d := d) (allData N k)
  have h : (D ∘ₗ G.symm.toLinearMap) ∘ₗ (G.toLinearMap ∘ₗ E) = LinearMap.id := by
    apply LinearMap.ext
    intro X
    change D (G.symm (G (E X))) = X
    rw [G.symm_apply_apply]
    exact LinearMap.congr_fun hDE X
  apply LinearMap.ext
  intro X
  change tensorMapIdLM (D ∘ₗ G.symm.toLinearMap)
    (S (S.symm (tensorMapIdLM (G.toLinearMap ∘ₗ E) X))) = X
  rw [S.apply_symm_apply]
  change (tensorMapIdLM (D ∘ₗ G.symm.toLinearMap) ∘ₗ
    tensorMapIdLM (G.toLinearMap ∘ₗ E)) X = X
  rw [← tensorMapIdLM_comp, h, tensorMapIdLM_id, LinearMap.id_apply]

/-- An exact native code intertwiner becomes an exact physical-channel intertwiner,
with the entire port/scratch system as an arbitrary reference. -/
theorem dataChannelLift_physicalEncoding
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ)
    (F : Matrix β β ℂ →ₗ[ℂ] Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ)
    (Φ : Module.End ℂ (Matrix (Fin N → Fin (d ^ k)) (Fin N → Fin (d ^ k)) ℂ))
    (Ψ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (h : Φ ∘ₗ E = F ∘ₗ Ψ) :
    dataChannelLift N k d Φ ∘ₗ physicalEncoding E =
      physicalEncoding F ∘ₗ tensorMapIdLM Ψ := by
  let G := nativeMatrixEquiv N k d
  let S := registerMatrixSplit (d := d) (allData N k)
  have hG : nativeChannelReindex N k d Φ ∘ₗ (G.toLinearMap ∘ₗ E) =
      (G.toLinearMap ∘ₗ F) ∘ₗ Ψ := by
    apply LinearMap.ext
    intro X
    change G (Φ (G.symm (G (E X)))) = G (F (Ψ X))
    rw [G.symm_apply_apply]
    exact congrArg G (LinearMap.congr_fun h X)
  apply LinearMap.ext
  intro X
  apply S.injective
  change S (S.symm (tensorMapIdLM (nativeChannelReindex N k d Φ)
      (S (S.symm (tensorMapIdLM (G.toLinearMap ∘ₗ E) X))))) =
    S (S.symm (tensorMapIdLM (G.toLinearMap ∘ₗ F) (tensorMapIdLM Ψ X)))
  simp only [S.apply_symm_apply]
  change (tensorMapIdLM (nativeChannelReindex N k d Φ) ∘ₗ
      tensorMapIdLM (G.toLinearMap ∘ₗ E)) X =
    (tensorMapIdLM (G.toLinearMap ∘ₗ F) ∘ₗ tensorMapIdLM Ψ) X
  rw [← tensorMapIdLM_comp, ← tensorMapIdLM_comp, hG]

end

end QuantumCircuit.PortRegisters

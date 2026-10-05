/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.WholeSiteChannels
import TNLean.Circuit.Channel.OnsiteRegisterEncoding

/-!
# Product zero-memory codes for physical-port input and output

The port code stores the input qudit on the physical port and initializes both memory
registers to zero. The data code stores its native register code in the data digits,
with zero port and scratch digits. Products of completed local channels move between
these two codes at zero physical depth. Both channels are CPTP on the entire physical
space, and their code identities hold on arbitrary operators.

The logical input and output alphabet in this construction is the physical alphabet
`Fin d`. No dilation or source QCcc protocol-block witness is asserted here.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace QuantumCircuit.PortRegisters

noncomputable section

variable {N k d w : ℕ}

/-- Convert a qudit-word code into the equivalent finite native alphabet. -/
def nativeWordCode (c : Fin d ↪ (Fin w → Fin d)) : Fin d ↪ Fin (d ^ w) :=
  c.trans finFunctionFinEquiv.toEmbedding

/-- The product configuration code, with each local word placed in its own spatial block. -/
def wordCodeConfiguration (c : Fin d ↪ (Fin w → Fin d)) :
    (Fin N → Fin d) ↪ (Fin (N * w) → Fin d) :=
  (Function.Embedding.piCongrRight fun _ : Fin N => nativeWordCode c).trans
    (groupedConfigurations N w d).symm.toEmbedding

@[simp] theorem wordCodeConfiguration_apply (c : Fin d ↪ (Fin w → Fin d))
    (x : Fin N → Fin d) (i : Fin N) (t : Fin w) :
    wordCodeConfiguration c x (finProdFinEquiv (i, t)) = c (x i) t := by
  change finFunctionFinEquiv.symm
    (nativeWordCode c (x (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1))
    (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2 = _
  rw [Equiv.symm_apply_apply]
  exact congrFun (finFunctionFinEquiv.symm_apply_apply (c (x i))) t

private theorem grouped_wordCodeConfiguration (c : Fin d ↪ (Fin w → Fin d))
    (x : Fin N → Fin d) :
    groupedConfigurations N w d (wordCodeConfiguration c x) = fun i => nativeWordCode c (x i) :=
  (groupedConfigurations N w d).apply_symm_apply _

/-- Initialize a product of local pure codewords on the physical wire blocks. -/
def wordInitialization (c : Fin d ↪ (Fin w → Fin d)) :
    Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N * w) → Fin d) (Fin (N * w) → Fin d) ℂ :=
  singleKrausMap (registerEncoding (wordCodeConfiguration c))

/-- Product code initialization preserves trace and complete positivity. -/
theorem wordInitialization_isKrausCPTP (c : Fin d ↪ (Fin w → Fin d)) :
    IsKrausCPTP (wordInitialization (N := N) c) :=
  registerEncoding_isKrausCPTP _

/-- The explicit product-code isometry is the sitewise encoder in physical coordinates. -/
theorem wordInitialization_eq (c : Fin d ↪ (Fin w → Fin d)) :
    wordInitialization (N := N) c = (nativeMatrixEquiv N w d).toLinearMap ∘ₗ
      (OnsiteChannel.encodeRegisters fun _ : Fin N => nativeWordCode c).map := by
  let U := rectKronecker fun _ : Fin N => registerEncoding (nativeWordCode c)
  have hV : registerEncoding (wordCodeConfiguration (N := N) c) =
      U.submatrix (groupedConfigurations N w d) id := by
    ext x y
    simp only [U, registerEncoding, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
      rectKronecker_apply, Fintype.prod_boole]
    congr 1
    apply propext
    rw [← funext_iff, ← grouped_wordCodeConfiguration c y]
    exact (groupedConfigurations N w d).injective.eq_iff.symm
  rw [wordInitialization, hV, OnsiteChannel.encodeRegisters_map]
  apply LinearMap.ext
  intro X
  change (U.submatrix (groupedConfigurations N w d) id) * X *
    (U.submatrix (groupedConfigurations N w d) id)ᴴ =
      (U * X * Uᴴ).submatrix (groupedConfigurations N w d) (groupedConfigurations N w d)
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id_eq]

/-- The independent completed local conversion from one pure code to another. -/
def wordCodeChange (c f : Fin d ↪ (Fin w → Fin d)) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    OnsiteChannel (d ^ w) (d ^ w) (Fin N) :=
  (OnsiteChannel.id d (Fin N)).encoded (fun _ => nativeWordCode c)
    (fun _ => nativeWordCode f) (fun _ => ρ) (fun _ => hρ) (fun _ => htr)

/-- Apply the completed local code conversions on the physical wire blocks. -/
def wordCodeChangeMap (c f : Fin d ↪ (Fin w → Fin d)) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    Module.End ℂ (Matrix (Fin (N * w) → Fin d) (Fin (N * w) → Fin d) ℂ) :=
  nativeChannelReindex N w d (wordCodeChange c f ρ hρ htr).map

/-- The completed product channel converts the first pure code exactly into the second. -/
theorem wordCodeChangeMap_initialization (c f : Fin d ↪ (Fin w → Fin d))
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    wordCodeChangeMap (N := N) c f ρ hρ htr ∘ₗ wordInitialization c =
      wordInitialization f := by
  have h := (OnsiteChannel.id d (Fin N)).encoded_map_encodeRegisters
    (fun _ => nativeWordCode c) (fun _ => nativeWordCode f) (fun _ => ρ)
    (fun _ => hρ) (fun _ => htr)
  simp only [OnsiteChannel.id_map, LinearMap.comp_id] at h
  rw [wordInitialization_eq, wordInitialization_eq]
  apply LinearMap.ext
  intro X
  let G := nativeMatrixEquiv N w d
  change G ((wordCodeChange c f ρ hρ htr).map
    (G.symm (G ((OnsiteChannel.encodeRegisters fun _ : Fin N => nativeWordCode c).map X)))) =
      G ((OnsiteChannel.encodeRegisters fun _ : Fin N => nativeWordCode f).map X)
  rw [G.symm_apply_apply]
  exact congrArg G (LinearMap.congr_fun h X)

/-- Independent code changes on complete physical site blocks have zero intersite depth. -/
theorem wordCodeChangeMap_isPhysicalPortProtocol [NeZero N] (hd : 0 < d)
    (c f : Fin d ↪ (Fin (1 + k + k) → Fin d)) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    IsPhysicalPortProtocol (layout N k) 0 (wordCodeChangeMap c f ρ hρ htr) :=
  wholeSite_onsiteChannel hd (wordCodeChange c f ρ hρ htr)

variable [NeZero d]

/-- Store the physical input on its port and set both memory registers to zero. -/
def portWordCode (d k : ℕ) [NeZero d] : Fin d ↪ (Fin (1 + k + k) → Fin d) where
  toFun x := Fin.append (Fin.append (fun _ : Fin 1 => x) (fun _ : Fin k => 0))
    (fun _ : Fin k => 0)
  inj' x y h := by
    have h0 := congrFun h (Fin.castAdd k (Fin.castAdd k (0 : Fin 1)))
    simpa only [Fin.append_left] using h0

/-- Store the input's register code on data digits, with zero port and scratch digits. -/
def dataWordCode (c : Fin d ↪ Fin (d ^ k)) : Fin d ↪ (Fin (1 + k + k) → Fin d) where
  toFun x := Fin.append (Fin.append (fun _ : Fin 1 => 0) (finFunctionFinEquiv.symm (c x)))
    (fun _ : Fin k => 0)
  inj' x y h := by
    apply c.injective
    apply finFunctionFinEquiv.symm.injective
    funext t
    have ht := congrFun h (Fin.castAdd k (Fin.natAdd 1 t))
    simpa only [Fin.append_left, Fin.append_right] using ht

@[simp] theorem portWordCode_apply (x : Fin d) :
    portWordCode d k x = Fin.append
      (Fin.append (fun _ : Fin 1 => x) (fun _ : Fin k => 0)) (fun _ : Fin k => 0) := rfl

@[simp] theorem dataWordCode_apply (c : Fin d ↪ Fin (d ^ k)) (x : Fin d) :
    dataWordCode c x = Fin.append
      (Fin.append (fun _ : Fin 1 => 0) (finFunctionFinEquiv.symm (c x)))
      (fun _ : Fin k => 0) := rfl

@[simp] theorem portWordCode_port (x : Fin d) :
    portWordCode d k x (Fin.castAdd k (Fin.castAdd k (0 : Fin 1))) = x := by
  simp only [portWordCode_apply, Fin.append_left]

@[simp] theorem portWordCode_data (x : Fin d) (t : Fin k) :
    portWordCode d k x (Fin.castAdd k (Fin.natAdd 1 t)) = 0 := by
  simp only [portWordCode_apply, Fin.append_left, Fin.append_right]

@[simp] theorem portWordCode_scratch (x : Fin d) (t : Fin k) :
    portWordCode d k x (Fin.natAdd (1 + k) t) = 0 := by
  simp only [portWordCode_apply, Fin.append_right]

@[simp] theorem dataWordCode_port (c : Fin d ↪ Fin (d ^ k)) (x : Fin d) :
    dataWordCode c x (Fin.castAdd k (Fin.castAdd k (0 : Fin 1))) = 0 := by
  simp only [dataWordCode_apply, Fin.append_left]

@[simp] theorem dataWordCode_data (c : Fin d ↪ Fin (d ^ k)) (x : Fin d) (t : Fin k) :
    dataWordCode c x (Fin.castAdd k (Fin.natAdd 1 t)) = finFunctionFinEquiv.symm (c x) t := by
  simp only [dataWordCode_apply, Fin.append_left, Fin.append_right]

@[simp] theorem dataWordCode_scratch (c : Fin d ↪ Fin (d ^ k)) (x : Fin d) (t : Fin k) :
    dataWordCode c x (Fin.natAdd (1 + k) t) = 0 := by
  simp only [dataWordCode_apply, Fin.append_right]

/-- Actual zero-depth pre- and postprocessing moves between original physical-port input
with product-zero memory and the data-register code with product-zero port/scratch wires. -/
theorem exists_portDataTransfers [NeZero N] (c : Fin d ↪ Fin (d ^ k))
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    ∃ pre post,
      IsPhysicalPortProtocol (layout N k) 0 pre ∧
      IsPhysicalPortProtocol (layout N k) 0 post ∧
      pre ∘ₗ wordInitialization (portWordCode d k) = wordInitialization (dataWordCode c) ∧
      post ∘ₗ wordInitialization (dataWordCode c) = wordInitialization (portWordCode d k) := by
  refine ⟨wordCodeChangeMap (portWordCode d k) (dataWordCode c) ρ hρ htr,
    wordCodeChangeMap (dataWordCode c) (portWordCode d k) ρ hρ htr, ?_, ?_, ?_, ?_⟩
  · exact wordCodeChangeMap_isPhysicalPortProtocol (NeZero.pos d) _ _ ρ hρ htr
  · exact wordCodeChangeMap_isPhysicalPortProtocol (NeZero.pos d) _ _ ρ hρ htr
  · exact wordCodeChangeMap_initialization _ _ ρ hρ htr
  · exact wordCodeChangeMap_initialization _ _ ρ hρ htr

end

end QuantumCircuit.PortRegisters

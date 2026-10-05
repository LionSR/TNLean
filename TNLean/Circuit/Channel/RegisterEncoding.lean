/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.SupportCompletion
import QICLean.Channel.TensorMap
import QICLean.Algebra.MatrixUnitaryBetween
import Mathlib.Data.Nat.Log

/-!
# Channel encodings into bounded qudit registers

A finite local state space embeds isometrically in a register of fixed-dimensional qudits.
Decoding must also act on matrices outside the encoded subspace: projecting alone loses
trace. We use the existing support-completion channel to prepare a fixed state on that
complement. Decoding after encoding is exactly the identity on every operator, so the
construction preserves arbitrary input states, including correlations with a reference.

This is the local encoding step for the physical-port resource comparison of
Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8. It does not itself
implement communication between sites or establish a circuit-depth comparison.
-/

open Matrix
open scoped ComplexOrder

namespace QuantumCircuit

noncomputable section

variable {α β : Type*} [Fintype β] [DecidableEq β]
  [Fintype α] [DecidableEq α]

/-- An isometric matrix for an injective assignment of input basis labels to register words. -/
def registerEncoding (e : α ↪ β) : Matrix β α ℂ :=
  (1 : Matrix β β ℂ).submatrix id e

omit [Fintype α] in
/-- The chosen register encoding preserves inner products. -/
theorem registerEncoding_isIsometry (e : α ↪ β) :
    (registerEncoding e).IsIsometry := by
  change ((1 : Matrix β β ℂ).submatrix id e)ᴴ *
    (1 : Matrix β β ℂ).submatrix id e = 1
  simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix β β ℂ).submatrix e
    (Equiv.refl _) * (1 : Matrix β β ℂ).submatrix
      (Equiv.refl _) e = 1
  rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
  exact Matrix.submatrix_one e e.injective

/-- Encoding a local operator into the register is a channel. -/
theorem registerEncoding_isKrausCPTP (e : α ↪ β) :
    IsKrausCPTP (singleKrausMap (registerEncoding e)) :=
  singleKrausMap_isKrausCPTP _ (registerEncoding_isIsometry e)

/-- A trace-preserving decoder; the unused register subspace is sent to a fixed state `ρ`. -/
def registerDecoding (e : α ↪ β) (ρ : Matrix α α ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix α α ℂ :=
  supportCompletion (singleKrausMap (registerEncoding e)ᴴ)
    (registerEncoding e * (registerEncoding e)ᴴ) ρ

/-- The completed decoder is a channel for every density matrix chosen on the complement. -/
theorem registerDecoding_isKrausCPTP (e : α ↪ β)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    IsKrausCPTP (registerDecoding e ρ) := by
  let V := registerEncoding e
  have hV : Vᴴ * V = 1 := registerEncoding_isIsometry e
  apply supportCompletion_isKrausCPTP
  · exact singleKrausMap_isKrausCP _
  · exact isHermitian_mul_conjTranspose_self _
  · change V * Vᴴ * (V * Vᴴ) = V * Vᴴ
    calc V * Vᴴ * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
         _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  · intro X
    simp only [singleKrausMap_apply, conjTranspose_conjTranspose]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · exact hρ
  · exact htr

/-- Decoding an encoded operator recovers it exactly, without any positivity assumption. -/
theorem registerDecoding_encoding (e : α ↪ β)
    (ρ X : Matrix α α ℂ) :
    registerDecoding e ρ (singleKrausMap (registerEncoding e) X) = X := by
  let V := registerEncoding e
  have hV : Vᴴ * V = 1 := registerEncoding_isIsometry e
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    calc V * Vᴴ * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
         _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  change supportCompletion (singleKrausMap Vᴴ) (V * Vᴴ) ρ (V * X * Vᴴ) = X
  rw [supportCompletion_apply_of_supported _ _ ρ _ (isHermitian_mul_conjTranspose_self _) hP]
  · simp only [singleKrausMap_apply, conjTranspose_conjTranspose]
    calc Vᴴ * (V * X * Vᴴ) * V = (Vᴴ * V) * X * (Vᴴ * V) := by
           simp only [Matrix.mul_assoc]
         _ = X := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  · calc V * Vᴴ * (V * X * Vᴴ) * (V * Vᴴ) =
          V * (Vᴴ * V) * X * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
         _ = V * X * Vᴴ := by rw [hV, Matrix.mul_one, Matrix.mul_one]

/-- Encoding followed by decoding is the identity channel, as an equality of linear maps. -/
theorem registerDecoding_comp_encoding (e : α ↪ β)
    (ρ : Matrix α α ℂ) :
    registerDecoding e ρ ∘ₗ singleKrausMap (registerEncoding e) = LinearMap.id := by
  apply LinearMap.ext
  exact registerDecoding_encoding e ρ

/-- Encoding and decoding leave an arbitrary external reference untouched. -/
theorem registerDecoding_encoding_reference {δ : Type*}
    (e : α ↪ β) (ρ : Matrix α α ℂ) :
    tensorMapIdLM (δ := δ) (registerDecoding e ρ) ∘ₗ
      tensorMapIdLM (δ := δ) (singleKrausMap (registerEncoding e)) = LinearMap.id := by
  rw [← tensorMapIdLM_comp, registerDecoding_comp_encoding, tensorMapIdLM_id]

variable {γ δ : Type*} [Fintype δ] [DecidableEq δ] [Fintype γ] [DecidableEq γ]

/-- Extend a channel to the complete input register, including words outside its code. -/
def registerEncodedMap (e : α ↪ β) (f : γ ↪ δ)
    (ρ : Matrix α α ℂ) (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix γ γ ℂ) :
    Matrix β β ℂ →ₗ[ℂ] Matrix δ δ ℂ :=
  singleKrausMap (registerEncoding f) ∘ₗ Φ ∘ₗ registerDecoding e ρ

/-- The extension outside the code is genuinely CPTP, not a trace-losing compression. -/
theorem registerEncodedMap_isKrausCPTP (e : α ↪ β) (f : γ ↪ δ)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    {Φ : Matrix α α ℂ →ₗ[ℂ] Matrix γ γ ℂ} (hΦ : IsKrausCPTP Φ) :
    IsKrausCPTP (registerEncodedMap e f ρ Φ) :=
  isKrausCPTP_comp (isKrausCPTP_comp (registerDecoding_isKrausCPTP e hρ htr) hΦ)
    (registerEncoding_isKrausCPTP f)

omit [DecidableEq γ] in
/-- On encoded inputs the extended channel agrees exactly with the original channel. -/
theorem registerEncodedMap_encoding (e : α ↪ β) (f : γ ↪ δ)
    (ρ : Matrix α α ℂ) (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix γ γ ℂ)
    (X : Matrix α α ℂ) :
    registerEncodedMap e f ρ Φ (singleKrausMap (registerEncoding e) X) =
      singleKrausMap (registerEncoding f) (Φ X) := by
  simp only [registerEncodedMap, LinearMap.comp_apply, registerDecoding_encoding]

omit [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α] in
/-- The ceiling logarithm suffices uniformly for all local dimensions bounded by `B`. -/
theorem le_registerDimension {d B m : ℕ} (hd : 2 ≤ d) (hm : m ≤ B) :
    m ≤ d ^ Nat.clog d B :=
  hm.trans (Nat.le_pow_clog hd B)

/-- Choose a register basis encoding from the numerical dimension bound. -/
def registerBasisEmbedding {d k m : ℕ} (h : m ≤ d ^ k) :
    Fin m ↪ (Fin k → Fin d) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

end

end QuantumCircuit

/-!
## Independent encodings of two local systems into qudit registers

The joint basis encoding is the tensor product of its two local encodings. Thus choosing
a register code does not supply hidden communication or entangling operations between
sites. Combining this identity with the completed register-channel extension allows
arbitrary bounded-dimensional pair channels to use the physical-port routing construction.

Source resource convention: Piroli, Styliaris and Cirac, arXiv:2103.13367,
Supplement pp. 7–8. The encoding identities are derived finite-dimensional statements.
-/

open Matrix

namespace QuantumCircuit

variable {d k : ℕ} {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

/-- Encode the two systems separately into the first and second qudit registers. -/
def pairRegisterBasisEmbedding (e : α ↪ (Fin k → Fin d)) (f : β ↪ (Fin k → Fin d)) :
    (α × β) ↪ (Fin (k + k) → Fin d) where
  toFun x := Fin.append (e x.1) (f x.2)
  inj' a b hab := by
    apply Prod.ext
    · apply e.injective
      funext t
      simpa only [Fin.append_left] using congrFun hab (Fin.castAdd k t)
    · apply f.injective
      funext t
      simpa only [Fin.append_right] using congrFun hab (Fin.natAdd k t)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] theorem pairRegisterBasisEmbedding_apply
    (e : α ↪ (Fin k → Fin d)) (f : β ↪ (Fin k → Fin d)) (a : α) (b : β) :
    pairRegisterBasisEmbedding e f (a, b) = Fin.append (e a) (f b) := rfl

omit [Fintype α] [DecidableEq α] in
/-- The entries of a register basis inclusion are Kronecker deltas. -/
theorem registerEncoding_apply {ι : Type*} [Fintype ι]
    (e : α ↪ (ι → Fin d)) (x : ι → Fin d) (a : α) :
    registerEncoding e x a = if x = e a then 1 else 0 := by
  simp only [registerEncoding, Matrix.submatrix_apply, id_eq, Matrix.one_apply]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The joint encoding factors exactly into the two local encoding matrices. -/
theorem registerEncoding_pair (e : α ↪ (Fin k → Fin d)) (f : β ↪ (Fin k → Fin d))
    (x : Fin (k + k) → Fin d) (a : α) (b : β) :
    registerEncoding (pairRegisterBasisEmbedding e f) x (a, b) =
      registerEncoding e (x ∘ Fin.castAdd k) a *
        registerEncoding f (x ∘ Fin.natAdd k) b := by
  have hiff : x = Fin.append (e a) (f b) ↔
      x ∘ Fin.castAdd k = e a ∧ x ∘ Fin.natAdd k = f b := by
    constructor
    · rintro rfl
      constructor <;> funext t <;> simp only [Function.comp_apply,
        Fin.append_left, Fin.append_right]
    · rintro ⟨hleft, hright⟩
      funext t
      refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · rw [Fin.append_left]
        exact congrFun hleft t
      · rw [Fin.append_right]
        exact congrFun hright t
  simp only [registerEncoding_apply, pairRegisterBasisEmbedding_apply, hiff]
  split_ifs <;> simp_all

end QuantumCircuit

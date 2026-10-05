/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.GHZSeedCircuit
import TNLean.MPS.Preparation.PolarFrame
import TNLean.Circuit.CoherentEncoder

/-!
# Canonical sector encoders and coherent block encoders

The actual periodic vectors of a labelled family of tensors form a column matrix `V`.
Its polar isometry is the canonical encoder of this family. The endpoint depends on the
family and ring length, and is independent of any approximation accuracy or block partition.
When the columns are independent, this encoder is isometric and has their exact span.

The encoded GHZ configurations give a common isometric seed `J`. The simultaneous block
circuit satisfies `U J = W` for the entire matrix of block-isometry states. Thus `W` is an
isometry on all logical amplitudes, without separate circuits or phase choices by sector.

## Main results

* `MPSTensor.sectorEncoder` is the polar encoder of the actual sector vectors.
* `MPSPreparation.isIsometry_registerEncoder` identifies the common isometric seed.
* `MPSPreparation.exists_isLocalCircuitOfDepth_registerEncoder` implements the whole block
  encoder by one genuine local unitary with a uniform linear block-length bound.
* `MPSPreparation.norm_sectorEncoder_conversion_le` converts the fixed polar endpoints from
  phase-sensitive Gram and cross estimates, with one unitary for every logical input.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equation (25), the paragraph
  "Long-range MPS using measurements", and discussion and outlook. The canonical polar
  encoding of the complete sector span is an additional precise choice, not a definition
  of a phase relation from that paper.
-/

open Matrix MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace MPSTensor

variable {d b : ℕ} {D : Fin b → ℕ}

/-- The actual periodic sector vectors as columns, with no normalization or phase changes. -/
noncomputable def sectorColumnMatrix (A : (j : Fin b) → MPSTensor d (D j)) (N : ℕ) :
    Matrix (Cfg d N) (Fin b) ℂ := fun s j => mpv (A j) s

/-- The polar orthonormal encoding of the labelled periodic sector vectors. It is independent
of an error tolerance and a partition; it is an isometry when those vectors are independent. -/
noncomputable def sectorEncoder (A : (j : Fin b) → MPSTensor d (D j)) (N : ℕ) :
    Matrix (Cfg d N) (Fin b) ℂ := Matrix.polarIso (sectorColumnMatrix A N)

/-- Linear independence of the actual periodic columns makes the canonical encoder isometric. -/
theorem isIsometry_sectorEncoder (A : (j : Fin b) → MPSTensor d (D j)) (N : ℕ)
    (hA : Function.Injective (sectorColumnMatrix A N).mulVec) :
    (sectorEncoder A N).IsIsometry := Matrix.isIsometry_polarIso_of_injective _ hA

/-- The canonical encoder has exactly the span of the original periodic sector vectors,
even at lengths where those vectors are linearly dependent. -/
theorem range_sectorEncoder (A : (j : Fin b) → MPSTensor d (D j)) (N : ℕ) :
    LinearMap.range (sectorEncoder A N).mulVecLin =
      Submodule.span ℂ (Set.range fun j => (mpv (A j) : Cfg d N → ℂ)) := by
  change LinearMap.range (sectorEncoder A N).mulVecLin =
    Submodule.span ℂ (Set.range (sectorColumnMatrix A N).col)
  rw [← Matrix.range_mulVecLin (sectorColumnMatrix A N)]
  apply le_antisymm
  · rw [sectorEncoder, Matrix.polarIso, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rintro _ ⟨v, rfl⟩
    refine ⟨Matrix.polarPos (sectorColumnMatrix A N) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, sectorEncoder, Matrix.mulVec_mulVec,
      Matrix.polarIso_mul_polarPos]

/-- Entries of the sector Gram matrix are the full complex periodic overlaps. -/
theorem gram_sectorColumnMatrix_apply (A : (j : Fin b) → MPSTensor d (D j)) (N : ℕ)
    (i j : Fin b) :
    ((sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N) i j =
      ⟪mpvState (A i) N, mpvState (A j) N⟫_ℂ := by
  simp [Matrix.mul_apply, sectorColumnMatrix, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The matrix of simultaneous blocked polar states, one column for each logical label. -/
noncomputable def blockIsometryEncoder {D M N : ℕ} (A : MPSTensor d D)
    (ω : Fin b → Fin D × Fin D → ℂ) {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N) :
    Matrix (Cfg d N) (Fin b) ℂ := fun s j => blockIsometryState A (ω j) hN s

/-- The complex cross matrix between a block encoder and the actual sector columns records
all phase-sensitive overlaps, including off-diagonal ones. -/
theorem cross_blockIsometryEncoder_sectorColumnMatrix_apply {D' M N : ℕ}
    (A : MPSTensor d D') (ω : Fin b → Fin D' × Fin D' → ℂ)
    {ℓ : Fin M → ℕ} (hN : ∑ k, ℓ k = N)
    (B : (j : Fin b) → MPSTensor d (D j)) (i j : Fin b) :
    ((blockIsometryEncoder A ω hN)ᴴ * sectorColumnMatrix B N) i j =
      ⟪blockIsometryState A (ω i) hN, mpvState (B j) N⟫_ℂ := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, blockIsometryEncoder,
    sectorColumnMatrix, PiLp.inner_apply, RCLike.inner_apply, mpvState_apply]
  congr 1
  ext s
  exact mul_comm _ _

end MPSTensor

namespace MPSPreparation

variable {d b r M N : ℕ} [NeZero d] [NeZero M] {ℓ : Fin M → ℕ}

/-- Reading any one register recovers the register configuration. -/
theorem registerCfg_injective (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k) :
    Function.Injective (registerCfg (d := d) hN hr) := by
  intro u v h
  funext i
  have hi := congrFun h (registerSite hN hr 0 i)
  simpa only [registerCfg_registerSite] using hi

/-- The whole-ring logical seed maps each sector label to its repeated register configuration,
with all unused physical sites zero. -/
noncomputable def registerEncoder (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k)
    (dig : Fin b → Cfg d r) : Matrix (Cfg d N) (Fin b) ℂ :=
  (1 : Matrix (Cfg d N) (Cfg d N) ℂ).submatrix id (fun j => registerCfg hN hr (dig j))

/-- Injective logical register words give an isometric whole-ring seed. -/
theorem isIsometry_registerEncoder (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k)
    {dig : Fin b → Cfg d r} (hdig : Function.Injective dig) :
    (registerEncoder hN hr dig).IsIsometry := by
  classical
  change ((1 : Matrix (Cfg d N) (Cfg d N) ℂ).submatrix id _)ᴴ *
    (1 : Matrix (Cfg d N) (Cfg d N) ℂ).submatrix id _ = 1
  simp only [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : Matrix (Cfg d N) (Cfg d N) ℂ).submatrix _ (Equiv.refl _) *
    (1 : Matrix (Cfg d N) (Cfg d N) ℂ).submatrix (Equiv.refl _) _ = 1
  rw [Matrix.submatrix_mul_equiv, Matrix.one_mul]
  exact Matrix.submatrix_one _ ((registerCfg_injective hN hr).comp hdig)

omit [NeZero M] in
/-- A simultaneous sector circuit is an equality of the entire encoder matrices. -/
theorem mul_registerEncoder_eq_blockIsometryEncoder {D : ℕ}
    (hN : ∑ k, ℓ k = N) (hr : ∀ k, r + r ≤ ℓ k) (dig : Fin b → Cfg d r)
    (A : MPSTensor d D) (ω : Fin b → Fin D × Fin D → ℂ)
    {U : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hU : ∀ j, U *ᵥ Pi.single (registerCfg hN hr (dig j)) 1 =
      fun s => blockIsometryState A (ω j) hN s) :
    U * registerEncoder hN hr dig = blockIsometryEncoder A ω hN := by
  classical
  ext s j
  have hj := congrFun (hU j) s
  simpa [registerEncoder, blockIsometryEncoder, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, Matrix.one_apply, Pi.single_apply] using hj

/-- One genuine local circuit implements the full block encoder from the common seed.
The constant is chosen before the tensor, pair vectors, partition, and logical amplitudes.
No preparation cost for the seed is included. -/
theorem exists_isLocalCircuitOfDepth_registerEncoder
    {D : ℕ} {r : ℕ} (hr : 2 ≤ r) {dig : Fin D → Cfg d r} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ (A : MPSTensor d D) (S : Finset (Fin D × Fin D))
      (ω : Fin b → Fin D × Fin D → ℂ),
      (∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0) →
      (∀ j {M : ℕ} (c : Fin M → Fin D × Fin D), pairProductState (ω j) c ≠ 0 → ∀ k, c k ∈ S) →
      ∀ {M : ℕ} [NeZero M] (ℓ : Fin M → ℕ) {N : ℕ} [NeZero N] (hN : ∑ k, ℓ k = N) (L : ℕ),
        ∀ hℓ : ∀ k, 3 * r ≤ ℓ k, (∀ k, ℓ k ≤ L) →
        (∀ k, IsInjectiveOn (blockTensor A (ℓ k)) (S : Set (Fin D × Fin D))) →
        ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
          IsLocalCircuitOfDepth U T ∧ T ≤ C * L ∧
          U * registerEncoder hN (fun k => by have := hℓ k; omega) dig₀ =
            blockIsometryEncoder A ω hN ∧ (blockIsometryEncoder A ω hN).IsIsometry := by
  obtain ⟨C, hC⟩ := exists_isLocalCircuitOfDepth_registerCfg_of_isInjectiveOn hr hdig hdig₀ hD
  refine ⟨C, fun A S ω hω hωS M _ ℓ N _ hN L hℓ hL hinj => ?_⟩
  obtain ⟨U, T, hU, hT, hj⟩ := hC A S ω hω hωS ℓ hN L hℓ hL hinj
  have heq := mul_registerEncoder_eq_blockIsometryEncoder hN
    (fun k => by have := hℓ k; omega) dig₀ A ω hj
  refine ⟨U, T, hU, hT, heq, ?_⟩
  rw [← heq]
  change (U * registerEncoder hN _ dig₀)ᴴ * (U * registerEncoder hN _ dig₀) = 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
    (show Uᴴ * U = 1 from Unitary.star_mul_self_of_mem hU.mem_unitary), Matrix.one_mul]
  exact isIsometry_registerEncoder hN _ hdig₀

section Conversion

variable [NeZero N] {DA DB : Fin b → ℕ}

/-- Phase-sensitive Gram and cross estimates give coherent conversion of the fixed canonical
sector encoders. This finite-length statement does not yet assert logarithmic depth or
supply the quantitative estimates from transfer spectra. -/
theorem norm_sectorEncoder_conversion_le
    (A : (j : Fin b) → MPSTensor d (DA j)) (B : (j : Fin b) → MPSTensor d (DB j))
    (hA : Function.Injective (sectorColumnMatrix A N).mulVec)
    (hB : Function.Injective (sectorColumnMatrix B N).mulVec)
    {UA UB : Matrix (Cfg d N) (Cfg d N) ℂ} {TA TB : ℕ}
    (hUA : IsLocalCircuitOfDepth UA TA) (hUB : IsLocalCircuitOfDepth UB TB)
    (J : Matrix (Cfg d N) (Fin b) ℂ) (hJ : J.IsIsometry)
    {ηA ζA ηB ζB : ℝ}
    (hηA : ‖(sectorColumnMatrix A N)ᴴ * sectorColumnMatrix A N - 1‖ ≤ ηA)
    (hζA : ‖(UA * J)ᴴ * sectorColumnMatrix A N - 1‖ ≤ ζA)
    (hηB : ‖(sectorColumnMatrix B N)ᴴ * sectorColumnMatrix B N - 1‖ ≤ ηB)
    (hζB : ‖(UB * J)ᴴ * sectorColumnMatrix B N - 1‖ ≤ ζB) :
    IsLocalCircuitOfDepth (UB * UAᴴ) (TA + TB) ∧
      ‖UB * UAᴴ * sectorEncoder A N - sectorEncoder B N‖ ≤
        (Real.sqrt (ηA + 2 * ζA) + ηA) + (Real.sqrt (ηB + 2 * ζB) + ηB) := by
  have hWA : (UA * J).IsIsometry := Matrix.IsIsometry.mul _ _
    (show UA.IsIsometry from Unitary.star_mul_self_of_mem hUA.mem_unitary) hJ
  have hWB : (UB * J).IsIsometry := Matrix.IsIsometry.mul _ _
    (show UB.IsIsometry from Unitary.star_mul_self_of_mem hUB.mem_unitary) hJ
  have hFA := Matrix.norm_polarIso_sub_isometry_le (sectorColumnMatrix A N) hA hWA
  have hFB := Matrix.norm_polarIso_sub_isometry_le (sectorColumnMatrix B N) hB hWB
  have hFA' : ‖sectorEncoder A N - UA * J‖ ≤ Real.sqrt (ηA + 2 * ζA) + ηA := by
    refine hFA.trans ?_
    gcongr
  have hFB' : ‖sectorEncoder B N - UB * J‖ ≤ Real.sqrt (ηB + 2 * ζB) + ηB := by
    refine hFB.trans ?_
    gcongr
  obtain ⟨hU, herr⟩ := hUA.norm_encoder_conversion_le hUB (sectorEncoder A N) (sectorEncoder B N) J
  exact ⟨hU, herr.trans (add_le_add hFA' hFB')⟩

end Conversion

end MPSPreparation

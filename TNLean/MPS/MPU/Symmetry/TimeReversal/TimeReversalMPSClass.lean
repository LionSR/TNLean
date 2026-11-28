/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Conjugation.ConjugationMPSClass
import TNLean.MPS.MPU.Simple.SuppliedFixedWitnesses
import TNLean.MPS.MPU.Symmetry.TimeReversal.TimeReversalTwistedTransfer
import TNLean.MPS.MPU.StandardForm.TwoSiteStandardFormSourceCuts
import TNLean.MPS.FundamentalTheorem.TimeReversalIndex

/-!
# The MPS sign of a time-reversal-invariant matrix product unitary

Proposition `prop:dagger-mps-class-and-mpu-class-equal` of arXiv:1703.09188
(lines 1808--1815) compares two signs of a time-reversal-invariant MPU in
standard form. Viewed as a matrix product state, the standard-form tensor and
its time reversal `𝒲ᵃᵇ ↦ conj(𝒲ᵇᵃ)` are related by a unitary gauge,
`conj(𝒲ᵇᵃ) = ζ G† 𝒲ᵃᵇ G`, and `G conj(G) = ±1` is the sign of the
classification of MPS phases (`eq:mps-class-gauge-trafo`, lines 1761--1788).
On the other hand, Proposition `PropChiral` applied after blocking two sites
gives the sign `σ⁽²⁾`, read from the normalized trace `d⁻¹ tr(𝕊 U⁽²⁾)` of the
blocked standard form (`eq:sigma-from-trace`, lines 1595--1610). The
proposition states that the two signs agree.

The source proof (lines 1817--1829) contracts four gates against the gauge
relation. The proof here works with the trace instead. Write `𝒲₂` for the
two-site block of the standard form. Using the gauge relation once,
`tr(𝕊 U⁽²⁾) = ∑_{a,b} tr(𝒲₂ᵇᵃ 𝒲₂ᵃᵇ) = conj(ζ) ∑_{a,b} tr(Gᵀ conj(𝒲₂ᵃᵇ) conj(G) 𝒲₂ᵃᵇ)`.
For a simple MPU in canonical form II the normalized double-layer diagonal `E`
satisfies `E² = |ρ)(1|` (from `simple2` and `Erightleft`), and the double layer
of `𝒲₂` is `E²`. The sum is then `d tr(G conj(G) ρ)`. Invariance at length two
gives `ζ = 1`, and `G conj(G) = ±1` by normality, so `σ⁽²⁾ = ±1` is the
MPS sign.

As in `PropChiral`, a tensor in standard form is the two-site block of a simple
tensor in canonical form II
(`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`), and invariance
under time reversal is required at even lengths of the two-spin chain
(`docs/paper-gaps/mpu_standard_form_parity_gap.tex`).

## Main results

* `MPOTensor.IsMPUCanonicalFormII.normalizedDiagonal_sq_eq_fixedPairProjector`.
* `MPOTensor.sum_trace_mul_map_star_mul_eq`.
* `MPOTensor.IsMPUCanonicalFormII.mps_timeReversal_sign_eq`,
  `MPOTensor.IsMPUCanonicalFormII.mps_timeReversal_sign_eq_of_gauge`: Proposition
  `prop:dagger-mps-class-and-mpu-class-equal`, for a gauge of the two-site block
  and of the standard-form tensor.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The rank-one projector `|ρ)(1|` on the doubled bond, in the encoding of
`normalizedDiagonal`. -/
noncomputable def fixedPairProjector (ρ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  Matrix.vecMulVec (fun x : Fin (D * D) ↦ ρ.vec (finProdFinEquiv.symm x))
    (fun x : Fin (D * D) ↦ (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x))

/-- The normalized double-layer diagonal of a simple MPU in canonical form II
squares to the rank-one projector `|ρ)(1|`. Source: arXiv:1703.09188,
equations `Erightleft` and `simple2`, lines 269--281 and 356--374. -/
theorem IsMPUCanonicalFormII.normalizedDiagonal_sq_eq_fixedPairProjector
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    normalizedDiagonal (doubleLayerTensor U) * normalizedDiagonal (doubleLayerTensor U) =
      fixedPairProjector hU.ρ := by
  have := hU.neZero_phys
  set E := normalizedDiagonal (doubleLayerTensor U)
  set P := fixedPairProjector hU.ρ
  -- `E² = E P E` from `simple2`.
  have hEPE : E * E = E * P * E := by
    have h2 := hU.simple2_recorded_fixed_pair hsimple
    have hE : E = (d : ℂ)⁻¹ • ∑ q : Fin d, doubleLayerTensor U (q, q) :=
      normalizedDiagonal_eq_smul_sum_diagonal _
    rw [hE]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum, h2]
    rfl
  -- `E |ρ) = |ρ)`.
  have hEρ : E *ᵥ (fun x : Fin (D * D) ↦ hU.ρ.vec (finProdFinEquiv.symm x)) =
      fun x ↦ hU.ρ.vec (finProdFinEquiv.symm x) := by
    have h := transferMatrix_mulVec_eq (Kraus.transferMap U.normalizedFlattening) hU.ρ
    rw [hU.ρ_fixed] at h
    simp only [E, normalizedDiagonal_doubleLayerTensor]
    ext x
    have := congrFun h (finProdFinEquiv.symm x)
    rw [← this, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
    have hcomp : (fun x : Fin (D * D) ↦ hU.ρ.vec (finProdFinEquiv.symm x)) ∘ finProdFinEquiv =
        hU.ρ.vec := by
      funext y
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hcomp]
    rfl
  have hEP : E * P = P := by
    simp only [P, fixedPairProjector, Matrix.mul_vecMulVec, hEρ]
  -- `E` commutes with `E^J = P`.
  have hPE : P * E = P := by
    have hJ : E ^ max (D * D - 1) 1 = P := hU.normalizedDiagonal_pow_eq_vecMulVec
    have hcomm : E * E ^ max (D * D - 1) 1 = E ^ max (D * D - 1) 1 * E :=
      (pow_mul_comm' E _).symm
    rw [hJ] at hcomm
    rw [← hcomm, hEP]
  rw [hEPE, hEP, hPE]

/-- Physical relabelling does not change the normalized double-layer diagonal. -/
theorem normalizedDiagonal_doubleLayerTensor_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d)
    (U : MPOTensor d D) :
    normalizedDiagonal (doubleLayerTensor (reindexPhysical e U)) =
      normalizedDiagonal (doubleLayerTensor U) := by
  rw [normalizedDiagonal_eq_smul_sum_diagonal, normalizedDiagonal_eq_smul_sum_diagonal]
  simp only [doubleLayerTensor_reindexPhysical]
  have hcard : d' = d := by simpa using Fintype.card_congr e
  subst hcard
  congr 1
  exact Equiv.sum_comp e (fun q ↦ doubleLayerTensor U (q, q))

/-- Two-site blocking squares the normalized double-layer diagonal. Source:
arXiv:1703.09188, lines 397--405. -/
theorem normalizedDiagonal_doubleLayerTensor_blockTwo [NeZero d] (U : MPOTensor d D) :
    normalizedDiagonal (doubleLayerTensor (MPOTensor.blockTwo U)) =
      normalizedDiagonal (doubleLayerTensor U) * normalizedDiagonal (doubleLayerTensor U) := by
  have hb : MPOTensor.blockTwo U = reindexPhysical (twoSiteBlockEquiv d) (blockTensor U 2) :=
    blockTwo_eq_blockTensor_reindex U
  rw [hb, normalizedDiagonal_doubleLayerTensor_reindexPhysical,
    normalizedDiagonal_doubleLayerTensor_blockTensor, normalizedDiagonal_doubleLayerTensor,
    pow_two]
  exact (Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _).symm

/-- Entries of the normalized double-layer diagonal. -/
theorem normalizedDiagonal_doubleLayerTensor_apply (K : MPOTensor d D) (p₁ p₂ q₁ q₂ : Fin D) :
    normalizedDiagonal (doubleLayerTensor K) (finProdFinEquiv (p₁, p₂))
        (finProdFinEquiv (q₁, q₂)) =
      (d : ℂ)⁻¹ * ∑ a : Fin d, ∑ b : Fin d, starRingEnd ℂ (K (a, b) p₁ q₁) * K (a, b) p₂ q₂ := by
  classical
  simp only [normalizedDiagonal, contractPhysical, doubleLayerTensor_apply,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply,
    physicalAdjointTensor_apply, Matrix.kronecker_apply,
    Equiv.symm_apply_apply, Matrix.one_apply, smul_eq_mul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, RCLike.star_def]
  rw [Finset.sum_comm]

/-- Under `E = |ρ)(1|`, the letters of `K` satisfy
`∑_{a,b} conj(K^{ab}_{p q}) K^{ab}_{β α} = d ρ_{β p} δ_{α q}`. -/
theorem sum_star_mul_eq_of_normalizedDiagonal_eq [NeZero d] {K : MPOTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hE : normalizedDiagonal (doubleLayerTensor K) = fixedPairProjector ρ)
    (p q β α : Fin D) :
    ∑ a : Fin d, ∑ b : Fin d, starRingEnd ℂ (K (a, b) p q) * K (a, b) β α =
      (d : ℂ) * (ρ β p * (1 : Matrix (Fin D) (Fin D) ℂ) α q) := by
  have h := normalizedDiagonal_doubleLayerTensor_apply K p β q α
  have h2 : fixedPairProjector ρ (finProdFinEquiv (p, β)) (finProdFinEquiv (q, α)) =
      ρ β p * (1 : Matrix (Fin D) (Fin D) ℂ) α q := by
    rw [fixedPairProjector, Matrix.vecMulVec_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
    rfl
  rw [hE, h2] at h
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [h, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/-- **The twisted trace under a rank-one double layer.** If the normalized
double-layer diagonal of `K` is `|ρ)(1|`, then
`∑_{a,b} tr(M conj(K^{ab}) M' K^{ab}) = d tr(Mᵀ M' ρ)`. -/
theorem sum_trace_mul_map_star_mul_eq [NeZero d] {K : MPOTensor d D}
    {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hE : normalizedDiagonal (doubleLayerTensor K) = fixedPairProjector ρ)
    (M M' : Matrix (Fin D) (Fin D) ℂ) :
    ∑ a : Fin d, ∑ b : Fin d,
        Matrix.trace (M * (K (a, b)).map (starRingEnd ℂ) * M' * K (a, b)) =
      (d : ℂ) * Matrix.trace (Mᵀ * M' * ρ) := by
  have hS := sum_star_mul_eq_of_normalizedDiagonal_eq hE
  calc
    _ = ∑ α : Fin D, ∑ p : Fin D, ∑ q : Fin D, ∑ β : Fin D,
          M α p * M' q β *
            ∑ a : Fin d, ∑ b : Fin d, starRingEnd ℂ (K (a, b) p q) * K (a, b) β α := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply,
          Finset.sum_mul, Finset.mul_sum]
        conv_lhs => enter [2, a]; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, a, 2, b, 2, β]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, a, 2, b]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, a]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, p, 2, a, 2, b]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, p, 2, a]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, p]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, p, 2, q, 2, a]; rw [Finset.sum_comm]
        conv_lhs => enter [2, α, 2, p, 2, q]; rw [Finset.sum_comm]
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = _ := by
        simp only [hS, Matrix.one_apply, mul_ite, mul_one, mul_zero]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
          Finset.mul_sum, Finset.sum_mul]
        conv_lhs => enter [2, α, 2, p]; rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
        ring

/-- **The MPS sign of a time-reversal-invariant MPU is `σ⁽²⁾`.** Let `𝒱` be a
simple tensor in canonical form II whose standard form `𝒲 = 𝒱₂` generates an
MPU fixed by the adjoint at every even length of the two-spin chain. Let `G` be
a unitary gauge of the matrix product state of the two-site block `𝒲₂` under
time reversal: `conj(𝒲₂ᵇᵃ) = ζ G† 𝒲₂ᵃᵇ G` for all physical indices. Then
`G conj(G) = σ⁽²⁾ 1`, where `σ⁽²⁾` is the time-reversal sign of `𝒲₂`, read
from the normalized trace `d⁻¹ tr(𝕊 U⁽²⁾)`.

Source: arXiv:1703.09188, Proposition
`prop:dagger-mps-class-and-mpu-class-equal`, lines 1808--1815, with the sign
`G conj(G) = ±1` of `eq:mps-class-gauge-trafo` (lines 1761--1770) and the
unitary choice of `G` (lines 1780--1782). Invariance is required at even
lengths of the standard-form chain, as in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`. -/
theorem IsMPUCanonicalFormII.mps_timeReversal_sign_eq
    {V : MPOTensor d D} (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ)
    (G : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hgauge : ∀ a b, (MPOTensor.blockTwo (MPOTensor.blockTwo V) (b, a)).map (starRingEnd ℂ) =
      ζ • ((G : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        MPOTensor.blockTwo (MPOTensor.blockTwo V) (a, b) * G)) :
    (G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      intrinsicTimeReversalSign (MPOTensor.blockTwo (MPOTensor.blockTwo V)) • 1 := by
  let : NeZero d := hV.neZero_phys
  let : NeZero D := hV.neZero_bond
  set W := MPOTensor.blockTwo V
  set W₂ := MPOTensor.blockTwo W
  set Gm : Matrix (Fin D) (Fin D) ℂ := (G : Matrix (Fin D) (Fin D) ℂ)
  have hW : IsMPUCanonicalFormII W := hV.blockTwo
  have hWs : IsMPUSimple W := hV.isMPUSimple_blockTwo hsimple
  have hGG : Gm * Gmᴴ = 1 := by
    simpa [Gm, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp G.property
  have hGG' : Gmᴴ * Gm = 1 := by
    simpa [Gm, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp G.property
  -- The double layer of `𝒲₂` is the rank-one projector.
  have hE : normalizedDiagonal (doubleLayerTensor W₂) = fixedPairProjector hW.ρ := by
    rw [normalizedDiagonal_doubleLayerTensor_blockTwo,
      hW.normalizedDiagonal_sq_eq_fixedPairProjector hWs]
  -- Inverting the gauge relation.
  have hinv : ∀ a b, W₂ (b, a) = starRingEnd ℂ ζ • (Gmᵀ * (W₂ (a, b)).map (starRingEnd ℂ) *
      Gm.map (starRingEnd ℂ)) := by
    intro a b
    have h := congrArg (·.map (starRingEnd ℂ)) (hgauge a b)
    have hmap : ((W₂ (b, a)).map (starRingEnd ℂ)).map (starRingEnd ℂ) = W₂ (b, a) := by
      ext i j; simp
    simp only [hmap, map_star_smul, Matrix.map_mul, conjTranspose_map_star] at h
    exact h
  -- Applying the symmetry twice: `G conj(G) = ±1`.
  have hconjT : (Gm.map (starRingEnd ℂ))ᴴ = Gmᵀ := by ext i j; simp
  have htwice : ∀ a b, W₂ (a, b) = (starRingEnd ℂ ζ * ζ) •
      ((Gm * Gm.map (starRingEnd ℂ))ᴴ * W₂ (a, b) * (Gm * Gm.map (starRingEnd ℂ))) := by
    intro a b
    have h := hinv b a
    rw [hgauge a b] at h
    conv_lhs => rw [h]
    rw [Matrix.conjTranspose_mul, hconjT, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    simp only [Matrix.mul_assoc]
  have hN : Kraus.IsNormal W₂.normalizedFlattening :=
    hW.blockTwo.isNormalTensor_normalizedFlattening.isNormal
  have hsign := MPSTensor.mul_map_star_eq_one_or_neg_one_of_twice hN G
    (c := starRingEnd ℂ ζ * ζ) (fun ⟨a, b⟩ => by
      simp only [normalizedFlattening, Matrix.mul_smul, Matrix.smul_mul]
      conv_lhs => rw [htwice]
      rw [smul_comm])
  -- The phase is one, from the length-two invariance.
  have htrW₂ : ∀ σ τ : Fin 2 → Fin (d * d),
      Matrix.trace (W₂ (finProdFinEquiv (σ 0, σ 1), finProdFinEquiv (τ 0, τ 1))) =
        mpo W 2 σ τ := by
    intro σ τ
    simp [W₂, mpo_apply, mpoMatrixEntry, List.ofFn_succ]
  have hζ : ζ = 1 := by
    have hU2 := hW.isMPU 2 (by norm_num)
    obtain ⟨σ, τ, hne⟩ : ∃ σ τ, mpo W 2 σ τ ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : mpo W 2 = 0 := Matrix.ext h
      have := Matrix.mem_unitaryGroup_iff.mp hU2
      rw [h0, zero_mul] at this
      have := congrFun (congrFun this (fun _ => 0)) (fun _ => 0)
      simp at this
    have hherm := congrFun (congrFun (hTR 2 (by norm_num) even_two) σ) τ
    rw [Matrix.conjTranspose_apply] at hherm
    have hg := congrArg Matrix.trace
      (hgauge (finProdFinEquiv (σ 0, σ 1)) (finProdFinEquiv (τ 0, τ 1)))
    rw [Matrix.trace_smul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hGG,
      Matrix.mul_one, htrW₂] at hg
    have hmapTr : ∀ X : Matrix (Fin D) (Fin D) ℂ,
        Matrix.trace (X.map (starRingEnd ℂ)) = starRingEnd ℂ (Matrix.trace X) := by
      intro X; simp [Matrix.trace]
    rw [hmapTr, htrW₂] at hg
    have hstar : starRingEnd ℂ (mpo W 2 τ σ) = mpo W 2 σ τ := hherm.symm
    rw [hstar, smul_eq_mul] at hg
    have : (ζ - 1) * mpo W 2 σ τ = 0 := by linear_combination -hg
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  subst hζ
  -- The trace.
  have hT : intrinsicTimeReversalSign W₂ = Matrix.trace (Gm * Gm.map (starRingEnd ℂ) * hW.ρ) := by
    rw [intrinsicTimeReversalSign, timeReversalPeriodicTrace_eq_sum]
    have hsum : ∑ i, ∑ j, Matrix.trace (W₂ (i, j) * W₂ (j, i)) =
        ∑ a, ∑ b, Matrix.trace (Gmᵀ * (W₂ (a, b)).map (starRingEnd ℂ) *
          Gm.map (starRingEnd ℂ) * W₂ (a, b)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hinv a b]
      simp
    rw [hsum, sum_trace_mul_map_star_mul_eq hE, Matrix.transpose_transpose, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne _)), one_mul]
  have hρ := hW.ρ_trace
  rcases hsign with h | h
  · change Gm * Gm.map (starRingEnd ℂ) = 1 at h
    rw [hT, h, Matrix.one_mul, hρ, one_smul]
  · change Gm * Gm.map (starRingEnd ℂ) = -1 at h
    rw [hT, h, Matrix.neg_mul, Matrix.one_mul, Matrix.trace_neg, hρ, neg_one_smul]

/-- A time-reversal gauge of a tensor is a time-reversal gauge of its two-site
block, with the square of the phase. -/
theorem blockTwo_timeReversal_gauge {W : MPOTensor d D} (G : Matrix (Fin D) (Fin D) ℂ)
    (hG : G * Gᴴ = 1) (ζ : ℂ)
    (hgauge : ∀ a b, (W (b, a)).map (starRingEnd ℂ) = ζ • (Gᴴ * W (a, b) * G))
    (a b : Fin (d * d)) :
    (MPOTensor.blockTwo W (b, a)).map (starRingEnd ℂ) =
      (ζ * ζ) • (Gᴴ * MPOTensor.blockTwo W (a, b) * G) := by
  simp only [MPOTensor.blockTwo_apply, Matrix.map_mul, hgauge, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G, hG, Matrix.one_mul]

/-- **The MPS sign of a time-reversal-invariant MPU, for a gauge of the
standard-form tensor.** The comparison of `mps_timeReversal_sign_eq` for a
unitary gauge `conj(𝒲ᵇᵃ) = ζ G† 𝒲ᵃᵇ G` of the standard-form tensor `𝒲`
itself; the source notes that `G` is invariant under blocking (line 1774).
Source: arXiv:1703.09188, Proposition
`prop:dagger-mps-class-and-mpu-class-equal`, lines 1808--1815. -/
theorem IsMPUCanonicalFormII.mps_timeReversal_sign_eq_of_gauge
    {V : MPOTensor d D} (hV : IsMPUCanonicalFormII V) (hsimple : IsMPUSimple V)
    (hTR : ∀ N : ℕ, 1 < N → Even N →
      mpo (MPOTensor.blockTwo V) N = (mpo (MPOTensor.blockTwo V) N)ᴴ)
    (G : Matrix.unitaryGroup (Fin D) ℂ) (ζ : ℂ)
    (hgauge : ∀ a b, (MPOTensor.blockTwo V (b, a)).map (starRingEnd ℂ) =
      ζ • ((G : Matrix (Fin D) (Fin D) ℂ)ᴴ * MPOTensor.blockTwo V (a, b) * G)) :
    (G : Matrix (Fin D) (Fin D) ℂ) * (G : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) =
      intrinsicTimeReversalSign (MPOTensor.blockTwo (MPOTensor.blockTwo V)) • 1 :=
  hV.mps_timeReversal_sign_eq hsimple hTR G (ζ * ζ)
    (blockTwo_timeReversal_gauge (G : Matrix (Fin D) (Fin D) ℂ)
      (by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp G.property)
      ζ hgauge)

end MPOTensor

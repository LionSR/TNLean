/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Dimer.TwistedDimerBondRFP
import TNLean.MPS.Examples.Dimer.TwistedDimerVerticalCF
import QICLean.Algebra.Matrix.MatrixSingleSpan
import QICLean.Analysis.Real.ComplexSqrt
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.CanonicalForm.SimpleMPO.Simple
import TNLean.MPS.Operator.Periodic.BondOneOperator
import TNLean.MPS.CanonicalForm.VerticalForm.SectorTrace
import TNLean.MPS.CanonicalForm.PhysicalReindex
import TNLean.MPS.Operator.PairAlphabetBridge
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Simplicity of the exact mixed-Bell bond factor

The independent bond factor of the twisted dimer has Bell weights seven eighths
and one eighth. Its matrix-unit tensor `sigmaDimer` was defined, together with
its channel fixed-point witnesses, in `TwistedDimerBondRFP`. This module proves
that this exact factor is simple in the sense of arXiv:1606.00608, Definition
4.7, lines 815–822.

The sixteen letters are nonzero multiples of the sixteen matrix units, so the
tensor is injective at one site. Their adjoint-square sum is `(25 / 32) • 1`.
Scaling by `4 √2 / 5` gives a normal left-canonical representative. Its
physical-trace transfer has trace `4 √2 / 5`, and hence is not nilpotent. The
one-representative presentation after one-site blocking proves simplicity.

This is a project construction motivated by the question following Theorem
4.14 of arXiv:1606.00608, lines 995–1010. It is not a tensor printed in that
paper. The source construction is preserved in
`docs/audits/2026-09-05_twisted_dimer_unitary_factorization.md`.
Simplicity of this factor does not assert a tensor factorization of the original
twisted dimer by on-site physical unitaries or virtual similarities. The
normalizing scalar is used only for the normal representative; no channel
fixed-point assertion is made for the rescaled tensor.

## Main results

* `sigmaDimer_isInjective`: one-site injectivity of the exact mixed-Bell factor.
* `sigmaDimerBasis_isNormalTensor`: its normalized normal representative.
* `sigmaDimer_isSimple`: simplicity of the original, trace-one factor.

## References

* Cirac, Pérez-García, Schuch and Verstraete,
  *Matrix product density operators: Renormalization fixed points and boundary theories*,
  arXiv:1606.00608, lines 224–235 (normal representatives), Definition 4.7,
  lines 815–822 (simplicity), and lines 995–1010 (the motivating question).
* Project construction provenance:
  `docs/audits/2026-09-05_twisted_dimer_unitary_factorization.md`.
-/

open scoped Matrix BigOperators
namespace MPOTensor.TwistedDimer

/-- The letters span every matrix unit of the auxiliary algebra. -/
theorem sigmaDimer_isInjective : Kraus.IsInjective sigmaDimer := by
  unfold Kraus.IsInjective
  apply Submodule.eq_top_of_forall_single_mem
  intro p q
  obtain ⟨⟨p₁, p₂⟩, rfl⟩ := bondSiteEquiv.surjective p
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := bondSiteEquiv.surjective q
  let v : Fin 4 × Fin 4 := (bondSiteEquiv (p₁, q₁), bondSiteEquiv (p₂, q₂))
  have hv : sigmaDimer v =
      (Cmat 0 p₁ p₂ : ℂ) •
        Matrix.single (bondSiteEquiv (p₁, p₂)) (bondSiteEquiv (q₁, q₂)) 1 := by
    simp [v, sigmaDimer, Matrix.smul_single]
  have hc : (Cmat 0 p₁ p₂ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Cmat_ne_zero 0 p₁ p₂)
  have hmem : sigmaDimer v ∈ Submodule.span ℂ (Set.range sigmaDimer) :=
    Submodule.subset_span ⟨v, rfl⟩
  rw [hv] at hmem
  have hscaled := (Submodule.span ℂ (Set.range sigmaDimer)).smul_mem
    (Cmat 0 p₁ p₂ : ℂ)⁻¹ hmem
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hscaled

/-- The adjoint-square sum fixes the one-block normalization. -/
theorem sigmaDimer_sum_conjTranspose_mul :
    (∑ i : Fin 4 × Fin 4, (sigmaDimer i)ᴴ * sigmaDimer i) =
    (25 / 32 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [Fintype.sum_prod_type, sigmaDimer,
    Matrix.conjTranspose_single,
    Matrix.single_mul_single_same, Complex.star_def, Complex.conj_ofReal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bondSiteEquiv, finProdFinEquiv, Fin.divNat, Fin.modNat, Cmat,
      cDiag_eq, cOff_eq, Fin.sum_univ_succ, Matrix.single_apply, Matrix.one_apply]

/-- The positive normalizing scalar `4 √2 / 5`, written using the shared
complex square-root constant. -/
noncomputable def sigmaDimerNormalizingScalar : ℂ := (8 / 5) * Complex.invSqrtTwo

/-- The normalizing scalar does not vanish. -/
lemma sigmaDimerNormalizingScalar_ne_zero : sigmaDimerNormalizingScalar ≠ 0 :=
  mul_ne_zero (by norm_num) Complex.invSqrtTwo_ne_zero

/-- The single normalized normal representative of the mixed-Bell factor.

Source convention: arXiv:1606.00608, lines 224–235. -/
noncomputable def sigmaDimerBasis : MPOTensor 4 4 :=
  sigmaDimerNormalizingScalar • sigmaDimer

/-- The normalized representative is left-canonical. -/
lemma sigmaDimerBasis_isLeftCanonical : MPTensor.IsLeftCanonical sigmaDimerBasis := by
  change (∑ i, (sigmaDimerBasis i)ᴴ * sigmaDimerBasis i) = 1
  simp only [sigmaDimerBasis, Pi.smul_apply, Matrix.conjTranspose_smul,
    smul_mul_smul_comm]
  rw [← Finset.smul_sum, sigmaDimer_sum_conjTranspose_mul, smul_smul]
  have hc : star sigmaDimerNormalizingScalar * sigmaDimerNormalizingScalar *
      (25 / 32 : ℂ) = 1 := by
    simp only [sigmaDimerNormalizingScalar, star_mul, star_div₀, star_ofNat,
      Complex.star_invSqrtTwo]
    calc
      Complex.invSqrtTwo * (8 / 5) * (8 / 5 * Complex.invSqrtTwo) * (25 / 32 : ℂ) =
          (8 / 5 * (8 / 5) * (25 / 32 : ℂ)) *
            (Complex.invSqrtTwo * Complex.invSqrtTwo) := by ring
      _ = 1 := by rw [Complex.invSqrtTwo_mul_self]; norm_num
  rw [hc, one_smul]

/-- One-site injectivity and left-canonical normalization give source normality.
The normality criterion is stated on the doubled-index alphabet `Fin (4 * 4)`, so it is
applied there and transported back along `finProdFinEquiv`.

Source notion: arXiv:1606.00608, lines 224–235. -/
lemma sigmaDimerBasis_isNormalTensor : MPTensor.IsNormalTensor sigmaDimerBasis := by
  have hNormal : Kraus.IsNormal sigmaDimerBasis :=
    (sigmaDimer_isInjective.smul sigmaDimerNormalizingScalar_ne_zero).isNormal
  have h := (MPSTensor.isNormalTensor_of_isNormal_leftCanonical sigmaDimerBasis.toMPSTensor
    ((MPOTensor.isNormal_toMPSTensor_iff _).2 hNormal)
    ((MPOTensor.isTP_toMPSTensor_iff _).2 sigmaDimerBasis_isLeftCanonical)).reindexPhysical
      finProdFinEquiv
  have he : Kraus.reindexPhysical finProdFinEquiv sigmaDimerBasis.toMPSTensor =
      sigmaDimerBasis :=
    funext fun i ↦ congrArg sigmaDimerBasis (finProdFinEquiv.symm_apply_apply i)
  rwa [he] at h

/-- The physical-trace transfer of the representative has nonzero trace.
This is the nilpotency exclusion of Definition 4.7, lines 815–822. -/
lemma sigmaDimerBasis_trace_physTransfer :
    Matrix.trace (physTraceTransfer sigmaDimerBasis) = sigmaDimerNormalizingScalar := by
  have ht : Matrix.trace (physTraceTransfer sigmaDimer) = 1 := by
    have h := trace_mpo_sigmaDimer (N := 1) (by decide)
    rw [trace_mpo_eq_trace_verticalLoop_pow, verticalLoop_eq_physTraceTransfer,
      pow_one] at h
    exact h
  have he : physTraceTransfer sigmaDimerBasis =
      sigmaDimerNormalizingScalar • physTraceTransfer sigmaDimer := by
    simp only [physTraceTransfer, sigmaDimerBasis, Pi.smul_apply]
    rw [← Finset.smul_sum]
  rw [he, Matrix.trace_smul, ht, smul_eq_mul, mul_one]

/-- The ket-bra alphabet of one-site blocking identified with the original pair alphabet. -/
private noncomputable def singleBlockPairEquiv (d : ℕ) :
    Fin (Kraus.blockPhysDim d 1 * Kraus.blockPhysDim d 1) ≃ Fin d × Fin d :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Kraus.singleBlockEquiv d) (Kraus.singleBlockEquiv d))

/-- One-site blocking, read on the doubled-index alphabet of the simplicity predicate, is a
physical relabelling of the tensor on the pair alphabet. -/
private lemma blockTensor_one_doubled_eq_reindexPhysical {d D : ℕ} (M : MPOTensor d D) :
    (blockTensor M 1).toMPSTensor =
      Kraus.reindexPhysical (singleBlockPairEquiv d) M := by
  funext ij
  change
    M (Kraus.singleBlockEquiv d ij.divNat, Kraus.singleBlockEquiv d ij.modNat) * 1 =
      M (singleBlockPairEquiv d ij)
  simp [singleBlockPairEquiv]

private lemma doubledPhysTraceTransfer_reindex_singleBlock {d D : ℕ} (A : MPOTensor d D) :
    doubledPhysTraceTransfer (Kraus.blockPhysDim d 1)
        (Kraus.reindexPhysical (singleBlockPairEquiv d) A) =
      physTraceTransfer A := by
  rw [doubledPhysTraceTransfer, physTraceTransfer]
  change (∑ i : Fin (Kraus.blockPhysDim d 1),
      A (singleBlockPairEquiv d (finProdFinEquiv (i, i)))) = ∑ i : Fin d, A (i, i)
  simpa [singleBlockPairEquiv] using (Kraus.singleBlockEquiv d).sum_comp
    (fun i : Fin d => A (i, i))

/-- The exact mixed-Bell bond factor is simple in the sense of CPSV16
Definition 4.7, arXiv:1606.00608, lines 815–822.

There is one normal representative, of weight `5 / (4 √2)`. Its
physical-trace transfer has nonzero trace and therefore cannot be nilpotent. -/
theorem sigmaDimer_isSimple : IsSimple sigmaDimer := by
  classical
  let e := singleBlockPairEquiv 4
  let B := Kraus.reindexPhysical e sigmaDimerBasis
  let P : MPSTensor.SectorDecomposition
      (Kraus.blockPhysDim 4 1 * Kraus.blockPhysDim 4 1) := {
    basisCount := 1
    basisDim := fun _ => 4
    basis := fun _ => B
    sectors := {
      copies := fun _ => 1
      copies_pos := fun _ => Nat.one_pos
      weight := fun _ _ => sigmaDimerNormalizingScalar⁻¹
      weight_ne_zero := fun _ _ => inv_ne_zero sigmaDimerNormalizingScalar_ne_zero } }
  have hB : MPTensor.IsNormalTensor B := sigmaDimerBasis_isNormalTensor.reindexPhysical e
  have hBlock := blockTensor_one_doubled_eq_reindexPhysical sigmaDimer
  refine ⟨sigmaDimer_isMPDO, 1, Nat.one_pos, P, ?_, ?_⟩
  · refine ⟨Nat.one_pos, ?_, fun _ => hB, ?_⟩
    · intro N hN σ
      rw [hBlock, P.mpv_toTensor_eq_sum_coeff]
      simp only [P, MPSTensor.SectorDecomposition.coeff,
        MPSTensor.SectorWeightData.coeff, Fin.sum_univ_one]
      change MPTensor.mpv (Kraus.reindexPhysical e sigmaDimer) σ =
        sigmaDimerNormalizingScalar⁻¹ ^ N * MPTensor.mpv B σ
      simp only [B, sigmaDimerBasis, MPTensor.mpv, MPTensor.coeff]
      rw [show Kraus.reindexPhysical e (sigmaDimerNormalizingScalar • sigmaDimer) =
        (fun i => sigmaDimerNormalizingScalar • Kraus.reindexPhysical e sigmaDimer i) from rfl,
        Kraus.evalWord_smul, Matrix.trace_smul, List.length_ofFn, smul_eq_mul,
        ← mul_assoc, ← mul_pow, inv_mul_cancel₀ sigmaDimerNormalizingScalar_ne_zero,
        one_pow, one_mul]
    · exact MPSTensor.exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
        (fun _ : Fin 1 => B) (fun _ => hB) (by
          intro j k hjk
          exact (hjk (Subsingleton.elim j k)).elim)
  · intro j hNil
    have hTransfer := doubledPhysTraceTransfer_reindex_singleBlock (d := 4) sigmaDimerBasis
    change IsNilpotent (doubledPhysTraceTransfer (Kraus.blockPhysDim 4 1) B) at hNil
    rw [hTransfer] at hNil
    have hz := (Matrix.isNilpotent_trace_of_isNilpotent hNil).eq_zero
    rw [sigmaDimerBasis_trace_physTransfer] at hz
    exact sigmaDimerNormalizingScalar_ne_zero hz

end MPOTensor.TwistedDimer

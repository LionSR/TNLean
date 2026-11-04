/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.WeightedOverlapBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalAccumulationBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalLocalEnergyCost

/-!
# Denominators and norms in rational local-energy evaluation

The matrix-unit weights are zero or one. A common denominator for the actual
tensor coordinates, scalar caps, and local operator coefficients therefore
controls every summand in the local-energy calculation. The same denominator
is preserved by both finite accumulations: the physical matrix-unit expansion
and the sum of local terms. Bounds on the decoded norms also bound the reduced
rational coordinates stored at every accumulation prefix.

## References

- LVV, arXiv:1307.5143, Claim 2.7: matrix elements for boundary minimization.
- Nature Physics 11 (2015), 566–569, supplementary information.
-/

namespace TNLean.MPS.AreaLaw

/-- Matrix-unit product factors have any positive common denominator and entry
norm at most one, including the identity factors away from the chosen sites. -/
theorem twoSiteMatrixUnitCodeFactors_bounds {q n M C : ℕ}
    (p r : Fin n) (a b c d : Fin q) (hM : 0 < M) (hC : 1 ≤ C) :
    ∀ j s t,
      HasGaussianIntegerDenominator M
        (decodeRationalComplex (twoSiteMatrixUnitCodeFactors p r a b c d j s t)) ∧
      ‖decodeRationalComplex (twoSiteMatrixUnitCodeFactors p r a b c d j s t)‖ ≤ (C : ℝ) := by
  have hzero : HasGaussianIntegerDenominator M (decodeRationalComplex (0 : ℚ × ℚ)) ∧
      ‖decodeRationalComplex (0 : ℚ × ℚ)‖ ≤ (C : ℝ) := by
    simpa only [decodeRationalComplex_zero, norm_zero] using
      And.intro (HasGaussianIntegerDenominator.zero hM) (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hone : HasGaussianIntegerDenominator M (decodeRationalComplex (1, 0)) ∧
      ‖decodeRationalComplex (1, 0)‖ ≤ (C : ℝ) := by
    constructor
    · refine ⟨hM, ⟨(M : GaussianInt), ?_⟩⟩
      simp
    · simpa using (show (1 : ℝ) ≤ C by exact_mod_cast hC)
  intro j s t
  unfold twoSiteMatrixUnitCodeFactors
  split_ifs <;>
    simp only [RationalRectMatrixCode.matrixUnit, RationalRectMatrixCode.identity] <;>
    split_ifs <;> first | exact hone | exact hzero

namespace RationalLocalEnergyCost

open RationalContractionCost

/-- The actual summand at a flattened physical matrix-unit label. -/
def twoSiteMatrixElementSummand {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (j : Fin ((q * q) * (q * q))) : Arithmetic (ℚ × ℚ) :=
  let uv : Fin (q * q) × Fin (q * q) := finProdFinEquiv.symm j
  let ab : Fin q × Fin q := finProdFinEquiv.symm uv.1
  let cd : Fin q × Fin q := finProdFinEquiv.symm uv.2
  weightedMatrixElementTerm A B capA capB PA PB
    (twoSiteMatrixUnitCodeFactors p r ab.1 ab.2 cd.1 cd.2)
    (K (ab.1, cd.1) (ab.2, cd.2))

/-- These summands are exactly those accumulated by the counted evaluator. -/
theorem twoSiteMatrixElementOfRationalParameters_eq_sumFin {q Da Db n : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q)) :
    twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K =
      RationalGramContractionCost.sumFin ((q * q) * (q * q))
        (twoSiteMatrixElementSummand A B capA capB PA PB p r K) := rfl

section CommonData

variable {q Da Db n M C : ℕ}
    (A : OBCChainTensor q Da n) (B : OBCChainTensor q Db n)
    (capA capB : ℚ × ℚ)
    (PA : OBCChainTensor.ParameterIndex A → ℚ × ℚ)
    (PB : OBCChainTensor.ParameterIndex B → ℚ × ℚ)
    (hM : 0 < M) (hC : 1 ≤ C)
    (hcapA : HasGaussianIntegerDenominator M (decodeRationalComplex capA))
    (hcapB : HasGaussianIntegerDenominator M (decodeRationalComplex capB))
    (hPA : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PA e)))
    (hPB : ∀ e, HasGaussianIntegerDenominator M (decodeRationalComplex (PB e)))
    (hcapAnorm : ‖decodeRationalComplex capA‖ ≤ (C : ℝ))
    (hcapBnorm : ‖decodeRationalComplex capB‖ ≤ (C : ℝ))
    (hPAnorm : ∀ e, ‖decodeRationalComplex (PA e)‖ ≤ (C : ℝ))
    (hPBnorm : ∀ e, ‖decodeRationalComplex (PB e)‖ ≤ (C : ℝ))

include hM hC hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm

/-- Each actual counted matrix-unit summand has denominator `M^(3n+3)` and
norm at most `C³ (Da Db q² C³)^n`, including its local operator coefficient. -/
theorem weightedMatrixElementTerm_bounds (p r : Fin n) (a b c d : Fin q)
    (weight : ℚ × ℚ)
    (hweight : HasGaussianIntegerDenominator M (decodeRationalComplex weight))
    (hweightnorm : ‖decodeRationalComplex weight‖ ≤ (C : ℝ)) :
    let z := (weightedMatrixElementTerm A B capA capB PA PB
      (twoSiteMatrixUnitCodeFactors p r a b c d) weight).run.1
    let R := C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n
    HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (R : ℝ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 3) * max 1 R ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 3) * max 1 R := by
  intro z R
  have hfactors := twoSiteMatrixUnitCodeFactors_bounds p r a b c d hM hC
  have hoverlap := OBCChainTensor.weightedOverlapOfRationalParameters_bounds
    A B capA capB PA PB (twoSiteMatrixUnitCodeFactors p r a b c d) hM
    hcapA hcapB hPA hPB (fun j s t ↦ (hfactors j s t).1)
    hcapAnorm hcapBnorm hPAnorm hPBnorm (fun j s t ↦ (hfactors j s t).2)
  have hden : HasGaussianIntegerDenominator (M ^ (3 * n + 3))
      (decodeRationalComplex z) := by
    have h := hweight.mul hoverlap.1
    have hp : M * M ^ (3 * n + 2) = M ^ (3 * n + 3) := by
      rw [← pow_succ']
    rw [hp] at h
    simpa only [z, run_weightedMatrixElementTerm, RationalComplexCode.decode_mul] using h
  have hnorm : ‖decodeRationalComplex z‖ ≤ (R : ℝ) := by
    simp only [z, run_weightedMatrixElementTerm, RationalComplexCode.decode_mul, norm_mul]
    calc
      _ ≤ (C : ℝ) * ((C ^ 2 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n : ℕ) : ℝ) :=
        mul_le_mul hweightnorm hoverlap.2.1 (norm_nonneg _) (Nat.cast_nonneg C)
      _ = (R : ℝ) := by simp only [R, Nat.cast_mul, Nat.cast_pow]; ring
  exact ⟨hden, hnorm,
    RationalComplexCode.coordinate_heights_of_common_denominator _ hden hnorm⟩

/-- Every actual prefix of the physical matrix-unit accumulation preserves
the common denominator; its norm and coordinate heights grow linearly in the
number of physical matrix units already accumulated. -/
theorem twoSiteMatrixElement_prefix_bounds {t : ℕ} (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K s u)))
    (hKnorm : ∀ s u, ‖decodeRationalComplex (K s u)‖ ≤ (C : ℝ))
    (ht : t ≤ (q * q) * (q * q)) :
    let z := (RationalGramContractionCost.sumFin t (fun j ↦
      twoSiteMatrixElementSummand A B capA capB PA PB p r K (Fin.castLE ht j))).run.1
    let R := C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n
    HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (t * R : ℕ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 3) * max 1 (t * R) ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 3) * max 1 (t * R) := by
  have hterms := fun j : Fin ((q * q) * (q * q)) ↦
    let uv : Fin (q * q) × Fin (q * q) := finProdFinEquiv.symm j
    let ab : Fin q × Fin q := finProdFinEquiv.symm uv.1
    let cd : Fin q × Fin q := finProdFinEquiv.symm uv.2
    weightedMatrixElementTerm_bounds A B capA capB PA PB hM hC hcapA hcapB hPA hPB
      hcapAnorm hcapBnorm hPAnorm hPBnorm p r ab.1 ab.2 cd.1 cd.2
      (K (ab.1, cd.1) (ab.2, cd.2)) (hK _ _) (hKnorm _ _)
  exact RationalGramContractionCost.sumFin_prefix_bounds
    (twoSiteMatrixElementSummand A B capA capB PA PB p r K) ht (pow_pos hM _)
    (fun j ↦ (hterms j).1) (fun j ↦ (hterms j).2.1)

/-- The complete two-site sum has the same denominator as its summands and
at most the fourth power of the physical dimension times their norm bound. -/
theorem twoSiteMatrixElementOfRationalParameters_bounds (p r : Fin n)
    (K : RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K s u)))
    (hKnorm : ∀ s u, ‖decodeRationalComplex (K s u)‖ ≤ (C : ℝ)) :
    let z := OBCChainTensor.twoSiteMatrixElementOfRationalParameters A B capA capB PA PB p r K
    let R := q ^ 4 * (C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n)
    HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (R : ℝ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 3) * max 1 R ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 3) * max 1 R := by
  have h := twoSiteMatrixElement_prefix_bounds A B capA capB PA PB hM hC
    hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm p r K hK hKnorm
    (Nat.le_refl ((q * q) * (q * q)))
  have hfour : (q * q) * (q * q) = q ^ 4 := by ring
  simpa only [Fin.castLE_refl, ← twoSiteMatrixElementOfRationalParameters_eq_sumFin,
    run_twoSiteMatrixElementOfRationalParameters, hfour] using h

/-- Every prefix of the actual local-term accumulation keeps the common
denominator. Its norm and coordinate heights grow linearly with the number
of local terms already accumulated. -/
theorem matrixElementOfLocalTerms_prefix_bounds {m t : ℕ}
    (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ i s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K i s u)))
    (hKnorm : ∀ i s u, ‖decodeRationalComplex (K i s u)‖ ≤ (C : ℝ))
    (ht : t ≤ m) :
    let z := (RationalGramContractionCost.sumFin t (fun j ↦
      let i := Fin.castLE ht j
      twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i))).run.1
    let R := q ^ 4 * (C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n)
    HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (t * R : ℕ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 3) * max 1 (t * R) ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 3) * max 1 (t * R) := by
  have hterms := fun i : Fin m ↦
    twoSiteMatrixElementOfRationalParameters_bounds A B capA capB PA PB hM hC
      hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm
      (p i) (r i) (K i) (hK i) (hKnorm i)
  apply RationalGramContractionCost.sumFin_prefix_bounds
    (fun i ↦ twoSiteMatrixElementOfRationalParameters A B capA capB PA PB (p i) (r i) (K i))
    ht (pow_pos hM _)
  · intro i
    simpa only [run_twoSiteMatrixElementOfRationalParameters] using (hterms i).1
  · intro i
    simpa only [run_twoSiteMatrixElementOfRationalParameters] using (hterms i).2.1

/-- The actual full rational local-energy sum has denominator `M^(3n+3)`.
Its norm is at most the number of local terms times the fourth power of the
physical dimension times the single-summand norm bound. -/
theorem matrixElementOfLocalTerms_bounds {m : ℕ}
    (p r : Fin m → Fin n)
    (K : Fin m → RationalRectMatrixCode (Fin q × Fin q) (Fin q × Fin q))
    (hK : ∀ i s u, HasGaussianIntegerDenominator M (decodeRationalComplex (K i s u)))
    (hKnorm : ∀ i s u, ‖decodeRationalComplex (K i s u)‖ ≤ (C : ℝ)) :
    let z := OBCChainTensor.matrixElementOfLocalTerms A B capA capB PA PB p r K
    let R := m * (q ^ 4 * (C ^ 3 * (Da * Db * (q ^ 2 * C ^ 3)) ^ n))
    HasGaussianIntegerDenominator (M ^ (3 * n + 3)) (decodeRationalComplex z) ∧
      ‖decodeRationalComplex z‖ ≤ (R : ℝ) ∧
      rationalHeight z.1 ≤ M ^ (3 * n + 3) * max 1 R ∧
      rationalHeight z.2 ≤ M ^ (3 * n + 3) * max 1 R := by
  have h := matrixElementOfLocalTerms_prefix_bounds A B capA capB PA PB hM hC
    hcapA hcapB hPA hPB hcapAnorm hcapBnorm hPAnorm hPBnorm p r K hK hKnorm
    (Nat.le_refl m)
  simp only [Fin.castLE_refl] at h
  rw [← matrixElementOfLocalTerms] at h
  simpa only [run_matrixElementOfLocalTerms] using h

end CommonData

end RationalLocalEnergyCost

end TNLean.MPS.AreaLaw

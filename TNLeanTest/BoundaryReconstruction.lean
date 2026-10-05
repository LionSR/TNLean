/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryZipperBlocked
import TNLean.MPS.MPDO.BoundaryZipperUniqueness
import TNLean.MPS.MPDO.CompleteZipperFusionGauge
import TNLean.MPS.MPDO.CompleteZipperFusionPentagon

/-!
# Reverse arbitrary-boundary decomposition regressions

Source-facing tests retain unnormalized injective blocks and genuine
incoming-block indices. Algebraic support and empty-factor tests are in
`PiMatrixRepresentation.lean`.
-/

-- These regressions intentionally inspect declaration and kernel-dependency reports.
set_option linter.hashCommand false

open scoped Matrix BigOperators Kronecker

namespace BoundaryReconstructionTest

-- Neither original spectral normalization nor a supplied simultaneous
-- inverse is an assumption of this source-block spanning theorem.
example {d r : ℕ} {dim : Fin r → ℕ}
    (A : (c : Fin r) → MPSTensor d (dim c))
    (hInj : ∀ c, Kraus.IsInjective (A c)) (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv A) :
    ∃ L : ℕ, 0 < L ∧ MPSTensor.WordTupleSpanTop A L :=
  MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hDim hDistinct

-- Each fixed pair of incoming MPO blocks gets its own multiplicities and
-- exact local tensors, rather than just an identity on periodic traces.
example {d r : ℕ} {dim : Fin r → ℕ}
    (T : MPOTensor d (∑ c : Fin r, dim c)) (hT : MPOTensor.IsBoundaryClosed T)
    (A : (c : Fin r) → MPOTensor d (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun c ↦ (A c).toMPSTensor))
    (hInj : ∀ c, Kraus.IsInjective (A c).toMPSTensor) (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (A c).toMPSTensor))
    (a b : Fin r) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (dim a * dim b)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (dim a * dim b)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (MPOTensor.mulTensor (A a) (A b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (m c) ↦ (A q.1).toMPSTensor)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  exact hT.exists_blockFusionDecomposition_of_isInjective A hBlocks hInj hDim hDistinct a b

-- The action theorem requires only the state blocks to be injective and
-- separated. The incoming operator blocks have no such hypotheses.
example {d r s : ℕ} {opDim : Fin r → ℕ} {dim : Fin s → ℕ}
    (T : MPOTensor d (∑ a : Fin r, opDim a))
    (A : MPSTensor d (∑ c : Fin s, dim c)) (h : MPOTensor.IsBoundaryCompatible T A)
    (S : (a : Fin r) → MPOTensor d (opDim a))
    (B : (c : Fin s) → MPSTensor d (dim c))
    (hT : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (S a).toMPSTensor))
    (hA : A = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    (hInj : ∀ c, Kraus.IsInjective (B c)) (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv B)
    (a : Fin r) (x : Fin s) :
    ∃ (m : Fin s → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (opDim a * dim x)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (opDim a * dim x)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (MPOTensor.actTensor (S a) (B x))
        (fun q : (c : Fin s) × Fin (m c) ↦ B q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) :=
  h.exists_blockActionDecomposition_of_isInjective S B hT hA hInj hDim hDistinct a x

-- The empty target family is included in the simultaneous-span theorem.
example (A : (c : Fin 0) → MPSTensor 1 (Fin.elim0 c)) :
    ∃ L : ℕ, 0 < L ∧ MPSTensor.WordTupleSpanTop A L := by
  exact MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective
    (fun c ↦ Fin.elim0 c) (fun c ↦ Fin.elim0 c) (fun c ↦ Fin.elim0 c)

-- The complete family is constructed at a derived positive physical
-- blocking. Its tensors are the blocked original blocks, not replacements.
example {p g : ℕ} {D : Fin g → ℕ}
    (T : MPOTensor p (∑ c : Fin g, D c)) (h : MPOTensor.IsBoundaryClosed T)
    (A : (c : Fin g) → MPOTensor p (D c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun c ↦ (A c).toMPSTensor))
    (hInj : ∀ c, Kraus.IsInjective (A c).toMPSTensor) (hD : ∀ c, 0 < D c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (A c).toMPSTensor)) :
    ∃ L : ℕ, 0 < L ∧
      ∃ F : MPOTensor.CompleteZipperFusionFamily (Fin g) (MPSTensor.blockPhysDim p L),
        (F).bondDim = D ∧ HEq (F).tensor (fun c ↦ MPOTensor.blockTensor (A c) L) := by
  obtain ⟨N, V, W, hVW, L, hL, F, hFD, hFN, hFT, hFW, hFV⟩ :=
    h.exists_completeZipperFusionFamily A hBlocks hInj hD hne
  exact ⟨L, hL, F, hFD, hFT⟩

-- Independent exact decompositions have the same multiplicity function.
example {d DB g : ℕ} {dim N M : Fin g → ℕ} {B : MPSTensor d DB}
    {A : ∀ c, MPSTensor d (dim c)}
    {VN : ∀ c, Fin (N c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WN : ∀ c, Fin (N c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    {VM : ∀ c, Fin (M c) → Matrix (Fin (dim c)) (Fin DB) ℂ}
    {WM : ∀ c, Fin (M c) → Matrix (Fin DB) (Fin (dim c)) ℂ}
    (hN : MPSTensor.IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (N c) ↦ A q.1)
      (fun q ↦ VN q.1 q.2) (fun q ↦ WN q.1 q.2))
    (hM : MPSTensor.IsBiorthogonalDecomposition B
      (fun q : (c : Fin g) × Fin (M c) ↦ A q.1)
      (fun q ↦ VM q.1 q.2) (fun q ↦ WM q.1 q.2))
    (hInj : ∀ c, Kraus.IsInjective (A c)) (hD : ∀ c, 0 < dim c)
    (hne : MPSTensor.BlocksNotGaugePhaseEquiv A) : N = M :=
  hN.multiplicity_eq_of_isInjective hM hInj hD hne

section BlockedCoherence

variable {p g : ℕ} {D : Fin g → ℕ} {T : ∀ c, MPOTensor p (D c)}
  {N : Fin g → Fin g → Fin g → ℕ}
  (hNormal : ∀ c, Kraus.IsNormal (T c).toMPSTensor) (hDim : ∀ c, 0 < D c)
  (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (T c).toMPSTensor))
  (V : ∀ a b c, Fin (N a b c) → Matrix (Fin (D c)) (Fin (D a * D b)) ℂ)
  (W : ∀ a b c, Fin (N a b c) → Matrix (Fin (D a * D b)) (Fin (D c)) ℂ)
  (hVW : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (MPOTensor.mulTensor (T a) (T b)).toMPSTensor
      (fun q : (c : Fin g) × Fin (N a b c) ↦ (T q.1).toMPSTensor)
      (fun q ↦ V a b q.1 q.2) (fun q ↦ W a b q.1 q.2))

local notation "F" =>
  MPOTensor.CompleteZipperFusionFamily.ofBiorthogonalBlocked hNormal hDim hDistinct V W hVW

example (a b c : Fin g) (μ : Fin (N a b c))
    (x : Fin (D a) × Fin (D b)) (z : Fin (D c)) :
    (F).fusionTensor a b c μ x z = W a b c μ (finProdFinEquiv x) z := rfl

example (a b c : Fin g) (μ : Fin (N a b c))
    (z : Fin (D c)) (x : Fin (D a) × Fin (D b)) :
    (F).fusionTensorLeftInverse a b c μ z x = V a b c μ z (finProdFinEquiv x) := rfl

-- Existing coherence results apply directly to the constructed family.
example (a b c d : Fin g) :
    (F).rightTripleSynthesis a b c d *
      ((F).printedFMatrix a b c d ⊗ₖ (1 : Matrix (Fin (D d)) (Fin (D d)) ℂ)) =
        (F).leftTripleSynthesis a b c d :=
  (F).rightTripleSynthesis_mul_printedFMatrix a b c d

example (a b c d : Fin g) :
    (F).printedFMatrix a b c d * (F).inversePrintedFMatrix a b c d = 1 :=
  (F).printedFMatrix_mul_inversePrintedFMatrix a b c d

example (a b c d e : Fin g) :
    (F).threeEdgePrintedFMatrix a b c d e = (F).twoEdgePrintedFMatrix a b c d e :=
  (F).threeEdgePrintedFMatrix_eq_twoEdgePrintedFMatrix a b c d e

example (Y : (F).FusionGauge) (a b c d : Fin g) :
    ((F).regauge Y).printedFMatrix a b c d =
      (F).rightTreeGaugeInv Y a b c d * (F).printedFMatrix a b c d *
        (F).leftTreeGauge Y a b c d :=
  (F).printedFMatrix_regauge Y a b c d

end BlockedCoherence

#print axioms Matrix.exists_rankFactorization_of_idempotent
#print axioms Matrix.exists_piMatrix_blocks
#print axioms MPSTensor.familyTraceAdjoint_map_mul
#print axioms MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective
#print axioms MPOTensor.IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective
#print axioms MPOTensor.IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective
#print axioms MPOTensor.IsBoundaryClosed.exists_completeZipperFusionFamily
#print axioms MPSTensor.IsBiorthogonalDecomposition.multiplicity_eq_of_isInjective
#print axioms MPSTensor.IsBiorthogonalDecomposition.exists_unique_multiplicityGauge_of_isInjective

end BoundaryReconstructionTest

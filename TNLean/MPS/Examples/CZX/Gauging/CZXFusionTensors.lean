/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Reduction.ReductionBlocking
import TNLean.MPS.Examples.CZX.Gauging.CZXDaggerGauge
import TNLean.MPS.Operator.Unitary.Identity
import TNLean.MPS.Operator.PairAlphabetBridge

/-!
# The concrete CZX `g,g` fusion tensors

This file records only the concrete fusion slice of arXiv:2502.20257,
`eq:Fgg` for the CZX tensor: the product of the displayed CZX MPU tensor with
itself reduces to the bond-one identity tensor. The two rectangular matrices
are the displayed `Y`-decorated caps, with the `1/2` weight on the right cap
as printed in lines 4671--4689.

No general fusion, anomaly, action, defect, or gauging statement is made here.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace MPOTensor.CZX

/-- The left `Y`-decorated cap in arXiv:2502.20257, `eq:Fgg`, lines 2000--2037
and 4671--4689. The product bond is ordered by `finProdFinEquiv`. -/
def fusionV : Matrix (Fin 1) (Fin 4) ℂ :=
  fun _ ab ↦ if ab = 1 then -Complex.I else if ab = 2 then Complex.I else 0

/-- The right `Y`-decorated cap in arXiv:2502.20257, `eq:Fgg`, lines 2000--2037
and 4671--4689. The printed CZX specialization carries the factor `1/2` on
this cap. -/
def fusionW : Matrix (Fin 4) (Fin 1) ℂ :=
  fun ab _ ↦ if ab = 1 then Complex.I / 2 else if ab = 2 then -Complex.I / 2 else 0

/-- Coordinate form of the printed CZX `g,g` fusion caps: under the product-bond
order `finProdFinEquiv`, the left cap is `Y_ab` and the right cap is
`(1/2) Y_ba`.

Source: arXiv:2502.20257, `eq:Fgg`, lines 4671--4689. -/
theorem fusion_caps_apply (a b : Fin 2) :
    fusionV 0 (finProdFinEquiv (a, b)) = daggerGauge a b ∧
      fusionW (finProdFinEquiv (a, b)) 0 = (1 / 2 : ℂ) * daggerGauge b a := by
  fin_cases a <;> fin_cases b <;>
    norm_num +decide [fusionV, fusionW, daggerGauge, SpinCover.pauli_one, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.reduceEq] <;>
    ring_nf

/-- Sparse diagonal letters of the `CZX.tensor * CZX.tensor` product, in the
product-bond order `00, 01, 10, 11`. -/
private def fusionProductDiagonalLetter (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun x y ↦
    if i = 0 then
      if x = 1 then if y = 0 then -1 else if y = 1 then 1 else if y = 2 then -1 else 1
      else 0
    else if i = 1 then
      if x = 1 then if y = 0 then 1 else if y = 1 then 1 else if y = 2 then -1 else -1
      else 0
    else if i = 2 then
      if x = 2 then if y = 0 then 1 else if y = 1 then -1 else if y = 2 then 1 else -1
      else 0
    else
      if x = 2 then if y = 0 then -1 else if y = 1 then -1 else if y = 2 then 1 else 1
      else 0

/-- Sparse form of the letter `(i, j)` of the product tensor over the pair alphabet. -/
private def fusionProductLetter (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  if i = j then fusionProductDiagonalLetter i else 0

private theorem fusion_product_letter_eq (i j : Fin 4) :
    MPOTensor.mulTensor tensor tensor (i, j) = fusionProductLetter i j := by
  have hc : ∀ j : Fin 4, complementSite j = j.rev := by decide
  have hcc : ∀ j : Fin 4, complementSite (complementSite j) = j := by decide
  have hb : ∀ i : Fin 4, siteBits i =
      (show ZMod 2 from Fin.divNat (m := 2) (n := 2) i,
        show ZMod 2 from Fin.modNat (m := 2) (n := 2) i) := by decide
  simp only [MPOTensor.mulTensor_apply]
  ext x y
  rcases finProdFinEquiv.surjective x with ⟨⟨x₁, x₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective y with ⟨⟨y₁, y₂⟩, rfl⟩
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    finProdFinEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single (complementSite i)]
  · by_cases hij : i = j
    · subst j
      by_cases hx : x₁ = (show Fin 2 from (siteBits i).1) ∧
          x₂ = (show Fin 2 from (siteBits (complementSite i)).1)
      · rcases hx with ⟨rfl, rfl⟩
        fin_cases i <;> fin_cases y₁ <;> fin_cases y₂ <;>
          norm_num +decide [fusionProductLetter, fusionProductDiagonalLetter,
            tensor_apply, hc, hb, edgeExponent, Fin.divNat, Fin.modNat, Fin.rev,
            ZMod.val, Fin.reduceEq, finProdFinEquiv]
      · have hz : fusionProductLetter i i (finProdFinEquiv (x₁, x₂))
            (finProdFinEquiv (y₁, y₂)) = 0 := by
          fin_cases i <;> fin_cases x₁ <;> fin_cases x₂ <;>
            norm_num +decide [hc, hb, Fin.divNat, Fin.modNat, Fin.rev, ZMod.val,
              Fin.reduceEq] at hx <;>
            norm_num +decide [fusionProductLetter, fusionProductDiagonalLetter,
              Fin.reduceEq, finProdFinEquiv]
        rw [hz]
        simp only [tensor_apply, ite_zero_mul_ite_zero]
        split_ifs with h
        · exact (hx ⟨h.1.2, h.2.2⟩).elim
        · rfl
    · have hne : complementSite i ≠ complementSite j := complementSite.injective.ne hij
      simp [tensor_apply, hne, fusionProductLetter, hij]
  · intro b _ hbne
    have hfirst : i ≠ complementSite b := by
      intro hi
      apply hbne
      calc
        b = complementSite (complementSite b) := (hcc b).symm
        _ = complementSite i := by rw [← hi]
    rw [tensor_apply]
    simp [hfirst]
  · intro hbnot
    exact (hbnot (Finset.mem_univ _)).elim

/-- Coordinates of the two supported diagonal letters of the product tensor
`CZX.tensor * CZX.tensor`: the physical letter `(3x, 3x)` carried by the GHZ
block `x`, in the product-bond order `finProdFinEquiv`.

Source: arXiv:2502.20257, `eq:MPU_CZX`, lines 4505--4547. -/
theorem mulTensor_diagonal_letter_coordinates (x : Fin 2) :
    MPOTensor.mulTensor tensor tensor (finProdFinEquiv (x, x), finProdFinEquiv (x, x)) =
      if x = 0 then !![0, 0, 0, 0; -1, 1, -1, 1; 0, 0, 0, 0; 0, 0, 0, 0]
      else !![0, 0, 0, 0; 0, 0, 0, 0; -1, -1, 1, 1; 0, 0, 0, 0] := by
  rw [fusion_product_letter_eq]
  fin_cases x <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num +decide [fusionProductLetter, fusionProductDiagonalLetter, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.reduceEq]

private theorem fusionV_mul_fusionW :
    fusionV * fusionW = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [fusionV, fusionW, Matrix.mul_apply, Fin.sum_univ_four]
  ring_nf
  simp [Complex.I_sq]

private theorem fusion_letter_compression (ij : Fin 4 × Fin 4) :
    fusionV * MPOTensor.mulTensor tensor tensor ij * fusionW = identityMPUTensor 4 ij := by
  obtain ⟨i, j⟩ := ij
  rw [fusion_product_letter_eq]
  ext a b
  fin_cases a
  fin_cases b
  fin_cases i <;> fin_cases j <;>
    simp [fusionV, fusionW, fusionProductLetter, fusionProductDiagonalLetter,
      identityMPUTensor, idTensor, Matrix.mul_apply, Fin.sum_univ_four, Fin.reduceEq] <;>
    ring_nf <;>
    simp [Complex.I_sq]

set_option maxHeartbeats 800000 in
-- The diagonal core is a finite 4-by-4 product-bond calculation with complex `I` entries.
private theorem fusion_projection_insertion (ij kl : Fin 4 × Fin 4) :
    MPOTensor.mulTensor tensor tensor ij * fusionW * fusionV *
        MPOTensor.mulTensor tensor tensor kl =
      MPOTensor.mulTensor tensor tensor ij * MPOTensor.mulTensor tensor tensor kl := by
  obtain ⟨i, j⟩ := ij
  obtain ⟨k, l⟩ := kl
  rw [fusion_product_letter_eq, fusion_product_letter_eq]
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      ext a b
      by_cases ha : a = (if i = 0 ∨ i = 1 then 1 else 2)
      · subst a
        fin_cases i <;> fin_cases b <;> fin_cases k <;>
          simp [fusionV, fusionW, fusionProductLetter, fusionProductDiagonalLetter,
            Matrix.mul_apply, Fin.sum_univ_four, Fin.reduceEq] <;>
          ring_nf <;>
          simp [Complex.I_sq]
      · have hz : ∀ c, fusionProductLetter i i a c = 0 := by
          intro c
          fin_cases i <;>
            simp_all [fusionProductLetter, fusionProductDiagonalLetter, Fin.reduceEq]
        simp [Matrix.mul_apply, hz]
    · simp [fusionProductLetter, hkl]
  · simp [fusionProductLetter, hij]

private theorem evalWord_fusion_projection_insertion (p q : List (Fin 4 × Fin 4))
    (hp : p ≠ []) (hq : q ≠ []) :
    Kraus.evalWord (MPOTensor.mulTensor tensor tensor) p * fusionW * fusionV *
        Kraus.evalWord (MPOTensor.mulTensor tensor tensor) q =
      Kraus.evalWord (MPOTensor.mulTensor tensor tensor) (p ++ q) := by
  induction p with
  | nil => contradiction
  | cons i p ih =>
      cases p with
      | nil =>
          cases q with
          | nil => contradiction
          | cons j q =>
              calc
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor) [i] *
                      fusionW * fusionV *
                    Kraus.evalWord (MPOTensor.mulTensor tensor tensor)
                      (j :: q) =
                    (MPOTensor.mulTensor tensor tensor i *
                        fusionW * fusionV *
                      MPOTensor.mulTensor tensor tensor j) *
                        Kraus.evalWord (MPOTensor.mulTensor tensor tensor) q := by
                  simp [Matrix.mul_assoc]
                _ = (MPOTensor.mulTensor tensor tensor i *
                        MPOTensor.mulTensor tensor tensor j) *
                      Kraus.evalWord (MPOTensor.mulTensor tensor tensor) q := by
                  rw [fusion_projection_insertion]
                _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor)
                    ([i] ++ j :: q) := by
                  simp [Matrix.mul_assoc]
      | cons j p =>
          have hp_tail : j :: p ≠ [] := by simp
          calc
            Kraus.evalWord (MPOTensor.mulTensor tensor tensor) (i :: j :: p) *
                  fusionW * fusionV *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor) q =
                MPOTensor.mulTensor tensor tensor i *
                  (Kraus.evalWord (MPOTensor.mulTensor tensor tensor)
                    (j :: p) * fusionW * fusionV *
                    Kraus.evalWord (MPOTensor.mulTensor tensor tensor) q) := by
              simp [Matrix.mul_assoc]
            _ = MPOTensor.mulTensor tensor tensor i *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor)
                  ((j :: p) ++ q) := by rw [ih hp_tail]
            _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor)
                ((i :: j :: p) ++ q) := by simp

/-- The printed CZX `F^<_{g,g}` and `F^>_{g,g}` caps form an all-word
rectangular reduction from the actual product tensor to the bond-one identity.

Source: arXiv:2502.20257, `eq:fusion_2`, `main.tex` lines 1458--1498
(all-word identity); `eq:Fgg`, lines 2000--2037, specialized by the CZX
display in lines 4671--4689 (caps). -/
theorem fusion_isReduction :
    MPTensor.IsReduction (MPOTensor.mulTensor tensor tensor) (identityMPUTensor 4)
      fusionV fusionW :=
  MPTensor.IsReduction.of_local_compression fusionV_mul_fusionW
    fusion_letter_compression fusion_projection_insertion

/-- The concrete CZX fusion reduction satisfies the exterior identity with
one physical letter on each side. This is only the reduction-buffer statement
for the concrete `g,g` product slice. It is stated on the doubled index `Fin (4 * 4)` of the
pair alphabet, the alphabet of the buffer-length predicate.

Source: arXiv:2502.20257, `eq:fusion_1`, `main.tex` lines 1405--1457,
with the length conditions in line 1498 (exterior identity); `eq:Fgg`,
lines 2000--2037 and the CZX display in lines 4671--4689 (caps). -/
theorem fusion_isReductionExteriorBufferLength_one :
    MPSTensor.IsReductionExteriorBufferLength
      (MPOTensor.mulTensor tensor tensor).toMPSTensor
      (identityMPUTensor 4).toMPSTensor fusionV fusionW 1 := by
  intro p c q hc hp hq
  simp only [evalWord_toMPSTensor, List.map_append]
  have hne : ∀ w : List (Fin (4 * 4)), w ≠ [] → w.map finProdFinEquiv.symm ≠ [] := by
    simp
  rw [← fusion_isReduction.evalWord, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    evalWord_fusion_projection_insertion _ _ (hne p (List.ne_nil_of_length_pos hp)) (hne c hc),
    evalWord_fusion_projection_insertion _ _ (by simp [hne c hc])
      (hne q (List.ne_nil_of_length_pos hq))]

end MPOTensor.CZX

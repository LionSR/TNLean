/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionBlocking
import TNLean.MPS.MPDO.CZXDaggerGauge
import TNLean.MPS.MPU.Examples.Shift

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

/-- Sparse form of one product-tensor letter after converting to the doubled
MPS index. -/
private def fusionProductLetter (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  if i = j then fusionProductDiagonalLetter i else 0

private theorem fusion_product_letter_eq (i j : Fin 4) :
    (MPOTensor.mulTensor tensor tensor).toMPSTensor (finProdFinEquiv (i, j)) =
      fusionProductLetter i j := by
  have hc : ∀ j : Fin 4, complementSite j = j.rev := by decide
  have hcc : ∀ j : Fin 4, complementSite (complementSite j) = j := by decide
  have hb : ∀ i : Fin 4, siteBits i =
      (show ZMod 2 from Fin.divNat (m := 2) (n := 2) i,
        show ZMod 2 from Fin.modNat (m := 2) (n := 2) i) := by decide
  simp only [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, MPOTensor.mulTensor_apply]
  ext x y
  rcases finProdFinEquiv.surjective x with ⟨⟨x₁, x₂⟩, rfl⟩
  rcases finProdFinEquiv.surjective y with ⟨⟨y₁, y₂⟩, rfl⟩
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    finProdFinEquiv.symm_apply_apply]
  rw [Finset.sum_eq_single (complementSite i)]
  · fin_cases i <;> fin_cases j <;> fin_cases x₁ <;> fin_cases x₂ <;>
      fin_cases y₁ <;> fin_cases y₂ <;>
      norm_num +decide [fusionProductLetter, fusionProductDiagonalLetter,
        tensor_apply, hc, hb, edgeExponent, Fin.divNat, Fin.modNat, Fin.rev,
        ZMod.val, Fin.reduceEq, finProdFinEquiv, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
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

private theorem isReduction_of_local_compression {d D₁ D₂ : ℕ}
    {B : MPSTensor d D₂} {A : MPSTensor d D₁}
    {V : Matrix (Fin D₁) (Fin D₂) ℂ} {W : Matrix (Fin D₂) (Fin D₁) ℂ}
    (hVW : V * W = 1)
    (hletter : ∀ i, V * B i * W = A i)
    (hinsert : ∀ i j, B i * W * V * B j = B i * B j) :
    MPSTensor.IsReduction B A V W := by
  refine ⟨hVW, fun w ↦ ?_⟩
  induction w with
  | nil =>
      simp [hVW]
  | cons i w ih =>
      cases w with
      | nil =>
          simpa using hletter i
      | cons j w =>
          calc
            V * Kraus.evalWord B (i :: j :: w) * W =
                V * ((B i * W * V * B j) * Kraus.evalWord B w) * W := by
              rw [Kraus.evalWord_cons, Kraus.evalWord_cons, hinsert i j]
              simp [Matrix.mul_assoc]
            _ = (V * B i * W) * (V * Kraus.evalWord B (j :: w) * W) := by
              simp [Matrix.mul_assoc]
            _ = A i * Kraus.evalWord A (j :: w) := by
              rw [hletter i, ih]
            _ = Kraus.evalWord A (i :: j :: w) := rfl

private theorem fusionV_mul_fusionW :
    fusionV * fusionW = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [fusionV, fusionW, Matrix.mul_apply, Fin.sum_univ_four]
  ring_nf
  simp [Complex.I_sq]

private theorem fusion_letter_compression (ij : Fin (4 * 4)) :
    fusionV * (MPOTensor.mulTensor tensor tensor).toMPSTensor ij * fusionW =
      (identityMPUTensor 4).toMPSTensor ij := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  rw [fusion_product_letter_eq]
  ext a b
  fin_cases a
  fin_cases b
  fin_cases i <;> fin_cases j <;>
    simp [fusionV, fusionW, fusionProductLetter, fusionProductDiagonalLetter,
      identityMPUTensor, idTensor,
      MPOTensor.toMPSTensor, Matrix.mul_apply, Fin.sum_univ_four, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.reduceEq] <;>
    ring_nf <;>
    simp [Complex.I_sq]

set_option maxHeartbeats 800000 in
-- The diagonal core is a finite 4-by-4 product-bond calculation with complex `I` entries.
private theorem fusion_projection_insertion (ij kl : Fin (4 * 4)) :
    (MPOTensor.mulTensor tensor tensor).toMPSTensor ij * fusionW * fusionV *
        (MPOTensor.mulTensor tensor tensor).toMPSTensor kl =
      (MPOTensor.mulTensor tensor tensor).toMPSTensor ij *
        (MPOTensor.mulTensor tensor tensor).toMPSTensor kl := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective kl
  rw [fusion_product_letter_eq, fusion_product_letter_eq]
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      ext a b
      fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases k <;>
        simp [fusionV, fusionW, fusionProductLetter, fusionProductDiagonalLetter,
          Matrix.mul_apply, Fin.sum_univ_four, Fin.reduceEq] <;>
        ring_nf <;>
        simp [Complex.I_sq]
    · simp [fusionProductLetter, hkl]
  · simp [fusionProductLetter, hij]

private theorem evalWord_fusion_projection_insertion (p q : List (Fin (4 * 4)))
    (hp : p ≠ []) (hq : q ≠ []) :
    Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor p * fusionW * fusionV *
        Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor q =
      Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (p ++ q) := by
  induction p with
  | nil => contradiction
  | cons i p ih =>
      cases p with
      | nil =>
          cases q with
          | nil => contradiction
          | cons j q =>
              calc
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor [i] *
                      fusionW * fusionV *
                    Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                      (j :: q) =
                    ((MPOTensor.mulTensor tensor tensor).toMPSTensor i *
                        fusionW * fusionV *
                      (MPOTensor.mulTensor tensor tensor).toMPSTensor j) *
                        Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor q := by
                  simp [Matrix.mul_assoc]
                _ = ((MPOTensor.mulTensor tensor tensor).toMPSTensor i *
                        (MPOTensor.mulTensor tensor tensor).toMPSTensor j) *
                      Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor q := by
                  rw [fusion_projection_insertion]
                _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                    ([i] ++ j :: q) := by
                  simp [Matrix.mul_assoc]
      | cons j p =>
          have hp_tail : j :: p ≠ [] := by simp
          calc
            Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (i :: j :: p) *
                  fusionW * fusionV *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor q =
                (MPOTensor.mulTensor tensor tensor).toMPSTensor i *
                  (Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                    (j :: p) * fusionW * fusionV *
                    Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor q) := by
              simp [Matrix.mul_assoc]
            _ = (MPOTensor.mulTensor tensor tensor).toMPSTensor i *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                  ((j :: p) ++ q) := by rw [ih hp_tail]
            _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                ((i :: j :: p) ++ q) := by simp

/-- The printed CZX `F^<_{g,g}` and `F^>_{g,g}` caps form an all-word
rectangular reduction from the actual product tensor to the bond-one identity.

Source: arXiv:2502.20257, `eq:fusion_2`, `main.tex` lines 1458--1498
(all-word identity); `eq:Fgg`, lines 2000--2037, specialized by the CZX
display in lines 4671--4689 (caps). -/
theorem fusion_isReduction :
    MPSTensor.IsReduction
      (MPOTensor.mulTensor tensor tensor).toMPSTensor
      (identityMPUTensor 4).toMPSTensor fusionV fusionW :=
  isReduction_of_local_compression fusionV_mul_fusionW
    fusion_letter_compression fusion_projection_insertion

set_option maxHeartbeats 2000000 in
-- The proof reassociates three nonempty word insertions around the rectangular caps.
/-- The concrete CZX fusion reduction satisfies the exterior identity with
one physical letter on each side. This is only the reduction-buffer statement
for the concrete `g,g` product slice.

Source: arXiv:2502.20257, `eq:fusion_1`, `main.tex` lines 1405--1457,
with the length conditions in line 1498 (exterior identity); `eq:Fgg`,
lines 2000--2037 and the CZX display in lines 4671--4689 (caps). -/
theorem fusion_isReductionExteriorBufferLength_one :
    MPSTensor.IsReductionExteriorBufferLength
      (MPOTensor.mulTensor tensor tensor).toMPSTensor
      (identityMPUTensor 4).toMPSTensor fusionV fusionW 1 := by
  intro p c q hc hp hq
  cases p with
  | nil => simp at hp
  | cons p₀ p =>
      cases q with
      | nil => simp at hq
      | cons q₀ q =>
          have hcEval := fusion_isReduction.evalWord c
          rw [← hcEval]
          calc
            Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (p₀ :: p) *
                  fusionW *
                (fusionV * Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor c *
                  fusionW) * fusionV *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (q₀ :: q) =
                (Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (p₀ :: p) *
                    fusionW * fusionV *
                  Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor c) *
                    fusionW * fusionV *
                  Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (q₀ :: q) := by
              simp only [Matrix.mul_assoc]
            _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                  ((p₀ :: p) ++ c) * fusionW * fusionV *
                Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor (q₀ :: q) := by
              rw [evalWord_fusion_projection_insertion (p₀ :: p) c (by simp) hc]
            _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                (((p₀ :: p) ++ c) ++ (q₀ :: q)) := by
              rw [evalWord_fusion_projection_insertion ((p₀ :: p) ++ c) (q₀ :: q)
                (by simp) (by simp)]
            _ = Kraus.evalWord (MPOTensor.mulTensor tensor tensor).toMPSTensor
                (p₀ :: p ++ c ++ q₀ :: q) := by
              simp only [List.cons_append, List.append_assoc]

end MPOTensor.CZX

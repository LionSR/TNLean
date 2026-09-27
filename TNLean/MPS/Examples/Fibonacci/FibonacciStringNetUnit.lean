/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciGSymbol

/-!
# Fibonacci string-net: the unit compressions on both edge labels

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` lines 1262–1268: the
blocks `B_1`, `B_τ` of the string-net operator tensor, on the physical letters (plaquette, edge
label), satisfy the Fibonacci fusion rules.

**Formalized here.** The compression data of the products `1 ⊗ 1`, `1 ⊗ τ` and `τ ⊗ 1` of the
extended F-symbol blocks `fibBlockFull` (`FibonacciGSymbol.lean`) on the sixteen letters of the
stacked tensors, with the gauges of `FibonacciUnit.lean`. At edge label `τ` the conjugated letters
are the recorded block-diagonal ones; at edge label `1` they are block upper triangular, with the
edge-label-`1` letters of the target block on the diagonal and further entries only in the columns
of the zero slots. Every clause is decided over `ℤ[σ]`.

## Main definitions

* `FibonacciCompression.fibConjFull`: conjugated letters on the four physical letters.
* `FibonacciCompression.fibOneOneFull_compression`,
  `FibonacciCompression.fibOneTauFull_compression`,
  `FibonacciCompression.fibTauOneFull_compression`: the three unit compression data.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-! ### Fusion of the extended blocks

The four compression data of `Fibonacci.lean` and `FibonacciUnit.lean` extend to the sixteen
letters of the stacked products of the extended blocks with the same gauges. At the letters with
edge label `τ` the conjugated letters are the recorded block-diagonal ones; at the letters with
edge label `1` they are block upper triangular, with the edge-label-`1` letters of the target
blocks on the diagonal and further entries only in the columns of the zero slots, so the
remainder no longer vanishes but the trace identity of the compression still holds. -/

/-- The conjugated letters of a stacked product on the four physical letters: the recorded
letters `Kτ` of the product of the F-symbol blocks at edge label `τ` (indexed by the pair
alphabet `Fin 4`), the letters `K₁` at edge label `1`, and zero when the edge label changes. -/
def fibConjFull {n : ℕ} (Kτ : Fin 4 → Matrix (Fin n) (Fin n) GoldenInt)
    (K₁ : Fin 2 → Fin 2 → Matrix (Fin n) (Fin n) GoldenInt) :
    Fin 4 → Fin 4 → Matrix (Fin n) (Fin n) GoldenInt :=
  fibEdgeGraded (fun x' x => Kτ (finProdFinEquiv (x', x))) K₁

/-- A graded letter identity `S G = G K` follows from the identities at edge label `τ` and at
edge label `1`; the letters that change the edge label vanish on both sides. -/
theorem fibConjFull_mul_eq {n : ℕ} {Sτ Kτ : Fin 4 → Matrix (Fin n) (Fin n) GoldenInt}
    {S₁ K₁ : Fin 2 → Fin 2 → Matrix (Fin n) (Fin n) GoldenInt}
    {G : Matrix (Fin n) (Fin n) GoldenInt}
    (hτ : ∀ e, Sτ e * G = G * Kτ e) (h₁ : ∀ x' x, S₁ x' x * G = G * K₁ x' x) (i j : Fin 4) :
    fibConjFull Sτ S₁ i j * G = G * fibConjFull Kτ K₁ i j := by
  unfold fibConjFull fibEdgeGraded
  split_ifs
  · exact hτ _
  · exact h₁ _ _
  · rw [Matrix.zero_mul, Matrix.mul_zero]

/-- The conjugated letters of `1 ⊗ 1` at edge label `1`. -/
def fibOneOneEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 4) (Fin 4) GoldenInt
  | 0, 0 => Matrix.single 0 0 1 + Matrix.single 0 2 1 + Matrix.single 0 3 1
  | 1, 1 => Matrix.single 1 1 1
  | _, _ => 0

/-- The conjugated letters of `1 ⊗ τ` at edge label `1`. -/
def fibOneTauEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 0 0 1 + Matrix.single 0 3 1 + Matrix.single 0 4 1 + Matrix.single 0 5 1
  | 1, 0 => Matrix.single 1 1 1 + Matrix.single 1 5 ⟨0, 1, 0, 1⟩
  | 1, 1 => Matrix.single 2 2 1 + Matrix.single 2 5 (-1)
  | _, _ => 0

/-- The conjugated letters of `τ ⊗ 1` at edge label `1`. -/
def fibTauOneEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 0 0 1 + Matrix.single 0 5 ⟨-1, 0, 1, 0⟩
  | 1, 0 => Matrix.single 1 1 1 + Matrix.single 1 3 1 + Matrix.single 1 4 ⟨0, -1, 0, 0⟩ +
      Matrix.single 1 5 ⟨0, 0, 0, -1⟩
  | 1, 1 => Matrix.single 2 2 1 + Matrix.single 2 5 ⟨1, 0, -1, 0⟩
  | _, _ => 0

/-- The conjugated letters of `τ ⊗ τ` at edge label `1`. -/
def fibTauTauEdgeOneConjGolden : Fin 2 → Fin 2 → Matrix (Fin 9) (Fin 9) GoldenInt
  | 0, 0 => Matrix.single 0 0 1 + Matrix.single 0 8 ⟨-1, 0, -1, 0⟩
  | 0, 1 => Matrix.single 2 2 1 + Matrix.single 2 7 ⟨0, 0, 0, 1⟩ + Matrix.single 2 8 ⟨-1, 0, 1, 0⟩
  | 1, 0 => Matrix.single 3 3 1 + Matrix.single 3 7 ⟨0, 0, -1, 0⟩
  | 1, 1 => Matrix.single 1 1 1 + Matrix.single 1 5 ⟨0, 0, 0, -1⟩ +
      Matrix.single 1 6 ⟨0, 0, -1, 0⟩ + Matrix.single 4 4 1 + Matrix.single 4 5 ⟨0, 0, 0, 1⟩ +
      Matrix.single 4 6 ⟨0, 0, 1, 0⟩ +
      Matrix.single 4 8 1

/-- The stacked letters of `1 ⊗ 1` on the four physical letters over `ℤ[σ]`. -/
def fibOneOneFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 4) (Fin 4) GoldenInt :=
  mulGoldenTensor fibOneFullGolden fibOneFullGolden a.divNat a.modNat

/-- The conjugated letters of `1 ⊗ 1` on the four physical letters. -/
def fibOneOneFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 4) (Fin 4) GoldenInt :=
  fibConjFull fibOneOneConjGolden fibOneOneEdgeOneConjGolden a.divNat a.modNat

/-- The stacked letters of `1 ⊗ 1` at edge label `1`: diagonal matrix units. -/
def fibOneOneEdgeOneStackGolden : Fin 2 → Fin 2 → Matrix (Fin 4) (Fin 4) GoldenInt
  | 0, 0 => Matrix.single 0 0 1
  | 1, 1 => Matrix.single 3 3 1
  | _, _ => 0

/-- The stacked letters of `1 ⊗ 1` on the four physical letters are the recorded letters
`fibOneOneStackGolden` at edge label `τ` and the diagonal matrix units
`fibOneOneEdgeOneStackGolden` at edge label `1`. -/
theorem fibOneOneFullStack_eq (a : Fin (4 * 4)) :
    fibOneOneFullStackGolden a =
      fibConjFull fibOneOneStackGolden fibOneOneEdgeOneStackGolden a.divNat a.modNat := by
  revert a
  decide +kernel

theorem fibOneOneFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibOneOneFullStackGolden a * fibOneOneGaugeInvGolden =
      fibOneOneGaugeInvGolden * fibOneOneFullConjGolden a := by
  rw [fibOneOneFullStack_eq]
  exact fibConjFull_mul_eq fibOneOneStack_mul_gaugeInv (by decide +kernel) _ _

private theorem fibOneOneFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 2) oneSlot 2) (h : unitOrd 2 y.1 < unitOrd 2 x.1) :
    fibOneOneFullConjGolden a (unitCoord 2 2 x) (unitCoord 2 2 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibOneOneFull_matched (a : Fin (4 * 4)) (p q : Fin 2) :
    fibOneOneFullConjGolden a (unitCoord 2 2 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 2 2 ⟨Sum.inl oneSlotMem, q⟩) = fibOneFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibOneOneFull_unmatched (a : Fin (4 * 4)) (t : Fin 2) (p q : Fin 1) :
    fibOneOneFullConjGolden a (unitCoord 2 2 ⟨Sum.inr t, p⟩)
      (unitCoord 2 2 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `1 ⊗ 1` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibOneOneFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibOneFull fibOneFull).toMPSTensor oneSlot
      (fun _ : Unit => fibOneFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 2 (unitOrd 2) (unitCoord 2 2) fibOneOneFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibOneFullGolden fibOneFullGolden _ _)
    (fun _ a => fibOneFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibOneOneGaugeGolden fibOneOneGaugeInvGolden fibOneOneGauge_mul_inv fibOneOneGaugeInv_mul
    fibOneOneFullConjGolden fibOneOneFullStack_mul_gaugeInv fibOneOneFull_triangular
    (fun a s _ p q => by cases s; exact fibOneOneFull_matched a p q) fibOneOneFull_unmatched

/-- The stacked letters of `1 ⊗ τ` on the four physical letters over `ℤ[σ]`. -/
def fibOneTauFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  mulGoldenTensor fibOneFullGolden fibTauFullGolden a.divNat a.modNat

/-- The conjugated letters of `1 ⊗ τ` on the four physical letters. -/
def fibOneTauFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  fibConjFull fibOneTauConjGolden fibOneTauEdgeOneConjGolden a.divNat a.modNat

/-- The stacked letters of `1 ⊗ τ` at edge label `1`: diagonal matrix units. -/
def fibOneTauEdgeOneStackGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 0 0 1
  | 1, 0 => Matrix.single 4 4 1
  | 1, 1 => Matrix.single 5 5 1
  | _, _ => 0

/-- The stacked letters of `1 ⊗ τ` on the four physical letters are the recorded letters
`fibOneTauStackGolden` at edge label `τ` and the diagonal matrix units
`fibOneTauEdgeOneStackGolden` at edge label `1`. -/
theorem fibOneTauFullStack_eq (a : Fin (4 * 4)) :
    fibOneTauFullStackGolden a =
      fibConjFull fibOneTauStackGolden fibOneTauEdgeOneStackGolden a.divNat a.modNat := by
  revert a
  decide +kernel

theorem fibOneTauFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibOneTauFullStackGolden a * fibOneTauGaugeInvGolden =
      fibOneTauGaugeInvGolden * fibOneTauFullConjGolden a := by
  rw [fibOneTauFullStack_eq]
  exact fibConjFull_mul_eq fibOneTauStack_mul_gaugeInv (by decide +kernel) _ _

private theorem fibOneTauFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 3) oneSlot 3) (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibOneTauFullConjGolden a (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibOneTauFull_matched (a : Fin (4 * 4)) (p q : Fin 3) :
    fibOneTauFullConjGolden a (unitCoord 3 3 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 3 3 ⟨Sum.inl oneSlotMem, q⟩) = fibTauFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibOneTauFull_unmatched (a : Fin (4 * 4)) (t : Fin 3) (p q : Fin 1) :
    fibOneTauFullConjGolden a (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `1 ⊗ τ` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibOneTauFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibOneFull fibTauFull).toMPSTensor oneSlot
      (fun _ : Unit => fibTauFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibOneTauFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibOneFullGolden fibTauFullGolden _ _)
    (fun _ a => fibTauFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibOneTauGaugeGolden fibOneTauGaugeInvGolden fibOneTauGauge_mul_inv fibOneTauGaugeInv_mul
    fibOneTauFullConjGolden fibOneTauFullStack_mul_gaugeInv fibOneTauFull_triangular
    (fun a s _ p q => by cases s; exact fibOneTauFull_matched a p q) fibOneTauFull_unmatched

/-- The stacked letters of `τ ⊗ 1` on the four physical letters over `ℤ[σ]`. -/
def fibTauOneFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  mulGoldenTensor fibTauFullGolden fibOneFullGolden a.divNat a.modNat

/-- The conjugated letters of `τ ⊗ 1` on the four physical letters. -/
def fibTauOneFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 6) (Fin 6) GoldenInt :=
  fibConjFull fibTauOneConjGolden fibTauOneEdgeOneConjGolden a.divNat a.modNat

/-- The stacked letters of `τ ⊗ 1` at edge label `1`: diagonal matrix units. -/
def fibTauOneEdgeOneStackGolden : Fin 2 → Fin 2 → Matrix (Fin 6) (Fin 6) GoldenInt
  | 0, 1 => Matrix.single 1 1 1
  | 1, 0 => Matrix.single 2 2 1
  | 1, 1 => Matrix.single 5 5 1
  | _, _ => 0

/-- The stacked letters of `τ ⊗ 1` on the four physical letters are the recorded letters
`fibTauOneStackGolden` at edge label `τ` and the diagonal matrix units
`fibTauOneEdgeOneStackGolden` at edge label `1`. -/
theorem fibTauOneFullStack_eq (a : Fin (4 * 4)) :
    fibTauOneFullStackGolden a =
      fibConjFull fibTauOneStackGolden fibTauOneEdgeOneStackGolden a.divNat a.modNat := by
  revert a
  decide +kernel

theorem fibTauOneFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibTauOneFullStackGolden a * fibTauOneGaugeInvGolden =
      fibTauOneGaugeInvGolden * fibTauOneFullConjGolden a := by
  rw [fibTauOneFullStack_eq]
  exact fibConjFull_mul_eq fibTauOneStack_mul_gaugeInv (by decide +kernel) _ _

private theorem fibTauOneFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace (fun _ : Unit => 3) oneSlot 3) (h : unitOrd 3 y.1 < unitOrd 3 x.1) :
    fibTauOneFullConjGolden a (unitCoord 3 3 x) (unitCoord 3 3 y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibTauOneFull_matched (a : Fin (4 * 4)) (p q : Fin 3) :
    fibTauOneFullConjGolden a (unitCoord 3 3 ⟨Sum.inl oneSlotMem, p⟩)
      (unitCoord 3 3 ⟨Sum.inl oneSlotMem, q⟩) = fibTauFullGolden a.divNat a.modNat p q := by
  revert a
  revert p q
  decide +kernel

private theorem fibTauOneFull_unmatched (a : Fin (4 * 4)) (t : Fin 3) (p q : Fin 1) :
    fibTauOneFullConjGolden a (unitCoord 3 3 ⟨Sum.inr t, p⟩)
      (unitCoord 3 3 ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `τ ⊗ 1` on the four physical letters: the gauge of the compression
on edge label `τ`, with a nonzero nilpotent remainder at edge label `1`. -/
def fibTauOneFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibTauFull fibOneFull).toMPSTensor oneSlot
      (fun _ : Unit => fibTauFull.toMPSTensor) :=
  MultiBlockCompression.ofGolden 3 (unitOrd 3) (unitCoord 3 3) fibTauOneFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibTauFullGolden fibOneFullGolden _ _)
    (fun _ a => fibTauFullGolden a.divNat a.modNat) (fun _ _ => rfl)
    fibTauOneGaugeGolden fibTauOneGaugeInvGolden fibTauOneGauge_mul_inv fibTauOneGaugeInv_mul
    fibTauOneFullConjGolden fibTauOneFullStack_mul_gaugeInv fibTauOneFull_triangular
    (fun a s _ p q => by cases s; exact fibTauOneFull_matched a p q) fibTauOneFull_unmatched

end FibonacciCompression

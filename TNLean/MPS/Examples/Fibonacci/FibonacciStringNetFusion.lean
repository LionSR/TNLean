/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Fibonacci.FibonacciStringNetUnit

/-!
# Fibonacci string-net: fusion rules on both edge labels

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman and Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` line 1268: the blocks
`B_1`, `B_τ` of the string-net operator tensor `G^{abc}_{def} √(v_a v_b v_c v_d)`
(lines 1257–1267) satisfy the Fibonacci fusion rules.

**Formalized here.** The compression datum of `τ ⊗ τ` of the extended F-symbol blocks on the
sixteen letters, with the gauge of `Fibonacci.lean` and a nonzero nilpotent remainder at edge
label `1`; the Fibonacci fusion rules of the extended blocks; and, through the diagonal bond
similarity `mpo_fibStringNetTensor`, the source's fusion rules for its tensor on the full alphabet
of four physical letters (plaquette, edge label) per site, stated as an instance of
`MPOTensor.IsMPOFusionAlgebra` with the table `fibNim`.

## Main definitions

* `FibonacciCompression.fibTauTauFull_compression`: the compression datum of `τ ⊗ τ`.

## Main results

* `FibonacciCompression.isMPOFusionAlgebra_fibBlockFull`: the extended blocks satisfy the
  Fibonacci fusion rules.
* `FibonacciCompression.isMPOFusionAlgebra_fibStringNetTensor`: the source's blocks satisfy the
  Fibonacci fusion rules on both edge labels.

## References

- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

noncomputable section

open scoped Matrix

namespace FibonacciCompression

open GoldenInt MPSTensor MPOTensor

/-- The golden letters of the extended blocks, indexed by the label. -/
def fibBlockFullGolden : (s : Fin 2) → Fin 4 → Fin 4 →
    Matrix (Fin (fibBlockDim s)) (Fin (fibBlockDim s)) GoldenInt
  | 0 => fibOneFullGolden
  | 1 => fibTauFullGolden

theorem fibBlockFull_toMPSTensor_eq (s : Fin 2) (a : Fin (4 * 4)) :
    (fibBlockFull s).toMPSTensor a = complexOfGolden (fibBlockFullGolden s a.divNat a.modNat) := by
  fin_cases s <;> rfl

/-- The stacked letters of `τ ⊗ τ` on the four physical letters over `ℤ[σ]`. -/
def fibTauTauFullStackGolden (a : Fin (4 * 4)) : Matrix (Fin 9) (Fin 9) GoldenInt :=
  mulGoldenTensor fibTauFullGolden fibTauFullGolden a.divNat a.modNat

/-- The conjugated letters of `τ ⊗ τ` on the four physical letters. -/
def fibTauTauFullConjGolden (a : Fin (4 * 4)) : Matrix (Fin 9) (Fin 9) GoldenInt :=
  fibConjFull fibConjGolden fibTauTauEdgeOneConjGolden a.divNat a.modNat

/-- The stacked letters of `τ ⊗ τ` at edge label `1`: diagonal matrix units. -/
def fibTauTauEdgeOneStackGolden : Fin 2 → Fin 2 → Matrix (Fin 9) (Fin 9) GoldenInt
  | 0, 0 => Matrix.single 1 1 1
  | 0, 1 => Matrix.single 2 2 1
  | 1, 0 => Matrix.single 7 7 1
  | 1, 1 => Matrix.single 3 3 1 + Matrix.single 8 8 1

/-- The stacked letters of `τ ⊗ τ` on the four physical letters are the recorded letters
`fibStackGolden` at edge label `τ` and the diagonal matrix units
`fibTauTauEdgeOneStackGolden` at edge label `1`. -/
theorem fibTauTauFullStack_eq (a : Fin (4 * 4)) :
    fibTauTauFullStackGolden a =
      fibConjFull fibStackGolden fibTauTauEdgeOneStackGolden a.divNat a.modNat := by
  revert a
  decide +kernel

theorem fibTauTauFullStack_mul_gaugeInv (a : Fin (4 * 4)) :
    fibTauTauFullStackGolden a * fibGaugeInvGolden =
      fibGaugeInvGolden * fibTauTauFullConjGolden a := by
  rw [fibTauTauFullStack_eq]
  exact fibConjFull_mul_eq fibStack_mul_gaugeInv (by decide +kernel) _ _

private theorem fibTauTauFull_triangular (a : Fin (4 * 4))
    (x y : BlockSpace fibBlockDim fibSlots 4) (h : fibOrd y.1 < fibOrd x.1) :
    fibTauTauFullConjGolden a (fibCoord x) (fibCoord y) = 0 := by
  revert a x y
  decide +kernel

private theorem fibTauTauFull_matched (a : Fin (4 * 4)) (s : Fin 2)
    (p q : Fin (fibBlockDim s)) :
    fibTauTauFullConjGolden a (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (fibCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩) =
      fibBlockFullGolden s a.divNat a.modNat p q := by
  revert a
  fin_cases s <;> revert p q <;> decide +kernel

private theorem fibTauTauFull_unmatched (a : Fin (4 * 4)) (t : Fin 4) (p q : Fin 1) :
    fibTauTauFullConjGolden a (fibCoord ⟨Sum.inr t, p⟩) (fibCoord ⟨Sum.inr t, q⟩) = 0 := by
  revert a t p q
  decide +kernel

/-- The compression datum of `τ ⊗ τ` on the four physical letters, onto both extended blocks. -/
def fibTauTauFull_compression :
    MultiBlockCompression (MPOTensor.mulTensor fibTauFull fibTauFull).toMPSTensor fibSlots
      (fun s => (fibBlockFull s).toMPSTensor) :=
  MultiBlockCompression.ofGolden 4 fibOrd fibCoord fibTauTauFullStackGolden
    (fun _ => mulTensor_complexOfGolden fibTauFullGolden fibTauFullGolden _ _)
    (fun s a => fibBlockFullGolden s a.divNat a.modNat) fibBlockFull_toMPSTensor_eq
    fibGaugeGolden fibGaugeInvGolden fibGauge_mul_inv fibGaugeInv_mul fibTauTauFullConjGolden
    fibTauTauFullStack_mul_gaugeInv fibTauTauFull_triangular
    (fun a s _ p q => fibTauTauFull_matched a s p q) fibTauTauFull_unmatched

/-- **The Fibonacci fusion rules of the extended blocks.** On the four physical letters
(plaquette, edge label), the periodic operators of the extended F-symbol blocks satisfy
`O_1 O_1 = O_1`, `O_1 O_τ = O_τ O_1 = O_τ` and `O_τ O_τ = O_1 + O_τ` at every positive length. -/
theorem isMPOFusionAlgebra_fibBlockFull : IsMPOFusionAlgebra fibBlockFull fibNim := by
  intro a b L hL
  match a, b with
  | 0, 0 =>
    simp only [fibBlockFull, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, add_zero]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibOneFull)
      fibOneOneFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 0, 1 =>
    simp only [fibBlockFull, fibNim, Fin.sum_univ_two, Matrix.one_apply, Fin.isValue,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ↓reduceIte, Nat.cast_one, Nat.cast_zero, one_smul,
      zero_smul, zero_add]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTauFull)
      fibOneTauFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 1, 0 =>
    simp only [fibBlockFull, fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, Nat.cast_zero, one_smul, zero_smul, zero_add]
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fun _ : Unit => fibTauFull)
      fibTauOneFull_compression L hL
    rwa [Finset.sum_singleton] at h
  | 1, 1 =>
    have h := mpo_mul_eq_sum_of_multiBlockCompression (C := fibBlockFull)
      fibTauTauFull_compression L hL
    rw [show fibSlots = Finset.univ from rfl, Fin.sum_univ_two] at h
    simp only [fibNim, fibFusionMatrix, Fin.sum_univ_two, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Nat.cast_one, one_smul]
    exact h

/-- Source: arXiv:1511.08090, `AnyonsPEPS.tex` line 1268: the blocks `B_1`, `B_τ` of the
string-net operator tensor `G^{abc}_{def} √(v_a v_b v_c v_d)` satisfy the Fibonacci fusion rules,
on the full alphabet of four physical letters (plaquette, edge label) per site. This is
`isMPOFusionAlgebra_fibBlockFull` transported along `mpo_fibStringNetTensor`. -/
theorem isMPOFusionAlgebra_fibStringNetTensor :
    IsMPOFusionAlgebra fibStringNetTensor fibNim :=
  isMPOFusionAlgebra_fibBlockFull.of_mpo_eq_mul_mul (fun _ => 1) (fun _ => 1)
    (fun _ _ => Matrix.one_mul 1) fun a L _ => by
      rw [mpo_fibStringNetTensor, Matrix.one_mul, Matrix.mul_one]

end FibonacciCompression

/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.ExplicitGauge
import TNLean.MPS.Examples.KramersWannier.KramersWannier
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace
import TNLean.MPS.MPDO.ActionTensor
import TNLean.MPS.Examples.KramersWannier.KramersWannierSource

/-!
# Kramers–Wannier duality on product and GHZ states

For `L > 0`, the unnormalised periodic Ising kernel
`⟨s'|D~|s⟩ = ∏_j (-1)^{s'_j (s_j + s_{j+1})}` acts on the unnormalised states
`P_L = (|0⟩ + |1⟩)^{⊗ L}` and `G_L = |0…0⟩ + |1…1⟩` by
`D~ P_L = 2^L G_L` and `D~ G_L = 2 P_L`.
The word-trace identities below establish these coefficient formulas. Since
`P_L = 2^{L/2} |+⟩^{⊗ L}` for normalized `|+⟩`, converting the latter formula to
normalized product-state notation introduces a norm factor, not a new tensor weight.

These are the product-state and symmetry-broken GHZ examples of Ising duality.
Aasen–Mong–Fendley, arXiv:1601.07185, discuss the ordered/disordered interpretation;
their defect kernel has an additional factor `2^{-L/2}`. The explicit action tensors
and gauges here are recorded in `Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §2.
`kwTensor` is imported from `KramersWannier` with the raw normalization above.

For the action on `P_L`, the two GHZ targets each carry weight `2`, the remainder
vanishes, and both compression pairs are sitewise intertwiners. For the action on `G_L`,
the target is two unweighted copies of the product-state tensor. A nonzero right
intertwiner exists, but every left intertwiner vanishes, ruling out a biorthogonal
sitewise pair. The word-level compression still holds.

## Main definitions

* `KWExample.plusTensor`, `KWExample.ghz0`, `KWExample.ghz1`: the product-state tensor and the
  two Greenberger–Horne–Zeilinger sectors.
* `KWExample.kwPlus`, `KWExample.kwGHZ`: the two action tensors.
* `KWExample.plusCompression`, `KWExample.kwGHZCompression`: the multi-block compression data.

## Main results

* `KWExample.kwPlus_trace_evalWord_eq_sum`, `KWExample.kwGHZ_trace_evalWord_eq_two`: the
  word-trace identities.
* `KWExample.plus_remainder_eq_zero`: the split occurrence of part (a).
* `KWExample.kwGHZ_left_intertwiner_eq_zero`, `KWExample.kwGHZ_right_intertwiner`: the
  obstruction to a biorthogonal sitewise pair in part (b), and the one-sided witness that
  survives.
* `KWExample.mpv_plusTensor_eq_plusState`, `KWExample.mpv_ghz_eq_ghzState`: the periodic
  states of `plusTensor` and `ghz` are the states `plusState` and `ghzState` on which
  `KWExample.kwTensor_mpo_mulVec_plus` and `KWExample.kwTensor_mpo_mulVec_ghz` compute the
  action of the kernel directly.

## References

* `Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §2.
* Aasen–Mong–Fendley, arXiv:1601.07185 (topological defects on the lattice; the Kramers–Wannier
  duality defect of the Ising chain).
* Seiberg–Shao, arXiv:2307.02534 (Majorana chains and non-invertible symmetries).
-/

noncomputable section

open scoped Matrix Kronecker BigOperators
open Matrix

namespace KWExample

open MPSTensor

/-! ### The Kramers–Wannier duality kernel -/

/-! The Kramers–Wannier tensor `kwTensor` is defined in `Examples/KramersWannier.lean`. -/

/-! ### Part (a): the duality on the product state -/

/-- The integer matrices of the bond-one product-state tensor `A^{s'} = 1`. -/
def plusIntTensor : Fin 2 → Matrix (Fin 1) (Fin 1) ℤ := fun _ => 1

/-- The product-state tensor generating the unnormalised paramagnetic state `∑_s |s⟩` (data
file §2.1). -/
def plusTensor : MPSTensor 2 1 := fun _ => 1

theorem plusTensor_eq : plusTensor = fun j => complexOfInt (plusIntTensor j) := by
  funext j
  simp [plusTensor, plusIntTensor, complexOfInt_one]

/-- The action tensor `Ãtilde = D~ · P_L` of part (a) (data file §2.1). -/
def kwPlus : MPSTensor 2 2 := MPOTensor.actTensor kwTensor plusTensor

/-- The integer matrices of `kwPlus`, `Ãtilde^0 = 2 P_+`, `Ãtilde^1 = 2 P_-` (data file §2.1). -/
def kwPlusInt : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1, 1; 1, 1]
  | 1 => !![1, -1; -1, 1]

theorem kwPlus_eq (i : Fin 2) : kwPlus i = complexOfInt (kwPlusInt i) := by
  have hi : actTensorR kwIntTensor plusIntTensor i = kwPlusInt i := by revert i; decide
  change MPOTensor.actTensor kwTensor plusTensor i = _
  unfold kwTensor
  rw [plusTensor_eq, actTensor_complexOfRing _ kwIntTensor plusIntTensor i, hi]

/-- The all-zero Greenberger–Horne–Zeilinger sector, `A_0^{s'} = δ_{s',0}` (data file §2.1). -/
def ghz0 : MPSTensor 2 1 := ![!![1], !![0]]

/-- The all-one Greenberger–Horne–Zeilinger sector, `A_1^{s'} = δ_{s',1}` (data file §2.1). -/
def ghz1 : MPSTensor 2 1 := ![!![0], !![1]]

/-- The target slots of part (a): both Greenberger–Horne–Zeilinger sectors. -/
abbrev PlusS : Finset (Fin 2) := Finset.univ

/-- The bond dimension of each target slot: both sectors are one-dimensional. -/
abbrev PlusD : Fin 2 → ℕ := fun _ => 1

/-- The weighted targets of part (a): each Greenberger–Horne–Zeilinger sector with weight `2`
(data file §2.1). -/
def plusTarget : (s : Fin 2) → MPSTensor 2 (PlusD s) := ![(2 : ℂ) • ghz0, (2 : ℂ) • ghz1]

/-- The identity block ordering of part (a): the all-zero sector at position `0`, the all-one
sector at position `1`. -/
def plusOrd : BlockIndex PlusS 0 ≃ Fin 2 where
  toFun
    | Sum.inl ⟨s, _⟩ => s
    | Sum.inr t => t.elim0
  invFun n := Sum.inl ⟨n, Finset.mem_univ n⟩
  left_inv := by decide
  right_inv := by decide

/-- The coordinate change of part (a) on the graded block space, agreeing with `plusOrd`. -/
def plusTau : BlockSpace PlusD PlusS 0 ≃ Fin 2 where
  toFun x := plusOrd x.1
  invFun n := ⟨Sum.inl ⟨n, Finset.mem_univ n⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The integral matrix `[[1,1],[1,-1]]` underlying the gauge of part (a) (data file §2.1,
`G^{-1}`); it squares to `2 • 1`. -/
def plusGaugeInt : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]

/-- The gauge matrix of part (a), `G`. -/
def plusG : Matrix (Fin 2) (Fin 2) ℂ := complexOfInt plusGaugeInt

/-- The inverse gauge matrix of part (a), `G^{-1} = (1/2) G` (data file §2.1). -/
def plusGinv : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • complexOfInt plusGaugeInt

theorem plusGaugeInt_sq : plusGaugeInt * plusGaugeInt = !![2, 0; 0, 2] := by decide

theorem plusG_mul_plusGinv : plusG * plusGinv = 1 := by
  rw [plusG, plusGinv, Matrix.mul_smul, ← complexOfInt_mul, plusGaugeInt_sq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [complexOfInt]

theorem plusGinv_mul_plusG : plusGinv * plusG = 1 := by
  rw [plusG, plusGinv, Matrix.smul_mul, ← complexOfInt_mul, plusGaugeInt_sq]
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [complexOfInt]

/-- The gauge of part (a). -/
def plusGauge : (Fin 2 → ℂ) ≃ₗ[ℂ] (BlockSpace PlusD PlusS 0 → ℂ) :=
  gaugeOfMatrix plusTau plusG plusGinv plusG_mul_plusGinv plusGinv_mul_plusG

/-- The doubled conjugated matrices of part (a) before halving,
`plusGaugeInt * kwPlusInt i * plusGaugeInt`. -/
def plusDoubledConjInt : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![4, 0; 0, 0]
  | 1 => !![0, 0; 0, 4]

theorem plusGaugeInt_mul_kwPlusInt_mul (i : Fin 2) :
    plusGaugeInt * kwPlusInt i * plusGaugeInt = plusDoubledConjInt i := by
  revert i
  decide

/-- The conjugated matrices of part (a): `G Ãtilde^{s'} G^{-1} = diag(2 δ_{s'0}, 2 δ_{s'1})`
(data file §2.1). -/
def plusConjInt : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![2, 0; 0, 0]
  | 1 => !![0, 0; 0, 2]

theorem plusConj_eq (i : Fin 2) : plusG * kwPlus i * plusGinv = complexOfInt (plusConjInt i) := by
  rw [kwPlus_eq, plusG, plusGinv, Matrix.mul_smul, ← complexOfInt_mul, ← complexOfInt_mul,
    plusGaugeInt_mul_kwPlusInt_mul]
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    norm_num [plusDoubledConjInt, plusConjInt, complexOfInt]

theorem plusConjMatrix (i : Fin 2) :
    conjMatrix plusGauge (kwPlus i) = (complexOfInt (plusConjInt i)).submatrix plusTau plusTau := by
  rw [plusGauge, conjMatrix_gaugeOfMatrix, plusConj_eq]

/-- **The multi-block asymmetric compression datum of part (a).** -/
def plusCompression : MultiBlockCompression kwPlus PlusS plusTarget where
  z := 0
  ord := plusOrd
  gauge := plusGauge
  triangular i x y hxy := by
    rw [plusConjMatrix, Matrix.submatrix_apply]
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      first
        | exact absurd hxy (by decide)
        | simp [plusTau, plusOrd, plusConjInt, complexOfInt]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, plusConjMatrix, Matrix.submatrix_apply]
    fin_cases p; fin_cases q
    obtain ⟨s, hs⟩ := s
    fin_cases i <;> fin_cases s <;>
      simp [plusTau, plusOrd, plusConjInt, plusTarget, ghz0, ghz1, complexOfInt]
  unmatched _ t := t.elim0

/-- **The word-trace identity of part (a)** (data file §2.1). -/
theorem kwPlus_trace_evalWord_eq_sum (w : List (Fin 2)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord kwPlus w) =
      Matrix.trace (Kraus.evalWord ((2 : ℂ) • ghz0) w) +
        Matrix.trace (Kraus.evalWord ((2 : ℂ) • ghz1) w) := by
  have h := plusCompression.trace_evalWord_eq_sum w hw
  simpa [plusTarget, Fin.sum_univ_two] using h

/-- **Biorthogonal compression of each Greenberger–Horne–Zeilinger sector out of `kwPlus`.** -/
theorem plus_isReduction (s : {s // s ∈ PlusS}) :
    IsReduction kwPlus (plusTarget s.1) (plusCompression.left s) (plusCompression.right s) :=
  plusCompression.isReduction s

/-- **The dimension count of part (a)**: `2 = 1 + 1 + 0`. -/
theorem plus_dim_eq : (2 : ℕ) = ∑ s ∈ PlusS, PlusD s + 0 :=
  plusCompression.dim_eq

/-- Off the diagonal, the conjugated matrix of part (a) vanishes entrywise: `plusConjInt` is a
diagonal `2 × 2` matrix. -/
private theorem plusConjInt_offDiag (i a b : Fin 2) (h : a ≠ b) : plusConjInt i a b = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp_all [plusConjInt]

/-- **The residual of part (a) vanishes**: the extension splits (data file §2.1). -/
theorem plus_remainder_eq_zero (i : Fin 2) : plusCompression.remainder i = 0 := by
  refine conjMatrix_injective plusCompression.gauge ?_
  rw [conjMatrix_zero, MultiBlockCompression.conjMatrix_remainder]
  change conjMatrix plusGauge (kwPlus i) -
      Matrix.blockDiagonal' (conjMatrix plusGauge (kwPlus i)).blockDiag' = 0
  ext x y
  simp only [Matrix.sub_apply, Matrix.zero_apply]
  by_cases hxy : plusTau x = plusTau y
  · obtain rfl : x = y := plusTau.injective hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply, sub_self]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun h => hxy (congrArg plusOrd h)), sub_zero]
    rw [plusConjMatrix, Matrix.submatrix_apply, complexOfInt_apply,
      plusConjInt_offDiag i (plusTau x) (plusTau y) hxy]
    norm_num

/-- The explicit compression witnesses of part (a) for the all-zero sector, in the closed form
of `MultiBlockCompression.left_gaugeOfMatrix`/`right_gaugeOfMatrix`. -/
def plusLeft0 : Matrix (Fin 1) (Fin 2) ℂ := !![1, 1]

def plusRight0 : Matrix (Fin 2) (Fin 1) ℂ := (1 / 2 : ℂ) • !![1; 1]

/-- The explicit compression witnesses of part (a) for the all-one sector. -/
def plusLeft1 : Matrix (Fin 1) (Fin 2) ℂ := !![1, -1]

def plusRight1 : Matrix (Fin 2) (Fin 1) ℂ := (1 / 2 : ℂ) • !![1; -1]

/-- **The four sitewise intertwiners of part (a)** (data file §2.1: "sitewise intertwiners
exist in both directions for both sectors"). -/
theorem plusRight0_isIntertwiner (i : Fin 2) :
    kwPlus i * plusRight0 = plusRight0 * plusTarget 0 i := by
  rw [kwPlus_eq]
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    simp [plusRight0, plusTarget, ghz0, kwPlusInt, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

theorem plusLeft0_isIntertwiner (i : Fin 2) :
    plusLeft0 * kwPlus i = plusTarget 0 i * plusLeft0 := by
  rw [kwPlus_eq]
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    simp [plusLeft0, plusTarget, ghz0, kwPlusInt, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

theorem plusRight1_isIntertwiner (i : Fin 2) :
    kwPlus i * plusRight1 = plusRight1 * plusTarget 1 i := by
  rw [kwPlus_eq]
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    simp [plusRight1, plusTarget, ghz1, kwPlusInt, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

theorem plusLeft1_isIntertwiner (i : Fin 2) :
    plusLeft1 * kwPlus i = plusTarget 1 i * plusLeft1 := by
  rw [kwPlus_eq]
  ext p q
  fin_cases i <;> fin_cases p <;> fin_cases q <;>
    simp [plusLeft1, plusTarget, ghz1, kwPlusInt, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num

/-! ### Part (b): the duality on the Greenberger–Horne–Zeilinger state -/

/-- The integer matrices of the Greenberger–Horne–Zeilinger tensor, `A^0 = diag(1,0)`,
`A^1 = diag(0,1)` (data file §2.2). -/
def ghzIntTensor : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 0; 0, 1]

/-- The Greenberger–Horne–Zeilinger tensor, generating `|0…0⟩ + |1…1⟩`. -/
def ghz : MPSTensor 2 2 := ![!![1, 0; 0, 0], !![0, 0; 0, 1]]

theorem ghz_eq (i : Fin 2) : ghz i = complexOfInt (ghzIntTensor i) := by
  fin_cases i <;> ext p q <;> fin_cases p <;> fin_cases q <;>
    norm_num [ghz, ghzIntTensor, complexOfInt]

/-- The action tensor `B~ = D~ · (|0…0⟩ + |1…1⟩)` of part (b) (data file §2.2). -/
def kwGHZ : MPSTensor 2 4 := MPOTensor.actTensor kwTensor ghz

/-- The integer matrices of `kwGHZ` (data file §2.2). -/
def kwGHZInt : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![1, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 1]
  | 1 => !![1, 0, -1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, -1, 0, 1]

theorem kwGHZ_eq (i : Fin 2) : kwGHZ i = complexOfInt (kwGHZInt i) := by
  have hi : actTensorR kwIntTensor ghzIntTensor i = kwGHZInt i := by revert i; decide
  change MPOTensor.actTensor kwTensor ghz i = _
  unfold kwTensor
  rw [show ghz = fun j => complexOfInt (ghzIntTensor j) from funext ghz_eq,
    actTensor_complexOfRing _ kwIntTensor ghzIntTensor i, hi]

/-- The target slots of part (b): two copies of the same paramagnetic product-state target
(data file §2.2, "multiplicity two"). -/
abbrev KWGHZS : Finset (Fin 2) := Finset.univ

/-- The bond dimension of each copy: the product-state tensor is one-dimensional. -/
abbrev KWGHZD : Fin 2 → ℕ := fun _ => 1

/-- The repeated target of part (b): two unweighted copies of `plusTensor` (data file §2.2). -/
def kwGHZTarget : (s : Fin 2) → MPSTensor 2 (KWGHZD s) := fun _ => plusTensor

/-- The block ordering of part (b): the first product-state copy (coordinate `e₀`) at position
`0`, the second copy (coordinate `e₃`) at position `1`, and the two zero slots (coordinates `e₁`,
`e₂`) at positions `2`, `3` (data file §2.2, the reordering `(e₀, e₃, e₁, e₂)`). -/
def kwGHZOrd : BlockIndex KWGHZS 2 ≃ Fin 4 where
  toFun
    | Sum.inl ⟨s, _⟩ => if s = 0 then 0 else 1
    | Sum.inr t => if t = 0 then 2 else 3
  invFun
    | 0 => Sum.inl ⟨0, Finset.mem_univ 0⟩
    | 1 => Sum.inl ⟨1, Finset.mem_univ 1⟩
    | 2 => Sum.inr 0
    | 3 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

/-- The coordinate change of part (b) on the graded block space: the copy at rank `0` sits at
the original coordinate `e₀`, the copy at rank `1` at `e₃`, the zero slot at rank `2` at `e₁`,
and the zero slot at rank `3` at `e₂` (data file §2.2, the reordering `(e₀, e₃, e₁, e₂)`). This
is a *different* permutation of `Fin 4` from `kwGHZOrd`'s ranks: the rank order places both
targets before both zero slots, while the coordinate order interleaves them. -/
def kwGHZTau : BlockSpace KWGHZD KWGHZS 2 ≃ Fin 4 where
  toFun
    | ⟨Sum.inl ⟨s, _⟩, _⟩ => if s = 0 then 0 else 3
    | ⟨Sum.inr t, _⟩ => if t = 0 then 1 else 2
  invFun
    | 0 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, 0⟩
    | 1 => ⟨Sum.inr 0, 0⟩
    | 2 => ⟨Sum.inr 1, 0⟩
    | 3 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The identity reindexing of the bond space of `kwGHZ` into the block coordinates given by
`kwGHZTau`: the gauge of part (b) is a pure coordinate permutation, with no fractional entries
(data file §2.2). -/
noncomputable def kwGHZGauge : (Fin 4 → ℂ) ≃ₗ[ℂ] (BlockSpace KWGHZD KWGHZS 2 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ kwGHZTau

theorem conjMatrix_kwGHZGauge (A : Matrix (Fin 4) (Fin 4) ℂ) :
    conjMatrix kwGHZGauge A = A.submatrix kwGHZTau kwGHZTau := by
  rw [kwGHZGauge, conjMatrix_apply, toMatrix'_conj_funCongrLeft, LinearMap.toMatrix'_toLin']

private theorem kwGHZ_triangular_int (i : Fin 2) (x y : BlockSpace KWGHZD KWGHZS 2)
    (h : kwGHZOrd y.1 < kwGHZOrd x.1) :
    kwGHZInt i (kwGHZTau x) (kwGHZTau y) = 0 := by
  revert i x y
  decide

private theorem kwGHZ_matched_int (i : Fin 2) (s : {s // s ∈ KWGHZS}) (p q : Fin 1) :
    kwGHZInt i (kwGHZTau ⟨Sum.inl s, p⟩) (kwGHZTau ⟨Sum.inl s, q⟩) = plusIntTensor i p q := by
  obtain rfl : p = 0 := Subsingleton.elim p 0
  obtain rfl : q = 0 := Subsingleton.elim q 0
  obtain ⟨s, hs⟩ := s
  revert i s
  decide

private theorem kwGHZ_unmatched_int (i : Fin 2) (t : Fin 2) (p q : Fin 1) :
    kwGHZInt i (kwGHZTau ⟨Sum.inr t, p⟩) (kwGHZTau ⟨Sum.inr t, q⟩) = 0 := by
  obtain rfl : p = 0 := Subsingleton.elim p 0
  obtain rfl : q = 0 := Subsingleton.elim q 0
  revert i t
  decide

/-- **The multi-block asymmetric compression datum of part (b).** -/
def kwGHZCompression : MultiBlockCompression kwGHZ KWGHZS kwGHZTarget where
  z := 2
  ord := kwGHZOrd
  gauge := kwGHZGauge
  triangular i x y h := by
    rw [conjMatrix_kwGHZGauge, Matrix.submatrix_apply, kwGHZ_eq, complexOfInt_apply,
      Int.cast_eq_zero]
    exact kwGHZ_triangular_int i x y h
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_kwGHZGauge, Matrix.submatrix_apply, kwGHZ_eq,
      complexOfInt_apply]
    simp only [kwGHZTarget, plusTensor_eq]
    rw [complexOfInt_apply, Int.cast_inj]
    exact kwGHZ_matched_int i s p q
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_kwGHZGauge, Matrix.submatrix_apply, kwGHZ_eq,
      complexOfInt_apply, Matrix.zero_apply, Int.cast_eq_zero]
    exact kwGHZ_unmatched_int i t p q

/-- Every word evaluation of the constant product-state tensor is the identity, since every
letter's matrix is `1`. -/
theorem plusTensor_evalWord (w : List (Fin 2)) : Kraus.evalWord plusTensor w = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [Kraus.evalWord, plusTensor, ih, Matrix.one_mul]

/-- **The word-trace identity of part (b)**: the generated coefficient family is constant
(data file §2.2). -/
theorem kwGHZ_trace_evalWord_eq_two (w : List (Fin 2)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord kwGHZ w) = 2 := by
  have h := kwGHZCompression.trace_evalWord_eq_sum w hw
  simp only [kwGHZTarget, Fin.sum_univ_two, plusTensor_evalWord, Matrix.trace_fin_one,
    Matrix.one_apply_eq] at h
  rw [h]
  norm_num

/-- **Biorthogonal compression of each copy out of `kwGHZ`.** -/
theorem kwGHZ_isReduction (s : {s // s ∈ KWGHZS}) :
    IsReduction kwGHZ (kwGHZTarget s.1) (kwGHZCompression.left s) (kwGHZCompression.right s) :=
  kwGHZCompression.isReduction s

/-- **The dimension count of part (b)**: `4 = 1 + 1 + 2`. -/
theorem kwGHZ_dim_eq : (4 : ℕ) = ∑ s ∈ KWGHZS, KWGHZD s + 2 :=
  kwGHZCompression.dim_eq

/-- **Nilpotency of the residual of part (b)** at the theorem's bound `r = |S| + z = 4`. -/
theorem kwGHZ_evalWord_remainder_eq_zero (w : List (Fin 2)) (hw : 4 ≤ w.length) :
    Kraus.evalWord kwGHZCompression.remainder w = 0 := by
  refine kwGHZCompression.evalWord_remainder_eq_zero w ?_
  change 2 + 2 ≤ w.length
  omega

/-- Every block of part (b) (both target slots and both zero slots) has size exactly one, so a
common block already forces equal block-space coordinates. -/
private theorem kwGHZ_eq_of_fst_eq {x y : BlockSpace KWGHZD KWGHZS 2} (hb : x.1 = y.1) :
    x = y := by
  obtain ⟨bx, ix⟩ := x
  obtain ⟨by_, iy⟩ := y
  simp only at hb
  subst hb
  have h1 : slotSize KWGHZD bx = 1 := by
    cases bx with
    | inl s => rfl
    | inr t => rfl
  have hix : ix.1 = 0 := by have h := ix.2; omega
  have hiy : iy.1 = 0 := by have h := iy.2; omega
  exact congrArg (Sigma.mk bx) (Fin.ext (hix.trans hiy.symm))

/-- In the block coordinates, the conjugated residual of part (b) agrees with the conjugated
source tensor off the diagonal, and vanishes on it. -/
private theorem kwGHZ_conjMatrix_remainder_apply (i : Fin 2) (x y : BlockSpace KWGHZD KWGHZS 2) :
    conjMatrix kwGHZGauge (kwGHZCompression.remainder i) x y =
      if x = y then 0 else conjMatrix kwGHZGauge (kwGHZ i) x y := by
  change conjMatrix kwGHZCompression.gauge (kwGHZCompression.remainder i) x y = _
  rw [MultiBlockCompression.conjMatrix_remainder]
  change (conjMatrix kwGHZGauge (kwGHZ i) -
      Matrix.blockDiagonal' (conjMatrix kwGHZGauge (kwGHZ i)).blockDiag') x y =
    if x = y then 0 else conjMatrix kwGHZGauge (kwGHZ i) x y
  simp only [Matrix.sub_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    simp
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ (fun h => hxy (kwGHZ_eq_of_fst_eq h)), sub_zero]
    simp [hxy]

/-- **The explicit residual of part (b)**, in the original (unpermuted) coordinates. -/
theorem kwGHZ_remainder_apply (i : Fin 2) (a b : Fin 4) :
    kwGHZCompression.remainder i a b = if a = b then 0 else (kwGHZInt i a b : ℂ) := by
  have h := kwGHZ_conjMatrix_remainder_apply i (kwGHZTau.symm a) (kwGHZTau.symm b)
  simpa only [conjMatrix_kwGHZGauge, Matrix.submatrix_apply, Equiv.apply_symm_apply, kwGHZ_eq,
    complexOfInt_apply, Equiv.apply_eq_iff_eq] using h

/-- The explicit residual matrices of part (b) (data file §2.2, `R^0`, `R^1`). -/
def kwGHZRemainderInt : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 1, 0, 0]
  | 1 => !![0, 0, -1, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, -1, 0, 0]

theorem kwGHZRemainder_eq (i : Fin 2) :
    kwGHZCompression.remainder i = complexOfInt (kwGHZRemainderInt i) := by
  ext a b
  rw [kwGHZ_remainder_apply, complexOfInt_apply]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [kwGHZRemainderInt, kwGHZInt]

/-- **The sharpened nilpotency of part (b)**: the residual squares to zero directly, not merely
at the theorem's generic bound (data file §2.2, `R^i R^j = 0`). -/
theorem kwGHZ_remainder_mul_remainder (i j : Fin 2) :
    kwGHZCompression.remainder i * kwGHZCompression.remainder j = 0 := by
  rw [kwGHZRemainder_eq, kwGHZRemainder_eq, ← complexOfInt_mul]
  have hzero : kwGHZRemainderInt i * kwGHZRemainderInt j = 0 := by revert i j; decide
  rw [hzero]
  ext p q
  simp [complexOfInt]

/-- **The non-split obstruction of part (b)**: no nonzero left sitewise intertwiner exists for
the paramagnetic target, so the word-level compression is the strongest local relation available
(data file §2.2). -/
theorem kwGHZ_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* kwGHZ i = plusTensor i 0 0 • u) : u = 0 := by
  have h0 := h 0
  have h1 := h 1
  rw [kwGHZ_eq] at h0 h1
  simp only [plusTensor, Matrix.one_apply_eq] at h0 h1
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have f1 := congrFun h1 1
  have f2 := congrFun h1 2
  simp only [Matrix.vecMul_apply_eq_sum, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_fin_one, Fin.sum_univ_four,
    kwGHZInt, complexOfInt_apply, Pi.smul_apply, smul_eq_mul, one_mul] at e1 e2 f1 f2
  push_cast at e1 e2 f1 f2
  have hu3 : u 3 = 0 := by linear_combination (e1 - f1) / 2
  have hu1 : u 1 = 0 := by linear_combination hu3 - e1
  have hu0 : u 0 = 0 := by linear_combination (e2 - f2) / 2
  have hu2 : u 2 = 0 := by linear_combination hu0 - e2
  funext k
  fin_cases k
  exacts [hu0, hu1, hu2, hu3]

/-- **A sitewise right intertwiner does exist for the paramagnetic target of part (b)**: the
first coordinate `e₀` (data file §2.2, the sitewise right intertwiner space is two-dimensional,
spanned by `e₀` and `e₃`). -/
theorem kwGHZ_right_intertwiner (i : Fin 2) :
    kwGHZ i *ᵥ (Pi.single (0 : Fin 4) (1 : ℂ)) =
      plusTensor i 0 0 • Pi.single (0 : Fin 4) (1 : ℂ) := by
  rw [kwGHZ_eq]
  simp only [plusTensor, Matrix.one_apply_eq, one_smul]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mulVec_apply_eq_sum, Matrix.of_apply, kwGHZInt, complexOfInt, Pi.single_apply]

theorem kwGHZ_right_intertwiner_ne_zero :
    (Pi.single (0 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

/-! ### The periodic states of the product-state and GHZ tensors -/

/-- Bridge: the periodic state of `plusTensor` is the unnormalized paramagnetic state
`plusState`, at every length. -/
theorem mpv_plusTensor_eq_plusState (N : ℕ) :
    (fun σ : Fin N → Fin 2 => mpv plusTensor σ) = plusState N := by
  funext σ
  simp [plusTensor_evalWord, plusState]

/-- Every word evaluation of `ghz` is diagonal, with entry `1` at `k` exactly when every letter
of the word is `k`. -/
theorem ghz_evalWord (w : List (Fin 2)) :
    Kraus.evalWord ghz w = Matrix.diagonal fun k => if ∀ x ∈ w, x = k then 1 else 0 := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
    have hi : ghz i = Matrix.diagonal fun k => if i = k then 1 else 0 := by
      fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [ghz]
    rw [Kraus.evalWord, ih, hi, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : i = k <;> simp [hk]

/-- Bridge: the periodic state of `ghz` is the unnormalized ferromagnetic state `ghzState`, at
every length (at length zero both equal `2`). -/
theorem mpv_ghz_eq_ghzState (N : ℕ) :
    (fun σ : Fin N → Fin 2 => mpv ghz σ) = ghzState N := by
  funext σ
  rw [mpv_eq, coeff_eq, ghz_evalWord, Matrix.trace_diagonal, Fin.sum_univ_two, ghzState]
  have h0 : (∀ x ∈ List.ofFn σ, x = 0) ↔ σ = 0 := by
    simp [funext_iff]
  have h1 : (∀ x ∈ List.ofFn σ, x = 1) ↔ σ = flipConfig 0 := by
    simp only [List.forall_mem_ofFn_iff, funext_iff, flipConfig, Pi.zero_apply]
    rfl
  rw [if_congr h0 rfl rfl, if_congr h1 rfl rfl]

/-- The action tensor `kwPlus` has the periodic states `2^N` times those of `ghz`, the
tensor-level reading of `kwTensor_mpo_mulVec_plus`. -/
theorem mpv_kwPlus_eq_smul_mpv_ghz (N : ℕ) [NeZero N] :
    (fun σ : Fin N → Fin 2 => mpv kwPlus σ) = (2 : ℂ) ^ N • fun σ => mpv ghz σ := by
  rw [kwPlus, ← MPOTensor.mpo_mulVec_mpv, mpv_plusTensor_eq_plusState, mpv_ghz_eq_ghzState,
    kwTensor_mpo_mulVec_plus]

/-- The action tensor `kwGHZ` has the periodic states twice those of `plusTensor`, the
tensor-level reading of `kwTensor_mpo_mulVec_ghz`. -/
theorem mpv_kwGHZ_eq_two_smul_mpv_plusTensor (N : ℕ) [NeZero N] :
    (fun σ : Fin N → Fin 2 => mpv kwGHZ σ) = (2 : ℂ) • fun σ => mpv plusTensor σ := by
  rw [kwGHZ, ← MPOTensor.mpo_mulVec_mpv, mpv_plusTensor_eq_plusState, mpv_ghz_eq_ghzState,
    kwTensor_mpo_mulVec_ghz]

end KWExample

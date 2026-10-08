/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ClusterReview
import QICLean.Algebra.SpinCover.Basic

/-!
# Physical string order in the cluster state

For the tensor printed in Pérez-García, Wolf, Sanz, Verstraete, and Cirac,
arXiv:0802.0447, Example 2, the twist is `u = -σx` and its virtual eigenmatrix
is `V = σy`. Every one-site endpoint correlator vanishes once the middle string
has length at least two. Two-site endpoints `x = σz ⊗ σy` and `y = σy ⊗ σz`
instead give the value one for every middle length, including odd lengths.

The tensor is the existing `clusterTensorRMP`, with stationary density matrix
`Λ = (1/2) • 1`. The correlators are the stationary infinite-chain transfer
expressions of display `SOPMP`, rather than finite periodic expectations.
The blocked physical alphabet is little-endian: `i = s₀ + 2s₁` represents
`Aˢ⁰ Aˢ¹`.

**Scope restriction (specified twist):** The one-site absence result fixes
`u = -σx`; it does not exclude string order for arbitrary other physical twists.
This restriction is recorded in
`docs/paper-gaps/pgwsvc08_string_order_virtual_boundary.tex`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace MPSTensor

private lemma clusterTensorRMP_zero_smul :
    clusterTensorRMP 0 = Complex.invSqrtTwo • !![1, 1; 0, 0] := by
  simp [clusterTensorRMP, Complex.invSqrtTwo, one_div]

private lemma clusterTensorRMP_one_smul :
    clusterTensorRMP 1 = Complex.invSqrtTwo • !![0, 0; 1, -1] := by
  simp [clusterTensorRMP, Complex.invSqrtTwo, one_div]

/-- The physical transfer map for the printed cluster tensor, in coordinates.
Source: arXiv:0802.0447, Example 2 and display `EU`. -/
lemma clusterTensorRMP_twistedTransferMap (p X : Matrix (Fin 2) (Fin 2) ℂ) :
    twistedTransferMap clusterTensorRMP p X =
      !![p 0 0 * (X 0 0 + X 0 1 + X 1 0 + X 1 1) / 2,
          p 1 0 * (X 0 0 - X 0 1 + X 1 0 - X 1 1) / 2;
        p 0 1 * (X 0 0 + X 0 1 - X 1 0 - X 1 1) / 2,
          p 1 1 * (X 0 0 - X 0 1 - X 1 0 + X 1 1) / 2] := by
  simp only [twistedTransferMap_apply, Fin.sum_univ_two,
    clusterTensorRMP_zero_smul, clusterTensorRMP_one_smul,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_invSqrtTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_two] <;> ring_nf <;> simp [Complex.invSqrtTwo_sq] <;> ring

/-- The printed cluster tensor is unital.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
theorem clusterTensorRMP_transferMap_one : Kraus.transferMap clusterTensorRMP 1 = 1 := by
  rw [← twistedTransferMap_one, clusterTensorRMP_twistedTransferMap]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The maximally mixed density matrix is stationary for the printed cluster tensor.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
theorem clusterTensorRMP_adjoint_fixes_maximallyMixed :
    Kraus.transferMap (fun i => (clusterTensorRMP i)ᴴ) ((1 / 2 : ℂ) • 1) =
      (1 / 2 : ℂ) • 1 := by
  simp only [Kraus.transferMap_apply, Fin.sum_univ_two,
    clusterTensorRMP_zero_smul, clusterTensorRMP_one_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_invSqrtTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.invSqrtTwo_sq]

/-- The stationary matrix `Λ = I/2` is strictly positive and has trace one,
as required in arXiv:0802.0447, display `fixed` and the following paragraph. -/
theorem clusterTensorRMP_maximallyMixed_posDef_trace :
    Matrix.PosDef ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      Matrix.trace ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  constructor
  · exact Matrix.PosDef.one.smul (by norm_num)
  · norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The virtual matrix `σy` is fixed by the physical twist `-σx`.
Source: arXiv:0802.0447, Example 2. -/
theorem clusterTensorRMP_twistedTransferMap_pauliY :
    twistedTransferMap clusterTensorRMP (-pauliX) (SpinCover.pauli 1) = SpinCover.pauli 1 := by
  rw [clusterTensorRMP_twistedTransferMap]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliX, SpinCover.pauli]

/-- The physical twist `-σx` is implemented on the printed cluster tensor
by the virtual Pauli matrix `σy`. Source: arXiv:0802.0447, Example 2. -/
theorem clusterTensorRMP_pauliY_intertwine (i : Fin 2) :
    (∑ j : Fin 2, (-pauliX) i j • clusterTensorRMP j) * SpinCover.pauli 1 =
      SpinCover.pauli 1 * clusterTensorRMP i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [clusterTensorRMP, pauliX, SpinCover.pauli, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The one-site endpoint trace in Example 2 of arXiv:0802.0447 vanishes
for every pair of physical indices, with normalized `Λ = 1/2`. -/
theorem clusterTensorRMP_trace_pauliY_mul_letter_mul_conjTranspose (n j : Fin 2) :
    Matrix.trace (SpinCover.pauli 1 * ((1 / 2 : ℂ) • 1) *
      clusterTensorRMP n * (clusterTensorRMP j)ᴴ) = 0 := by
  fin_cases n <;> fin_cases j <;>
    simp [clusterTensorRMP, SpinCover.pauli, Matrix.trace, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

/-- Every one-site physical endpoint is killed by two applications of the twist.
Source: arXiv:0802.0447, Example 2. -/
lemma clusterTensorRMP_twist_twice_endpoint (y : Matrix (Fin 2) (Fin 2) ℂ) :
    twistedTransferMap clusterTensorRMP (-pauliX)
      (twistedTransferMap clusterTensorRMP (-pauliX)
        (twistedTransferMap clusterTensorRMP y 1)) = 0 := by
  simp only [clusterTensorRMP_twistedTransferMap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX]

/-- With the fixed twist `u = -σx`, arbitrary one-site physical endpoints have
zero string correlator for every middle length `N ≥ 2`.
Source: arXiv:0802.0447, Example 2 and display `SOPMP`. -/
theorem clusterTensorRMP_physicalStringOrderParam_eq_zero
    (x y : Matrix (Fin 2) (Fin 2) ℂ) {N : ℕ} (hN : 2 ≤ N) :
    physicalStringOrderParam clusterTensorRMP ((1 / 2 : ℂ) • 1)
      x y (-pauliX) N = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [physicalStringOrderParam, twistedTransferIter, pow_add]
  simp only [Module.End.mul_apply, pow_two, clusterTensorRMP_twist_twice_endpoint,
    map_zero, Matrix.mul_zero, Matrix.trace_zero]

/-- The printed twist cannot give physical string order with one-site endpoints.
This fixes the twist; it does not quantify over other possible twists.
Source: arXiv:0802.0447, Example 2. -/
theorem clusterTensorRMP_not_hasPhysicalStringOrderWith
    (x y : Matrix (Fin 2) (Fin 2) ℂ) :
    ¬ HasPhysicalStringOrderWith clusterTensorRMP ((1 / 2 : ℂ) • 1) x y (-pauliX) := by
  rintro ⟨s, hs, hlim⟩
  have hzero : Filter.Tendsto
      (fun N => ‖physicalStringOrderParam clusterTensorRMP ((1 / 2 : ℂ) • 1)
        x y (-pauliX) N‖) Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    rw [clusterTensorRMP_physicalStringOrderParam_eq_zero x y hN, norm_zero]
  exact (ne_of_gt hs) (tendsto_nhds_unique hlim hzero)

private lemma clusterString_decodeBlock (h : blockPhysDim 2 2 = 4) (i : Fin 4) :
    Kraus.decodeBlock 2 2 (Fin.cast h.symm i) =
      ![Fin.modNat (m := 2) (n := 2) i, Fin.divNat (m := 2) (n := 2) i] := by
  funext j
  apply Fin.ext
  simp only [Kraus.decodeBlock, Function.comp_apply,
    finFunctionFinEquiv_symm_apply_val]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.divNat, Fin.modNat]

/-- The blocked index `i` represents the ordered two-site word
`(i mod 2, i / 2)`.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
lemma clusterBlockedRMP_eq_mul (i : Fin 4) :
    clusterBlockedRMP i = clusterTensorRMP (Fin.modNat (m := 2) (n := 2) i) *
      clusterTensorRMP (Fin.divNat (m := 2) (n := 2) i) := by
  simp only [clusterBlockedRMP, Kraus.blockTensor, Kraus.wordOfBlock]
  rw [clusterString_decodeBlock (by simp [blockPhysDim_eq_pow]) i]
  simp [List.ofFn_succ, Kraus.evalWord]

/-- The two-site physical endpoint `σz ⊗ σy`, with the first site in the
least-significant blocked index, as for `clusterBlockedRMP`.
Source: arXiv:0802.0447, Example 2. -/
def clusterStringLeft : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    pauliZ (Fin.modNat (m := 2) (n := 2) i) (Fin.modNat (m := 2) (n := 2) j) *
      SpinCover.pauli 1 (Fin.divNat (m := 2) (n := 2) i) (Fin.divNat (m := 2) (n := 2) j)

/-- The two-site physical endpoint `σy ⊗ σz`, in the same blocked basis.
Source: arXiv:0802.0447, Example 2. -/
def clusterStringRight : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    SpinCover.pauli 1 (Fin.modNat (m := 2) (n := 2) i) (Fin.modNat (m := 2) (n := 2) j) *
      pauliZ (Fin.divNat (m := 2) (n := 2) i) (Fin.divNat (m := 2) (n := 2) j)

/-- The two-site physical twist `(-σx) ⊗ (-σx)`, in the same blocked basis.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
def clusterStringTwist : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    (-pauliX) (Fin.modNat (m := 2) (n := 2) i) (Fin.modNat (m := 2) (n := 2) j) *
      (-pauliX) (Fin.divNat (m := 2) (n := 2) i) (Fin.divNat (m := 2) (n := 2) j)

/-- The left endpoint acts on the decoded sites by `σz ⊗ σy`.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
lemma clusterStringLeft_apply_decode (h : blockPhysDim 2 2 = 4) (i j : Fin 4) :
    clusterStringLeft i j =
      pauliZ (decodeBlock 2 2 (Fin.cast h.symm i) 0)
          (decodeBlock 2 2 (Fin.cast h.symm j) 0) *
        SpinCover.pauli 1 (decodeBlock 2 2 (Fin.cast h.symm i) 1)
          (decodeBlock 2 2 (Fin.cast h.symm j) 1) := by
  simp [decodeBlock, clusterString_decodeBlock h i, clusterString_decodeBlock h j,
    clusterStringLeft]

/-- The right endpoint acts on the decoded sites by `σy ⊗ σz`.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
lemma clusterStringRight_apply_decode (h : blockPhysDim 2 2 = 4) (i j : Fin 4) :
    clusterStringRight i j =
      SpinCover.pauli 1 (decodeBlock 2 2 (Fin.cast h.symm i) 0)
          (decodeBlock 2 2 (Fin.cast h.symm j) 0) *
        pauliZ (decodeBlock 2 2 (Fin.cast h.symm i) 1)
          (decodeBlock 2 2 (Fin.cast h.symm j) 1) := by
  simp [decodeBlock, clusterString_decodeBlock h i, clusterString_decodeBlock h j,
    clusterStringRight]

/-- The blocked physical twist is the tensor square of `-σx`.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
lemma clusterStringTwist_eq_blockKron (h : blockPhysDim 2 2 = 4) :
    clusterStringTwist = (blockKron 2 (-pauliX)).submatrix
      (Fin.cast h.symm) (Fin.cast h.symm) := by
  ext i j
  simp [blockKron, decodeBlock, Matrix.submatrix_apply, Fin.prod_univ_two,
    clusterString_decodeBlock h i, clusterString_decodeBlock h j, clusterStringTwist]

/-- The right two-site physical endpoint produces `-σy` on the bond space.
Source: arXiv:0802.0447, Example 2. -/
lemma clusterBlockedRMP_twistedTransferMap_right :
    twistedTransferMap clusterBlockedRMP clusterStringRight 1 = -(SpinCover.pauli 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistedTransferMap_apply, Fin.sum_univ_four, clusterStringRight,
      SpinCover.pauli, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.divNat, Fin.modNat, map_ofNat] <;>
    ring_nf

/-- The left two-site physical endpoint sends `σy` to `-1`.
Source: arXiv:0802.0447, Example 2. -/
lemma clusterBlockedRMP_twistedTransferMap_left :
    twistedTransferMap clusterBlockedRMP clusterStringLeft (SpinCover.pauli 1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistedTransferMap_apply, Fin.sum_univ_four, clusterStringLeft,
      SpinCover.pauli, pauliZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.divNat, Fin.modNat, map_ofNat] <;>
    ring_nf <;> norm_num

/-- The printed two-site endpoints give string correlator one for every middle
length `N`. The endpoints each cover two sites, while `N` counts individual
sites carrying `-σx`; in particular, odd middle lengths are included.
Source: arXiv:0802.0447, Example 2 and display `SOPMP`. -/
theorem clusterTensorRMP_twoSite_physicalStringOrderParam (N : ℕ) :
    Matrix.trace (((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      twistedTransferMap clusterBlockedRMP clusterStringLeft
        (twistedTransferIter clusterTensorRMP (-pauliX) N
          (twistedTransferMap clusterBlockedRMP clusterStringRight 1))) = 1 := by
  have hN : twistedTransferIter clusterTensorRMP (-pauliX) N (SpinCover.pauli 1) =
      SpinCover.pauli 1 := by
    simpa only [twistedTransferIter, Module.End.pow_apply] using
      Function.iterate_fixed clusterTensorRMP_twistedTransferMap_pauliY N
  rw [clusterBlockedRMP_twistedTransferMap_right, map_neg, hN, map_neg,
    clusterBlockedRMP_twistedTransferMap_left, neg_neg, Matrix.mul_one,
    Matrix.trace_smul]
  norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The blocked twist fixes the same virtual eigenmatrix `σy`.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
lemma clusterBlockedRMP_twistedTransferMap_pauliY :
    twistedTransferMap clusterBlockedRMP clusterStringTwist (SpinCover.pauli 1) =
      SpinCover.pauli 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistedTransferMap_apply, Fin.sum_univ_four, clusterStringTwist,
      SpinCover.pauli, pauliX, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.divNat, Fin.modNat, map_ofNat] <;>
    ring_nf

/-- On the two-site blocked chain, the physical string correlator is one.
The middle length here counts two-site blocks.
Supporting calculation for arXiv:0802.0447, Example 2, lines 401–411. -/
theorem clusterBlockedRMP_physicalStringOrderParam (N : ℕ) :
    physicalStringOrderParam clusterBlockedRMP ((1 / 2 : ℂ) • 1)
      clusterStringLeft clusterStringRight clusterStringTwist N = 1 := by
  have hN : twistedTransferIter clusterBlockedRMP clusterStringTwist N (SpinCover.pauli 1) =
      SpinCover.pauli 1 := by
    simpa only [twistedTransferIter, Module.End.pow_apply] using
      Function.iterate_fixed clusterBlockedRMP_twistedTransferMap_pauliY N
  rw [physicalStringOrderParam, clusterBlockedRMP_twistedTransferMap_right,
    map_neg, hN, map_neg, clusterBlockedRMP_twistedTransferMap_left, neg_neg,
    Matrix.mul_one, Matrix.trace_smul]
  norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The printed two-site endpoints satisfy the physical string-order condition
with limiting absolute value one. Source: arXiv:0802.0447, Example 2. -/
theorem clusterBlockedRMP_hasPhysicalStringOrderWith :
    HasPhysicalStringOrderWith clusterBlockedRMP ((1 / 2 : ℂ) • 1)
      clusterStringLeft clusterStringRight clusterStringTwist := by
  refine ⟨1, zero_lt_one, ?_⟩
  simpa only [clusterBlockedRMP_physicalStringOrderParam, norm_one] using
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))

/-- The two-site blocked cluster state has physical string order under the
nonscalar unitary `(-σx) ⊗ (-σx)`.
Source: arXiv:0802.0447, Example 2. -/
theorem clusterBlockedRMP_hasPhysicalStringOrder :
    HasPhysicalStringOrder clusterBlockedRMP ((1 / 2 : ℂ) • 1) := by
  refine ⟨clusterStringTwist, clusterStringLeft, clusterStringRight, ?_, ?_,
    clusterBlockedRMP_hasPhysicalStringOrderWith⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [clusterStringTwist, pauliX, Matrix.mul_apply,
        Fin.sum_univ_four, Fin.divNat, Fin.modNat]
  · intro c h
    have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 3) h
    norm_num [clusterStringTwist, pauliX, Fin.divNat, Fin.modNat] at h03

end MPSTensor

end

/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockTrace

/-!
# GHZ sectors in an upper-triangular tensor

For positive length, the two bond-one tensors `ghzC 0` and `ghzC 1` generate
`|0…0⟩` and `|1…1⟩`, respectively, using the physical alphabet `Fin 2`.
The bond-four tensor `ghzB` has diagonal blocks in the order
`ghzC 1, 0, ghzC 0, 0`, with nonzero upper-triangular couplings.
Consequently its periodic word traces generate the unnormalised GHZ state
`|0…0⟩ + |1…1⟩`, not either product state separately.

The explicit construction is Example B of
`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`, `ex:p5ft-ghz`.
The compression retains both sectors and two zero slots. Although the word-level
reductions exist, the all-zero sector has no nonzero sitewise intertwiner in either
direction. Thus equality of the periodic states does not supply a sitewise splitting
of this upper-triangular representation.

## Main results

* `MPSTensor.ghzSectors_compression`: the multi-block compression datum of Theorem 7.7 for
  `ghzB` onto `{ghzC 0, ghzC 1}`.
* `MPSTensor.ghzB_trace_evalWord_eq_sum`: the word-trace identity for `ghzB`, specializing
  `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum`.
* `MPSTensor.ghzSectors_isReduction`: the biorthogonal compression pair for each sector.
* `MPSTensor.ghzSectors_dim_eq`: the dimension count `4 = 1 + 1 + 2`.
* `MPSTensor.ghzC0_right_intertwiner_eq_zero`, `MPSTensor.ghzC0_left_intertwiner_eq_zero`: the
  all-zeros sector has no nonzero sitewise intertwiner in either direction.
-/

open scoped Matrix

namespace MPSTensor

/-- The physical alphabet index type of Example B. -/
private abbrev GHZIx : Type := Fin 2

/-- The target slots of Example B: both letters of the alphabet. -/
private abbrev GHZS : Finset GHZIx := Finset.univ

/-- The bond dimension of each target slot: both sectors are one-dimensional. -/
private abbrev GHZD : GHZIx → ℕ := fun _ => 1

/-- The two symmetry-broken sectors of the GHZ family: `ghzC 0` is the all-zeros sector, and
`ghzC 1` is the all-ones sector (construction note, Example B, `ex:p5ft-ghz`). -/
def ghzC : (s : GHZIx) → MPSTensor 2 (GHZD s) := ![![!![1], !![0]], ![!![0], !![1]]]

/-- The source tensor of Example B: a four-dimensional tensor embedding the two GHZ sectors
with arbitrarily chosen coupling blocks (construction note, Example B, `ex:p5ft-ghz`). -/
def ghzB : MPSTensor 2 4 :=
  ![!![0, 1, 2, 0; 0, 0, 1, 1; 0, 0, 1, 3; 0, 0, 0, 0],
    !![1, 1, 0, 2; 0, 0, 2, 0; 0, 0, 0, 1; 0, 0, 0, 0]]

/-- The block ordering of Example B: the all-ones sector at position `0`, a zero slot at
position `1`, the all-zeros sector at position `2`, and a zero slot at position `3`, matching
the diagonal blocks of `ghzB` in order. -/
def ghzOrd : BlockIndex GHZS 2 ≃ Fin 4 where
  toFun
    | Sum.inl ⟨s, _⟩ => if s = 1 then 0 else 2
    | Sum.inr t => if t = 0 then 1 else 3
  invFun
    | 0 => Sum.inl ⟨1, Finset.mem_univ 1⟩
    | 1 => Sum.inr 0
    | 2 => Sum.inl ⟨0, Finset.mem_univ 0⟩
    | 3 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

/-- The coordinate change of Example B on the graded block space, agreeing with `ghzOrd` on
the (unique) coordinate of every block. -/
def ghzTau : BlockSpace GHZD GHZS 2 ≃ Fin 4 where
  toFun x := ghzOrd x.1
  invFun
    | 0 => ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, 0⟩
    | 1 => ⟨Sum.inr 0, 0⟩
    | 2 => ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, 0⟩
    | 3 => ⟨Sum.inr 1, 0⟩
  left_inv := by decide
  right_inv := by decide

/-- The identity reindexing of the bond space of `ghzB` into the block coordinates given by
`ghzTau`. -/
noncomputable def ghzGauge : (Fin 4 → ℂ) ≃ₗ[ℂ] (BlockSpace GHZD GHZS 2 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ ghzTau

/-- Conjugating a matrix by `ghzGauge` reindexes it along `ghzTau`. -/
theorem conjMatrix_ghzGauge (A : Matrix (Fin 4) (Fin 4) ℂ) :
    conjMatrix ghzGauge A = A.submatrix ghzTau ghzTau := by
  rw [ghzGauge, conjMatrix_apply, toMatrix'_conj_funCongrLeft, LinearMap.toMatrix'_toLin']

/-- **The multi-block asymmetric compression datum of Example B.** -/
noncomputable def ghzSectors_compression : MultiBlockCompression ghzB GHZS ghzC where
  z := 2
  ord := ghzOrd
  gauge := ghzGauge
  triangular i x y hxy := by
    rw [conjMatrix_ghzGauge, Matrix.submatrix_apply]
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      first
        | exact absurd hxy (by decide)
        | simp [ghzTau, ghzOrd, ghzB]
  matched i s := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_ghzGauge, Matrix.submatrix_apply]
    fin_cases p; fin_cases q
    obtain ⟨s, hs⟩ := s
    fin_cases i <;> fin_cases s <;> simp [ghzTau, ghzOrd, ghzB, ghzC]
  unmatched i t := by
    ext p q
    rw [Matrix.blockDiag'_apply, conjMatrix_ghzGauge, Matrix.submatrix_apply]
    fin_cases p; fin_cases q
    fin_cases i <;> fin_cases t <;> simp [ghzTau, ghzOrd, ghzB]

/-- **The word-trace identity of Example B**, specializing `trace_evalWord_eq_sum`: the trace of
every nonempty word of `ghzB` is the sum of the traces of the corresponding words of the two GHZ
sectors. -/
theorem ghzB_trace_evalWord_eq_sum (w : List (Fin 2)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord ghzB w) =
      Matrix.trace (Kraus.evalWord (ghzC 0) w) + Matrix.trace (Kraus.evalWord (ghzC 1) w) := by
  have h := ghzSectors_compression.trace_evalWord_eq_sum w hw
  rwa [Fin.sum_univ_two] at h

/-- **Biorthogonal compression of each GHZ sector out of `ghzB`.** -/
theorem ghzSectors_isReduction (s : {s // s ∈ GHZS}) :
    IsReduction ghzB (ghzC s.1) (ghzSectors_compression.left s) (ghzSectors_compression.right s) :=
  ghzSectors_compression.isReduction s

/-- **The dimension count of Example B**: `4 = 1 + 1 + 2`. -/
theorem ghzSectors_dim_eq : (4 : ℕ) = ∑ s ∈ GHZS, GHZD s + 2 :=
  ghzSectors_compression.dim_eq

/-- No nonzero right sitewise intertwiner for the all-zeros sector: there is no `v ≠ 0` with
`ghzB 0 *ᵥ v = v` and `ghzB 1 *ᵥ v = 0` (construction note, Example B). -/
theorem ghzC0_right_intertwiner_eq_zero (v : Fin 4 → ℂ) (h0 : ghzB 0 *ᵥ v = v)
    (h1 : ghzB 1 *ᵥ v = 0) : v = 0 := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e3 := congrFun h0 3
  have f1 := congrFun h1 1
  simp only [ghzB, Fin.isValue, Matrix.cons_val_zero, Matrix.mulVec_apply_eq_sum, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_four, zero_mul, Matrix.cons_val_one,
    one_mul, zero_add, Matrix.cons_val, add_zero, Pi.zero_apply, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or] at e0 e1 e3 f1
  have hv3 : v 3 = 0 := e3.symm
  have hv2 : v 2 = 0 := f1
  have hv1 : v 1 = 0 := by linear_combination -e1 + hv2 + hv3
  have hv0 : v 0 = 0 := by linear_combination -e0 + hv1 + 2 * hv2
  funext k
  fin_cases k
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3

/-- No nonzero left sitewise intertwiner for the all-zeros sector: there is no `u ≠ 0` with
`u ᵥ* ghzB 0 = u` and `u ᵥ* ghzB 1 = 0` (construction note, Example B). -/
theorem ghzC0_left_intertwiner_eq_zero (u : Fin 4 → ℂ) (h0 : u ᵥ* ghzB 0 = u)
    (h1 : u ᵥ* ghzB 1 = 0) : u = 0 := by
  have e3 := congrFun h0 3
  have g0 := congrFun h1 0
  have g2 := congrFun h1 2
  have g3 := congrFun h1 3
  simp only [ghzB, Fin.isValue, Matrix.cons_val_zero, Matrix.vecMul_apply_eq_sum, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one, Fin.sum_univ_four, mul_zero,
    Matrix.cons_val_one, mul_one, zero_add, add_zero, Pi.zero_apply, mul_eq_zero,
    OfNat.ofNat_ne_zero, or_false] at e3 g0 g2 g3
  have hu0 : u 0 = 0 := g0
  have hu1 : u 1 = 0 := g2
  have hu2 : u 2 = 0 := by linear_combination g3 - 2 * hu0
  have hu3 : u 3 = 0 := by linear_combination -e3 + hu1 + 3 * hu2
  funext k
  fin_cases k
  · exact hu0
  · exact hu1
  · exact hu2
  · exact hu3

end MPSTensor

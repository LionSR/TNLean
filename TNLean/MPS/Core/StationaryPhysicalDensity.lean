/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ObservableTransfer
import TNLean.MPS.Core.PhysicalMatrix
import TNLean.MPS.Core.BlockingTransfer
import Mathlib.Analysis.Matrix.Order

/-!
# Stationary physical block densities

For a unital matrix product tensor and a trace-one stationary dual matrix Λ,
the physical density on N consecutive sites has entries tr(Λ A_s A_t†).
The construction uses the physical block alphabet and is distinct from the
virtual matrix Λ and from a reduction of a finite periodic pure state.

The physical matrix of a blocked tensor factors the density through the
D²-dimensional virtual pair space. This proves positivity, the rank bound,
and consistency under tracing out either boundary site.

## References

* Pérez-García, Wolf, Sanz, Verstraete and Cirac, arXiv:0802.0447,
  canonical normalization and Theorem 2, lines 297–323.
-/

open scoped Matrix BigOperators Kronecker ComplexOrder MatrixOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The N-site physical density of the stationary finitely correlated family.
Its entries are tr(Λ A_s A_t†), with words in the existing block alphabet.
Source: arXiv:0802.0447, Theorem 2, lines 297–323. -/
noncomputable def stationaryBlockDensity (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    Matrix (Fin (blockPhysDim d N)) (Fin (blockPhysDim d N)) ℂ :=
  physicalMatrix (blockTensor A N) * (Λᵀ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
    (physicalMatrix (blockTensor A N))ᴴ

/-- The stationary physical density has the source trace coefficients.
Source: arXiv:0802.0447, Theorem 2, lines 297–323. -/
theorem stationaryBlockDensity_apply (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ)
    (s t : Fin (blockPhysDim d N)) :
    stationaryBlockDensity A Λ N s t =
      Matrix.trace (Λ * blockTensor A N s * (blockTensor A N t)ᴴ) := by
  rw [stationaryBlockDensity, ← physicalMatrix_mul_left_right,
    physicalMatrix_mul_conjTranspose_apply]
  simp only [Matrix.mul_one]

/-- The physical density in word coordinates, before the blocked alphabet
is encoded as a finite index. Source: arXiv:0802.0447, Theorem 2. -/
theorem stationaryBlockDensity_word (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) (s t : Fin N → Fin d) :
    stationaryBlockDensity A Λ N
        ((decodeBlockEquiv d N).symm s) ((decodeBlockEquiv d N).symm t) =
      Matrix.trace (Λ * Kraus.evalWord A (List.ofFn s) *
        (Kraus.evalWord A (List.ofFn t))ᴴ) := by
  simp only [stationaryBlockDensity_apply, Kraus.blockTensor, Kraus.wordOfBlock,
    decodeBlock_decodeBlockEquiv_symm]

/-- The stationary physical density represents the existing observable-transfer
functional on arbitrary block observables. The physical coefficients have the
source orientation O[t,s] and no Hermitian condition is required.
Source: arXiv:0802.0447, displays EU and SOPMP and Theorem 2, lines 166–181 and 297–323. -/
theorem trace_stationaryBlockDensity_mul_observable
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ)
    (O : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    Matrix.trace (Matrix.reindex (decodeBlockEquiv d N) (decodeBlockEquiv d N)
      (stationaryBlockDensity A Λ N) * O) =
      Matrix.trace (Λ * physicalObservableTransfer A N O 1) := by
  change (∑ s, ∑ t, Matrix.reindex (decodeBlockEquiv d N) (decodeBlockEquiv d N)
    (stationaryBlockDensity A Λ N) s t * O t s) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stationaryBlockDensity_word,
    physicalObservableTransfer_apply, Matrix.mul_one, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc, mul_comm]

/-- Tracing out the rightmost physical site uses unitality of the ordinary
transfer map. Source: arXiv:0802.0447, stationary reduced density family. -/
theorem stationaryBlockDensity_right_marginal
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hNorm : Kraus.transferMap A 1 = 1) (N : ℕ) (s t : Fin N → Fin d) :
    (∑ i : Fin d, stationaryBlockDensity A Λ (N + 1)
        ((decodeBlockEquiv d (N + 1)).symm (Fin.snoc s i))
        ((decodeBlockEquiv d (N + 1)).symm (Fin.snoc t i))) =
      stationaryBlockDensity A Λ N
        ((decodeBlockEquiv d N).symm s) ((decodeBlockEquiv d N).symm t) := by
  simp only [stationaryBlockDensity_word, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, List.concat_eq_append, Kraus.evalWord_append,
    Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, Matrix.conjTranspose_mul]
  rw [← Matrix.trace_sum]
  congr 1
  have hsum : ∑ i, A i * (A i)ᴴ = 1 := by
    simpa only [Kraus.transferMap_apply, Matrix.mul_one] using hNorm
  calc
    _ = (Λ * Kraus.evalWord A (List.ofFn s)) * (∑ i, A i * (A i)ᴴ) *
        (Kraus.evalWord A (List.ofFn t))ᴴ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = _ := by rw [hsum, Matrix.mul_one]

/-- Tracing out the leftmost physical site uses stationarity of the dual
boundary. Source: arXiv:0802.0447, stationary reduced density family. -/
theorem stationaryBlockDensity_left_marginal
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (N : ℕ) (s t : Fin N → Fin d) :
    (∑ i : Fin d, stationaryBlockDensity A Λ (N + 1)
        ((decodeBlockEquiv d (N + 1)).symm (Fin.cons i s))
        ((decodeBlockEquiv d (N + 1)).symm (Fin.cons i t))) =
      stationaryBlockDensity A Λ N
        ((decodeBlockEquiv d N).symm s) ((decodeBlockEquiv d N).symm t) := by
  simp only [stationaryBlockDensity_word, List.ofFn_succ, Fin.cons_zero,
    Fin.cons_succ, Kraus.evalWord_cons, Matrix.conjTranspose_mul]
  calc
    _ = ∑ i, Matrix.trace (((A i)ᴴ * Λ * A i) *
        Kraus.evalWord A (List.ofFn s) * (Kraus.evalWord A (List.ofFn t))ᴴ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm
          (Λ * A i * Kraus.evalWord A (List.ofFn s) *
            (Kraus.evalWord A (List.ofFn t))ᴴ) (A i)ᴴ
    _ = _ := by
      rw [← Matrix.trace_sum]
      congr 1
      simpa only [Kraus.transferMap_apply, Matrix.conjTranspose_conjTranspose,
        Matrix.sum_mul] using congrArg
          (fun X => X * Kraus.evalWord A (List.ofFn s) *
            (Kraus.evalWord A (List.ofFn t))ᴴ) hΛfix

/-- A positive virtual boundary gives positive physical block matrices.
Source: arXiv:0802.0447, Theorem 2, lines 297–323. -/
theorem stationaryBlockDensity_posSemidef (A : MPSTensor d D)
    {Λ : Matrix (Fin D) (Fin D) ℂ} (hΛ : Λ.PosSemidef) (N : ℕ) :
    (stationaryBlockDensity A Λ N).PosSemidef :=
  (hΛ.transpose.kronecker Matrix.PosSemidef.one).mul_mul_conjTranspose_same _

/-- Every stationary block density has rank at most D², independently of the
block length. Source: arXiv:0802.0447, proof of Theorem 2, lines 316–320. -/
theorem rank_stationaryBlockDensity_le (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    (stationaryBlockDensity A Λ N).rank ≤ D ^ 2 := by
  apply (Matrix.rank_mul_le_left _ _).trans
  apply (Matrix.rank_mul_le_left _ _).trans
  simpa [pow_two] using (physicalMatrix (blockTensor A N)).rank_le_card_width

/-- The physical trace is the stationary boundary applied to the N-fold
ordinary transfer map. Source: arXiv:0802.0447, canonical normalization. -/
theorem trace_stationaryBlockDensity (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (N : ℕ) :
    Matrix.trace (stationaryBlockDensity A Λ N) =
      Matrix.trace (Λ * (Kraus.transferMap A ^ N) 1) := by
  rw [← transferMap_blockTensor_apply]
  change (∑ s, stationaryBlockDensity A Λ N s s) = _
  simp only [stationaryBlockDensity_apply, Kraus.transferMap_apply,
    Matrix.mul_one, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]

/-- Unitality and a trace-one boundary normalize every physical block density.
Source: arXiv:0802.0447, canonical normalization and Theorem 2. -/
theorem trace_stationaryBlockDensity_eq_one (A : MPSTensor d D)
    (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛtr : Matrix.trace Λ = 1)
    (hNorm : Kraus.transferMap A 1 = 1) (N : ℕ) :
    Matrix.trace (stationaryBlockDensity A Λ N) = 1 := by
  rw [trace_stationaryBlockDensity, ← transferMap_blockTensor_apply,
    transferMap_blockTensor_fixedPoint A N 1 hNorm, Matrix.mul_one, hΛtr]

/-- Physical rotation conjugates each physical density by the corresponding
Kronecker power. Source: arXiv:0802.0447, local symmetry, lines 297–304. -/
theorem stationaryBlockDensity_rotatePhysical
    (A : MPSTensor d D) (Λ : Matrix (Fin D) (Fin D) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    stationaryBlockDensity (rotatePhysical u A) Λ N =
      blockKron N u * stationaryBlockDensity A Λ N * (blockKron N u)ᴴ := by
  simp only [stationaryBlockDensity, blockTensor_rotatePhysical,
    physicalMatrix_rotatePhysical, Matrix.conjTranspose_mul, Matrix.mul_assoc]


/-- A phase-unitary virtual gauge preserving Λ gives equal physical density
matrices at every block length. Source: arXiv:0802.0447, proof of Theorem 2,
lines 311–315. -/
theorem stationaryBlockDensity_eq_of_unitary_gaugePhase
    (A B : MPSTensor d D) (Λ V : Matrix (Fin D) (Fin D) ℂ)
    (μ : ℂ) (hV : V * Vᴴ = 1) (hμ : ‖μ‖ = 1)
    (hΛ : Vᴴ * Λ * V = Λ)
    (hAB : ∀ i, B i = μ • (V * A i * Vᴴ)) (N : ℕ) :
    stationaryBlockDensity B Λ N = stationaryBlockDensity A Λ N := by
  have hV' : Vᴴ * V = 1 := mul_eq_one_comm.mp hV
  let X : GL (Fin D) ℂ := ⟨V, Vᴴ, hV, hV'⟩
  have hw (w : List (Fin d)) :
      Kraus.evalWord B w = μ ^ w.length • (V * Kraus.evalWord A w * Vᴴ) := by
    rw [show B = (fun i => μ • (V * A i * Vᴴ)) from funext hAB,
      Kraus.evalWord_smul]
    congr 1
    exact evalWord_gauge (A := A) (B := fun i => V * A i * Vᴴ) X (fun _ => rfl) w
  have hphase : star (μ ^ N) * μ ^ N = 1 := by
    simp only [Complex.star_def, Complex.conj_mul', norm_pow, hμ, one_pow, Complex.ofReal_one]
  ext s t
  simp only [stationaryBlockDensity_apply]
  change Matrix.trace (Λ * Kraus.evalWord B (wordOfBlock d N s) *
    (Kraus.evalWord B (wordOfBlock d N t))ᴴ) = _
  rw [hw, hw, length_wordOfBlock, length_wordOfBlock]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, hphase, one_smul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV', Matrix.one_mul]
  calc
    _ = Matrix.trace ((Vᴴ * Λ * V) * blockTensor A N s * (blockTensor A N t)ᴴ) := by
      simpa only [Matrix.mul_assoc, Kraus.blockTensor] using Matrix.trace_mul_comm
        (Λ * V * blockTensor A N s * (blockTensor A N t)ᴴ) Vᴴ
    _ = _ := by simp only [hΛ, Matrix.mul_assoc]

end MPSTensor

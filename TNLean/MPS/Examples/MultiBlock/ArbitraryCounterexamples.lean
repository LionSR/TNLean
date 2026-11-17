/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.Worked
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessLongWords
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Counterexamples for the fundamental theorem for arbitrary tensors

Three examples show that hypotheses of the theorem for arbitrary tensors and of its companions
cannot be dropped or weakened.

**Proportional states with a constant not of the form `λ^N`.** Let `C` be the normal tensor with
letters `C¹ = [[1, 1], [0, 2]]`, `C² = [[0, 0], [1, 0]]`, and let `A = C ⊕ 2C`, `B = C ⊕ 3C`. Then
`V_N(A) = (1 + 2^N) V_N(C)` and `V_N(B) = (1 + 3^N) V_N(C)`, so the states are proportional at every
length with the nonzero constant `c_N = (1 + 2^N)/(1 + 3^N)`, but `c_2 = 1/2 ≠ 9/16 = c_1²`: no
scalar `μ` gives `V_N(A) = μ^N V_N(B)`. The composition factors `{C, 2C}` and `{C, 3C}` differ, so
for proportional states with an arbitrary length-dependent constant only the classes of the
factors up to scalars can be compared; the factor-by-factor comparison needs `c_N = λ^N`.

**Equal states and the form `IsIrreducibleForm` do not give a `ℤ_m`-gauge.** For one letter and bond
dimension two, the Jordan block `X = [[1, 1], [0, 1]]` and the identity `Y = 1` both satisfy
`IsIrreducibleForm`, which asks only for the same states as a weighted block sum (here two `1 × 1`
blocks `(1)` of period one and weight one), and they have the same states (trace `2` at every
length). A `ℤ_m`-gauge equivalence would give `Z X = 1` with `Z` commuting with `X` and `Z^m = 1`,
hence `X^m = 1`, while `X^m = [[1, m], [0, 1]]`. The same holds for every `d ≥ 1` and `D ≥ 2`, with
`1 + E₀₁` and `1` on one letter and the other letters zero. The source theorem (arXiv:1708.00029,
`thm:bdequal`) is not affected: its irreducible form is a block sum, which `X` is not, and block
sums with the same states are gauge equivalent
(`MPSTensor.gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks`).

**The long-word identity needs the block to be last in both reductions.** In the worked example of
*The asymmetric fundamental theorem of matrix product states* (Example 6.16,
`TNLean.MPS.Examples.MultiBlock.Worked`), the block `C₂` occurs once up to gauge and is the last
slot of the reduction `g = g₀`, in the order `(C₁, 0, C₂)`, but is followed by `C₁` in the second
reduction, here `ĝ' = diag(1, 1, Y⁻¹) ĝ` onto the same family `(C₁, C₂)` in the order
`(0, C₂, C₁)`. The reading maps `W_{C₂} = (0, -1, 0, 1)` and `Ŵ_{C₂} = (-2, -3, -1, 1)` are not
proportional, and `Ŵ_{C₂} B^w` is not proportional to `W_{C₂} B^w` for the word
`w = 1 ⋯ 1` of any length. All hypotheses of
`MPSTensor.MultiBlockCompression.exists_left_eq_smul_of_last` and
`MPSTensor.MultiBlockCompression.exists_left_mul_evalWord_eq_smul_of_last`
other than "last in the second reduction" hold.

## Main results

* `MPSTensor.not_exists_pow_of_nonzeroProportionalMPV₂_example`: proportional states whose
  constant is not `μ^N`.
* `MPSTensor.not_forall_exists_zGaugeEquiv_of_isIrreducibleForm_of_sameMPV`: no `ℤ_m`-gauge follows
  from `IsIrreducibleForm` and equal states, for `d ≥ 1`, `D ≥ 2`.
* `MultiBlockExamples.Worked.not_exists_left_eq_smul_of_last_in_one_reduction`,
  `MultiBlockExamples.Worked.not_exists_left_mul_evalWord_eq_smul_of_last_in_one_reduction`:
  for a block that is last in only one reduction.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.16;
arXiv:1708.00029, `thm:bdequal`.
-/

open scoped Matrix

namespace MPSTensor

/-! ### Proportional states with a constant not of the form `λ^N` -/

namespace ArbitraryExamples

/-- The normal tensor `C = ([[1, 1], [0, 2]], [[0, 0], [1, 0]])`. -/
noncomputable def propC : MPSTensor 2 2 := ![!![1, 1; 0, 2], !![0, 0; 1, 0]]

/-- `A = C ⊕ 2C`. -/
noncomputable def propA : MPSTensor 2 (∑ _k : Fin 2, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, 2] fun _ => propC

/-- `B = C ⊕ 3C`. -/
noncomputable def propB : MPSTensor 2 (∑ _k : Fin 2, 2) :=
  toTensorFromBlocks (d := 2) (dim := fun _ => 2) ![1, 3] fun _ => propC

theorem mpv_propA {N : ℕ} (σ : Fin N → Fin 2) : mpv propA σ = (1 + 2 ^ N) * mpv propC σ := by
  rw [propA, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, smul_eq_mul]
  ring

theorem mpv_propB {N : ℕ} (σ : Fin N → Fin 2) : mpv propB σ = (1 + 3 ^ N) * mpv propC σ := by
  rw [propB, mpv_toTensorFromBlocks_eq_sum, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, smul_eq_mul]
  ring

theorem mpv_propC_one : mpv propC (fun _ : Fin 1 => (0 : Fin 2)) = 3 := by
  simp [propC, Matrix.trace_fin_two]
  norm_num

theorem mpv_propC_two : mpv propC (fun _ : Fin 2 => (0 : Fin 2)) = 5 := by
  simp [propC, Matrix.trace_fin_two]
  norm_num

end ArbitraryExamples

open ArbitraryExamples in
/-- **Proportional states with a constant not of the form `μ^N`.** `A = C ⊕ 2C`
and `B = C ⊕ 3C` have `V_N(A) = c_N V_N(B)` with `c_N = (1 + 2^N)/(1 + 3^N) ≠ 0` at every positive
length, but no `μ` gives `V_N(A) = μ^N V_N(B)`, since `c_1 = 3/4` and `c_2 = 1/2 ≠ c_1²`. For
proportional states with an arbitrary constant only the classes of the composition factors up to
scalars can be compared; the factor-by-factor comparison needs `c_N = λ^N`. -/
theorem not_exists_pow_of_nonzeroProportionalMPV₂_example :
    NonzeroProportionalMPV₂ propA propB ∧
      ¬ ∃ μ : ℂ, ∀ N, 0 < N → ∀ σ : Fin N → Fin 2, mpv propA σ = μ ^ N * mpv propB σ := by
  refine ⟨fun N _ => ?_, ?_⟩
  · have h2 : (1 + 2 ^ N : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + 2 ^ N : ℕ) ≠ 0 by positivity)
    have h3 : (1 + 3 ^ N : ℂ) ≠ 0 := by
      exact_mod_cast (show (1 + 3 ^ N : ℕ) ≠ 0 by positivity)
    refine ⟨(1 + 2 ^ N) / (1 + 3 ^ N), div_ne_zero h2 h3, fun σ => ?_⟩
    rw [mpv_propA, mpv_propB, ← mul_assoc, div_mul_cancel₀ _ h3]
  · rintro ⟨μ, hμ⟩
    have h1 := hμ 1 one_pos fun _ => 0
    have h2 := hμ 2 two_pos fun _ => 0
    rw [mpv_propA, mpv_propB, mpv_propC_one] at h1
    rw [mpv_propA, mpv_propB, mpv_propC_two] at h2
    have h : (-25 / 8 : ℂ) = 0 := by
      linear_combination h2 - (50 / 144 * (12 * μ + 9)) * h1
    norm_num at h

/-! ### Equal states and `IsIrreducibleForm` do not give a `ℤ_m`-gauge -/

namespace ArbitraryExamples

variable {d D : ℕ}

/-- The tensor whose letter `i₀` is `M` and whose other letters vanish. -/
def letterTensor (i₀ : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) : MPSTensor d D :=
  fun i => if i = i₀ then M else 0

theorem evalWord_letterTensor (i₀ : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)) :
    Kraus.evalWord (letterTensor i₀ M) w = if ∀ i ∈ w, i = i₀ then M ^ w.length else 0 := by
  induction w with
  | nil => simp
  | cons j w ih =>
    rw [Kraus.evalWord_cons, ih, letterTensor]
    by_cases hj : j = i₀
    · subst hj
      by_cases hw : ∀ i ∈ w, i = j
      · simp [pow_succ']
      · simp [hw]
    · simp [hj]

theorem mpv_letterTensor (i₀ : Fin d) (M : Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (σ : Fin N → Fin d) :
    mpv (letterTensor i₀ M) σ = if ∀ i ∈ List.ofFn σ, i = i₀ then (M ^ N).trace else 0 := by
  rw [mpv_eq, coeff_eq, evalWord_letterTensor, List.length_ofFn]
  split_ifs <;> simp

/-- The `1 × 1` block with letter `i₀` equal to `1` and the other letters zero has period one. -/
theorem isPeriodic_one_letterTensor_one (i₀ : Fin d) :
    IsPeriodic 1 (letterTensor i₀ (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  have hMap : Kraus.transferMap (letterTensor i₀ (1 : Matrix (Fin 1) (Fin 1) ℂ)) =
      LinearMap.id := by
    refine LinearMap.ext fun X => ?_
    rw [Kraus.transferMap_apply, Finset.sum_eq_single i₀
      (fun i _ hi => by simp [letterTensor, hi]) (by simp)]
    simp [letterTensor]
  have hNormal := isNormalTensor_of_bondDim_one_of_transferMap_eq_id _ hMap
  apply (IsPeriodic.one_iff_primitive _).2
  refine ⟨hNormal.no_invariant_proj, ?_, hNormal.primitive_transfer⟩
  unfold IsLeftCanonical Kraus.IsTP
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [letterTensor, hi]) (by simp)]
  simp [letterTensor]

/-- The nilpotent `E₀₁`. -/
noncomputable def jordanE (hD : 2 ≤ D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.single ⟨0, by omega⟩ ⟨1, hD⟩ 1

theorem jordanE_mul_self (hD : 2 ≤ D) : jordanE hD * jordanE hD = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ (by simp [Fin.ext_iff]) _

theorem one_add_jordanE_pow (hD : 2 ≤ D) (m : ℕ) :
    (1 + jordanE hD) ^ m = 1 + (m : ℂ) • jordanE hD := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, jordanE_mul_self, smul_zero,
      add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem trace_one_add_jordanE_pow (hD : 2 ≤ D) (m : ℕ) : ((1 + jordanE hD) ^ m).trace = D := by
  rw [one_add_jordanE_pow, Matrix.trace_add, Matrix.trace_smul, jordanE,
    Matrix.trace_single_eq_of_ne _ _ _ (by simp [Fin.ext_iff]), Matrix.trace_one]
  simp

/-- An irreducible form of a tensor with the states of `D` copies of a `1 × 1` block with letter
`i₀` equal to `1`: `D` such blocks of period one and weight one. -/
noncomputable def irreducibleFormOfMpvEq {X : MPSTensor d D} (i₀ : Fin d)
    (hX : ∀ {N : ℕ} (σ : Fin N → Fin d),
      mpv X σ = if ∀ i ∈ List.ofFn σ, i = i₀ then (D : ℂ) else 0) :
    IsIrreducibleForm X where
  r := D
  dim := fun _ => 1
  blocks := fun _ => letterTensor i₀ 1
  μ := fun _ => 1
  period := fun _ => 1
  periodic := fun _ => isPeriodic_one_letterTensor_one i₀
  weight_pos := fun _ => by simp
  sameMPV := fun N σ => by
    rw [hX, mpv_toTensorFromBlocks_eq_sum]
    simp only [one_pow, one_smul, mpv_letterTensor]
    split_ifs <;> simp

/-- No `ℤ_m`-gauge equivalence relates `1 + E₀₁` to `1` on the letter `i₀`. -/
theorem not_zGaugeEquiv_letterTensor (i₀ : Fin d) (hD : 2 ≤ D) {m : ℕ} (hm : 0 < m) :
    ¬ ZGaugeEquiv m (letterTensor i₀ (1 + jordanE hD)) (letterTensor i₀ 1) := by
  rintro ⟨G, Z, hZm, hcomm, hconj⟩
  have h1 : Z * (1 + jordanE hD) = 1 := by
    have h := hconj i₀
    simp only [letterTensor, ↓reduceIte, Matrix.mul_one, Units.mul_inv] at h
    exact h
  have hc : Commute Z (1 + jordanE hD) := by
    have h := hcomm i₀
    simp only [letterTensor, ↓reduceIte] at h
    exact h
  have h := hc.mul_pow m
  rw [h1, one_pow, hZm, one_mul, one_add_jordanE_pow] at h
  have h01 := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, hD⟩
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [jordanE, hm'.symm] at h01

end ArbitraryExamples

open ArbitraryExamples in
/-- **For every `d ≥ 1` and `D ≥ 2`, equal states and `IsIrreducibleForm` do not give a
`ℤ_m`-gauge.** `X` with letter `0` equal to `1 + E₀₁` and `Y` with letter `0`
equal to `1`, all other letters zero, both satisfy `IsIrreducibleForm` (`D` blocks `(1)` on the
letter `0`, of period one and weight one) and have the same states, but no `ℤ_m`-gauge equivalence
relates them. For one letter and bond dimension two this is the Jordan block `X = [[1, 1], [0, 1]]`
and the identity. The source theorem (arXiv:1708.00029, `thm:bdequal`) is not affected: its
irreducible form is a block sum, which `X` is not, and block sums with the same states are gauge
equivalent (`MPSTensor.gaugeEquiv_of_sameMPV_of_isGaugeRelated_toTensorFromBlocks`). -/
theorem not_forall_exists_zGaugeEquiv_of_isIrreducibleForm_of_sameMPV {d D : ℕ} (hd : 0 < d)
    (hD : 2 ≤ D) :
    ¬ ∀ {X Y : MPSTensor d D}, IsIrreducibleForm X → IsIrreducibleForm Y → SameMPV X Y →
      ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m X Y := by
  intro h
  have hX : ∀ {N : ℕ} (σ : Fin N → Fin d), mpv (letterTensor ⟨0, hd⟩ (1 + jordanE hD)) σ =
      if ∀ i ∈ List.ofFn σ, i = ⟨0, hd⟩ then (D : ℂ) else 0 := fun σ => by
    rw [mpv_letterTensor, trace_one_add_jordanE_pow]
  have hY : ∀ {N : ℕ} (σ : Fin N → Fin d), mpv (letterTensor ⟨0, hd⟩ 1) σ =
      if ∀ i ∈ List.ofFn σ, i = ⟨0, hd⟩ then (D : ℂ) else 0 := fun σ => by
    rw [mpv_letterTensor, one_pow, Matrix.trace_one, Fintype.card_fin]
  obtain ⟨m, hm, hZ⟩ := h (irreducibleFormOfMpvEq _ hX) (irreducibleFormOfMpvEq _ hY)
    fun N σ => by rw [hX, hY]
  exact not_zGaugeEquiv_letterTensor _ hD hm hZ

end MPSTensor

/-! ### The long-word identity needs the block to be last in both reductions -/

namespace MultiBlockExamples

namespace Worked

open MPSTensor

/-- `ĝ' = diag(1, 1, Y⁻¹) ĝ`: the second reduction of the worked example, with its `C₁'` rows
multiplied by `Y⁻¹`, so that it reduces onto the first family `(C₁, C₂)`. -/
def gtOneInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![3, 2, 2, 3; -2, -3, -1, 1; 2, 2, 1, 1; 0, 0, 0, 1]

/-- `ĝ'⁻¹ = ĝ⁻¹ diag(1, 1, Y)`. -/
def gtOneInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, 2, 4, -3; 0, -1, -1, 2; 2, -2, -5, 1; 0, 0, 0, 1]

/-- `ĝ' B¹ ĝ'⁻¹`, `ĝ' B² ĝ'⁻¹`: block upper triangular in the order `(0, C₂, C₁)`. -/
def conjGtOne : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0, 2, 2, -1; 0, 1, 2, -2; 0, 0, 0, 1; 0, 0, 1, 0],
    !![0, 2, 3, -2; 0, 2, 1, -2; 0, 0, 1, 0; 0, 0, 0, 0]]

theorem conjGtOne_eq (i : Fin 2) : gtOneInt * tensorBInt i * gtOneInvInt = conjGtOne i := by
  fin_cases i <;> decide +kernel

/-- **The reduction `ĝ' = diag(1, 1, Y⁻¹) h P g₀`** of the worked example in the order
`(0, C₂, C₁)`, onto the same family `(C₁, C₂)` as `redG`. -/
noncomputable def redGtOne : MultiBlockCompression tensorB labels blocks :=
  MultiBlockCompression.ofRing (Int.castRingHom ℂ) ordGt tauGt
    (gaugeOfRingMatrix _ tauGt gtOneInt gtOneInvInt (by decide +kernel) (by decide +kernel))
    conjGtOne
    (fun i => by
      rw [conjMatrix_gaugeOfRingMatrix (Int.castRingHom ℂ) tauGt (by decide +kernel)
        (by decide +kernel) (tensorB_eq_complexOfRing i), conjGtOne_eq])
    blocksInt blocks_eq_complexOfRing (fun i x y h => by revert i x y; decide +kernel)
    (fun i s p q => by
      obtain ⟨s, hs⟩ := s
      obtain rfl : hs = Finset.mem_univ s := rfl
      revert p q
      fin_cases s <;> fin_cases i <;> intro p q <;> fin_cases p <;> fin_cases q <;> decide +kernel)
    (by decide +kernel)

theorem gauge_redGtOne :
    redGtOne.gauge = gaugeOfMatrix tauGt (toC gtOneInt) (toC gtOneInvInt)
      (complexOfRing_mul_eq_one _ (by decide +kernel))
      (complexOfRing_mul_eq_one _ (by decide +kernel)) :=
  rfl

theorem leftRow_redGtOne (b : BlockIndex labels 1) :
    redGtOne.leftRow b = toC (gtOneInt.submatrix (fun i => tauGt ⟨b, i⟩) id) := by
  rw [leftRow_gaugeOfMatrix redGtOne gauge_redGtOne b]
  rfl

/-- The reading map of `C₂` in the reduction `ĝ'` is the `C₂` row of `ĝ`. -/
theorem left_redGtOne_slotC2 : redGtOne.left slotC2 = toC !![-2, -3, -1, 1] :=
  (leftRow_redGtOne (Sum.inl slotC2)).trans (congrArg toC
    (Matrix.ext fun i j => by fin_cases i; fin_cases j <;> decide))

theorem left_redG_slotC2 : redG.left slotC2 = toC !![0, -1, 0, 1] :=
  redG_spec.2.2.2.2.2.2.2.2.1

/-- The hypotheses of the two long-word theorems that hold: the blocks are irreducible with a
nonzero letter, `C₂`
occurs once up to gauge, and `C₂` is the last slot of `g = g₀`. -/
theorem hypotheses_slotC2 :
    (∀ s ∈ labels, Matrix.IsIrreducibleAction (blocks s)) ∧
      (∀ s ∈ labels, ∃ i, blocks s i ≠ 0) ∧
      (∀ t ∈ labels, IsGaugeRelated (blocks slotC2.1) (blocks t) → t = slotC2.1) ∧
      ∀ b, redG.ord b ≤ redG.ord (Sum.inl slotC2) := by
  refine ⟨fun s hs => isIrreducibleAction_of_isNormal _ (isNormal_blocks s hs) (dims_pos s hs),
    fun s hs => ?_, fun t _ h => ?_, fun b => ?_⟩
  · have : NeZero (dims s) := ⟨(dims_pos s hs).ne'⟩
    exact exists_ne_zero_of_isNormal (isNormal_blocks s hs)
  · fin_cases t
    · exact absurd h.dim_eq (by decide)
    · rfl
  · change ordG b ≤ ordG (Sum.inl slotC2)
    revert b
    decide

/-- **No long-word identity for `C₂` at any length** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.16): for every `n` and every `c`,
`Ŵ_{C₂} B^w ≠ c W_{C₂} B^w` for the word `w = 1 ⋯ 1` of length `n`, since
`W_{C₂} B^w V_{C₁} = 0` while `Ŵ_{C₂} B^w V_{C₁} = (-1, 1) C₁^w` and `C₁¹ = σ_x` is invertible. -/
theorem left_mul_evalWord_replicate_ne_smul (n : ℕ) (c : ℂ) :
    redGtOne.left slotC2 * Kraus.evalWord tensorB (List.replicate n 0) ≠
      c • (redG.left slotC2 * Kraus.evalWord tensorB (List.replicate n 0)) := by
  set V : Matrix (Fin 4) (Fin 2) ℂ := toC !![1, -1; 0, 1; -1, -1; 0, 1] with hV
  set sx : Matrix (Fin 2) (Fin 2) ℂ := toC !![0, 1; 1, 0] with hsx
  have hBV : tensorB 0 * V = V * sx := by
    rw [hV, hsx, tensorB_eq_complexOfRing, ← complexOfRing_mul, ← complexOfRing_mul]
    exact congrArg toC (by decide +kernel)
  have hpow : ∀ n, Kraus.evalWord tensorB (List.replicate n 0) * V = V * sx ^ n := by
    intro n
    induction n with
    | zero => rw [List.replicate_zero, Kraus.evalWord_nil, pow_zero, Matrix.one_mul,
        Matrix.mul_one]
    | succ n ih =>
      rw [List.replicate_succ, Kraus.evalWord_cons, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
        hBV, Matrix.mul_assoc, pow_succ']
  have hsx2 : sx * sx = 1 := by
    rw [hsx, ← complexOfRing_mul, show (!![0, 1; 1, 0] * !![0, 1; 1, 0] :
      Matrix (Fin 2) (Fin 2) ℤ) = 1 by decide +kernel, complexOfRing_one]
  have hsxn : sx ^ n * sx ^ n = 1 := by
    rw [← (Commute.refl sx).mul_pow, hsx2, one_pow]
  have hWV : redGtOne.left slotC2 * V = toC !![-1, 1] := by
    rw [left_redGtOne_slotC2, hV]
    change (toC !![(-2 : ℤ), -3, -1, 1] : Matrix (Fin 1) (Fin 4) ℂ) *
      toC !![(1 : ℤ), -1; 0, 1; -1, -1; 0, 1] = (toC !![(-1 : ℤ), 1] : Matrix (Fin 1) (Fin 2) ℂ)
    rw [← complexOfRing_mul]
    exact congrArg toC (by decide +kernel)
  have hW0V : redG.left slotC2 * V = 0 := by
    rw [left_redG_slotC2, hV]
    change (toC !![(0 : ℤ), -1, 0, 1] : Matrix (Fin 1) (Fin 4) ℂ) *
      toC !![(1 : ℤ), -1; 0, 1; -1, -1; 0, 1] = (0 : Matrix (Fin 1) (Fin 2) ℂ)
    rw [← complexOfRing_mul,
      show (!![0, -1, 0, 1] * !![1, -1; 0, 1; -1, -1; 0, 1] : Matrix (Fin 1) (Fin 2) ℤ) = 0 by
        decide +kernel]
    exact Matrix.map_zero _ (map_zero _)
  intro h
  have h' : redGtOne.left slotC2 * Kraus.evalWord tensorB (List.replicate n 0) * V =
      c • (redG.left slotC2 * Kraus.evalWord tensorB (List.replicate n 0) * V) := by
    rw [h, Matrix.smul_mul]
  rw [Matrix.mul_assoc, hpow, ← Matrix.mul_assoc, hWV, Matrix.mul_assoc
    (redG.left slotC2), hpow, ← Matrix.mul_assoc, hW0V, Matrix.zero_mul, smul_zero] at h'
  have h4 : (toC !![(-1 : ℤ), 1] : Matrix (Fin 1) (Fin 2) ℂ) * sx ^ n = 0 := h'
  have h3 : (toC !![(-1 : ℤ), 1] : Matrix (Fin 1) (Fin 2) ℂ) = 0 := by
    rw [← Matrix.mul_one (toC !![(-1 : ℤ), 1]), ← hsxn, ← Matrix.mul_assoc, h4,
      Matrix.zero_mul]
  have h00 := congrFun (congrFun h3 0) 0
  simp at h00

/-- **The reading maps of a block last in only one reduction need not be proportional**
(*The asymmetric fundamental
theorem of matrix product states*, Example 6.16): in the worked example all
hypotheses of `MPSTensor.MultiBlockCompression.exists_left_eq_smul_of_last`
for `P = g₀`, `Q = ĝ'` and the block `C₂` hold except that `C₂` is not last in `Q`, and
`Ŵ_{C₂} = (-2, -3, -1, 1)` is not a multiple of `W_{C₂} = (0, -1, 0, 1)`. -/
theorem not_exists_left_eq_smul_of_last_in_one_reduction :
    (∀ s ∈ labels, Matrix.IsIrreducibleAction (blocks s)) ∧
      (∀ s ∈ labels, ∃ i, blocks s i ≠ 0) ∧
      (∀ t ∈ labels, IsGaugeRelated (blocks slotC2.1) (blocks t) → t = slotC2.1) ∧
      (∀ b, redG.ord b ≤ redG.ord (Sum.inl slotC2)) ∧
      ¬ ∃ c : ℂ, c ≠ 0 ∧ redGtOne.left slotC2 = c • redG.left slotC2 := by
  refine ⟨hypotheses_slotC2.1, hypotheses_slotC2.2.1, hypotheses_slotC2.2.2.1,
    hypotheses_slotC2.2.2.2, ?_⟩
  rintro ⟨c, -, hc⟩
  have h := left_mul_evalWord_replicate_ne_smul 0 c
  rw [List.replicate_zero, Kraus.evalWord_nil, Matrix.mul_one, Matrix.mul_one] at h
  exact h hc

/-- **Long words do not restore proportionality for a block last in only one reduction**
(*The asymmetric fundamental
theorem of matrix product states*, Example 6.16): in the worked example all
hypotheses of
`MPSTensor.MultiBlockCompression.exists_left_mul_evalWord_eq_smul_of_last`
for `P = g₀`, `Q = ĝ'` and the block `C₂` hold (with `C₂` even the last slot of `P`) except that
`C₂` is not the last block slot of `Q`, and no nonzero `c` gives
`Ŵ_{C₂} B^w = c W_{C₂} B^w` for all
words with `|w| ≥ z = 1`. -/
theorem not_exists_left_mul_evalWord_eq_smul_of_last_in_one_reduction :
    (∀ s ∈ labels, Matrix.IsIrreducibleAction (blocks s)) ∧
      (∀ s ∈ labels, ∃ i, blocks s i ≠ 0) ∧
      (∀ t ∈ labels, IsGaugeRelated (blocks slotC2.1) (blocks t) → t = slotC2.1) ∧
      (∀ b, redG.ord b ≤ redG.ord (Sum.inl slotC2)) ∧
      ¬ ∃ c : ℂ, c ≠ 0 ∧ ∀ w : List (Fin 2), redG.z ≤ w.length →
        redGtOne.left slotC2 * Kraus.evalWord tensorB w =
          c • (redG.left slotC2 * Kraus.evalWord tensorB w) := by
  refine ⟨hypotheses_slotC2.1, hypotheses_slotC2.2.1, hypotheses_slotC2.2.2.1,
    hypotheses_slotC2.2.2.2, ?_⟩
  rintro ⟨c, -, hc⟩
  exact left_mul_evalWord_replicate_ne_smul redG.z c (hc _ (List.length_replicate ..).ge)

end Worked

end MultiBlockExamples

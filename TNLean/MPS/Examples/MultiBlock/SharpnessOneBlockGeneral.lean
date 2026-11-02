/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlock

/-!
# Sharpness of the one-block bound for every number of zero slots

*The asymmetric fundamental theorem of matrix product states*, Example 6.10: the tensor `B` on
`ℂ^{1+z}` with one letter, `B e₀ = e₀` and `B e_j = e_{j-1}` for `1 ≤ j ≤ z`, and the block
`C = (1)`. The identity gauge puts the block first, `W = e₀ᵀ`, `V = e₀`; the gauge `g_tilde` with
`g_tilde⁻¹ = (f₁, …, f_z, e₀)`, `f_j = e_{j-1} - e_j`, puts the block last,
`W_tilde = e₀ᵀ + ⋯ + e_zᵀ`, `V_tilde = e₀`. Then `W Bⁿ = ∑_{j ≤ min(n,z)} e_jᵀ` and
`W_tilde Bⁿ = ∑_{j ≤ z} e_jᵀ` are proportional exactly when `n ≥ z`, so the bound `|w| ≥ D_B - D_C`
of the one-block theorem cannot be lowered for any `z ≥ 1`. The cases `z = 1, 2` of
`TNLean.MPS.Examples.MultiBlock.SharpnessOneBlock` are instances (`tensorBGen_one`,
`tensorBGen_two`).

## Main results

* `MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_first`,
  `MultiBlockExamples.SharpnessOneBlock.exists_multiBlockCompression_block_last`,
  `MultiBlockExamples.SharpnessOneBlock.rowE0_mul_pow_and_rowOnes_mul_pow`,
  `MultiBlockExamples.SharpnessOneBlock.exists_rowOnes_mul_pow_eq_smul_iff`,
  `MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul`,
  `MultiBlockExamples.SharpnessOneBlock.pow_mul_right_eq_of_eq_colE0`: the two reductions, the
  powers, and the failure at `|w| = z - 1`.

## References

*The asymmetric fundamental theorem of matrix product states*, Example 6.10; blueprint
`cor:asym_uniq_one_block`, *Bare uniqueness at the ends of the flag; the one-block theorem*.
-/

open scoped Matrix

namespace MultiBlockExamples.SharpnessOneBlock

open MPSTensor

/-! ### Every number of zero slots

*The asymmetric fundamental theorem of matrix product states*, Example 6.10: `B` on `ℂ^{1+z}` with
`B e₀ = e₀` and `B e_j = e_{j-1}` for `1 ≤ j ≤ z`, and the block `C = (1)`. The identity gauge puts
the block first, `W = e₀ᵀ`, `V = e₀`; the gauge `g_tilde` with `g_tilde⁻¹ = (f₁, …, f_z, e₀)`,
`f_j = e_{j-1} - e_j`, puts the block last, `W_tilde = e₀ᵀ + ⋯ + e_zᵀ`, `V_tilde = e₀`. Then
`W Bⁿ = ∑_{j ≤ min(n,z)} e_jᵀ` and `W_tilde Bⁿ = ∑_{j ≤ z} e_jᵀ`, proportional exactly when `n ≥ z`:
the bound `|w| ≥ D_B - D_C` of the one-block theorem cannot be lowered for any `z ≥ 1`. The cases
`z = 1, 2` above are instances (`tensorBGen_one`, `tensorBGen_two`). -/

section General

variable (z : ℕ)

/-- **The tensor** (*The asymmetric fundamental theorem of matrix product states*, Example 6.10):
`B` on `ℂ^{1+z}` with `B e₀ = e₀`, `B e_j = e_{j-1}`. -/
noncomputable def tensorBGen : MPSTensor 1 (1 + z) := fun _ =>
  Matrix.of fun i j => if (i.val = 0 ∧ j.val = 0) ∨ j.val = i.val + 1 then 1 else 0

/-- The row `e₀ᵀ`. -/
noncomputable def rowE0 : Matrix (Fin 1) (Fin (1 + z)) ℂ :=
  Matrix.of fun _ j => if j.val = 0 then 1 else 0

/-- The row `e₀ᵀ + ⋯ + e_zᵀ`. -/
noncomputable def rowOnes : Matrix (Fin 1) (Fin (1 + z)) ℂ := Matrix.of fun _ _ => 1

/-- The column `e₀`. -/
noncomputable def colE0 : Matrix (Fin (1 + z)) (Fin 1) ℂ :=
  Matrix.of fun i _ => if i.val = 0 then 1 else 0

/-- The case `z = 1` is the tensor `[[1, 1], [0, 0]]`. -/
theorem tensorBGen_one : tensorBGen 1 = tensorB := by
  funext a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensorBGen, tensorB, bInt, complexOfRing_apply]

/-- The case `z = 2` is the tensor `[[1, 1, 0], [0, 0, 1], [0, 0, 0]]`. -/
theorem tensorBGen_two : tensorBGen 2 = tensorBTwo := by
  funext a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensorBGen, tensorBTwo, bIntTwo, complexOfRing_apply]

variable {z}

/-- A sum against the indicator of one coordinate value. -/
theorem sum_mul_ite_val {n : ℕ} (f : Fin n → ℂ) (k : ℕ) :
    ∑ b : Fin n, f b * (if b.val = k then 1 else 0) = if h : k < n then f ⟨k, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨k, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      have hbk : b.val ≠ k := fun h' => hb (Fin.ext h')
      simp [hbk]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun b _ => ?_
    have hbk : b.val ≠ k := fun h' => h (by rw [← h']; exact b.isLt)
    simp [hbk]
/-- A row times `B`: `(r B)_j = r_0` for `j = 0` and `r_{j-1}` for `j ≥ 1`. -/
theorem mul_tensorBGen_apply (r : Matrix (Fin 1) (Fin (1 + z)) ℂ) (j : Fin (1 + z)) :
    (r * tensorBGen z 0) 0 j =
      if j.val = 0 then r 0 ⟨0, by omega⟩ else r 0 ⟨j.val - 1, by omega⟩ := by
  rw [Matrix.mul_apply]
  have h : ∀ c : Fin (1 + z), r 0 c * tensorBGen z 0 c j =
      r 0 c * (if j.val = 0 then 1 else 0) * (if c.val = 0 then 1 else 0) +
        r 0 c * (if j.val = 0 then 0 else 1) * (if c.val = j.val - 1 then 1 else 0) := by
    intro c
    simp only [tensorBGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h, Finset.sum_add_distrib, sum_mul_ite_val]
  split_ifs <;> simp_all
  omega

/-- `r Bⁿ` for the row `e₀ᵀ`: `∑_{j ≤ min(n,z)} e_jᵀ`. -/
theorem rowE0_mul_pow (n : ℕ) :
    rowE0 z * tensorBGen z 0 ^ n = Matrix.of (fun _ j => if j.val ≤ n then 1 else 0) := by
  induction n with
  | zero =>
    ext i j
    simp [rowE0]
  | succ n ih =>
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [pow_succ, ← Matrix.mul_assoc, mul_tensorBGen_apply, ih]
    split_ifs <;> simp_all

/-- `r Bⁿ` for the row of ones: the row of ones. -/
theorem rowOnes_mul_pow (n : ℕ) : rowOnes z * tensorBGen z 0 ^ n = rowOnes z := by
  induction n with
  | zero => rw [pow_zero, Matrix.mul_one]
  | succ n ih =>
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [pow_succ, ← Matrix.mul_assoc, ih, mul_tensorBGen_apply]
    split_ifs <;> simp [rowOnes]

/-- **The reading maps after words** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.10): `W Bⁿ = ∑_{j ≤ min(n,z)} e_jᵀ` and `W_tilde Bⁿ = ∑_{j ≤ z} e_jᵀ` for every `n ≥ 0`.
-/
theorem rowE0_mul_pow_and_rowOnes_mul_pow (n : ℕ) :
    rowE0 z * tensorBGen z 0 ^ n = Matrix.of (fun _ j => if j.val ≤ n then 1 else 0) ∧
    rowOnes z * tensorBGen z 0 ^ n = rowOnes z :=
  ⟨rowE0_mul_pow n, rowOnes_mul_pow n⟩

/-- **Proportional exactly from length `z` on** (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10): `W_tilde Bⁿ = λ W Bⁿ` for some `λ` iff `n ≥ z`. -/
theorem exists_rowOnes_mul_pow_eq_smul_iff (n : ℕ) :
    (∃ c : ℂ, rowOnes z * tensorBGen z 0 ^ n = c • (rowE0 z * tensorBGen z 0 ^ n)) ↔ z ≤ n := by
  rw [rowE0_mul_pow, rowOnes_mul_pow]
  constructor
  · rintro ⟨c, hc⟩
    by_contra hlt
    have := congrFun (congrFun hc 0) ⟨z, by omega⟩
    simp [rowOnes, show ¬ z ≤ n by omega] at this
  · intro hzn
    refine ⟨1, ?_⟩
    ext i j
    have : j.val ≤ n := by have := j.isLt; omega
    simp [rowOnes, this]

theorem evalWord_replicate (n : ℕ) :
    Kraus.evalWord (tensorBGen z) (List.replicate n 0) = tensorBGen z 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, Kraus.evalWord_cons, ih, pow_succ']

/-! #### The two reductions for every `z` -/

theorem slotSize_unit (b : BlockIndex oneSlot z) : slotSize (fun _ : Unit => 1) b = 1 := by
  cases b <;> rfl

/-- The bond coordinates of a reduction with one-dimensional slots, read off its order. -/
def coordOfOrd (ord : BlockIndex oneSlot z ≃ Fin (1 + z)) :
    BlockSpace (fun _ : Unit => 1) oneSlot z ≃ Fin (1 + z) where
  toFun x := ord x.1
  invFun n := ⟨ord.symm n, ⟨0, by rw [slotSize_unit]; exact Nat.one_pos⟩⟩
  left_inv x := by
    obtain ⟨b, p⟩ := x
    have hp : p.val = 0 := by have h1 := p.isLt; have h2 := slotSize_unit b; omega
    refine Sigma.ext (ord.symm_apply_apply b)
      ((Fin.heq_ext_iff (congrArg (slotSize (fun _ : Unit => 1)) (ord.symm_apply_apply b))).2 ?_)
    exact hp.symm
  right_inv n := by simp

/-- A reduction of `B` onto `C = (1)` with `z` zero slots from an explicit gauge `G` with
`G B G⁻¹ = K` upper triangular, `1` at the position of the block and `0` at the zero slots
(blueprint `thm:asym_multiblock`, *Multi-block asymmetric compression theorem*, clauses (i)–(iii)).
-/
noncomputable def compressionGen (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (G Ginv K : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (hK : G * tensorBGen z 0 * Ginv = K) (htri : ∀ a b, b < a → K a b = 0)
    (hblock : K (ord (Sum.inl oneSlotMem)) (ord (Sum.inl oneSlotMem)) = 1)
    (hzero : ∀ t, K (ord (Sum.inr t)) (ord (Sum.inr t)) = 0) :
    MultiBlockCompression (tensorBGen z) oneSlot blockC where
  z := z
  ord := ord
  gauge := gaugeOfMatrix (coordOfOrd ord) G Ginv hG hG'
  triangular i x y hxy := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rw [conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    exact htri _ _ hxy
  matched i s := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : s = oneSlotMem := eq_oneSlotMem s
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    simpa [blockC, coordOfOrd] using hblock
  unmatched i t := by
    obtain rfl : i = 0 := Subsingleton.elim i 0
    ext p q
    obtain rfl : p = 0 := Subsingleton.elim p 0
    obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [Matrix.blockDiag'_apply, conjMatrix_gaugeOfMatrix, Matrix.submatrix_apply, hK]
    exact hzero t

theorem gauge_compressionGen (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (G Ginv K : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (hG : G * Ginv = 1) (hG' : Ginv * G = 1)
    (hK : G * tensorBGen z 0 * Ginv = K) (htri : ∀ a b, b < a → K a b = 0)
    (hblock : K (ord (Sum.inl oneSlotMem)) (ord (Sum.inl oneSlotMem)) = 1)
    (hzero : ∀ t, K (ord (Sum.inr t)) (ord (Sum.inr t)) = 0) :
    (compressionGen ord G Ginv K hG hG' hK htri hblock hzero).gauge =
      gaugeOfMatrix (coordOfOrd ord) G Ginv hG hG' := rfl

theorem tensorBGen_apply (a b : Fin (1 + z)) :
    tensorBGen z 0 a b = if (a.val = 0 ∧ b.val = 0) ∨ b.val = a.val + 1 then 1 else 0 := rfl

theorem tensorBGen_tri (a b : Fin (1 + z)) (h : b < a) : tensorBGen z 0 a b = 0 := by
  rw [tensorBGen_apply, ite_eq_right]
  have := Fin.lt_def.1 h
  omega

/-- The order with the block first: the block at position `0`, the zero slot `t` at `t + 1`. -/
def firstOrdGen : BlockIndex oneSlot z ≃ Fin (1 + z) where
  toFun
    | Sum.inl _ => ⟨0, by omega⟩
    | Sum.inr t => ⟨t.val + 1, by have := t.isLt; omega⟩
  invFun n := if h : n.val = 0 then Sum.inl oneSlotMem else Sum.inr ⟨n.val - 1, by omega⟩
  left_inv b := by
    rcases b with s | t
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      simp
    · simp
  right_inv n := by
    by_cases h : n.val = 0
    · simp only [h, dite_true]
      ext
      simp [h]
    · simp only [h, dite_false]
      ext
      simp only
      omega

/-- **The reduction `g = 1`** with the block first (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10). -/
noncomputable def firstCompressionGen : MultiBlockCompression (tensorBGen z) oneSlot blockC :=
  compressionGen firstOrdGen 1 1 (tensorBGen z 0) (Matrix.mul_one 1) (Matrix.mul_one 1)
    (by rw [Matrix.one_mul, Matrix.mul_one]) tensorBGen_tri
    (by simp [tensorBGen_apply, firstOrdGen])
    (fun t => by
      rw [tensorBGen_apply, ite_eq_right]
      simp [firstOrdGen])

/-- The order with the block last: the zero slot `t` at position `t`, the block at `z`. -/
def lastOrdGen : BlockIndex oneSlot z ≃ Fin (1 + z) where
  toFun
    | Sum.inl _ => ⟨z, by omega⟩
    | Sum.inr t => ⟨t.val, by have := t.isLt; omega⟩
  invFun n := if h : n.val < z then Sum.inr ⟨n.val, h⟩ else Sum.inl oneSlotMem
  left_inv b := by
    rcases b with s | t
    · obtain rfl : s = oneSlotMem := eq_oneSlotMem s
      simp
    · simp [t.isLt]
  right_inv n := by
    by_cases h : n.val < z
    · simp [h]
    · simp only [h, dite_false]
      ext
      simp only
      have := n.isLt
      omega

/-- `g_tilde`: the row `z` is `e₀ᵀ + ⋯ + e_zᵀ`, the row `p < z` is `-(e_{p+1}ᵀ + ⋯ + e_zᵀ)`. -/
noncomputable def gGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun a b => if a.val = z then 1 else if a.val < b.val then -1 else 0

/-- `g_tilde⁻¹ = (f₁, …, f_z, e₀)`, `f_j = e_{j-1} - e_j`. -/
noncomputable def gInvGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun b c =>
    if c.val = z then (if b.val = 0 then 1 else 0)
    else if b.val = c.val then 1 else if b.val = c.val + 1 then -1 else 0

/-- `g_tilde B g_tilde⁻¹`: `1` at `(z, z)` and at `(p - 1, p)` for `1 ≤ p < z`. -/
noncomputable def kGen : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ :=
  Matrix.of fun a b => if (a.val = z ∧ b.val = z) ∨ (b.val = a.val + 1 ∧ b.val < z) then 1 else 0

theorem gGen_mul_gInvGen : gGen (z := z) * gInvGen = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have h : ∀ b : Fin (1 + z), gGen a b * gInvGen b c =
      gGen a b * (if c.val = z then 1 else 0) * (if b.val = 0 then 1 else 0) +
        gGen a b * (if c.val = z then 0 else 1) * (if b.val = c.val then 1 else 0) -
        gGen a b * (if c.val = z then 0 else 1) * (if b.val = c.val + 1 then 1 else 0) := by
    intro b
    simp only [gInvGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_mul_ite_val]
  simp only [gGen, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  have := a.isLt
  have := c.isLt
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem gGen_mul_tensorBGen : gGen (z := z) * tensorBGen z 0 = kGen * gGen := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have h1 : ∀ c : Fin (1 + z), gGen a c * tensorBGen z 0 c b =
      gGen a c * (if b.val = 0 then 1 else 0) * (if c.val = 0 then 1 else 0) +
        gGen a c * (if b.val = 0 then 0 else 1) * (if c.val = b.val - 1 then 1 else 0) := by
    intro c
    simp only [tensorBGen_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have h2 : ∀ c : Fin (1 + z), kGen a c * gGen c b =
      gGen c b * (if a.val = z then 1 else 0) * (if c.val = z then 1 else 0) +
        gGen c b * (if a.val + 1 < z then 1 else 0) * (if c.val = a.val + 1 then 1 else 0) := by
    intro c
    simp only [kGen, Matrix.of_apply]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h1, h2, Finset.sum_add_distrib, sum_mul_ite_val]
  simp only [gGen, Matrix.of_apply]
  have := a.isLt
  have := b.isLt
  split_ifs <;> first | ring1 | (exfalso; omega)

theorem gGen_conj : gGen (z := z) * tensorBGen z 0 * gInvGen = kGen := by
  rw [gGen_mul_tensorBGen, Matrix.mul_assoc, gGen_mul_gInvGen, Matrix.mul_one]

/-- **The reduction `g_tilde`** with the block last (*The asymmetric fundamental theorem of matrix
product states*, Example 6.10). -/
noncomputable def lastCompressionGen : MultiBlockCompression (tensorBGen z) oneSlot blockC :=
  compressionGen lastOrdGen gGen gInvGen kGen gGen_mul_gInvGen
    (mul_eq_one_comm.1 gGen_mul_gInvGen) gGen_conj
    (fun a b h => by
      have := Fin.lt_def.1 h
      simp only [kGen, Matrix.of_apply]
      rw [ite_eq_right]
      omega)
    (by simp [kGen, lastOrdGen])
    (fun t => by
      simp only [kGen, Matrix.of_apply, lastOrdGen, Equiv.coe_fn_mk]
      rw [ite_eq_right]
      have := t.isLt
      omega)

theorem gauge_firstCompressionGen :
    (firstCompressionGen (z := z)).gauge =
      gaugeOfMatrix (coordOfOrd firstOrdGen) 1 1 (Matrix.mul_one 1) (Matrix.mul_one 1) := rfl

theorem gauge_lastCompressionGen :
    (lastCompressionGen (z := z)).gauge =
      gaugeOfMatrix (coordOfOrd lastOrdGen) gGen gInvGen gGen_mul_gInvGen
        (mul_eq_one_comm.1 gGen_mul_gInvGen) := rfl

theorem coordOfOrd_apply (ord : BlockIndex oneSlot z ≃ Fin (1 + z))
    (x : BlockSpace (fun _ : Unit => 1) oneSlot z) : coordOfOrd ord x = ord x.1 := rfl

theorem firstOrdGen_inl (s : {s // s ∈ oneSlot}) : (firstOrdGen (z := z) (Sum.inl s)).val = 0 :=
  rfl

theorem firstOrdGen_inr (t : Fin z) : (firstOrdGen (z := z) (Sum.inr t)).val = t.val + 1 := rfl

theorem lastOrdGen_inl (s : {s // s ∈ oneSlot}) : (lastOrdGen (z := z) (Sum.inl s)).val = z := rfl

theorem lastOrdGen_inr (t : Fin z) : (lastOrdGen (z := z) (Sum.inr t)).val = t.val := rfl

/-- **The first reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.10): `g = 1` is a reduction onto `C = (1)` with the block first and `z` zero blocks, `W = e₀ᵀ`,
`V = e₀`; the zero slot at position `p` reads `e_pᵀ`. -/
theorem exists_multiBlockCompression_block_first :
    ∃ P : MultiBlockCompression (tensorBGen z) oneSlot blockC, P.z = z ∧
    (∀ b, P.ord (Sum.inl oneSlotMem) ≤ P.ord b) ∧
    P.left oneSlotMem = rowE0 z ∧ P.right oneSlotMem = colE0 z ∧
    ∀ t, P.leftRow (Sum.inr t) =
      Matrix.of fun _ j => if j.val = (P.ord (Sum.inr t)).val then 1 else 0 := by
  refine ⟨firstCompressionGen, rfl, fun b => ?_, ?_, ?_, fun t => ?_⟩
  · change firstOrdGen (Sum.inl oneSlotMem) ≤ firstOrdGen b
    rw [Fin.le_def]
    simp [firstOrdGen]
  · rw [← MultiBlockCompression.leftRow_inl,
      MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_firstCompressionGen]
    ext i j
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) (firstOrdGen (Sum.inl oneSlotMem)) j =
      rowE0 z i j
    simp only [Matrix.one_apply, Fin.ext_iff,
      firstOrdGen_inl, rowE0, Matrix.of_apply]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [← MultiBlockCompression.rightCol_inl,
      MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_firstCompressionGen]
    ext i j
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) i (firstOrdGen (Sum.inl oneSlotMem)) =
      colE0 z i j
    simp only [Matrix.one_apply, Fin.ext_iff,
      firstOrdGen_inl, colE0, Matrix.of_apply]
  · rw [MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_firstCompressionGen,
      show firstCompressionGen.ord = firstOrdGen from rfl]
    ext i j
    have ht : t.val < z := t.isLt
    change (1 : Matrix (Fin (1 + z)) (Fin (1 + z)) ℂ) ⟨t.val + 1, by omega⟩ j =
      (if j.val = t.val + 1 then 1 else 0)
    simp only [Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **The second reduction** (*The asymmetric fundamental theorem of matrix product states*, Example
6.10): `g_tilde` with `g_tilde⁻¹ = (f₁, …, f_z, e₀)`, `f_j = e_{j-1} - e_j`, is a reduction with the
block last, `W_tilde = e₀ᵀ + ⋯ + e_zᵀ`, `V_tilde = e₀`; the zero slot at position `p` has injection
`f_{p+1}`. -/
theorem exists_multiBlockCompression_block_last :
    ∃ Q : MultiBlockCompression (tensorBGen z) oneSlot blockC, Q.z = z ∧
    (∀ b, Q.ord b ≤ Q.ord (Sum.inl oneSlotMem)) ∧
    Q.left oneSlotMem = rowOnes z ∧ Q.right oneSlotMem = colE0 z ∧
    ∀ t, Q.rightCol (Sum.inr t) = Matrix.of fun i _ =>
      if i.val = (Q.ord (Sum.inr t)).val then 1
      else if i.val = (Q.ord (Sum.inr t)).val + 1 then -1 else 0 := by
  refine ⟨lastCompressionGen, rfl, fun b => ?_, ?_, ?_, fun t => ?_⟩
  · change lastOrdGen b ≤ lastOrdGen (Sum.inl oneSlotMem)
    rw [Fin.le_def]
    rcases b with s | t
    · simp [lastOrdGen]
    · simp only [lastOrdGen, Equiv.coe_fn_mk]
      exact t.isLt.le
  · rw [← MultiBlockCompression.leftRow_inl,
      MultiBlockExamples.leftRow_gaugeOfMatrix _ gauge_lastCompressionGen]
    ext i j
    change gGen (lastOrdGen (Sum.inl oneSlotMem)) j = rowOnes z i j
    simp only [gGen, Matrix.of_apply,
      lastOrdGen_inl, rowOnes]
    simp
  · rw [← MultiBlockCompression.rightCol_inl,
      MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_lastCompressionGen]
    ext i j
    change gInvGen i (lastOrdGen (Sum.inl oneSlotMem)) = colE0 z i j
    simp only [gInvGen, Matrix.of_apply,
      lastOrdGen_inl, colE0]
    simp
  · rw [MultiBlockExamples.rightCol_gaugeOfMatrix _ gauge_lastCompressionGen,
      show lastCompressionGen.ord = lastOrdGen from rfl]
    ext i j
    have ht : t.val < z := t.isLt
    change gInvGen i ⟨t.val, by omega⟩ = (if i.val = t.val then 1
      else if i.val = t.val + 1 then -1 else 0)
    simp only [gInvGen, Matrix.of_apply]
    rw [ite_eq_right (by omega)]

variable (hz : 0 < z)

include hz in
/-- **Sharpness** (*The asymmetric fundamental theorem of matrix product states*, Example 6.10;
blueprint `cor:asym_uniq_one_block`, *Bare uniqueness at the ends of the flag; the one-block
theorem*): the identity `W_tilde B^w = λ W B^w` fails at a word of length `z - 1 = D_B - D_A - 1`,
so the bound `|w| ≥ D_B - D_A` of the one-block theorem cannot be lowered. -/
theorem exists_length_eq_sub_one_not_exists_smul : ∃ w : List (Fin 1), w.length = z - 1 ∧
    ¬ ∃ c : ℂ, rowOnes z * Kraus.evalWord (tensorBGen z) w =
      c • (rowE0 z * Kraus.evalWord (tensorBGen z) w) := by
  refine ⟨List.replicate (z - 1) 0, List.length_replicate, ?_⟩
  rw [evalWord_replicate, exists_rowOnes_mul_pow_eq_smul_iff]
  omega

/-- **The injections after words** (*The asymmetric fundamental theorem of matrix product states*,
Example 6.10): `Bⁿ V_tilde = Bⁿ V` for reductions with `V = V_tilde = e₀`. -/
theorem pow_mul_right_eq_of_eq_colE0 (P Q : MultiBlockCompression (tensorBGen z) oneSlot blockC)
    (hP : P.right oneSlotMem = colE0 z) (hQ : Q.right oneSlotMem = colE0 z) (n : ℕ) :
    tensorBGen z 0 ^ n * Q.right oneSlotMem = tensorBGen z 0 ^ n * P.right oneSlotMem := by
  rw [hP, hQ]

end General

end MultiBlockExamples.SharpnessOneBlock

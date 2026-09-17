/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.IsingWeightedTwist

/-!
# The weighted Ising bond object acting on a fusion-tree product state

A machine-checked instance of the action-tensor form of the multi-block asymmetric compression
theorem (`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, §7.5,
Theorem 7.7; exact data in `Notes/OpenProblemsTN/checks/asym_ising_action_data.md`, §2,
verified by `checks/asym_ising_action_verify.py`, checks 2a–2g).

The full weighted bond object `Θ_3 = 5 A_1 ⊕ 3 A_ψ ⊕ 2 A_σ` of the Ising twist
(`Examples/IsingWeightedTwist.lean`, with the weights ten times the generic P6 point
`(1/2, 3/10, 1/5)`) acts on the product state `|σ1σ⟩^{⊗ L}`, the fusion tree of the trivial
anyon chain with the label `(σ,1,σ)` at every site. The action tensor is diagonal: its only
nonzero letters are `(1,1,1) ↦ 2 E_{88}`, `(ψ,1,ψ) ↦ 2 E_{99}` and
`(σ,1,σ) ↦ 5 E_{22} + 3 E_{55}`, and it compresses onto four bond-one product states, the
state `|σ1σ⟩^{⊗ L}` twice with the weights `5` and `3` (through the bond objects `1` and `ψ`)
and the states `|111⟩^{⊗ L}`, `|ψ1ψ⟩^{⊗ L}` with the weight `2` (through `σ`), with six zero
slots. The resulting identity

`O_L(Θ_3) |σ1σ⟩^{⊗ L} = (5^L + 3^L) |σ1σ⟩^{⊗ L} + 2^L (|111⟩^{⊗ L} + |ψ1ψ⟩^{⊗ L})`

is the weighted Verlinde action `∑_b λ_b^L ∑_y N^y_{bσ} |y⟩` of the bond object on the sector
labels (data file §2). Nothing here needs `√2`: the F-symbols with a trivial anyon label are
`1`, so the whole instance is integral. The gauge is a pure permutation of the ten bond
coordinates and the remainder vanishes.

## Main definitions

* `IsingTwist.thetaThree`: the full weighted bond object `5 A_1 ⊕ 3 A_ψ ⊕ 2 A_σ`.
* `IsingTwist.productState`: the bond-one tensor of a fusion-tree product state.
* `IsingTwist.sectorAction`: the action tensor of `Θ_3` on `|σ1σ⟩^{⊗ L}`.

## Main results

* `IsingTwist.sectorCompression`: the multi-block compression datum with four weighted bond-one
  slots and six zero slots.
* `IsingTwist.sectorAction_trace_evalWord`: the word-trace identity of the action tensor.
* `IsingTwist.thetaThree_mpo_sectorState`: the weighted Verlinde action as an identity of
  periodic vectors at every positive length.
* `IsingTwist.sectorAction_remainder`: the remainder vanishes.
-/

open scoped Matrix Kronecker

namespace IsingTwist

open MPSTensor Zsqrtd

/-! ### The full weighted bond object -/

/-- The weighted bond object `Θ_3 = 5 A_1 ⊕ 3 A_ψ ⊕ 2 A_σ` over `ℤ√2`, on
`ℂ^10 = P_1 ⊕ P_ψ ⊕ P_σ` (data file §1.4); the `σ` summand is `√2` times the rescaled tensor
`√2 A_σ`. -/
def thetaThreeZ (h h' : Fin 10) : Matrix (Fin 10) (Fin 10) (ℤ√2) :=
  (Matrix.fromBlocks ((5 : ℤ√2) • isingOneZ h h') 0 0
    (Matrix.fromBlocks ((3 : ℤ√2) • isingPsiZ h h') 0 0
      ((sqrtd : ℤ√2) • isingSigmaZ h h'))).submatrix
    ((finSumFinEquiv (m := 3) (n := 7)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 4)).symm))
    ((finSumFinEquiv (m := 3) (n := 7)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 4)).symm))

/-- The weighted bond object `Θ_3 = 5 A_1 ⊕ 3 A_ψ ⊕ 2 A_σ` as a matrix product operator tensor,
with the weights ten times the generic P6 point `(λ_1, λ_ψ, λ_σ) = (1/2, 3/10, 1/5)`
(data file §1.4). -/
noncomputable def thetaThree : MPOTensor 10 10 :=
  fun h h' => complexOfZsqrt2 (thetaThreeZ h h')

/-! ### The fusion-tree product states -/

/-- The bond-one tensor of the product state with the fusion-tree label `h₀` at every site, over
`ℤ√2`. -/
def productStateZ (h₀ : Fin 10) : Fin 10 → Matrix (Fin 1) (Fin 1) (ℤ√2) :=
  fun h => if h = h₀ then 1 else 0

/-- The bond-one tensor of the product state `|h₀⟩^{⊗ L}` (data file §2). -/
noncomputable def productState (h₀ : Fin 10) : MPSTensor 10 1 :=
  fun h => complexOfZsqrt2 (productStateZ h₀ h)

/-- The product state `|σ1σ⟩^{⊗ L}`, the fusion tree of the trivial anyon chain; the label
`(σ,1,σ)` is the sixth. -/
noncomputable def sectorState : MPSTensor 10 1 := productState 6

/-- **Every fusion-tree product state is normal at blocking length one**: its bond algebra is
one-dimensional and one letter is nonzero. -/
theorem productState_isNormal (h₀ : Fin 10) : Kraus.IsNormal (productState h₀) :=
  isNormal_of_single_eq_smul_zsqrt2 (productStateZ h₀) (fun _ => rfl) (fun _ _ => h₀)
    (fun _ _ => 1) (fun _ _ => one_ne_zero) fun x y => by
      obtain rfl : x = 0 := Subsingleton.elim x 0
      obtain rfl : y = 0 := Subsingleton.elim y 0
      refine Matrix.ext fun p q => ?_
      fin_cases p; fin_cases q
      simp [productStateZ]

/-! ### The action tensor -/

/-- The action tensor of `Θ_3` on `|σ1σ⟩^{⊗ L}` (data file §2, check 2a). -/
noncomputable def sectorAction : MPSTensor 10 10 := MPOTensor.actTensor thetaThree sectorState

/-- The three nonzero letters of the action tensor: `2 E_{88}` at `(1,1,1)`, `2 E_{99}` at
`(ψ,1,ψ)`, and `5 E_{22} + 3 E_{55}` at `(σ,1,σ)` (data file §2, check 2a). -/
def sectorActionZ : Fin 10 → Matrix (Fin 10) (Fin 10) (ℤ√2)
  | 0 => Matrix.single 8 8 2
  | 3 => Matrix.single 9 9 2
  | 6 => Matrix.single 2 2 5 + Matrix.single 5 5 3
  | _ => 0

private theorem actZsqrt2Tensor_thetaThreeZ :
    ∀ h, actZsqrt2Tensor thetaThreeZ (productStateZ 6) h = sectorActionZ h := by
  decide +kernel

theorem sectorAction_eq (h : Fin 10) : sectorAction h = complexOfZsqrt2 (sectorActionZ h) := by
  rw [← actZsqrt2Tensor_thetaThreeZ]
  exact actTensor_complexOfZsqrt2 thetaThreeZ (productStateZ 6) h

/-! ### The slots and the block coordinates -/

/-- The four weighted slots: `|σ1σ⟩` through the bond objects `1` and `ψ`, then `|111⟩` and
`|ψ1ψ⟩` through `σ`. -/
abbrev sectorSlots : Finset (Fin 4) := Finset.univ

/-- Every slot carries a bond-one product state. -/
abbrev sectorBlockDim : Fin 4 → ℕ := fun _ => 1

/-- The fusion-tree label of each slot: `(σ,1,σ)`, `(σ,1,σ)`, `(1,1,1)`, `(ψ,1,ψ)`. -/
def sectorLabel : Fin 4 → Fin 10 := ![6, 6, 0, 3]

/-- The weights of the four slots over `ℤ√2`: `5, 3` through `1, ψ` and `2, 2` through `σ`. -/
def sectorWeightsZ : Fin 4 → ℤ√2 := ![5, 3, 2, 2]

/-- The weights of the four slots, ten times the generic P6 point (data file §2). -/
noncomputable def sectorWeights : Fin 4 → ℂ := ![5, 3, 2, 2]

theorem zsqrt2ToComplex_sectorWeightsZ (s : Fin 4) :
    zsqrt2ToComplex (sectorWeightsZ s) = sectorWeights s := by
  fin_cases s <;> simp [sectorWeightsZ, sectorWeights, map_ofNat]

/-- The four target blocks: the weighted product states (data file §2). -/
noncomputable def sectorTargets : Fin 4 → MPSTensor 10 1 :=
  fun s => sectorWeights s • productState (sectorLabel s)

/-- The block ordering: the four weighted slots, then the six zero slots. -/
def sectorOrd : BlockIndex sectorSlots 6 ≃ Fin 10 where
  toFun := Sum.elim (fun s => Fin.castLE (by norm_num) s.1) fun t => ⟨t.val + 4, by omega⟩
  invFun i :=
    if h : i.val < 4 then Sum.inl ⟨⟨i.val, h⟩, Finset.mem_univ _⟩
    else Sum.inr ⟨i.val - 4, by omega⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The bond coordinate of each block: the slot coordinates `e_2, e_5, e_8, e_9` and the zero
slots at `e_0, e_1, e_3, e_4, e_6, e_7` (data file §2). -/
def sectorCoord : BlockIndex sectorSlots 6 → Fin 10 :=
  Sum.elim (fun s => ![2, 5, 8, 9] s.1) ![0, 1, 3, 4, 6, 7]

/-- The labelling of the ten bond coordinates by the graded block space. -/
def sectorTau : BlockSpace sectorBlockDim sectorSlots 6 ≃ Fin 10 where
  toFun x := sectorCoord x.1
  invFun i :=
    (![⟨Sum.inr 0, 0⟩, ⟨Sum.inr 1, 0⟩, ⟨Sum.inl ⟨0, Finset.mem_univ 0⟩, 0⟩, ⟨Sum.inr 2, 0⟩,
      ⟨Sum.inr 3, 0⟩, ⟨Sum.inl ⟨1, Finset.mem_univ 1⟩, 0⟩, ⟨Sum.inr 4, 0⟩, ⟨Sum.inr 5, 0⟩,
      ⟨Sum.inl ⟨2, Finset.mem_univ 2⟩, 0⟩, ⟨Sum.inl ⟨3, Finset.mem_univ 3⟩, 0⟩] :
        Fin 10 → BlockSpace sectorBlockDim sectorSlots 6) i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The gauge: the pure permutation of the bond coordinates given by `sectorTau`. -/
noncomputable def sectorGauge :
    (Fin 10 → ℂ) ≃ₗ[ℂ] (BlockSpace sectorBlockDim sectorSlots 6 → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ sectorTau

theorem conjMatrix_sectorGauge (A : Matrix (Fin 10) (Fin 10) ℂ) :
    conjMatrix sectorGauge A = A.submatrix sectorTau sectorTau := by
  rw [sectorGauge, conjMatrix_apply, toMatrix'_conj_funCongrLeft, LinearMap.toMatrix'_toLin']

/-- The prescribed diagonal blocks over `ℤ√2` at the letter `h`: the weighted product-state
letter on each slot and the `1 × 1` zero matrix on every zero slot. -/
def sectorBlockZ (h : Fin 10) :
    ∀ b : BlockIndex sectorSlots 6,
      Matrix (Fin (slotSize sectorBlockDim b)) (Fin (slotSize sectorBlockDim b)) (ℤ√2) :=
  Sum.rec (motive := fun b =>
      Matrix (Fin (slotSize sectorBlockDim b)) (Fin (slotSize sectorBlockDim b)) (ℤ√2))
    (fun s => sectorWeightsZ s.1 • productStateZ (sectorLabel s.1) h) fun _ => 0

private theorem sectorActionZ_submatrix :
    ∀ h, (sectorActionZ h).submatrix sectorTau sectorTau =
      Matrix.blockDiagonal' (sectorBlockZ h) := by
  decide +kernel

theorem sectorAction_conjMatrix (h : Fin 10) :
    conjMatrix sectorGauge (sectorAction h) =
      complexOfZsqrt2 (Matrix.blockDiagonal' (sectorBlockZ h)) := by
  rw [conjMatrix_sectorGauge, sectorAction_eq, ← complexOfZsqrt2_submatrix,
    sectorActionZ_submatrix]

/-! ### The compression datum -/

/-- **The multi-block asymmetric compression datum of the weighted Verlinde action** (P5 note,
Theorem 7.7(i)–(iii); data file §2, checks 2c–2e): four weighted bond-one product states and six
zero slots. -/
noncomputable def sectorCompression :
    MultiBlockCompression sectorAction sectorSlots sectorTargets where
  z := 6
  ord := sectorOrd
  gauge := sectorGauge
  triangular h x y hlt := by
    have h' : sectorOrd y.1 < sectorOrd x.1 := hlt
    have hxy : x.1 ≠ y.1 := fun e => by rw [e] at h'; exact lt_irrefl _ h'
    rw [sectorAction_conjMatrix, complexOfZsqrt2_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hxy,
      map_zero]
  matched h s := by
    rw [sectorAction_conjMatrix, complexOfZsqrt2, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [sectorBlockZ, sectorTargets, productState, zsqrt2ToComplex_sectorWeightsZ]
  unmatched h t := by
    rw [sectorAction_conjMatrix, complexOfZsqrt2, Matrix.blockDiag'_map,
      Matrix.blockDiag'_blockDiagonal']
    ext p q
    simp [sectorBlockZ]

/-- **The remainder of the weighted Verlinde action vanishes** (P5 note, Theorem 7.7(vi); data
file §2, check 2f): the action tensor is diagonal in the block coordinates. -/
theorem sectorAction_remainder : sectorCompression.remainder = 0 := by
  funext h
  have hc : conjMatrix sectorGauge (sectorCompression.remainder h) =
      conjMatrix sectorGauge (sectorAction h) -
        Matrix.blockDiagonal' (conjMatrix sectorGauge (sectorAction h)).blockDiag' :=
    sectorCompression.conjMatrix_remainder h
  refine conjMatrix_injective sectorGauge ?_
  rw [hc, Pi.zero_apply, conjMatrix_zero, sub_eq_zero, sectorAction_conjMatrix, complexOfZsqrt2,
    Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.blockDiag'_blockDiagonal']

/-! ### Consequences -/

private theorem trace_evalWord_sectorTargets (s : Fin 4) (w : List (Fin 10)) :
    Matrix.trace (Kraus.evalWord (sectorTargets s) w) =
      sectorWeights s ^ w.length *
        Matrix.trace (Kraus.evalWord (productState (sectorLabel s)) w) := by
  rw [sectorTargets, show sectorWeights s • productState (sectorLabel s) =
      fun i => sectorWeights s • productState (sectorLabel s) i from rfl,
    Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]

/-- **The word-trace identity of the weighted Verlinde action** (data file §2, check 2g). -/
theorem sectorAction_trace_evalWord (w : List (Fin 10)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord sectorAction w) =
      ((5 : ℂ) ^ w.length + 3 ^ w.length) * Matrix.trace (Kraus.evalWord sectorState w) +
        2 ^ w.length * (Matrix.trace (Kraus.evalWord (productState 0) w) +
          Matrix.trace (Kraus.evalWord (productState 3) w)) := by
  have h := sectorCompression.trace_evalWord_eq_sum w hw
  rw [h, show sectorSlots = Finset.univ from rfl, Fin.sum_univ_four,
    trace_evalWord_sectorTargets, trace_evalWord_sectorTargets, trace_evalWord_sectorTargets,
    trace_evalWord_sectorTargets]
  simp only [sectorWeights, sectorLabel, sectorState, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem mpv_smul (c : ℂ) (A : MPSTensor 10 1) {L : ℕ} (σ : Fin L → Fin 10) :
    mpv (c • A) σ = c ^ L * mpv A σ := by
  rw [show c • A = fun i => c • A i from rfl, mpv, mpv, coeff, coeff, Kraus.evalWord_smul,
    Matrix.trace_smul, smul_eq_mul, List.length_ofFn]

/-- **The weighted Verlinde action of the bond object on the sector labels** (data file §2,
check 2b): at every positive length, the periodic operator of `Θ_3 = 5 A_1 ⊕ 3 A_ψ ⊕ 2 A_σ`
applied to the product state `|σ1σ⟩^{⊗ L}` is
`(5^L + 3^L) |σ1σ⟩^{⊗ L} + 2^L (|111⟩^{⊗ L} + |ψ1ψ⟩^{⊗ L})`. The state `|σ1σ⟩^{⊗ L}` is
reached twice, through the bond objects `1` and `ψ`, with the two different weights. -/
theorem thetaThree_mpo_sectorState (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo thetaThree L *ᵥ (fun τ : Fin L → Fin 10 => mpv sectorState τ) =
      fun σ : Fin L → Fin 10 => ((5 : ℂ) ^ L + 3 ^ L) * mpv sectorState σ +
        2 ^ L * (mpv (productState 0) σ + mpv (productState 3) σ) := by
  rw [MPOTensor.mpo_mulVec_mpv]
  funext σ
  have h := sectorCompression.mpv_eq_sum L hL σ
  rw [show MPOTensor.actTensor thetaThree sectorState = sectorAction from rfl, h,
    show sectorSlots = Finset.univ from rfl, Fin.sum_univ_four]
  simp only [sectorTargets, mpv_smul, sectorWeights, sectorLabel, sectorState,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Biorthogonal compression onto each weighted product state** (P5 note,
Theorem 7.7(iv)–(v)). -/
theorem sectorAction_isReduction (s : {s // s ∈ sectorSlots}) :
    IsReduction sectorAction (sectorTargets s.1) (sectorCompression.left s)
      (sectorCompression.right s) :=
  sectorCompression.isReduction s

/-- The weighted Verlinde action has six zero slots. -/
theorem sectorAction_z_eq : sectorCompression.z = 6 := rfl

/-- **The dimension count** `10 = 1 + 1 + 1 + 1 + 6` (P5 note, Theorem 7.7(vii)). -/
theorem sectorAction_dim_eq : (10 : ℕ) = ∑ _s ∈ sectorSlots, 1 + 6 :=
  sectorCompression.dim_eq

end IsingTwist

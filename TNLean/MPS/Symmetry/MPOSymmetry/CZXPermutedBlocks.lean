/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Examples.CZX.CZXAnomalyClass
import TNLean.MPS.Symmetry.MPOSymmetry.PermutedBlocks

/-!
# The CZX anomaly from the L-symbols of the two product states

The decorated CZX matrix product unitary `U` of arXiv:2405.00439, Section III.D, exchanges the
product states `|0⟩^{⊗ N}` and `|1⟩^{⊗ N}` at every positive length. With the representation
`czxFamily` of `ℤ₂`, the two product states form a pair of blocks permuted by the group, and
the L-symbols of `MPOTensor.GroupFamily.BlockActionData` are defined. This file computes them
for explicit action tensors and recovers the anomaly from them:
`L^0_{g,g} = 1`, `L^1_{g,g} = -1`, and the compatibility relation gives
`ω(g,g,g) = L^0_{g,g} / L^1_{g,g} = -1`. This is the second route to the anomaly in
arXiv:2405.00439, lines 1246--1339, and it agrees with the direct computation
`CZXCompression.czxFusionData_omega_gen_gen_gen`.

**Local fix (printed left action vectors):** the source prints the left action vector
`⟨+̂|` for both product states (lines 1272 and 1300). With the right action vectors `|+̂⟩`
and `-|+̂⟩` printed there, these do not give reductions: for `|0⟩^{⊗ N}` their product is
`2`, and the three-site decomposition drawn at lines 1249--1301 has vanishing right-hand
side. The left vectors used here are `⟨1|` and `-⟨0|`, for which both decompositions hold.
The conclusion `L_0 / L_1 = -1` of line 1335 is unchanged. Documented in
`docs/paper-gaps/gs24_czx_action_left_vectors.tex`.

## Main definitions

* `CZXCompression.czxBlock`: the product states `|0⟩^{⊗ N}` and `|1⟩^{⊗ N}`, indexed by `ℤ₂`.
* `CZXCompression.czxBlockActionData`: explicit action tensors.

## Main results

* `CZXCompression.czx_carriesMPV`: `U` exchanges the two product states.
* `CZXCompression.czx_lSymbol_gen_gen_zero`, `CZXCompression.czx_lSymbol_gen_gen_one`:
  `L^0_{g,g} = 1` and `L^1_{g,g} = -1`.
* `CZXCompression.czx_omega_eq_lSymbol_div`: `ω(g,g,g) = L^0_{g,g} / L^1_{g,g} = -1`.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPOTensor.GroupFamily MPSTensor

namespace CZXCompression

/-! ### The two product states -/

/-- The bond dimension of the product states: one. -/
abbrev czxBlockDim : Multiplicative (Fin 2) → ℕ := fun _ ↦ 1

/-- The product states `|0⟩^{⊗ N}` and `|1⟩^{⊗ N}`, indexed by `ℤ₂` acting on itself.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1138--1140. -/
def czxBlock (x : Multiplicative (Fin 2)) : MPSTensor 2 (czxBlockDim x) :=
  ghzSectorTensor x.toAdd

private theorem forall_z2' {P : Multiplicative (Fin 2) → Prop}
    (h0 : P (Multiplicative.ofAdd 0)) (h1 : P (Multiplicative.ofAdd 1)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1]

/-- **The CZX representation permutes the two product states**: the identity fixes them and
`U` exchanges them, with phase one, at every positive length.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1138--1140
(`|1⟩^{⊗ N} = U_{CZX} |0⟩^{⊗ N}`). -/
theorem czx_carriesMPV (g x : Multiplicative (Fin 2)) :
    CarriesMPV (czxFamily.tensor g) (czxBlock x) (czxBlock (g • x)) := by
  intro N hN
  have : NeZero N := ⟨by omega⟩
  revert g x
  refine forall_z2' ?_ ?_ <;> refine forall_z2' ?_ ?_
  all_goals
    first
    | (change mpo (MPOTensor.idTensor 2) N *ᵥ _ = _
       rw [mpo_idTensor, Matrix.one_mulVec]; rfl)
    | (change mpo czxDecoratedTensor N *ᵥ
          (fun σ ↦ MPSTensor.mpv (ghzSectorTensor _) σ) =
          fun σ ↦ MPSTensor.mpv (ghzSectorTensor _) σ
       rw [mpv_ghzSectorTensor, mpv_ghzSectorTensor, mpo_czxDecoratedTensor,
         Matrix.monomial_mulVec_single]
       have hflip : ∀ c : Fin 2, spinFlip N (fun _ ↦ c) = fun _ ↦ c.rev := fun c ↦ rfl
       simp only [hflip, czExponent, spinParity, Finset.sum_const, Finset.card_univ,
         Fintype.card_fin, smul_eq_mul]
       norm_num
       try rfl)

/-! ### Action tensors -/

/-- The letters of the action tensor of the decorated CZX tensor on the product state `|s⟩`:
`T^{i s}`, which is `|+̂⟩⟨0|` for `(i, s) = (0, 1)`, `-|−̂⟩⟨1|` for `(i, s) = (1, 0)`, and zero
otherwise. -/
def czxActLetter (s i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = s then 0 else if s = 0 then !![0, -1; 0, 1] else !![1, 0; 1, 0]

theorem actTensor_czxDecoratedTensor_ghzSectorTensor (s i : Fin 2) :
    actTensor czxDecoratedTensor (ghzSectorTensor s) i = czxActLetter s i := by
  ext r c
  fin_cases s <;> fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [actTensor_apply, czxDecoratedTensor_apply, ghzSectorTensor, czxActLetter,
      Fin.sum_univ_two, Matrix.kroneckerMap_apply, finProdFinEquiv, Fin.rev, Fin.divNat,
      Fin.modNat]

/-- The left action tensors: the trivial identification of `isReduction_actTensor_idTensor` for
the identity, `⟨1|` on `|0⟩^{⊗ N}` and `-⟨0|` on
`|1⟩^{⊗ N}` for the generator.

**Local fix (printed left action vectors):** arXiv:2405.00439, lines 1272 and 1300, print
`⟨+̂|` for both states; see the module docstring and
`docs/paper-gaps/gs24_czx_action_left_vectors.tex`. -/
def czxActV : (a s : Fin 2) → Matrix (Fin 1) (Fin (czxLabelBondDim a * 1)) ℂ
  | ⟨0, _⟩, _ => (finCongr (one_mul 1)).symm.toPEquiv.toMatrix
  | ⟨1, _⟩, ⟨0, _⟩ => !![0, 1]
  | ⟨1, _⟩, ⟨1, _⟩ => !![-1, 0]
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- The right action tensors: the trivial identification for the identity, `|+̂⟩` on
`|0⟩^{⊗ N}` and `-|+̂⟩` on `|1⟩^{⊗ N}` for the generator, as printed in arXiv:2405.00439,
lines 1273 and 1301. -/
def czxActW : (a s : Fin 2) → Matrix (Fin (czxLabelBondDim a * 1)) (Fin 1) ℂ
  | ⟨0, _⟩, _ => (finCongr (one_mul 1)).toPEquiv.toMatrix
  | ⟨1, _⟩, ⟨0, _⟩ => !![1; 1]
  | ⟨1, _⟩, ⟨1, _⟩ => !![-1; -1]
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

private theorem isReduction_gen (s : Fin 2) :
    MPSTensor.IsReduction (actTensor czxDecoratedTensor (ghzSectorTensor s))
      (ghzSectorTensor s.rev) (czxActV 1 s) (czxActW 1 s) := by
  have hB : actTensor czxDecoratedTensor (ghzSectorTensor s) = czxActLetter s :=
    funext (actTensor_czxDecoratedTensor_ghzSectorTensor s)
  rw [hB]
  fin_cases s <;> dsimp only <;>
    refine MPSTensor.IsReduction.of_local_compression ?_ (fun i ↦ ?_) (fun i j ↦ ?_) <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
    simp [czxActV, czxActW, czxActLetter, ghzSectorTensor, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.rev]

private theorem isReduction_one (s : Fin 2) :
    MPSTensor.IsReduction (actTensor (MPOTensor.idTensor 2) (ghzSectorTensor s))
      (ghzSectorTensor s) (czxActV 0 s) (czxActW 0 s) := by
  fin_cases s <;> exact isReduction_actTensor_idTensor _

/-- **Action tensors of the CZX representation on the two product states.**

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1246--1301, with the local fix
of the module docstring. -/
def czxBlockActionData : BlockActionData czxFamily czxBlock where
  V g x := czxActV g.toAdd x.toAdd
  W g x := czxActW g.toAdd x.toAdd
  isReduction := by
    refine forall_z2' (forall_z2' ?_ ?_) (forall_z2' ?_ ?_)
    · exact isReduction_one 0
    · exact isReduction_one 1
    · exact isReduction_gen 0
    · exact isReduction_gen 1

end CZXCompression

namespace CZXCompression

/-! ### The anomaly as a ratio of L-symbols -/

/-- The two product states are normal. -/
theorem czxBlock_isNormal (x : Multiplicative (Fin 2)) : Kraus.IsNormal (czxBlock x) :=
  (ghzSectorTensor_isInjective x.toAdd).isNormal

/-- **The second route to the CZX anomaly** (arXiv:2405.00439, lines 1246--1339): for every
choice of action tensors on the two product states and every choice of fusion tensors, the
anomaly is the ratio of L-symbols
`ω(g,g,g) = L^x_{g,g} L^x_{g,1} / (L^{g • x}_{g,g} L^x_{1,g})` for either block `x`. With the
normalization `L_{g,1} = L_{1,g} = 1` of the source this is `L_0 / L_1` for `x = |0⟩^{⊗ N}`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1246--1339; the ratio formula is
`eq:omega_and_Ls` of arXiv:2502.20257 at `(g, g, g)`, as at its line 5121. -/
theorem czx_omega_eq_lSymbol_ratio (fd : czxFamily.FusionData)
    (ad : BlockActionData czxFamily czxBlock) (x : Multiplicative (Fin 2)) :
    fd.omega czxGen czxGen czxGen =
      ad.lSymbol fd x czxGen czxGen * ad.lSymbol fd x czxGen 1 /
        (ad.lSymbol fd (czxGen • x) czxGen czxGen * ad.lSymbol fd x 1 czxGen) :=
  LSymbol.eq_div_of_isCompatible_of_mul_self_eq_one
    (ad.isCompatible_lSymbol czxFamily_isNormalRepresentation czxBlock_isNormal
      (fun _ ↦ Nat.one_pos) czx_carriesMPV)
    x (by decide)

/-- **The L-symbol ratio of the two CZX product states is `-1`**: for every choice of action
tensors, with the fusion tensors `CZXCompression.czxFusionData`,
`L^0_{g,g} L^0_{g,1} / (L^1_{g,g} L^0_{1,g}) = -1`, the conclusion `L_0 / L_1 = -1` of
arXiv:2405.00439, line 1335, in gauge-invariant form.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1246--1339. -/
theorem czx_lSymbol_ratio_eq_neg_one (ad : BlockActionData czxFamily czxBlock) :
    ad.lSymbol czxFusionData (Multiplicative.ofAdd 0) czxGen czxGen *
        ad.lSymbol czxFusionData (Multiplicative.ofAdd 0) czxGen 1 /
      (ad.lSymbol czxFusionData (Multiplicative.ofAdd 1) czxGen czxGen *
        ad.lSymbol czxFusionData (Multiplicative.ofAdd 0) 1 czxGen) = -1 := by
  rw [← czxFusionData_omega_gen_gen_gen,
    czx_omega_eq_lSymbol_ratio czxFusionData ad (Multiplicative.ofAdd 0)]
  rfl

end CZXCompression

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.CZXPermutedBlocks
import TNLean.MPS.Symmetry.MPOSymmetry.DomainWall

/-!
# CZX: domain walls between the two product states and `c_{AB} c_{BA} = -1`

**Source.** Garre-Rubio, Schuch 2024 (arXiv:2405.00439), Section III,
`Papers/2405.00439/MPU-DW.tex` lines 643--838 (domain walls `e_{AB}`, `e_{BA}` and their phases
`c_{AB}`, `c_{BA}`, `eq:localcdef`), lines 1020--1121 (`eq:CC-LL`: `c_{AB} c_{BA} = ω`), and
lines 1123--1339 (the CZX symmetry exchanging `|0⟩^{⊗ N}` and `|1⟩^{⊗ N}`, with `ω = -1`).

**Formalized here.** For the decorated CZX representation of `ℤ₂` acting on the two product
states, every choice of action tensors and of domain walls exchanged by the generator gives
`c_{AB} c_{BA} = -1`: the domain walls between the two symmetry-broken ground states carry the
anomaly. With the action tensors of `CZXCompression.czxBlockActionData`, the walls
`e_{AB} = |0⟩` and `e_{BA} = -|1⟩` are exchanged with `c_{AB} = 1` and `c_{BA} = -1`. The
exchange of `e_{BA}` needs one site of buffer on the right of the wall: without it the
right action vector `|+̂⟩` of the source (line 1273) gives the opposite sign.

**Local fix (printed left action vectors):** the explicit walls use the action tensors of
`CZXCompression.czxBlockActionData`, whose left action vectors `⟨1|` and `-⟨0|` replace the vector
`⟨+̂|` printed at lines 1272 and 1300; this affects `czx_isDomainWallAction_ab`,
`czx_isDomainWallAction_ba` and `czx_mpo_mulVec_twoWallMPV`, not `czx_domainWall_mul_eq_neg_one`,
which holds for every choice of action tensors. Documented in
`docs/paper-gaps/gs24_czx_action_left_vectors.tex`.

## Main results

* `CZXCompression.czx_domainWall_mul_eq_neg_one`: `c_{AB} c_{BA} = -1` for every choice.
* `CZXCompression.czx_isDomainWallAction_ab`, `CZXCompression.czx_isDomainWallAction_ba`:
  explicit domain walls.
* `CZXCompression.czx_mpo_mulVec_twoWallMPV`: `U |ψ(0-1-0)⟩ = -|ψ(1-0-1)⟩`.

## References
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- Garre-Rubio, Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPOTensor.GroupFamily MPSTensor

namespace CZXCompression

theorem czxGen_smul_zero :
    czxGen • (Multiplicative.ofAdd 0 : Multiplicative (Fin 2)) = Multiplicative.ofAdd 1 := by
  decide

theorem czxGen_smul_one :
    czxGen • (Multiplicative.ofAdd 1 : Multiplicative (Fin 2)) = Multiplicative.ofAdd 0 := by
  decide

theorem czxGen_mul_self : czxGen * czxGen = 1 := by decide

/-- **The CZX domain walls carry the anomaly** (arXiv:2405.00439, `eq:CC-LL`,
`Papers/2405.00439/MPU-DW.tex` lines 1020--1121, for the CZX symmetry of lines 1123--1339):
for every choice of action tensors on the two product states and every pair of domain walls
exchanged by the generator, `c_{AB} c_{BA} = -1`. -/
theorem czx_domainWall_mul_eq_neg_one (ad : BlockActionData czxFamily czxBlock)
    {eAB : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ} {eBA : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ}
    {cAB cBA : ℂ}
    (hAB : ad.IsDomainWallAction czxGen czxGen_smul_zero czxGen_smul_one eAB eBA cAB)
    (hBA : ad.IsDomainWallAction czxGen czxGen_smul_one czxGen_smul_zero eBA eAB cBA) :
    cAB * cBA = -1 := by
  rw [BlockActionData.IsDomainWallAction.mul_eq_omega_of_mul_self_eq_one (fd := czxFusionData)
    czxFamily_isNormalRepresentation czxBlock_isNormal (fun _ ↦ Nat.one_pos) czx_carriesMPV
    czxGen_mul_self hAB hBA, czxFusionData_omega_gen_gen_gen,
    czxFusionData_omega_gen_one_gen]
  simp

/-! ### Explicit domain walls -/

/-- The domain wall `e_{AB} = |0⟩` from `|0⟩^{⊗ N}` to `|1⟩^{⊗ N}`. -/
def czxWallAB : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := fun j ↦ if j = 0 then 1 else 0

/-- The domain wall `e_{BA} = -|1⟩` from `|1⟩^{⊗ N}` to `|0⟩^{⊗ N}`. -/
def czxWallBA : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := fun j ↦ if j = 1 then -1 else 0

theorem czxWallAB_ne_zero : czxWallAB ≠ 0 := by
  intro h
  have := congrFun (congrFun (congrFun h 0) 0) 0
  simp [czxWallAB] at this

theorem czxWallBA_ne_zero : czxWallBA ≠ 0 := by
  intro h
  have := congrFun (congrFun (congrFun h 1) 0) 0
  simp [czxWallBA] at this

/-- Identifications of the bond spaces of the product states are trivial. -/
theorem castIndex_czxBlockDim {a b : Multiplicative (Fin 2)} (e : a = b) :
    castIndex czxBlockDim e = 1 := by
  subst e
  exact castIndex_rfl _ _

private theorem actTensor_gen (s : Fin 2) :
    actTensor (czxFamily.tensor czxGen) (czxBlock (Multiplicative.ofAdd s)) = czxActLetter s :=
  funext (actTensor_czxDecoratedTensor_ghzSectorTensor s)

local notation "x₀" => (Multiplicative.ofAdd (0 : Fin 2) : Multiplicative (Fin 2))
local notation "x₁" => (Multiplicative.ofAdd (1 : Fin 2) : Multiplicative (Fin 2))

/-- `e_{AB}` is carried to `e_{BA}` by the generator with `c_{AB} = 1`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 774--832 (`eq:localcdef`). -/
theorem czx_isDomainWallAction_ab :
    czxBlockActionData.IsDomainWallAction czxGen czxGen_smul_zero czxGen_smul_one czxWallAB
      czxWallBA 1 := by
  have hV : ∀ j, czxBlock x₁ j * czxBlockActionData.V czxGen x₀ =
      czxBlockActionData.V czxGen x₀ * actTensor (czxFamily.tensor czxGen) (czxBlock x₀) j := by
    intro j
    rw [actTensor_gen]
    change ghzSectorTensor 1 j * !![(0 : ℂ), 1] = !![(0 : ℂ), 1] * czxActLetter 0 j
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [czxActLetter, ghzSectorTensor, Matrix.mul_apply, Fin.sum_univ_succ]
  have hW : ∀ j, actTensor (czxFamily.tensor czxGen) (czxBlock x₁) j *
      czxBlockActionData.W czxGen x₁ = czxBlockActionData.W czxGen x₁ * czxBlock x₀ j := by
    intro j
    rw [actTensor_gen]
    change czxActLetter 1 j * !![(-1 : ℂ); -1] = !![(-1 : ℂ); -1] * ghzSectorTensor 0 j
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [czxActLetter, ghzSectorTensor, Matrix.mul_apply, Fin.sum_univ_succ]
  have hmid : ∀ i, czxBlockActionData.V czxGen x₀ * actRect (czxFamily.tensor czxGen) czxWallAB i *
      czxBlockActionData.W czxGen x₁ = czxWallBA i := by
    intro i
    change !![(0 : ℂ), 1] * (show Matrix (Fin 2) (Fin 2) ℂ from
        actRect czxDecoratedTensor czxWallAB i) * !![(-1 : ℂ); -1] = czxWallBA i
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [actRect, czxWallAB, czxWallBA, czxDecoratedTensor_apply, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.kroneckerMap_apply, Matrix.submatrix_apply, Matrix.vecMul,
        dotProduct, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.rev, Fin.fin_one_eq_zero]
  refine ⟨czxWallAB_ne_zero, czxWallBA_ne_zero, one_ne_zero, 0, fun u v i _ _ ↦ ?_⟩
  rw [castIndex_czxBlockDim, castIndex_czxBlockDim, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hL := Kraus.evalWord_intertwine _ _ _ hV u
  have hR := Kraus.evalWord_intertwine _ _ _ hW v
  calc _ = czxBlockActionData.V czxGen x₀ *
          Kraus.evalWord (actTensor (czxFamily.tensor czxGen) (czxBlock x₀)) u *
        actRect (czxFamily.tensor czxGen) czxWallAB i *
          (Kraus.evalWord (actTensor (czxFamily.tensor czxGen) (czxBlock x₁)) v *
            czxBlockActionData.W czxGen x₁) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [← hL, hR, ← hmid i]
      simp only [Matrix.mul_assoc]

/-- The right boundary `|+̂⟩` of the generator on `|0⟩^{⊗ N}` moved through one site of the
acted state: `-|0⟩ + |1⟩`. -/
private def czxBufferW :
    Matrix (Fin (czxFamily.bondDim czxGen * czxBlockDim x₀)) (Fin (czxBlockDim x₁)) ℂ :=
  !![-1; 1]

private theorem evalWord_mul_W_gen_zero (v : List (Fin 2)) (hv : v ≠ []) :
    Kraus.evalWord (actTensor (czxFamily.tensor czxGen) (czxBlock x₀)) v *
        czxBlockActionData.W czxGen x₀ =
      czxBufferW * Kraus.evalWord (czxBlock x₁) v := by
  have hstep : ∀ j, actTensor (czxFamily.tensor czxGen) (czxBlock x₀) j *
      czxBlockActionData.W czxGen x₀ = czxBufferW * czxBlock x₁ j := by
    intro j
    rw [actTensor_gen]
    change czxActLetter 0 j * !![(1 : ℂ); 1] = !![(-1 : ℂ); 1] * ghzSectorTensor 1 j
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [czxActLetter, ghzSectorTensor, Matrix.mul_apply, Fin.sum_univ_succ]
  have hbuf : ∀ j, actTensor (czxFamily.tensor czxGen) (czxBlock x₀) j * czxBufferW =
      czxBufferW * czxBlock x₁ j := by
    intro j
    rw [actTensor_gen]
    change czxActLetter 0 j * !![(-1 : ℂ); 1] = !![(-1 : ℂ); 1] * ghzSectorTensor 1 j
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [czxActLetter, ghzSectorTensor, Matrix.mul_apply, Fin.sum_univ_succ]
  obtain ⟨v', j, rfl⟩ := (List.eq_nil_or_concat' v).resolve_left hv
  rw [Kraus.evalWord_append, Kraus.evalWord_append, Matrix.mul_assoc]
  simp only [Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one]
  rw [hstep, ← Matrix.mul_assoc, Kraus.evalWord_intertwine _ _ _ hbuf v', Matrix.mul_assoc]

/-- `e_{BA}` is carried to `e_{AB}` by the generator with `c_{BA} = -1`, against words with at
least one site on each side of the wall.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 774--832 (`eq:localcdef`). -/
theorem czx_isDomainWallAction_ba :
    czxBlockActionData.IsDomainWallAction czxGen czxGen_smul_one czxGen_smul_zero czxWallBA
      czxWallAB (-1) := by
  have hV : ∀ j, czxBlock x₀ j * czxBlockActionData.V czxGen x₁ =
      czxBlockActionData.V czxGen x₁ * actTensor (czxFamily.tensor czxGen) (czxBlock x₁) j := by
    intro j
    rw [actTensor_gen]
    change ghzSectorTensor 0 j * !![(-1 : ℂ), 0] = !![(-1 : ℂ), 0] * czxActLetter 1 j
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [czxActLetter, ghzSectorTensor, Matrix.mul_apply, Fin.sum_univ_succ]
  have hmid : ∀ i, czxBlockActionData.V czxGen x₁ * actRect (czxFamily.tensor czxGen) czxWallBA i *
      czxBufferW = -czxWallAB i := by
    intro i
    change !![(-1 : ℂ), 0] * (show Matrix (Fin 2) (Fin 2) ℂ from
        actRect czxDecoratedTensor czxWallBA i) * !![(-1 : ℂ); 1] = -czxWallAB i
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [actRect, czxWallAB, czxWallBA, czxDecoratedTensor_apply, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.kroneckerMap_apply, Matrix.submatrix_apply, Matrix.vecMul,
        dotProduct, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.rev, Fin.fin_one_eq_zero]
  refine ⟨czxWallBA_ne_zero, czxWallAB_ne_zero, by norm_num, 1, fun u v i _ hv ↦ ?_⟩
  rw [castIndex_czxBlockDim, castIndex_czxBlockDim, Matrix.one_mul, Matrix.mul_one]
  have hL := Kraus.evalWord_intertwine _ _ _ hV u
  have hR := evalWord_mul_W_gen_zero v (List.ne_nil_of_length_pos hv)
  calc _ = czxBlockActionData.V czxGen x₁ *
          Kraus.evalWord (actTensor (czxFamily.tensor czxGen) (czxBlock x₁)) u *
        actRect (czxFamily.tensor czxGen) czxWallBA i *
          (Kraus.evalWord (actTensor (czxFamily.tensor czxGen) (czxBlock x₀)) v *
            czxBlockActionData.W czxGen x₀) := by simp only [Matrix.mul_assoc]
    _ = Kraus.evalWord (czxBlock x₀) u * (czxBlockActionData.V czxGen x₁ *
          actRect (czxFamily.tensor czxGen) czxWallBA i * czxBufferW) *
            Kraus.evalWord (czxBlock x₁) v := by
      rw [← hL, hR]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hmid]
      simp

/-- **The CZX symmetry acts on two domain walls with the sign `-1`**: with the explicit walls,
`U |ψ(0-1-0)⟩ = -|ψ(1-0-1)⟩` on every chain with long enough regions.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 833--838 (the product
`c_{BA} c_{AB}` is observed on `|ψ(A-B-A)⟩`) and line 1335 (`ω = -1` for CZX). -/
theorem czx_mpo_mulVec_twoWallMPV :
    ∃ N : ℕ, ∀ k l n : ℕ, N ≤ k → N ≤ l →
      mpo czxDecoratedTensor (k + 1 + l + 1 + n) *ᵥ
          twoWallMPV (ghzSectorTensor 0) czxWallAB (ghzSectorTensor 1) czxWallBA =
        -twoWallMPV (ghzSectorTensor 1) czxWallBA (ghzSectorTensor 0) czxWallAB := by
  obtain ⟨N, hN⟩ := BlockActionData.IsDomainWallAction.mpo_mulVec_twoWallMPV czx_carriesMPV
    czx_isDomainWallAction_ab czx_isDomainWallAction_ba
  refine ⟨N, fun k l n hk hl ↦ ?_⟩
  have := hN k l n hk hl
  rw [one_mul, neg_one_smul] at this
  exact this

end CZXCompression

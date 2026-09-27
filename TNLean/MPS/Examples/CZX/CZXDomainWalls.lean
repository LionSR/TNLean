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

## Main results

* `CZXCompression.czx_domainWall_mul_eq_neg_one`: `c_{AB} c_{BA} = -1` for every choice.
* `CZXCompression.czx_isDomainWallAction_ab`, `CZXCompression.czx_isDomainWallAction_ba`,
  `CZXCompression.czx_isDomainWallAction_one`: explicit domain walls.

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
exchanged by the generator, `c_{AB} c_{BA} = -1`. The identity acts on `e_{AB}` by a nonzero
scalar; see
`MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction.mul_eq_omega_of_mul_self_eq_one`. -/
theorem czx_domainWall_mul_eq_neg_one (ad : BlockActionData czxFamily czxBlock)
    {eAB : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ} {eBA : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ}
    {cAB cBA b : ℂ}
    (hAB : ad.IsDomainWallAction czxGen czxGen_smul_zero czxGen_smul_one eAB eBA cAB)
    (hBA : ad.IsDomainWallAction czxGen czxGen_smul_one czxGen_smul_zero eBA eAB cBA)
    (h1 : ad.IsDomainWallAction 1 (one_smul _ (Multiplicative.ofAdd 0))
      (one_smul _ (Multiplicative.ofAdd 1)) eAB eAB b) (hb : b ≠ 0)
    (he : eAB ≠ 0) : cAB * cBA = -1 := by
  rw [BlockActionData.IsDomainWallAction.mul_eq_omega_of_mul_self_eq_one (fd := czxFusionData)
    czxFamily_isNormalRepresentation czxBlock_isNormal (fun _ ↦ Nat.one_pos) czx_carriesMPV
    czxGen_mul_self hAB hBA h1 hb he, czxFusionData_omega_gen_gen_gen,
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
  refine ⟨0, fun u v i _ _ ↦ ?_⟩
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
  refine ⟨1, fun u v i _ hv ↦ ?_⟩
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

private instance (x : Multiplicative (Fin 2)) :
    Subsingleton (Fin (czxFamily.bondDim 1 * czxBlockDim x)) :=
  Fin.subsingleton_one

private instance : Subsingleton (Fin (czxFamily.bondDim 1 * 1)) := Fin.subsingleton_one

private instance : Subsingleton (Fin (czxFamily.bondDim 1)) := Fin.subsingleton_one

private theorem czxActV_zero_apply (s : Fin 2) (a : Fin 1) (b : Fin (czxLabelBondDim 0 * 1)) :
    czxActV 0 s a b = 1 := by
  fin_cases s <;> fin_cases a <;> fin_cases b <;> rfl

private theorem czxActW_zero_apply (s : Fin 2) (a : Fin (czxLabelBondDim 0 * 1)) (b : Fin 1) :
    czxActW 0 s a b = 1 := by
  fin_cases s <;> fin_cases a <;> fin_cases b <;> rfl

private theorem actTensor_one_apply (x : Multiplicative (Fin 2)) (j : Fin 2)
    (a b : Fin (czxFamily.bondDim 1 * czxBlockDim x)) :
    actTensor (czxFamily.tensor 1) (czxBlock x) j a b = czxBlock x j 0 0 := by
  have h := actTensor_idTensor_apply (czxBlock x) j (Fin.cast (by rfl) a) (Fin.cast (by rfl) b)
  refine h.trans ?_
  congr 1 <;> exact Subsingleton.elim _ _

private theorem actRect_one_apply (e : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ) (i : Fin 2)
    (a b : Fin (czxFamily.bondDim 1 * 1)) :
    actRect (czxFamily.tensor 1) e i a b = e i 0 0 := by
  revert a b
  change ∀ a b : Fin (1 * 1), (∑ j : Fin 2, MPOTensor.idTensor 2 i j ⊗ₖ e j).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm a b = e i 0 0
  intro a b
  rw [Matrix.submatrix_apply, Subsingleton.elim (finProdFinEquiv.symm a) (0, 0),
    Subsingleton.elim (finProdFinEquiv.symm b) (0, 0)]
  fin_cases i <;>
    simp [MPOTensor.idTensor, Matrix.sum_apply, Fin.sum_univ_two, Matrix.kroneckerMap_apply]

/-- The identity element acts trivially on `e_{AB}`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` line 861 (the identity merges
trivially). -/
theorem czx_isDomainWallAction_one :
    czxBlockActionData.IsDomainWallAction 1 (one_smul _ x₀) (one_smul _ x₁) czxWallAB
      czxWallAB 1 := by
  have hV : ∀ (s : Fin 2) j, czxBlock (Multiplicative.ofAdd s) j *
      czxBlockActionData.V 1 (Multiplicative.ofAdd s) = czxBlockActionData.V 1
        (Multiplicative.ofAdd s) *
          actTensor (czxFamily.tensor 1) (czxBlock (Multiplicative.ofAdd s)) j := by
    intro s j
    ext a b
    simp only [Matrix.mul_apply]
    rw [Fintype.sum_subsingleton _ 0, Fintype.sum_subsingleton _ b]
    simp only [actTensor_one_apply]
    have h1 : czxBlockActionData.V 1 (Multiplicative.ofAdd s) 0 b = 1 := czxActV_zero_apply s 0 b
    have h2 : czxBlockActionData.V 1 (Multiplicative.ofAdd s) a b = 1 := czxActV_zero_apply s a b
    rw [h1, h2, Subsingleton.elim a 0]
    ring
  have hW : ∀ (s : Fin 2) j,
      actTensor (czxFamily.tensor 1) (czxBlock (Multiplicative.ofAdd s)) j *
        czxBlockActionData.W 1 (Multiplicative.ofAdd s) =
      czxBlockActionData.W 1 (Multiplicative.ofAdd s) * czxBlock (Multiplicative.ofAdd s) j := by
    intro s j
    ext a b
    simp only [Matrix.mul_apply]
    rw [Fintype.sum_subsingleton _ a, Fintype.sum_subsingleton _ 0]
    simp only [actTensor_one_apply]
    have h1 : czxBlockActionData.W 1 (Multiplicative.ofAdd s) a b = 1 := czxActW_zero_apply s a b
    have h2 : czxBlockActionData.W 1 (Multiplicative.ofAdd s) a 0 = 1 := czxActW_zero_apply s a 0
    rw [h1, h2, Subsingleton.elim b 0]
    ring
  have hmid : ∀ i, czxBlockActionData.V 1 x₀ * actRect (czxFamily.tensor 1) czxWallAB i *
      czxBlockActionData.W 1 x₁ = czxWallAB i := by
    intro i
    ext a b
    simp only [Matrix.mul_apply]
    rw [Fintype.sum_subsingleton _ 0]
    simp only [Fintype.sum_subsingleton _ (0 : Fin (czxFamily.bondDim 1 * 1)), actRect_one_apply]
    have h1 : czxBlockActionData.V 1 x₀ a 0 = 1 := czxActV_zero_apply 0 a _
    have h2 : czxBlockActionData.W 1 x₁ 0 b = 1 := czxActW_zero_apply 1 _ b
    rw [h1, h2, Subsingleton.elim a 0, Subsingleton.elim b 0]
    ring
  refine ⟨0, fun u v i _ _ ↦ ?_⟩
  rw [castIndex_czxBlockDim, castIndex_czxBlockDim, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hL := Kraus.evalWord_intertwine _ _ _ (hV 0) u
  have hR := Kraus.evalWord_intertwine _ _ _ (hW 1) v
  have key : czxBlockActionData.V 1 x₀ *
      Kraus.evalWord (actTensor (czxFamily.tensor 1) (czxBlock x₀)) u *
        actRect (czxFamily.tensor 1) czxWallAB i *
          (Kraus.evalWord (actTensor (czxFamily.tensor 1) (czxBlock x₁)) v *
            czxBlockActionData.W 1 x₁) =
      Kraus.evalWord (czxBlock x₀) u * czxWallAB i * Kraus.evalWord (czxBlock x₁) v := by
    rw [← hL, hR, ← hmid i]
    simp only [Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc, one_smul] using key


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

import TNLean.MPS.MultiBlock
import TNLean.MPS.FundamentalTheorem

import Mathlib.Algebra.BigOperators.Fin

open scoped Matrix BigOperators

namespace MPSTensor

/-!
# Multi-block Fundamental Theorem of MPS (block-diagonal assembly)

This file contains the *assembly* step for the multi-block Fundamental Theorem.

The single-block theorem (`fundamentalTheorem_singleBlock`) shows that if an injective block tensor
`A` generates the same MPV family as `B`, then `A` and `B` are related by a gauge transform
(simultaneous similarity by some `X ∈ GL`).

For multi-block canonical forms, the key new ingredient is that blockwise gauge transforms assemble
into a *block-diagonal* global gauge transform.

To avoid the definitional-equality/cast issues that arise when comparing two `CanonicalForm`s, we
work with a parametric block-diagonal constructor `toTensorFromBlocks`.
-/

variable {d : ℕ}

/-- Build a block-diagonal tensor from raw block data. -/
noncomputable def toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) := fun i =>
  (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
    (Matrix.blockDiagonal' fun k => (μ k) • (A k i))

/-! ## Block-diagonal invertible matrices -/

section BlockDiagonalGL

variable {r : ℕ} {dim : Fin r → ℕ}

private theorem blockDiagonal'_mul_one
    (f g : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (hfg : ∀ k, f k * g k = 1) :
    Matrix.blockDiagonal' f * Matrix.blockDiagonal' g = 1 := by
  rw [← Matrix.blockDiagonal'_mul, show (fun k => f k * g k) = 1 from funext hfg,
    Matrix.blockDiagonal'_one]

/-- Assemble blockwise invertible matrices into a block-diagonal element of `GL`. -/
noncomputable def blockDiagonalGL (X : (k : Fin r) → GL (Fin (dim k)) ℂ) :
    GL ((k : Fin r) × Fin (dim k)) ℂ :=
  ⟨Matrix.blockDiagonal' (fun k => (X k : Matrix _ _ ℂ)),
   Matrix.blockDiagonal' (fun k => ((X k)⁻¹ : Matrix _ _ ℂ)),
   blockDiagonal'_mul_one _ _ (fun k => by simp),
   blockDiagonal'_mul_one _ _ (fun k => by simp)⟩

end BlockDiagonalGL

/-! ## Reindexing `GL` -/

section ReindexGL

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end ReindexGL

/-! ## Block-diagonal gauge assembly -/

section GaugeAssembly

variable {r : ℕ} {dim : Fin r → ℕ}
variable (μ : Fin r → ℂ)
variable (A B : (k : Fin r) → MPSTensor d (dim k))

/-- Block-diagonal gauge assembly with an explicit family of gauge matrices. -/
theorem gaugeEquiv_toTensorFromBlocks_of_blockConj
    (X : (k : Fin r) → GL (Fin (dim k)) ℂ)
    (hX : ∀ k : Fin r, ∀ i : Fin d,
      B k i =
        (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :
    GaugeEquiv (toTensorFromBlocks (d := d) (μ := μ) A)
      (toTensorFromBlocks (d := d) (μ := μ) B) := by
  classical
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  let f : Matrix α α ℂ →* Matrix (Fin _) (Fin _) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv.toMonoidHom
  let Xfin : GL (Fin _) ℂ := (Units.map f) (blockDiagonalGL X)
  refine ⟨Xfin, fun i => ?_⟩
  let BD := fun (T : (k : Fin r) → MPSTensor d (dim k)) =>
    Matrix.blockDiagonal' fun k => (μ k) • T k i
  let XBD : Matrix α α ℂ :=
    Matrix.blockDiagonal' fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
  let XBDinv : Matrix α α ℂ :=
    Matrix.blockDiagonal' fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
  have htoA : toTensorFromBlocks (d := d) (μ := μ) A i = f (BD A) := by
    simp [toTensorFromBlocks, BD, f, e]; rfl
  have htoB : toTensorFromBlocks (d := d) (μ := μ) B i = f (BD B) := by
    simp [toTensorFromBlocks, BD, f, e]; rfl
  have hBD : BD B = XBD * BD A * XBDinv := by
    simp only [BD, XBD, XBDinv]
    have : (fun k : Fin r => (μ k) • B k i) =
        fun k => (X k : Matrix _ _ ℂ) * ((μ k) • A k i) * ((X k)⁻¹ : Matrix _ _ ℂ) := by
      funext k; simp [hX k i, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Matrix.mul_assoc]
    rw [this, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  have hXfin : (Xfin : Matrix _ _ ℂ) = f XBD := by simp [Xfin, XBD, blockDiagonalGL]
  have hXfin_inv : ((Xfin⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) = f XBDinv := by
    simp [Xfin, XBDinv, blockDiagonalGL]
  rw [htoB, htoA, hBD]
  simp [map_mul, hXfin, hXfin_inv, Matrix.mul_assoc]

/-- Block-diagonal gauge assembly from blockwise `GaugeEquiv`. -/
theorem gaugeEquiv_toTensorFromBlocks_of_blockGauge
    (hGauge : ∀ k : Fin r, GaugeEquiv (A k) (B k)) :
    GaugeEquiv (toTensorFromBlocks (d := d) (μ := μ) A)
      (toTensorFromBlocks (d := d) (μ := μ) B) := by
  classical
  choose X hX using hGauge
  exact gaugeEquiv_toTensorFromBlocks_of_blockConj μ A B X hX

end GaugeAssembly

/-! ## Multi-block Fundamental Theorem (parametric version) -/

section FundamentalTheoremMulti

variable {r : ℕ} {dim : Fin r → ℕ}
variable (μ : Fin r → ℂ)
variable (A B : (k : Fin r) → MPSTensor d (dim k))

/-- Blockwise application of the single-block Fundamental Theorem. -/
theorem fundamentalTheorem_multiBlock_blocks
    (hA : ∀ k : Fin r, IsInjective (A k))
    (hSame : ∀ k : Fin r, SameMPV (A k) (B k)) :
    ∀ k : Fin r, GaugeEquiv (A k) (B k) :=
  fun k => fundamentalTheorem_singleBlock (hA k) (hSame k)

/-- Global multi-block Fundamental Theorem (assembly version). -/
theorem fundamentalTheorem_multiBlock_global
    (hA : ∀ k : Fin r, IsInjective (A k))
    (hSame : ∀ k : Fin r, SameMPV (A k) (B k)) :
    GaugeEquiv (toTensorFromBlocks (d := d) (μ := μ) A)
      (toTensorFromBlocks (d := d) (μ := μ) B) :=
  gaugeEquiv_toTensorFromBlocks_of_blockGauge μ A B
    (fundamentalTheorem_multiBlock_blocks A B hA hSame)

end FundamentalTheoremMulti

/-! ## Bridge to `CanonicalForm` -/

section CanonicalFormBridge

open CanonicalForm

/-- `CanonicalForm.toTensor` agrees with `toTensorFromBlocks`. -/
theorem CanonicalForm.toTensor_eq_toTensorFromBlocks (C : CanonicalForm d) :
    C.toTensor = toTensorFromBlocks C.μ C.blockTensor := rfl

theorem fundamentalTheorem_canonicalForm_sameStructure
    (C : CanonicalForm d)
    (B : (k : Fin C.numBlocks) → MPSTensor d (C.blockDim k))
    (hB_inj : ∀ k, IsInjective (C.blockTensor k))
    (hSame : ∀ k, SameMPV (C.blockTensor k) (B k)) :
    GaugeEquiv (C.toTensor) (toTensorFromBlocks C.μ B) := by
  rw [C.toTensor_eq_toTensorFromBlocks]
  exact fundamentalTheorem_multiBlock_global C.μ C.blockTensor B hB_inj hSame

end CanonicalFormBridge

/-! ## Converse and global `SameMPV` transfer -/

section Converse

variable {r : ℕ} {dim : Fin r → ℕ}

theorem gaugeEquiv_toTensorFromBlocks_implies_sameMPV
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hGauge : GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  GaugeEquiv.sameMPV hGauge

/-- MPV of `toTensorFromBlocks` expands as a sum over blocks. -/
theorem mpv_toTensorFromBlocks_eq_sum
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := μ) A) σ =
      ∑ k : Fin r, (μ k) ^ N • mpv (A k) σ := by
  classical
  set w := List.ofFn σ with hw
  have hwlen : w.length = N := by simp [w]
  simp only [MPSTensor.mpv, MPSTensor.coeff, hw.symm, smul_eq_mul]
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  let BD : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)
  have hEval : MPSTensor.evalWord (toTensorFromBlocks (d := d) (μ := μ) A) w =
      (Matrix.reindex e e) (_root_.evalWord BD w) := by
    simpa [toTensorFromBlocks, BD, e, show (fun i : Fin d => toTensorFromBlocks (d := d) (μ := μ)
      A i) = fun i => (Matrix.reindex e e) (BD i) from by funext i; rfl]
      using evalWord_reindex (d := d) (e := e) (A := BD) w
  rw [hEval, Matrix.trace_reindex]
  rw [show _root_.evalWord BD w = Matrix.blockDiagonal'
      (fun k => (μ k) ^ w.length • _root_.evalWord (A k) w) from by
    simpa [BD] using evalWord_blockDiagonal'_smul (μ := μ) (A := A) w]
  rw [Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.trace_smul, hwlen]

theorem sameMPV_toTensorFromBlocks_of_blockSameMPV
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  intro N σ
  simp only [mpv_toTensorFromBlocks_eq_sum]
  exact Finset.sum_congr rfl fun k _ => by simp [hSame k N σ]

end Converse

end MPSTensor

import MPSLean.MPS.MultiBlock
import MPSLean.MPS.FundamentalTheorem

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

/-- Build a block-diagonal tensor from raw block data.

This is a parametric version of `CanonicalForm.toTensor` that does *not* require a
`CanonicalForm` structure.  Each block `A k` is scaled by `μ k`, then placed on the diagonal using
`Matrix.blockDiagonal'`, and finally reindexed to `Fin (∑ k, dim k)` via `finSigmaFinEquiv`.
-/
noncomputable def toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) := fun i : Fin d =>
  let blocks : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    fun k => (μ k) • (A k i)
  let BD :
      Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ :=
    Matrix.blockDiagonal' blocks
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) :=
    finSigmaFinEquiv (m := r) (n := dim)
  (Matrix.reindex e e) BD

/-!
## Block-diagonal invertible matrices

The core construction is that a family of invertible matrices on each block induces an invertible
block-diagonal matrix on the `Σ`-type index `((k : Fin r) × Fin (dim k))`.
-/

section BlockDiagonalGL

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Assemble blockwise invertible matrices into a block-diagonal element of `GL`.

The underlying matrix is `Matrix.blockDiagonal' (fun k => X k)`. Its inverse is obtained by taking
blockwise inverses and again forming the block diagonal.
-/
noncomputable def blockDiagonalGL (X : (k : Fin r) → GL (Fin (dim k)) ℂ) :
    GL ((k : Fin r) × Fin (dim k)) ℂ := by
  classical
  refine
    ⟨Matrix.blockDiagonal' (fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)),
      Matrix.blockDiagonal' (fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)),
      ?_, ?_⟩
  · -- `val * inv = 1`
    calc
      Matrix.blockDiagonal' (fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) *
          Matrix.blockDiagonal' (fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
          = Matrix.blockDiagonal'
              (fun k =>
                (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
                  ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
            simpa using
              (Matrix.blockDiagonal'_mul
                (M := fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
                (N := fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))).symm
      _ = 1 := by
            simp
            change
              (Matrix.blockDiagonal'
                  (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) = 1
            exact
              (Matrix.blockDiagonal'_one (o := Fin r) (m' := fun k => Fin (dim k)) (α := ℂ))
  · -- `inv * val = 1`
    calc
      Matrix.blockDiagonal' (fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) *
          Matrix.blockDiagonal' (fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
          = Matrix.blockDiagonal'
              (fun k =>
                ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
                  (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
            simpa using
              (Matrix.blockDiagonal'_mul
                (M := fun k => ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
                (N := fun k => (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))).symm
      _ = 1 := by
            simp
            change
              (Matrix.blockDiagonal'
                  (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) = 1
            exact
              (Matrix.blockDiagonal'_one (o := Fin r) (m' := fun k => Fin (dim k)) (α := ℂ))

end BlockDiagonalGL

/-!
## Reindexing `GL`

The constructor `toTensorFromBlocks` uses `Matrix.reindex` to turn a `Σ`-indexed block-diagonal
matrix into a `Fin`-indexed matrix.  Since `Matrix.reindexAlgEquiv` is an algebra equivalence, it
maps units to units, hence gives a multiplicative equivalence on `GL`.
-/

section ReindexGL

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Transport a `GL` element across a reindexing equivalence. -/
noncomputable def reindexGL (e : m ≃ n) : GL m ℂ ≃* GL n ℂ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv.toMulEquiv

@[simp] lemma reindexGL_coe (e : m ≃ n) (X : GL m ℂ) :
    ((reindexGL (m := m) (n := n) e X : GL n ℂ) : Matrix n n ℂ) =
      Matrix.reindex e e (X : Matrix m m ℂ) := by
  rfl

end ReindexGL

/-!
## Block-diagonal gauge assembly

If each block tensor satisfies a gauge relation
$$
  B_k(i) = X_k A_k(i) X_k^{-1},
$$
then the corresponding block-diagonal tensors constructed by `toTensorFromBlocks` are related by a
*global* gauge transform given by the reindexed block-diagonal matrix.
-/

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
  -- `Σ`-type indices and reindexing equivalence.
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv (m := r) (n := dim)
  -- View `reindex` as a monoid hom so we can use `map_mul`.
  let f : Matrix α α ℂ →* Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv.toMonoidHom
  -- Block-diagonal gauge matrix on `α` and its reindexing to `Fin (∑ dim)`.
  let Xσ : GL α ℂ := blockDiagonalGL (r := r) (dim := dim) X
  let Xfin : GL (Fin (∑ k : Fin r, dim k)) ℂ := Units.map f Xσ
  refine ⟨Xfin, ?_⟩
  intro i
  -- Abbreviations for the `α`-indexed block-diagonal tensors.
  let BD_A : Matrix α α ℂ :=
    Matrix.blockDiagonal' (fun k : Fin r => (μ k) • (A k i))
  let BD_B : Matrix α α ℂ :=
    Matrix.blockDiagonal' (fun k : Fin r => (μ k) • (B k i))
  let XBD : Matrix α α ℂ :=
    Matrix.blockDiagonal' (fun k : Fin r =>
      (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
  let XBDinv : Matrix α α ℂ :=
    Matrix.blockDiagonal' (fun k : Fin r =>
      ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))

  -- Unfold the `Fin`-indexed block-diagonal tensors as reindexings of the `α`-indexed ones.
  have htoA : toTensorFromBlocks (d := d) (μ := μ) A i = f BD_A := by
    simp [toTensorFromBlocks, BD_A, f, e]
    rfl
  have htoB : toTensorFromBlocks (d := d) (μ := μ) B i = f BD_B := by
    simp [toTensorFromBlocks, BD_B, f, e]
    rfl

  -- Blockwise scaling + conjugation.
  have hblock :
      (fun k : Fin r => (μ k) • (B k i)) =
        fun k : Fin r =>
          (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
            ((μ k) • (A k i)) *
              ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
    funext k
    -- Rewrite `B k i` using the gauge relation, then move the scalar onto the middle factor.
    have hBk : B k i =
        (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
      simpa using hX k i
    -- Now manipulate the scalar factor.
    calc
      (μ k) • (B k i) =
          (μ k) •
            ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
              (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
            simp [hBk]
      _ =
          ((μ k) • ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i)) *
            (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
            -- Pull the scalar out of the right multiplication.
            simpa [Matrix.mul_assoc] using
              (Matrix.smul_mul (μ k)
                ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i)
                (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)).symm
      _ =
          ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * ((μ k) • (A k i))) *
            (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
            -- Move the scalar onto `A k i`.
            -- `X * (μ • A) = μ • (X * A)`.
            simpa [Matrix.mul_assoc] using
              congrArg (fun M : Matrix (Fin (dim k)) (Fin (dim k)) ℂ =>
                M * (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
                (Matrix.mul_smul
                  (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (μ k) (A k i) |>.symm)
      _ =
          (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
            ((μ k) • (A k i)) *
              (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
            simp [Matrix.mul_assoc]
      _ =
          (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
            ((μ k) • (A k i)) *
              ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
            -- Convert the inverse coming from `GL` into the matrix inverse.
            simpa [Matrix.GeneralLinearGroup.coe_inv]

  -- Factor the block diagonal into a product of block diagonals.
  have hBD : BD_B = XBD * BD_A * XBDinv := by
    have hrewrite :
        (fun k : Fin r => (μ k) • (B k i)) =
          fun k : Fin r =>
            (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
              ((μ k) • (A k i)) *
                ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := hblock
    calc
      BD_B =
          Matrix.blockDiagonal' (fun k : Fin r =>
            (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
              ((μ k) • (A k i)) *
                ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
            simp [BD_B, hrewrite]
      _ =
          Matrix.blockDiagonal'
              (fun k : Fin r =>
                (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) *
                  ((μ k) • (A k i))) *
            Matrix.blockDiagonal'
              (fun k : Fin r =>
                ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) := by
            -- Split off the right factor blockwise.
            simpa [Matrix.mul_assoc] using
              (Matrix.blockDiagonal'_mul
                (M := fun k : Fin r =>
                  (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * ((μ k) • (A k i)))
                (N := fun k : Fin r =>
                  ((X k)⁻¹ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)))
      _ = (XBD * BD_A) * XBDinv := by
            -- Split the left factor blockwise using `blockDiagonal'_mul`.
            have hleft :
                Matrix.blockDiagonal'
                    (fun k : Fin r =>
                      (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * ((μ k) • (A k i))) =
                  XBD * BD_A := by
                simpa [XBD, BD_A] using
                  (Matrix.blockDiagonal'_mul
                    (M := fun k : Fin r =>
                      (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
                    (N := fun k : Fin r =>
                      (μ k) • (A k i)))
            rw [hleft]
      _ = XBD * BD_A * XBDinv := by
            simp [Matrix.mul_assoc, Matrix.GeneralLinearGroup.coe_inv]

  -- Push the `α`-indexed equality through `f` (i.e. through `reindex`).
  rw [htoB, htoA]
  have hXfin :
      (Xfin : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ) = f XBD := by
    simp [Xfin, Xσ, XBD, f, blockDiagonalGL]
  have hXfin_inv :
      ((Xfin⁻¹ : GL (Fin (∑ k : Fin r, dim k)) ℂ) :
        Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ) = f XBDinv := by
    simp [Xfin, Xσ, XBDinv, f, blockDiagonalGL]

  calc
    f BD_B = f (XBD * BD_A * XBDinv) := by
          simpa [hBD]
    _ = f XBD * f BD_A * f XBDinv := by
          -- `f` is multiplicative.
          simp [Matrix.mul_assoc, map_mul]
    _ = (Xfin : Matrix _ _ ℂ) * f BD_A *
          ((Xfin⁻¹ : GL (Fin (∑ k : Fin r, dim k)) ℂ) : Matrix _ _ ℂ) := by
          simp [hXfin, hXfin_inv, Matrix.mul_assoc]

/-- Block-diagonal gauge assembly from blockwise `GaugeEquiv`. -/
theorem gaugeEquiv_toTensorFromBlocks_of_blockGauge
    (hGauge : ∀ k : Fin r, GaugeEquiv (A k) (B k)) :
    GaugeEquiv (toTensorFromBlocks (d := d) (μ := μ) A)
      (toTensorFromBlocks (d := d) (μ := μ) B) := by
  classical
  choose X hX using hGauge
  exact gaugeEquiv_toTensorFromBlocks_of_blockConj (d := d) (μ := μ) (A := A) (B := B) X hX

end GaugeAssembly

/-!
## Multi-block Fundamental Theorem (parametric version)

This is the pragmatic multi-block statement used in the project: we assume per-block MPV equality
(`SameMPV`) and injectivity, then assemble the resulting blockwise gauge transforms.
-/

section FundamentalTheoremMulti

variable {r : ℕ} {dim : Fin r → ℕ}
variable (μ : Fin r → ℂ)
variable (A B : (k : Fin r) → MPSTensor d (dim k))

/-- Blockwise application of the single-block Fundamental Theorem. -/
theorem fundamentalTheorem_multiBlock_blocks
    (hA : ∀ k : Fin r, IsInjective (A k))
    (hSame : ∀ k : Fin r, SameMPV (A k) (B k)) :
    ∀ k : Fin r, GaugeEquiv (A k) (B k) := by
  intro k
  exact fundamentalTheorem_singleBlock (hA k) (hSame k)

/-- Global multi-block Fundamental Theorem (assembly version). -/
theorem fundamentalTheorem_multiBlock_global
    (hA : ∀ k : Fin r, IsInjective (A k))
    (hSame : ∀ k : Fin r, SameMPV (A k) (B k)) :
    GaugeEquiv (toTensorFromBlocks (d := d) (μ := μ) A)
      (toTensorFromBlocks (d := d) (μ := μ) B) := by
  -- First obtain blockwise gauge equivalence.
  have hGauge : ∀ k : Fin r, GaugeEquiv (A k) (B k) :=
    fundamentalTheorem_multiBlock_blocks (d := d) (A := A) (B := B) hA hSame
  -- Then assemble into a block-diagonal gauge.
  exact gaugeEquiv_toTensorFromBlocks_of_blockGauge (d := d) (μ := μ) (A := A) (B := B) hGauge

end FundamentalTheoremMulti

end MPSTensor

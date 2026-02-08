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
            simp only [Matrix.mul_inv_of_invertible]
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
            simp only [Matrix.inv_mul_of_invertible]
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
      simp [hX]
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
            simp [Matrix.mul_assoc]
      _ =
          ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * ((μ k) • (A k i))) *
            (((X k)⁻¹ : GL (Fin (dim k)) ℂ) : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
            -- Move the scalar onto `A k i`.
            -- `X * (μ • A) = μ • (X * A)`.
            simp [Matrix.mul_assoc]
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
            simp
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
            simp [Matrix.mul_assoc]
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
          simp [hBD]
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

/-!
## Bridge to `CanonicalForm`

We show that `CanonicalForm.toTensor` and `toTensorFromBlocks` agree, then lift the multi-block
theorem to the `CanonicalForm` API.
-/

section CanonicalFormBridge

open CanonicalForm

/-- `CanonicalForm.toTensor` agrees with `toTensorFromBlocks`. -/
theorem CanonicalForm.toTensor_eq_toTensorFromBlocks (C : CanonicalForm d) :
    C.toTensor = toTensorFromBlocks C.μ C.blockTensor := by
  rfl

/-- If two block-tensor families over the same skeleton have pairwise `SameMPV`,
the induced block-diagonal tensors are gauge equivalent. -/
theorem fundamentalTheorem_canonicalForm_sameStructure
    (C : CanonicalForm d)
    (B : (k : Fin C.numBlocks) → MPSTensor d (C.blockDim k))
    (hB_inj : ∀ k, IsInjective (C.blockTensor k))
    (hSame : ∀ k, SameMPV (C.blockTensor k) (B k)) :
    GaugeEquiv (C.toTensor) (toTensorFromBlocks C.μ B) := by
  rw [C.toTensor_eq_toTensorFromBlocks]
  exact fundamentalTheorem_multiBlock_global C.μ C.blockTensor B hB_inj hSame

end CanonicalFormBridge

/-!
## Converse and global `SameMPV` transfer

The converse direction: global gauge equivalence implies global `SameMPV` (unconditional).
Also: per-block `SameMPV` implies global `SameMPV` for the block-diagonal tensors.
-/

section Converse

variable {r : ℕ} {dim : Fin r → ℕ}

/-- Global gauge equivalence of block-diagonal tensors implies they generate the same MPV
family. This is an immediate consequence of `GaugeEquiv.sameMPV`. -/
theorem gaugeEquiv_toTensorFromBlocks_implies_sameMPV
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hGauge : GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  GaugeEquiv.sameMPV hGauge

/-- Per-block `SameMPV` implies global `SameMPV` for the block-diagonal tensors.

The proof goes through `mpv_toTensor_eq_sum` on both sides: each MPV expands as
`∑ k, μ_k^N · mpv(blockTensor_k)(σ)`, and the per-block hypothesis makes the summands agree. -/
theorem sameMPV_toTensorFromBlocks_of_blockSameMPV
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    SameMPV (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) := by
  -- Build canonical forms to use `mpv_toTensor_eq_sum`.
  -- We work directly with `toTensorFromBlocks` and expand both sides.
  intro N σ
  -- Build CanonicalForms for A and B sides (with dummy injectivity).
  -- Instead, unfold everything manually.
  -- Both sides equal `∑ k, μ_k^N • mpv(A_k or B_k)(σ)` via `mpv_toTensor_eq_sum`.
  --
  -- We use the fact that `toTensorFromBlocks μ A = (C_A).toTensor` for an appropriate
  -- `CanonicalForm`, but constructing a `CanonicalForm` requires `block_injective`.
  -- Instead, we replicate the calculation directly.
  --
  -- Actually, `mpv_toTensor_eq_sum` requires a `CanonicalForm` which bundles injectivity.
  -- We don't have injectivity here. So we prove it directly by unfolding.
  simp only [mpv, coeff]
  -- Let `w` be the word for σ.
  set w := List.ofFn σ
  have hwlen : w.length = N := by simp [w]
  -- Abbreviations for the `Σ`-type index.
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k, dim k) := finSigmaFinEquiv (m := r) (n := dim)
  -- Both `toTensorFromBlocks μ X` unfold to `reindex e e ∘ blockDiagonal' (fun k => μ k • X k i)`.
  -- Trace is invariant under reindex.
  -- evalWord commutes with reindex.
  -- evalWord of blockDiagonal' with scaling gives blockDiagonal' with μ^N scaling.
  -- Trace of blockDiagonal' is sum of traces.
  let BD_A : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)
  let BD_B : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • B k i)
  -- Step 1: evalWord of toTensorFromBlocks = reindex of evalWord of BD
  have hEvalA : MPSTensor.evalWord (toTensorFromBlocks μ A) w =
      (Matrix.reindex e e) (_root_.evalWord BD_A w) := by
    have hTensorA : (fun i : Fin d => toTensorFromBlocks μ A i) =
        fun i => (Matrix.reindex e e) (BD_A i) := by
      funext i; simp [toTensorFromBlocks, BD_A, e]; rfl
    simpa [hTensorA] using (evalWord_reindex (d := d) (e := e) (A := BD_A) w)
  have hEvalB : MPSTensor.evalWord (toTensorFromBlocks μ B) w =
      (Matrix.reindex e e) (_root_.evalWord BD_B w) := by
    have hTensorB : (fun i : Fin d => toTensorFromBlocks μ B i) =
        fun i => (Matrix.reindex e e) (BD_B i) := by
      funext i; simp [toTensorFromBlocks, BD_B, e]; rfl
    simpa [hTensorB] using (evalWord_reindex (d := d) (e := e) (A := BD_B) w)
  rw [hEvalA, hEvalB]
  -- Step 2: Remove reindex from trace
  rw [Matrix.trace_reindex, Matrix.trace_reindex]
  -- Step 3: Expand evalWord of BD into blockDiagonal'
  have hBDA : _root_.evalWord BD_A w =
      Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • _root_.evalWord (A k) w) := by
    simpa [BD_A] using (evalWord_blockDiagonal'_smul (μ := μ) (A := A) w)
  have hBDB : _root_.evalWord BD_B w =
      Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • _root_.evalWord (B k) w) := by
    simpa [BD_B] using (evalWord_blockDiagonal'_smul (μ := μ) (A := B) w)
  rw [hBDA, hBDB]
  -- Step 4: Trace of blockDiagonal' = sum of traces
  rw [Matrix.trace_blockDiagonal', Matrix.trace_blockDiagonal']
  -- Step 5: Per-block SameMPV makes the summands equal
  congr 1; funext k
  rw [Matrix.trace_smul, Matrix.trace_smul, hwlen]
  congr 1
  -- Convert _root_.evalWord to MPSTensor.evalWord, then use hSame
  simp only [evalWord_aux_eq]
  exact (hSame k N σ)

end Converse

end MPSTensor

# MultiBlock.lean audit / repair plan

_Date_: 2026-02-08

## 0. What I actually found in this repository

In the current snapshot, there is **no** file `MPSLean/MPS/MultiBlock.lean`.

What *is* present is `MPSLean/MPS/CanonicalForm.lean`, which already contains the core multi-block bookkeeping:

- `MPSTensor.CanonicalForm` (block count, block dimensions, block tensors, scalars `μ`, injectivity hypotheses)
- `CanonicalForm.totalDim`
- `CanonicalForm.toTensor` built from `Matrix.blockDiagonal'` and a `Matrix.reindex` along `finSigmaFinEquiv`

So the “multi-block” story appears to be **planned but not yet implemented**.

The remainder of this document is therefore written as a **forward-looking audit** of the *typical* lemmas you will need in a future `MultiBlock.lean`, based on the definitions you already chose (and on the common failure modes when trying to prove these lemmas with `simp`).

If you *do* have a draft `MultiBlock.lean` elsewhere (or under another name), you can treat the lemma names below as a checklist: each item comes with a recommended statement and a proof strategy that is robust in Mathlib.

---

## 1. Letter to the author (high-level guidance)

You made a great choice in `CanonicalForm.toTensor`: build a dependent block diagonal matrix

- `BD := Matrix.blockDiagonal' blocks` on the **Sigma index type** `((k : Fin numBlocks) × Fin (blockDim k))`

and only at the end move to the concrete `Fin totalDim` index type by

- `Matrix.reindex (finSigmaFinEquiv ...) (finSigmaFinEquiv ...)`.

That design lets most proofs stay “block-structured” and avoid painful `Fin` arithmetic.

The main advice for the future multi-block development is:

1. **Stay on Sigma indices as long as possible.**
   Any lemma whose conclusion is an entrywise statement on `Fin totalDim` indices is likely to become a cast/permutation fight.

2. Use Mathlib’s block-diagonal API rather than unfolding definitions:

   - `Matrix.blockDiagonal'_apply_eq` and `Matrix.blockDiagonal'_apply_ne`
   - `Matrix.blockDiagonal'_mul`
   - `Matrix.blockDiagonal'_smul`
   - `Matrix.trace_blockDiagonal'`

3. Add a small “glue” layer of lemmas you can reuse everywhere:

   - `trace_reindex`:
     `Matrix.trace (Matrix.reindex e e M) = Matrix.trace M`
   - `evalWord_reindex`:
     `evalWord (fun i => Matrix.reindex e e (A i)) w = Matrix.reindex e e (evalWord A w)`

   These are true because `Matrix.reindex` is an algebra equivalence (`Matrix.reindexAlgEquiv`) for square matrices.

4. Avoid proving block-permutation facts by entrywise calculation on `Fin (∑ k, blockDim k)`.
   Instead, prove a reindexing lemma on Sigma types using `Equiv.sigmaCongrLeft'`.

---

## 2. Checklist of expected MultiBlock lemmas and how to do them

Below are the “usual suspects” for a `MultiBlock.lean` that continues from `CanonicalForm.lean`.
I list each item with (i) status, (ii) recommended statement, and (iii) proof strategy.

### 2.1 `renameCanon` (permute blocks)

**Status:** should be *kept*, but do it inside `CanonicalForm` and make the type-casts explicit.

**Recommended definition (sketch):**

- Input: `C : CanonicalForm d` and a permutation `π : Fin C.numBlocks ≃ Fin C.numBlocks`.
- Output: canonical form with the same `numBlocks`, but
  - `blockDim' k := C.blockDim (π k)`
  - `blockTensor' k := C.blockTensor (π k)`
  - `μ' k := C.μ (π k)`

**Proof obligations:** injectivity of each block transports trivially.

**Pitfall:** `totalDim` becomes a *definitional* sum over `blockDim'`; you’ll need a lemma

- `totalDim_renameCanon : (renameCanon C π).totalDim = C.totalDim`

proved by `Finset.sum_equiv` (a permutation on `Fin n`), not by `simp`.

---

### 2.2 `blockDiagonal_renameCanon_eq`

**Status:** *rewrite required* (don’t try to `simp` this with `Fin` indices).

**What you actually want:** a reindexing statement on Sigma indices.

Let `blocks : (k : Fin n) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ` and define renamed blocks
`blocks' k := blocks (π k)` with `dim' k := dim (π k)`.

Then the block diagonal matrices are the same up to reindexing by a Sigma equivalence:

- the equivalence on row/col indices is `Equiv.sigmaCongrLeft' π` (or a small variant) so that
  `((k) × Fin (dim k))` is transported to `((k) × Fin (dim' k))`.

**Strategy:**

- Prove equality by `Matrix.ext` on Sigma indices.
- Use `Matrix.blockDiagonal'_apply` (or `_apply_eq` / `_apply_ne`) to reduce both sides.
- Avoid unfolding `blockDiagonal'` beyond what `simp` already knows.

---

### 2.3 `reindex_finSigmaFinEquiv_blockDiagonal'_apply_same/diff`

**Status:** strongly consider *deleting* these lemmas.

These are the typical “entrywise after the `Fin` reindexing” statements:

- **same block** ⇒ entry equals the corresponding block entry
- **different block** ⇒ entry is zero

They are true, but proving them directly is painful because it requires reasoning about
`finSigmaFinEquiv.symm` and casts inside `Fin`.

**Replacement:**

- Do all block-structured reasoning on Sigma indices.
- Only use reindexing at the end for trace-level statements, via a lemma like `trace_reindex`.

If you really need an entrywise lemma on `Fin totalDim`, prove it via:

1. Rewrite `Matrix.reindex` as `submatrix` using `Matrix.reindex_apply`.
2. Rewrite `blockDiagonal'` entries using `Matrix.blockDiagonal'_apply`.
3. Keep the statement in terms of `finSigmaFinEquiv.symm i` rather than trying to simplify it.

This yields a lemma that is usable (because it’s explicit) even if it isn’t pretty.

---

### 2.4 `toTensor_renameCanon_eq`

**Status:** *rewrite required / restate*.

If `renameCanon` permutes blocks, then `toTensor` will typically not be *definitionally equal*.
What is true is that it is equal **up to a reindexing of `Fin totalDim`**, i.e. conjugation by a
permutation matrix.

**Recommended statement:**

- either an explicit `Matrix.reindex`-equality (preferred):

  `toTensor (renameCanon C π) i = Matrix.reindex e e (toTensor C i)`

  for an appropriate `e : Fin C.totalDim ≃ Fin C.totalDim` induced by the block permutation;

- or a gauge-style statement: there exists a permutation matrix `P : GL (Fin totalDim) ℂ` such that
  `(toTensor (renameCanon C π)) i = P * (toTensor C i) * P⁻¹`.

**Strategy:**

- Construct the equivalence on Sigma indices using `Equiv.sigmaCongrLeft' π`.
- Then transport to `Fin totalDim` via `finSigmaFinEquiv`.
- Use `Matrix.reindex_trans` to compose the reindexings.

---

### 2.5 `mpv_toTensor_eq_sum` (MPV of a block diagonal tensor)

**Status:** *very valuable lemma; rewrite required if attempted via entrywise expansions*.

**Target statement (typical):** for `C : CanonicalForm d` and `N : ℕ` and `σ : Fin N → Fin d`,

\[
  mpv (C.toTensor)\,σ
  = \sum_{k : Fin C.numBlocks}
      (C.μ k)^{N} \cdot mpv (C.blockTensor k)\,σ.
\]

(or with `coeff`/`evalWord` and `w := List.ofFn σ`).

**Proof strategy (robust):**

1. Work with the word `w := List.ofFn σ` and rewrite `mpv` as `trace (evalWord ...)`.

2. Prove an `evalWord` lemma for the Sigma-index block diagonal tensor:

   - `evalWord (fun i => Matrix.blockDiagonal' (fun k => (μ k) • blockTensor k i)) w`
     is `Matrix.blockDiagonal' (fun k => (μ k)^(w.length) • evalWord (blockTensor k) w)`.

   This is a straightforward induction using:

   - `Matrix.blockDiagonal'_mul`
   - `Matrix.blockDiagonal'_smul`
   - and `simp [MPSTensor.evalWord, Matrix.mul_assoc]`.

3. Move from Sigma indices to `Fin totalDim` **only using trace**:

   - add lemma `trace_reindex` so you can replace
     `trace (Matrix.reindex e e M)` with `trace M`.

4. Apply `Matrix.trace_blockDiagonal'` to turn the trace of a block diagonal into a sum of traces.

This route avoids all hard `Fin`-index computations.

---

## 3. Minimal helper lemmas I recommend adding (in a future PR)

These are small, local lemmas that make the multi-block file pleasant.

### 3.1 Trace invariance under reindex

```lean
lemma Matrix.trace_reindex {n n' : Type*} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n']
    (e : n ≃ n') (M : Matrix n n ℂ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  classical
  -- `trace` is a sum over diagonal entries and `e.symm` is a permutation.
  simp [Matrix.trace, Matrix.reindex_apply, Finset.sum_equiv e.symm]
```

(You may need to massage `simp` a bit; the idea is stable.)

### 3.2 `evalWord` respects reindex (algebra equivalence)

Use `Matrix.reindexAlgEquiv` from `Mathlib/LinearAlgebra/Matrix/Reindex`.

```lean
lemma evalWord_reindex (e : Fin D ≃ Fin D') (A : MPSTensor d D) (w) :
    evalWord (fun i => Matrix.reindex e e (A i)) w
      = Matrix.reindex e e (evalWord A w) := by
  classical
  induction w with
  | nil => simp [MPSTensor.evalWord]
  | cons i w ih =>
      simp [MPSTensor.evalWord, ih, Matrix.mul_assoc, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
```

(Depending on your imports, you can replace the last line by a one-liner using `Matrix.reindexAlgEquiv` and `map_mul`.)

---

## 4. Suggested file organisation

- Keep the existing `CanonicalForm.lean` as “pure data + `toTensor` construction”.
- Create `MultiBlock.lean` that imports `CanonicalForm` and proves:
  - permutation invariance lemmas (`renameCanon`, `toTensor_renameCanon` up to reindex/gauge)
  - the key MPV decomposition lemma (`mpv_toTensor_eq_sum`)
  - any uniqueness-of-canonical-form / block-matching results later.

This separation prevents `CanonicalForm.lean` from turning into a “proof jungle” while you iterate.

---

## 5. Mathlib facts that should be your workhorses

From the current Mathlib (v4.27.0 as pinned in `lake-manifest.json`):

- `Matrix.blockDiagonal'_apply`, `Matrix.blockDiagonal'_apply_eq`, `Matrix.blockDiagonal'_apply_ne`
- `Matrix.blockDiagonal'_mul`
- `Matrix.blockDiagonal'_smul`
- `Matrix.trace_blockDiagonal'`
- `Matrix.reindex_apply`, `Matrix.reindex_trans`
- `Matrix.reindexAlgEquiv` / `Matrix.reindexLinearEquiv_mul`
- `Equiv.sigmaCongrLeft` / `Equiv.sigmaCongrLeft'`
- `finSigmaFinEquiv` (`Mathlib/Algebra/BigOperators/Fin`)


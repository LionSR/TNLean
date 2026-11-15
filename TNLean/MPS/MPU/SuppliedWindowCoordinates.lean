/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteSuppliedWindow
import TNLean.MPS.MPU.TwoSiteBufferedAction

/-!
# Physical relabelling and canonical coordinates of supplied windows

Physical letters may be labelled by any finite alphabet equivalent to
the two-half-site alphabet. The complete three-cell input/output windows
and their arbitrary buffers are transported sitewise through that
actual equivalence. No quasi-local relabelling automorphism is introduced.

Source: CPSV17, StandardForm and eq:appendix-1, lines 603–622 and
2300–2306; physical reindexing in IndexTh(ii), lines 824–847.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- A physical half-pair gives the singleton-cell configuration with
constant letter e.symm(finProdFinEquiv c). Source: CPSV17 StandardForm,
lines 603–622, in an equivalent physical alphabet. -/
def twoSiteSuppliedCellEquiv {d b : ℕ} (e : Fin b ≃ Fin (d * d)) :
    (Fin d × Fin d) ≃ (Fin 1 → Fin b) :=
  finProdFinEquiv.trans (e.symm.trans (Equiv.funUnique (Fin 1) (Fin b)).symm)

/-- Complete input coordinates of the fixed three-cell window after
sitewise physical relabelling. Source: CPSV17 StandardForm, lines 603–622. -/
def twoSiteSuppliedInputWindowEquiv {d b : ℕ} (e : Fin b ≃ Fin (d * d)) :
    ((Fin (d * d) × Fin (d * d)) × (Fin d × Fin d)) ≃ (Fin 3 → Fin b) :=
  (windowInputHeadEquiv d).trans (reindexPhysicalConfigEquiv 3 e).symm

/-- The output order is exterior half-pair followed by the four actual
output half-sites, then sitewise physical relabelling.
Source: CPSV17 StandardForm, lines 603–622. -/
def twoSiteSuppliedOutputWindowEquiv {d b : ℕ} (e : Fin b ≃ Fin (d * d)) :
    ((Fin d × Fin d) × ((Fin d × Fin d) × (Fin d × Fin d))) ≃ (Fin 3 → Fin b) :=
  (windowOutputHeadEquiv d).trans (reindexPhysicalConfigEquiv 3 e).symm

/-- The actual central input matrix on the three supplied cells.
Source: CPSV17 StandardForm, lines 603–622. -/
noncomputable def twoSiteSuppliedInputWindow {d b : ℕ} (e : Fin b ≃ Fin (d * d))
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin 3 → Fin b) (Fin 3 → Fin b) ℂ :=
  Matrix.reindex (twoSiteSuppliedInputWindowEquiv e)
    (twoSiteSuppliedInputWindowEquiv e)
    (Matrix.rightKroneckerEmbed (m := Fin (d * d) × Fin (d * d)) A)

/-- The actual four-half-site output, with identity exterior halves,
on the same three supplied cells. Source: CPSV17 StandardForm,
lines 603–622 and eq:appendix-1, lines 2300–2306. -/
noncomputable def twoSiteSuppliedOutputWindow {d b ℓ r : ℕ}
    (e : Fin b ≃ Fin (d * d))
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin 3 → Fin b) (Fin 3 → Fin b) ℂ :=
  Matrix.reindex (twoSiteSuppliedOutputWindowEquiv e)
    (twoSiteSuppliedOutputWindowEquiv e)
    (Matrix.rightKroneckerEmbed (m := Fin d × Fin d) (twoLinkOutputObservable u v A))

private theorem suppliedWindow_matrix_eq_buffer
    {d p s : ℕ} {E C : Type*} [Fintype E] [Fintype C]
    [DecidableEq E] [DecidableEq C]
    (head : (E × C) ≃ (Fin 3 → Fin (d * d)))
    (full : (((Fin p → Fin (d * d)) × (E × (Fin s → Fin (d * d)))) × C) ≃
      (Fin (p + (3 + s)) → Fin (d * d)))
    (hfull : ∀ pre ex suf c, full ((pre, (ex, suf)), c) =
      bufferedWindowConfigEquiv (d * d) 3 p s ((pre, suf), head (ex, c)))
    (A : Matrix C C ℂ) :
    Matrix.reindex full full (Matrix.rightKroneckerEmbed A) =
      bufferedWindowMatrix (d * d) 3 p s
        (Matrix.reindex head head (Matrix.rightKroneckerEmbed A)) := by
  classical
  ext row col
  obtain ⟨⟨⟨pre, ex, suf⟩, c⟩, rfl⟩ := full.surjective row
  obtain ⟨⟨⟨pre', ex', suf'⟩, c'⟩, rfl⟩ := full.surjective col
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [hfull, hfull]
  simp only [bufferedWindowMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases hp : pre = pre' <;> by_cases hs : suf = suf' <;>
    by_cases he : ex = ex' <;> simp [hp, hs, he]

/-- Direct supplied-tensor conjugation as a canonical three-cell
window with arbitrary complete-cell exterior buffers.
Source: CPSV17 StandardForm and eq:appendix-1, lines 603–622 and 2300–2306. -/
theorem mpo_suppliedBufferedWindow_conjugation {d D ℓ r : ℕ}
    {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (p s : ℕ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    mpo W (p + (3 + s)) *
        bufferedWindowMatrix (d * d) 3 p s (twoSiteSuppliedInputWindow (Equiv.refl _) A) *
        (mpo W (p + (3 + s)))ᴴ =
      bufferedWindowMatrix (d * d) 3 p s
        (twoSiteSuppliedOutputWindow (Equiv.refl _) u v A) := by
  have hi := suppliedWindow_matrix_eq_buffer (windowInputHeadEquiv d)
    (twoSiteSuppliedInputEquiv d p s) (fun _ _ _ _ => rfl) A
  have ho := suppliedWindow_matrix_eq_buffer (windowOutputHeadEquiv d)
    (twoSiteSuppliedOutputEquiv d p s) (fun _ _ _ _ => rfl)
    (twoLinkOutputObservable u v A)
  have h := mpo_suppliedWindow_conjugation S p s A
  rw [hi, ho] at h
  exact h

private theorem bufferedWindowConfig_reindexPhysical
    {b d n p s : ℕ} (e : Fin b ≃ Fin d)
    (pre : Fin p → Fin b) (suf : Fin s → Fin b) (mid : Fin n → Fin b) :
    reindexPhysicalConfigEquiv (p + (n + s)) e
        (bufferedWindowConfigEquiv b n p s ((pre, suf), mid)) =
      bufferedWindowConfigEquiv d n p s
        ((reindexPhysicalConfigEquiv p e pre, reindexPhysicalConfigEquiv s e suf),
          reindexPhysicalConfigEquiv n e mid) := by
  funext i
  change e (Fin.append pre (Fin.append mid suf) i) =
    Fin.append (fun j => e (pre j))
      (Fin.append (fun j => e (mid j)) (fun j => e (suf j))) i
  refine Fin.addCases (fun _ => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
  · refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j
    · simp only [Fin.append_right, Fin.append_left]
    · simp only [Fin.append_right]

/-- Sitewise physical reindexing commutes with adjoining identity
buffers to a finite matrix window. Source: CPSV17 identity-tensor
inclusion, lines 2292–2295, and IndexTh(ii), lines 824–847. -/
theorem bufferedWindowMatrix_reindexPhysical {b d n p s : ℕ}
    (e : Fin b ≃ Fin d) (A : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix.reindex (reindexPhysicalConfigEquiv (p + (n + s)) e).symm
        (reindexPhysicalConfigEquiv (p + (n + s)) e).symm
        (bufferedWindowMatrix d n p s A) =
      bufferedWindowMatrix b n p s
        (Matrix.reindex (reindexPhysicalConfigEquiv n e).symm
          (reindexPhysicalConfigEquiv n e).symm A) := by
  classical
  ext row col
  obtain ⟨⟨⟨pre, suf⟩, mid⟩, rfl⟩ := (bufferedWindowConfigEquiv b n p s).surjective row
  obtain ⟨⟨⟨pre', suf'⟩, mid'⟩, rfl⟩ := (bufferedWindowConfigEquiv b n p s).surjective col
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [bufferedWindowConfig_reindexPhysical, bufferedWindowConfig_reindexPhysical]
  simp only [bufferedWindowMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.mk.injEq, Equiv.apply_eq_iff_eq]

/-- Canonical supplied-window conjugation after any bijective physical
relabelling, with arbitrary complete-cell buffers. No standard-form
preimage under blocking is added.
Source: CPSV17 StandardForm, eq:appendix-1 and IndexTh(ii),
lines 603–622, 2300–2306 and 824–847. -/
theorem mpo_reindexPhysical_suppliedBufferedWindow_conjugation
    {d b D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (e : Fin b ≃ Fin (d * d)) (S : TwoSiteStandardFormData W u v) (p s : ℕ)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    mpo (reindexPhysical e W) (p + (3 + s)) *
        bufferedWindowMatrix b 3 p s (twoSiteSuppliedInputWindow e A) *
        (mpo (reindexPhysical e W) (p + (3 + s)))ᴴ =
      bufferedWindowMatrix b 3 p s (twoSiteSuppliedOutputWindow e u v A) := by
  let E := reindexPhysicalConfigEquiv (p + (3 + s)) e
  have h := congrArg (Matrix.reindexRingEquiv ℂ E.symm)
    (mpo_suppliedBufferedWindow_conjugation S p s A)
  simp only [map_mul] at h
  change Matrix.reindex E.symm E.symm (mpo W (p + (3 + s))) *
      Matrix.reindex E.symm E.symm
        (bufferedWindowMatrix (d * d) 3 p s (twoSiteSuppliedInputWindow (Equiv.refl _) A)) *
      Matrix.reindex E.symm E.symm (mpo W (p + (3 + s)))ᴴ =
        Matrix.reindex E.symm E.symm (bufferedWindowMatrix (d * d) 3 p s
          (twoSiteSuppliedOutputWindow (Equiv.refl _) u v A)) at h
  rw [← Matrix.conjTranspose_reindex] at h
  have hM : Matrix.reindex E.symm E.symm (mpo W (p + (3 + s))) =
      mpo (reindexPhysical e W) (p + (3 + s)) := (mpo_reindexPhysical e W _).symm
  simp only [hM] at h
  dsimp only [E] at h
  simp only [bufferedWindowMatrix_reindexPhysical] at h
  exact h

private theorem suppliedInputWindow_buffer_config {d b : ℕ}
    (e : Fin b ≃ Fin (d * d)) (j₀ j₂ : Fin (d * d)) (c : Fin d × Fin d) :
    twoSiteSuppliedInputWindowEquiv e ((j₀, j₂), c) =
      bufferedWindowConfigEquiv b 1 1 1
        ((fun _ => e.symm j₀, fun _ => e.symm j₂), twoSiteSuppliedCellEquiv e c) := by
  funext i
  fin_cases i <;> rfl

private theorem const_word_eq {α β : Type*} (e : α ≃ β) (x y : α) :
    (fun _ : Fin 1 => e x) = (fun _ : Fin 1 => e y) ↔ x = y := by
  constructor
  · intro h
    exact e.injective (congrFun h 0)
  · rintro rfl
    rfl

/-- The supplied three-cell input is exactly the singleton input with
one identity cell adjoined on each side, in the relabelled alphabet.
Source: CPSV17 StandardForm and identity-tensor inclusion,
lines 603–622 and 2292–2295. -/
theorem twoSiteSuppliedInputWindow_eq_bufferedCell {d b : ℕ}
    (e : Fin b ≃ Fin (d * d))
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    twoSiteSuppliedInputWindow e A = bufferedWindowMatrix b 1 1 1
      (Matrix.reindex (twoSiteSuppliedCellEquiv e) (twoSiteSuppliedCellEquiv e) A) := by
  classical
  ext row col
  obtain ⟨⟨⟨j₀, j₂⟩, c⟩, rfl⟩ := (twoSiteSuppliedInputWindowEquiv e).surjective row
  obtain ⟨⟨⟨j₀', j₂'⟩, c'⟩, rfl⟩ := (twoSiteSuppliedInputWindowEquiv e).surjective col
  simp only [twoSiteSuppliedInputWindow, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [suppliedInputWindow_buffer_config, suppliedInputWindow_buffer_config]
  simp only [bufferedWindowMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Prod.mk.injEq, const_word_eq]

end MPOTensor

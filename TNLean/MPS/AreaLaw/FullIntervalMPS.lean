/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming
import TNLean.MPS.AreaLaw.OpenMPSSpan
import TNLean.MPS.AreaLaw.ViableSet.LeftCoordinates

/-!
# Native matrix product states from full-interval generators

A vector on the interval `[0,L)` is read on the chain by restricting a
chain configuration to the recorded interval sites. The existing left-block
cut identity identifies its internal regional Schmidt ranks with the native
chain cut ranks. The existing finite-span theorem then bounds every vector
in the span by the generator count times the generator bond bound.

These are coordinate and span consequences supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 660–697, and the degenerate
merge analysis, lines 1777–1817. The finite-span argument is LVV13,
arXiv:1307.5143v1, Claim `c:2`, lines 520–527. No new area law or independent
MPS approximation theorem is used.
-/

namespace TNLean.MPS.AreaLaw

/-- Read the actual full-interval vector on native chain configurations.
Supporting ALVV, arXiv:1602.08828v2, full-chain output in `t:alg1`,
lines 1777–1817. -/
def fullIntervalRead (L q : ℕ)
    (u : EuclideanSpace ℂ (interval L 0 L → Fin q)) : (Fin L → Fin q) → ℂ :=
  fun x ↦ u (fun v ↦ x v.val)

/-- The existing full-left-block cut identity, with the site region kept
as a variable until its identification with the full left block. Supporting
ALVV, arXiv:1602.08828v2, `def:trimming`, lines 646–655; LVV13,
arXiv:1307.5143v1, `def:viable`, lines 240–244. -/
private theorem rank_cutMatrix_full_region {L q : ℕ} {J : Finset (Fin L)}
    (hJ : J = leftBlock L L) (u : EuclideanSpace ℂ (J → Fin q)) (k : ℕ) :
    (cutMatrix (WithLp.toLp 2 (fun x : Fin L → Fin q ↦ u (fun v ↦ x v.val))) k).rank =
      Matrix.schmidtRank (WithLp.ofLp (Entropy.cutVector
        (Finset.univ.filter fun v : J ↦ v.val.val < k) u)) := by
  subst J
  have hconfig (x : Fin L → Fin q) : leftConfigOfFin (L := L) x =
      (fun v : {v : Fin L // v ∈ leftBlock L L} ↦ x v.val) := by
    funext v
    apply congrArg x
    apply Fin.ext
    rfl
  simpa only [hconfig] using
    rank_cutMatrix_leftConfigOfFin (L := L) (q := q) (i := L) le_rfl u k

/-- The actual internal full-interval cut is the native chain cut.
Supporting ALVV, arXiv:1602.08828v2, collective trimming,
lines 660–697, and its final full-chain merge, lines 1777–1817. -/
theorem rank_cutMatrix_fullIntervalRead {L q : ℕ}
    (u : EuclideanSpace ℂ (interval L 0 L → Fin q)) (k : ℕ) (hk : 0 < k) :
    (cutMatrix (WithLp.toLp 2 (fullIntervalRead L q u)) k).rank =
      Matrix.schmidtRank (WithLp.ofLp (Entropy.cutVector
        (intervalTrimCut L 0 L (k - 1)) u)) := by
  have hJ : interval L 0 L = leftBlock L L := by
    rw [interval_zero_eq_univ (L := L) le_rfl]
    ext v
    constructor
    · intro _
      exact mem_leftBlock.mpr v.isLt
    · intro _
      exact Finset.mem_univ v
  have hcut : (Finset.univ.filter fun v : interval L 0 L ↦ v.val.val < k) =
      intervalTrimCut L 0 L (k - 1) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      intervalTrimCut, Entropy.mem_subregionCut, mem_interval]
    omega
  have h := rank_cutMatrix_full_region hJ u k
  rw [hcut] at h
  exact h

/-- Internal rank bounds for the actual recorded full-interval vector give
its native open-boundary matrix product representation. Supporting ALVV,
arXiv:1602.08828v2, `lem:trimming`, lines 660–697. -/
theorem isOpenMPS_fullIntervalRead_of_rank_le {L q D : ℕ}
    (u : EuclideanSpace ℂ (interval L 0 L → Fin q))
    (hrank : ∀ j : ℕ, j < L - 1 → Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutVector (intervalTrimCut L 0 L j) u)) ≤ D) :
    IsOpenMPS L q D (fullIntervalRead L q u) := by
  apply (isOpenMPS_iff_internal_cutMatrix_rank_le
    (WithLp.toLp 2 (fullIntervalRead L q u))).mpr
  intro k hk0 hkL
  rw [rank_cutMatrix_fullIntervalRead u k hk0]
  exact hrank (k - 1) (by omega)

/-- The native bond bound for a span has the additional generator-count
factor. The proof reuses the existing finite-span theorem rather than
assuming the rank bound of each generator for its whole span. Supporting
LVV13, arXiv:1307.5143v1, Claim `c:2`, lines 520–527, and ALVV,
arXiv:1602.08828v2, the final merge analysis, lines 1777–1817. -/
theorem isOpenMPS_fullIntervalRead_of_mem_span {L q n D : ℕ}
    (u : Fin n → EuclideanSpace ℂ (interval L 0 L → Fin q))
    (hrank : ∀ (i : Fin n) (j : ℕ), j < L - 1 → Matrix.schmidtRank (WithLp.ofLp
      (Entropy.cutVector (intervalTrimCut L 0 L j) (u i))) ≤ D)
    {v : EuclideanSpace ℂ (interval L 0 L → Fin q)}
    (hv : v ∈ Submodule.span ℂ (Set.range u)) :
    IsOpenMPS L q (n * D) (fullIntervalRead L q v) := by
  classical
  let A : Finset ((Fin L → Fin q) → ℂ) := Finset.univ.image (fun i ↦ fullIntervalRead L q (u i))
  have hcard : A.card ≤ n := by
    calc
      A.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have hA : ∀ w ∈ A, IsOpenMPS L q D w := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact isOpenMPS_fullIntervalRead_of_rank_le (u i) (hrank i)
  let R : EuclideanSpace ℂ (interval L 0 L → Fin q) →ₗ[ℂ] ((Fin L → Fin q) → ℂ) :=
    { toFun := fullIntervalRead L q
      map_add' := by intro a b; ext x; rfl
      map_smul' := by intro c a; ext x; rfl }
  have himage : R '' Set.range u = (A : Set ((Fin L → Fin q) → ℂ)) := by
    rw [← Set.range_comp]
    change Set.range (fun i ↦ fullIntervalRead L q (u i)) = _
    simp only [A, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hv' : fullIntervalRead L q v ∈ Submodule.span ℂ (A : Set ((Fin L → Fin q) → ℂ)) := by
    change R v ∈ _
    rw [← himage]
    exact Submodule.apply_mem_span_image_of_mem_span R hv
  exact (isOpenMPS_of_mem_span A hA hv').mono (Nat.mul_le_mul_right D hcard)

end TNLean.MPS.AreaLaw

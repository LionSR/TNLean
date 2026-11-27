/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.CutRank

/-!
# Physical cuts and coordinate slicing

For a finite physical chain, the cut after `k` sites separates the configurations of the left
block `interval N 0 k` from those of the remaining sites. The cut matrix
`cutMatrix (interval N 0 k) ψ` at that cut has a column space on the left block. Fixing
the next physical letter maps the next column space into the preceding one. For a nonzero
tensor, both endpoint column spaces are one-dimensional.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the Schmidt cut-rank
interpretation is arXiv:quant-ph/0608197, local
`Papers/quant-ph_0608197/MPSarchive.tex`, lines 444--458.

It also contains the following results.

* `MPSPreparation.cutColumnBasis`, `MPSPreparation.exists_cutBasisFamily_with_endpoints`: cut bases
  with prescribed endpoint vectors.
* `MPSPreparation.cutPrefixConfigEquiv`, `MPSPreparation.cutSuffixConfigEquiv`: numbering the
  sites of the two blocks of a valid cut reads their configurations as configurations of chains
  of `k` and of `N - k` sites.
-/

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

open Matrix
open scoped BigOperators
open ManyBody (RegionConfig ComplConfig cutMatrix cutRank interval mem_interval
  cutEquiv_symm_apply_mem cutEquiv_symm_apply_not_mem)

namespace MPSPreparation

section MinimalCutRepresentationCuts

/-- A site lies in the left block of the cut after `k` sites exactly when it precedes `k`. -/
theorem mem_interval_zero_iff {N k : ℕ} {s : Fin N} : s ∈ interval N 0 k ↔ s.val < k := by
  simp

/-- A site lies after the cut after `k` sites exactly when it is at least `k`. -/
theorem notMem_interval_zero_iff {N k : ℕ} {s : Fin N} : s ∉ interval N 0 k ↔ k ≤ s.val := by
  simp

/-- At the cut after `k` sites, the configuration glued from `u` on the left block and `v` on
the remaining sites reads `u` at the sites `s < k` and `v` at the others.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEquiv_symm_interval_zero {d N k : ℕ}
    (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))
    (v : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    (ManyBody.cutEquiv (fun _ : Fin N ↦ Fin d) (interval N 0 k)).symm (u, v) = fun s ↦
      if h : s.val < k then u ⟨s, mem_interval.mpr ⟨Nat.zero_le _, h⟩⟩
      else v ⟨s, fun hm ↦ h (mem_interval.mp hm).2⟩ := by
  funext s
  by_cases h : s.val < k
  · rw [cutEquiv_symm_apply_mem _ _ (mem_interval.mpr ⟨Nat.zero_le _, h⟩)]
    simp [h]
  · rw [cutEquiv_symm_apply_not_mem _ _ fun hm ↦ h (mem_interval.mp hm).2]
    simp [h]

/-- Adjoining one physical letter to a configuration of the left block of a cut.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def extendCutPrefix {d N : ℕ} (k : ℕ)
    (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (i : Fin d) :
    RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) :=
  fun s ↦ if h : s.val < k then u ⟨s.1, mem_interval.mpr ⟨Nat.zero_le _, h⟩⟩ else i

/-- Adjoining one physical letter before a configuration of the sites after a cut.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def extendCutSuffix {d N : ℕ} (k : ℕ) (i : Fin d)
    (v : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) :
    ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) :=
  fun s ↦ if h : k + 1 ≤ s.val then
    v ⟨s.1, fun hm ↦ absurd (mem_interval.mp hm).2 (not_lt.mpr h)⟩ else i

/-- The two adjacent physical cuts agree after adjoining the same letter
to the prefix or to the suffix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutMatrix_adjacent {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (k : ℕ) (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) (i : Fin d)
    (v : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) :
    cutMatrix (interval N 0 (k + 1)) ψ (extendCutPrefix k u i) v =
      cutMatrix (interval N 0 k) ψ u (extendCutSuffix k i v) := by
  rw [ManyBody.cutMatrix_apply, ManyBody.cutMatrix_apply]
  apply congrArg ψ
  funext s
  by_cases h : s.val < k
  · rw [cutEquiv_symm_apply_mem _ _ (mem_interval.mpr ⟨Nat.zero_le _, by omega⟩),
      cutEquiv_symm_apply_mem _ _ (mem_interval.mpr ⟨Nat.zero_le _, h⟩)]
    simp [extendCutPrefix, h]
  · by_cases h' : s.val < k + 1
    · rw [cutEquiv_symm_apply_mem _ _ (mem_interval.mpr ⟨Nat.zero_le _, h'⟩),
        cutEquiv_symm_apply_not_mem _ _ fun hm ↦ h (mem_interval.mp hm).2]
      have hn : ¬ k + 1 ≤ s.val := by omega
      simp [extendCutPrefix, extendCutSuffix, h, hn]
    · rw [cutEquiv_symm_apply_not_mem _ _ fun hm ↦ h' (mem_interval.mp hm).2,
        cutEquiv_symm_apply_not_mem _ _ fun hm ↦ h (mem_interval.mp hm).2]
      have hle : k + 1 ≤ s.val := by omega
      simp [extendCutSuffix, hle]

/-- Adjoining a last prefix letter enumerates the next physical prefix
exactly once. Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
def extendCutPrefixEquiv {d N k : ℕ} (hk : k < N) :
    RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) × Fin d ≃ RegionConfig
        (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) where
  toFun ui := extendCutPrefix k ui.1 ui.2
  invFun w := (fun s ↦ w ⟨s.val, ManyBody.interval_mono le_rfl (Nat.le_succ k) s.2⟩,
    w ⟨⟨k, hk⟩, mem_interval_zero_iff.mpr (Nat.lt_succ_self k)⟩)
  left_inv := by
    rintro ⟨u, i⟩
    apply Prod.ext
    · funext s
      simp only [extendCutPrefix, mem_interval_zero_iff.mp s.property, dite_true]
    · simp only [extendCutPrefix, Nat.lt_irrefl, dite_false]
  right_inv w := by
    funext s
    by_cases hs : s.val.val < k
    · simp only [extendCutPrefix, hs, dite_true]
    · simp only [extendCutPrefix, hs, dite_false]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change k = s.val.val
      have := mem_interval_zero_iff.mp s.property
      omega

/-- Adjoining a first suffix letter enumerates the preceding physical
suffix exactly once. Source: PGVWC07, Theorem thm:OBC-Vidal, lines 431--458. -/
def extendCutSuffixEquiv {d N k : ℕ} (hk : k < N) :
    Fin d × ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) ≃ ComplConfig
        (fun _ : Fin N ↦ Fin d) (interval N 0 k) where
  toFun iv := extendCutSuffix k iv.1 iv.2
  invFun w := (w ⟨⟨k, hk⟩, notMem_interval_zero_iff.mpr le_rfl⟩,
    fun s ↦ w ⟨s.val, fun h ↦ s.2 (ManyBody.interval_mono le_rfl (Nat.le_succ k) h)⟩)
  left_inv := by
    rintro ⟨i, v⟩
    apply Prod.ext
    · simp only [extendCutSuffix, Nat.not_succ_le_self, dite_false]
    · funext s
      simp only [extendCutSuffix, notMem_interval_zero_iff.mp s.property, dite_true]
  right_inv w := by
    funext s
    by_cases hs : k + 1 ≤ s.val.val
    · simp only [extendCutSuffix, hs, dite_true]
    · simp only [extendCutSuffix, hs, dite_false]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change k = s.val.val
      have := notMem_interval_zero_iff.mp s.property
      omega

/-- Restriction of a global physical configuration to the left block of a cut.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutPrefixRestriction {d N : ℕ} (σ : Fin N → Fin d) (k : ℕ) :
    RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) := fun s ↦ σ s.1

/-- Restriction of a global physical configuration to the sites after a cut.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutSuffixRestriction {d N : ℕ} (σ : Fin N → Fin d) (k : ℕ) :
    ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) := fun s ↦ σ s.1

/-- Adjoining the next physical letter recovers the longer prefix restriction.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem extendCutPrefix_restriction {d N : ℕ} (σ : Fin N → Fin d) (p : Fin N) :
    extendCutPrefix p.val (cutPrefixRestriction σ p.val) (σ p) =
      cutPrefixRestriction σ (p.val + 1) := by
  funext s
  by_cases h : s.val < p.val
  · simp [extendCutPrefix, cutPrefixRestriction, h]
  · have heq : s.1 = p := Fin.ext (by have := (mem_interval.mp s.2).2; omega)
    simp [extendCutPrefix, cutPrefixRestriction, heq]

/-- The coefficient column space on the prefix side of a physical cut.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutColumnSpace {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    Submodule ℂ (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) → ℂ) :=
  Submodule.span ℂ (Set.range (cutMatrix (interval N 0 k) ψ).col)

/-- The dimension of the cut column space is the cut rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem finrank_cutColumnSpace {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    Module.finrank ℂ (cutColumnSpace ψ k) = cutRank (interval N 0 k) ψ :=
  (Matrix.rank_eq_finrank_span_cols _).symm

/-- Fixing the last physical coordinate of a longer prefix is a linear map.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutSliceLinearMap {d N : ℕ} (k : ℕ) (i : Fin d) :
    (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)) → ℂ) →ₗ[ℂ]
      (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun u ↦ extendCutPrefix k u i)

/-- Fixing one physical coordinate maps the next cut column space into
the preceding cut column space.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSliceLinearMap_maps_columnSpace {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) (i : Fin d) :
    Submodule.map (cutSliceLinearMap k i) (cutColumnSpace ψ (k + 1)) ≤
      cutColumnSpace ψ k := by
  rw [cutColumnSpace, LinearMap.map_span]
  apply Submodule.span_le.mpr
  rintro v ⟨w, ⟨ν, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨extendCutSuffix k i ν, ?_⟩
  funext u
  exact (cutMatrix_adjacent ψ k u i ν).symm

/-- The coordinate-slicing map restricted to the adjacent cut column spaces.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutSlice {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) (i : Fin d) :
    cutColumnSpace ψ (k + 1) →ₗ[ℂ] cutColumnSpace ψ k :=
  (cutSliceLinearMap k i).restrict fun v hv ↦
    cutSliceLinearMap_maps_columnSpace ψ k i ⟨v, hv, rfl⟩

/-- The restricted slicing map evaluates a longer prefix at its next physical letter.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSlice_apply_restriction {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (σ : Fin N → Fin d) (p : Fin N) (v : cutColumnSpace ψ (p.val + 1)) :
    (cutSlice ψ p.val (σ p) v).val (cutPrefixRestriction σ p.val) =
      v.val (cutPrefixRestriction σ (p.val + 1)) := by
  change v.val (extendCutPrefix p.val (cutPrefixRestriction σ p.val) (σ p)) = _
  rw [extendCutPrefix_restriction]

/-- There is exactly one configuration of the left block of the cut `0`.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_regionConfig_interval_zero_zero (d N : ℕ) :
    Fintype.card (RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 0)) = 1 := by
  let : IsEmpty {v : Fin N // v ∈ interval N 0 0} :=
    ⟨fun s ↦ Nat.not_lt_zero _ (mem_interval.mp s.2).2⟩
  simp only [RegionConfig, Fintype.card_pi, Finset.univ_eq_empty, Finset.prod_empty]

/-- There is exactly one configuration of the sites after the cut `N`.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem card_complConfig_interval_zero_self (d N : ℕ) :
    Fintype.card (ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N)) = 1 := by
  let : IsEmpty {v : Fin N // v ∉ interval N 0 N} :=
    ⟨fun s ↦ s.2 (mem_interval.mpr ⟨Nat.zero_le _, s.1.isLt⟩)⟩
  simp only [ComplConfig, Fintype.card_pi, Finset.univ_eq_empty, Finset.prod_empty]

/-- The left endpoint column space of a nonzero tensor is the full scalar space.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutColumnSpace_zero_eq_top {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0) :
    cutColumnSpace ψ 0 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_cutColumnSpace, cutRank_zero_eq_one hψ, Module.finrank_pi,
    card_regionConfig_interval_zero_zero]

/-- The complete coefficient tensor viewed as a vector on the final prefix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def fullCutVector {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) :
    RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N) → ℂ :=
  fun u ↦ ψ (fun s ↦ u ⟨s, mem_interval.mpr ⟨Nat.zero_le _, s.isLt⟩⟩)

/-- Every final-cut column is the complete coefficient vector.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutMatrix_last {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (u : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N))
    (v : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N)) :
    cutMatrix (interval N 0 N) ψ u v = fullCutVector ψ u := by
  rw [ManyBody.cutMatrix_apply]
  apply congrArg ψ
  funext s
  exact cutEquiv_symm_apply_mem _ _ (mem_interval.mpr ⟨Nat.zero_le _, s.isLt⟩)

/-- The complete coefficient vector belongs to the final cut column space.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem fullCutVector_mem {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) :
    fullCutVector ψ ∈ cutColumnSpace ψ N := by
  let ν : ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 N) := fun s ↦
    False.elim (s.2 (mem_interval.mpr ⟨Nat.zero_le _, s.1.isLt⟩))
  apply Submodule.subset_span
  refine ⟨ν, ?_⟩
  funext u
  exact cutMatrix_last ψ u ν

/-- Evaluating the complete coefficient vector recovers the original coefficient.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem fullCutVector_restriction {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (σ : Fin N → Fin d) : fullCutVector ψ (cutPrefixRestriction σ N) = ψ σ := rfl

/-- A nonzero coefficient tensor gives a nonzero final cut vector.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem fullCutVector_ne_zero {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0) :
    fullCutVector ψ ≠ 0 := by
  intro hz
  apply hψ
  funext σ
  exact congrFun hz (cutPrefixRestriction σ N)

end MinimalCutRepresentationCuts

section MinimalCutRepresentationBases

/-!
## Cut bases with prescribed endpoint vectors

A basis is chosen in every physical cut column space. At the left endpoint
its vector is fixed to one; at the right endpoint its vector is the complete
coefficient tensor. Positive length makes these endpoints distinct, so the
two choices preserve the entire complex amplitude without a phase convention.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

/-- A basis of the coefficient column space indexed by its cut rank.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutColumnBasis {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (k : ℕ) :
    Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k) :=
  Module.finBasisOfFinrankEq ℂ (cutColumnSpace ψ k) (finrank_cutColumnSpace ψ k)

/-- A nonzero tensor of positive length admits a basis at every cut,
with the left endpoint vector equal to one and the right endpoint vector equal
to the complete coefficient tensor. The complete complex amplitude is retained.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_cutBasisFamily_with_endpoints {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0) (hN : 0 < N) :
    ∃ B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k),
      (∀ q, (B 0 q).val = 1) ∧ (∀ q, (B N q).val = fullCutVector ψ) := by
  classical
  let v0 : cutColumnSpace ψ 0 :=
    ⟨1, by rw [cutColumnSpace_zero_eq_top ψ hψ]; trivial⟩
  have hv0 : v0 ≠ 0 := by
    intro hz
    let u0 : RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 0) := fun s ↦
      False.elim (Nat.not_lt_zero _ (mem_interval.mp s.2).2)
    exact one_ne_zero (congrFun (congrArg Subtype.val hz) u0)
  let vN : cutColumnSpace ψ N := ⟨fullCutVector ψ, fullCutVector_mem ψ⟩
  have hvN : vN ≠ 0 := by
    intro hz
    exact fullCutVector_ne_zero ψ hψ (congrArg Subtype.val hz)
  have hd0 : Module.finrank ℂ (cutColumnSpace ψ 0) = 1 :=
    (finrank_cutColumnSpace ψ 0).trans (cutRank_zero_eq_one hψ)
  have hdN : Module.finrank ℂ (cutColumnSpace ψ N) = 1 :=
    (finrank_cutColumnSpace ψ N).trans (cutRank_self_eq_one hψ)
  let : Unique (Fin (cutRank (interval N 0 0) ψ)) :=
    Equiv.unique (finCongr (cutRank_zero_eq_one hψ))
  let : Unique (Fin (cutRank (interval N 0 N) ψ)) :=
    Equiv.unique (finCongr (cutRank_self_eq_one hψ))
  let e0 := FiniteDimensional.basisSingleton (Fin (cutRank (interval N 0 0) ψ)) hd0
    v0 hv0
  let eN := FiniteDimensional.basisSingleton (Fin (cutRank (interval N 0 N) ψ)) hdN
    vN hvN
  have he0 : ∀ q, (e0 q).val = 1 := by
    intro q
    exact congrArg Subtype.val (FiniteDimensional.basisSingleton_apply
      (Fin (cutRank (interval N 0 0) ψ)) hd0 v0 hv0 q)
  have heN : ∀ q, (eN q).val = fullCutVector ψ := by
    intro q
    exact congrArg Subtype.val (FiniteDimensional.basisSingleton_apply
      (Fin (cutRank (interval N 0 N) ψ)) hdN vN hvN q)
  let B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ
      (cutColumnSpace ψ k) := fun k ↦
    if h0 : k = 0 then by subst k; exact e0
    else if hlast : k = N then by subst k; exact eN
    else cutColumnBasis ψ k
  refine ⟨B, ?_, ?_⟩
  · intro q
    simpa only [B, dite_eq_left rfl] using he0 q
  · intro q
    have hN0 : N ≠ 0 := Nat.ne_of_gt hN
    simpa only [B, dite_eq_right hN0, dite_eq_left rfl, dite_true] using heN q

end MinimalCutRepresentationBases

section CutSiteCoordinates

/-!
## Numbered sites of the two blocks of a cut

Numbering the sites of the left block of a valid cut `k ≤ N` by `Fin k`, and the sites after it
by `Fin (N - k)`, reads their configurations as configurations of chains of `k` and of `N - k`
sites.

Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

variable {d N k : ℕ}

/-- Numbered prefix sites are identified with the actual sites before a
valid cut. Source: Section 5 of the exact MPU circuit note. -/
def cutPrefixSiteEquiv (hk : k ≤ N) : Fin k ≃ {s : Fin N // s ∈ interval N 0 k} where
  toFun i := ⟨Fin.castLE hk i, mem_interval.mpr ⟨Nat.zero_le _, i.isLt⟩⟩
  invFun s := ⟨s.val.val, (mem_interval.mp s.property).2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

/-- Numbered suffix sites are identified with the actual sites after a
valid cut, by adding the cut position. Source: Section 5 of the exact
MPU circuit note. -/
def cutSuffixSiteEquiv (hk : k ≤ N) : Fin (N - k) ≃ {s : Fin N // s ∉ interval N 0 k} where
  toFun i := ⟨⟨k + i.val, by have := i.isLt; omega⟩, fun h ↦ by
    have := (mem_interval.mp h).2
    dsimp at this
    omega⟩
  invFun s := ⟨s.val.val - k, by
    have := s.val.isLt
    have := Nat.le_of_not_lt fun h ↦ s.property (mem_interval.mpr ⟨Nat.zero_le _, h⟩)
    omega⟩
  left_inv i := Fin.ext (by dsimp; omega)
  right_inv s := Subtype.ext (Fin.ext (by
    have := Nat.le_of_not_lt fun h ↦ s.property (mem_interval.mpr ⟨Nat.zero_le _, h⟩)
    dsimp
    omega))

/-- Prefix configurations as configurations of a chain of `k` sites.
Source: Section 5 of the exact MPU circuit note. -/
def cutPrefixConfigEquiv (hk : k ≤ N) :
    (Fin k → Fin d) ≃ RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) :=
  Equiv.arrowCongr (cutPrefixSiteEquiv hk) (Equiv.refl (Fin d))

/-- Suffix configurations as configurations of a chain of `N - k` sites.
Source: Section 5 of the exact MPU circuit note. -/
def cutSuffixConfigEquiv (hk : k ≤ N) :
    (Fin (N - k) → Fin d) ≃ ComplConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k) :=
  Equiv.arrowCongr (cutSuffixSiteEquiv hk) (Equiv.refl (Fin d))

end CutSiteCoordinates

end MPSPreparation

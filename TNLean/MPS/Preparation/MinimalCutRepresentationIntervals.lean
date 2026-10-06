/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.MinimalCutRepresentationFactorization

/-!
# Coherent intervals of the minimal cut representation

Fixing a physical configuration between two cuts restricts the later
coefficient column space into the earlier one. In chosen cut bases this
restriction has a matrix that propagates both physical prefix and suffix
factors. Its matrices compose exactly across an intermediate cut, and the
one-site matrices coincide with the constructed open-boundary chain sites.

Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- A physical configuration on the half-open interval between two cuts.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
abbrev CutIntervalConfig (d N j k : ℕ) :=
  {s : Fin N // j ≤ s.val ∧ s.val < k} → Fin d

/-- Joining a prefix configuration with a middle interval configuration.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def joinCutPrefix {d N : ℕ} (j k : ℕ) (u : CutPrefixConfig d N j)
    (w : CutIntervalConfig d N j k) : CutPrefixConfig d N k :=
  fun s ↦ if h : s.val < j then u ⟨s.1, h⟩
    else w ⟨s.1, Nat.le_of_not_lt h, s.2⟩

/-- Joining a middle interval configuration with a suffix configuration.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def joinCutSuffix {d N : ℕ} (j k : ℕ) (w : CutIntervalConfig d N j k)
    (v : CutSuffixConfig d N k) : CutSuffixConfig d N j :=
  fun s ↦ if h : s.val < k then w ⟨s.1, s.2, h⟩
    else v ⟨s.1, Nat.le_of_not_lt h⟩

/-- Splitting a longer prefix into its shorter prefix and middle interval
is a bijection on physical configurations.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutPrefixIntervalConfigEquiv (d N j k : ℕ) (hjk : j ≤ k) :
    CutPrefixConfig d N k ≃ (CutPrefixConfig d N j × CutIntervalConfig d N j k) where
  toFun v := (fun s ↦ v ⟨s.1, Nat.lt_of_lt_of_le s.2 hjk⟩,
    fun s ↦ v ⟨s.1, s.2.2⟩)
  invFun uw := joinCutPrefix j k uw.1 uw.2
  left_inv v := by
    funext s
    change (if _h : s.val < j then v s else v s) = v s
    split_ifs <;> rfl
  right_inv uw := by
    apply Prod.ext
    · funext s
      simp [joinCutPrefix, s.2]
    · funext s
      simp [joinCutPrefix, Nat.not_lt_of_ge s.2.1]

/-- The two bounding coefficient flattenings agree when the same middle
configuration is joined to the prefix or to the suffix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutCoefficientMatrix_interval {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    {j k : ℕ} (hjk : j ≤ k) (u : CutPrefixConfig d N j)
    (w : CutIntervalConfig d N j k) (v : CutSuffixConfig d N k) :
    cutCoefficientMatrix ψ k (joinCutPrefix j k u w) v =
      cutCoefficientMatrix ψ j u (joinCutSuffix j k w v) := by
  apply congrArg ψ
  funext s
  by_cases h : s.val < j
  · have h' : s.val < k := Nat.lt_of_lt_of_le h hjk
    simp [joinCutPrefix, h, h']
  · by_cases h' : s.val < k
    · simp [joinCutPrefix, joinCutSuffix, h, h']
    · simp [joinCutSuffix, h, h']

/-- Fixing a middle physical configuration restricts vectors on a later
prefix to vectors on an earlier prefix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutIntervalSliceLinearMap {d N : ℕ} (j k : ℕ) (w : CutIntervalConfig d N j k) :
    (CutPrefixConfig d N k → ℂ) →ₗ[ℂ] (CutPrefixConfig d N j → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun u ↦ joinCutPrefix j k u w)

/-- Middle-coordinate restriction maps the later physical coefficient
column space into the earlier coefficient column space.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutIntervalSliceLinearMap_maps_columnSpace {d N : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) {j k : ℕ} (hjk : j ≤ k)
    (w : CutIntervalConfig d N j k) :
    Submodule.map (cutIntervalSliceLinearMap j k w) (cutColumnSpace ψ k) ≤
      cutColumnSpace ψ j := by
  rw [cutColumnSpace, LinearMap.map_span]
  apply Submodule.span_le.mpr
  rintro v ⟨z, ⟨ν, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨joinCutSuffix j k w ν, ?_⟩
  funext u
  exact (cutCoefficientMatrix_interval ψ hjk u w ν).symm

/-- Middle-coordinate restriction between the actual physical cut spaces.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutIntervalSlice {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    {j k : ℕ} (hjk : j ≤ k) (w : CutIntervalConfig d N j k) :
    cutColumnSpace ψ k →ₗ[ℂ] cutColumnSpace ψ j :=
  (cutIntervalSliceLinearMap j k w).restrict fun v hv ↦
    cutIntervalSliceLinearMap_maps_columnSpace ψ hjk w ⟨v, hv, rfl⟩

/-- The matrix of middle-coordinate restriction in the chosen cut bases.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutIntervalMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    {j k : ℕ} (hjk : j ≤ k) (w : CutIntervalConfig d N j k) :
    Matrix (Fin (cutRank ψ j)) (Fin (cutRank ψ k)) ℂ :=
  LinearMap.toMatrix (B k) (B j) (cutIntervalSlice ψ hjk w)

/-- The longer prefix factor is the shorter prefix factor multiplied
by the constructed interval matrix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixMatrix_interval {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    {j k : ℕ} (hjk : j ≤ k) (u : CutPrefixConfig d N j)
    (w : CutIntervalConfig d N j k) (q : Fin (cutRank ψ k)) :
    cutPrefixMatrix ψ B k (joinCutPrefix j k u w) q =
      (cutPrefixMatrix ψ B j * cutIntervalMatrix ψ B hjk w) u q := by
  classical
  let E : cutColumnSpace ψ j →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) u).comp (cutColumnSpace ψ j).subtype
  have h := congrArg (fun M : Matrix (Fin 1) (Fin (cutRank ψ k)) ℂ ↦ M 0 q)
    (LinearMap.toMatrix_comp (B k) (B j) (Module.Basis.singleton (Fin 1) ℂ)
      E (cutIntervalSlice ψ hjk w))
  simp only [LinearMap.toMatrix_apply, Module.Basis.singleton_repr, Matrix.mul_apply] at h
  change (B k q).val (joinCutPrefix j k u w) =
    ∑ p, (B j p).val u * cutIntervalMatrix ψ B hjk w p q
  simp only [cutIntervalMatrix, LinearMap.toMatrix_apply]
  change (B k q).val (joinCutPrefix j k u w) =
    ∑ p, (B j p).val u * (B j).repr (cutIntervalSlice ψ hjk w (B k q)) p at h
  exact h

/-- Restricting a later physical column gives the earlier column with
the middle configuration joined to its suffix.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutIntervalSlice_column {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    {j k : ℕ} (hjk : j ≤ k) (w : CutIntervalConfig d N j k)
    (v : CutSuffixConfig d N k) :
    cutIntervalSlice ψ hjk w
      ⟨(cutCoefficientMatrix ψ k).col v, Submodule.subset_span ⟨v, rfl⟩⟩ =
      ⟨(cutCoefficientMatrix ψ j).col (joinCutSuffix j k w v),
        Submodule.subset_span ⟨joinCutSuffix j k w v, rfl⟩⟩ := by
  apply Subtype.ext
  funext u
  exact cutCoefficientMatrix_interval ψ hjk u w v

/-- The shorter suffix factor is the constructed interval matrix
multiplied by the longer-cut suffix factor.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutSuffixMatrix_interval {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    {j k : ℕ} (hjk : j ≤ k) (w : CutIntervalConfig d N j k)
    (v : CutSuffixConfig d N k) :
    (cutSuffixMatrix ψ B j).col (joinCutSuffix j k w v) =
      cutIntervalMatrix ψ B hjk w *ᵥ (cutSuffixMatrix ψ B k).col v := by
  have h := LinearMap.toMatrix_mulVec_repr (B k) (B j) (cutIntervalSlice ψ hjk w)
    ⟨(cutCoefficientMatrix ψ k).col v, Submodule.subset_span ⟨v, rfl⟩⟩
  rw [cutIntervalSlice_column] at h
  exact h.symm

/-- Joining two consecutive middle physical configurations.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def joinCutInterval {d N : ℕ} (j k l : ℕ) (w : CutIntervalConfig d N j k)
    (z : CutIntervalConfig d N k l) : CutIntervalConfig d N j l :=
  fun s ↦ if h : s.val < k then w ⟨s.1, s.2.1, h⟩
    else z ⟨s.1, Nat.le_of_not_lt h, s.2.2⟩

/-- Joining consecutive physical intervals to a prefix is associative.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem joinCutPrefix_assoc {d N : ℕ} {j k l : ℕ} (hjk : j ≤ k)
    (u : CutPrefixConfig d N j) (w : CutIntervalConfig d N j k)
    (z : CutIntervalConfig d N k l) :
    joinCutPrefix j l u (joinCutInterval j k l w z) =
      joinCutPrefix k l (joinCutPrefix j k u w) z := by
  funext s
  by_cases h : s.val < j
  · have h' : s.val < k := Nat.lt_of_lt_of_le h hjk
    simp [joinCutPrefix, h, h']
  · by_cases h' : s.val < k <;> simp [joinCutPrefix, joinCutInterval, h, h']

/-- The constructed interval restrictions compose exactly across
an intermediate cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutIntervalSlice_comp {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    {j k l : ℕ} (hjk : j ≤ k) (hkl : k ≤ l)
    (w : CutIntervalConfig d N j k) (z : CutIntervalConfig d N k l) :
    cutIntervalSlice ψ (hjk.trans hkl) (joinCutInterval j k l w z) =
      (cutIntervalSlice ψ hjk w).comp (cutIntervalSlice ψ hkl z) := by
  ext v u
  change v.val (joinCutPrefix j l u (joinCutInterval j k l w z)) =
    v.val (joinCutPrefix k l (joinCutPrefix j k u w) z)
  rw [joinCutPrefix_assoc hjk]

/-- The constructed interval matrices multiply exactly across
an intermediate cut.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutIntervalMatrix_comp {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    {j k l : ℕ} (hjk : j ≤ k) (hkl : k ≤ l)
    (w : CutIntervalConfig d N j k) (z : CutIntervalConfig d N k l) :
    cutIntervalMatrix ψ B (hjk.trans hkl) (joinCutInterval j k l w z) =
      cutIntervalMatrix ψ B hjk w * cutIntervalMatrix ψ B hkl z := by
  rw [cutIntervalMatrix, cutIntervalSlice_comp]
  exact LinearMap.toMatrix_comp (B l) (B k) (B j)
    (cutIntervalSlice ψ hjk w) (cutIntervalSlice ψ hkl z)

/-- On one physical site, the constructed interval matrix equals
the site matrix of the minimal open-boundary chain.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutIntervalMatrix_adjacent {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank ψ k)) ℂ (cutColumnSpace ψ k))
    (j : ℕ) (i : Fin d) :
    cutIntervalMatrix ψ B (Nat.le_succ j) (fun _ ↦ i) = cutSiteMatrix ψ B j i := by
  have h : cutIntervalSlice ψ (Nat.le_succ j) (fun _ ↦ i) = cutSlice ψ j i := by
    ext v u
    rfl
  rw [cutIntervalMatrix, cutSiteMatrix, h]

end MPSPreparation

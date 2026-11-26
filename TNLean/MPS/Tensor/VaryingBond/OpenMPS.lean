/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement
import QICLean.Channel.Schmidt.Rank
import QICLean.ManyBody.Sites.CutMatrix
import QICLean.ManyBody.Sites.Lattice.Chain
import TNLean.MPS.Tensor.VaryingBond.VaryingBondOBC

/-!
# Open-boundary matrix product states on a chain

A vector on `L` sites of local dimension `q` is a matrix product state of bond
dimension at most `D` when it is a scalar multiple of a rectangular tensor contraction
with one-dimensional endpoint spaces and internal bond dimensions at most `D`.
The scalar cap also represents an arbitrary coefficient at length zero. The cut after `k`
sites is the interval `ManyBody.interval L 0 k` of the sites of index less than `k`; the cut
matrix `ManyBody.cutMatrix (interval L 0 k) ψ` comes from QICLean
(`QICLean/ManyBody/Sites/CutMatrix.lean`). It has the configurations of the left sites as rows
and those of the remaining sites as columns; its rank is the Schmidt rank across that cut.

## Main definitions

* `IsOpenMPS L q D ψ`: `ψ` is an open-boundary matrix product state of bond
  dimension at most `D`.

## Main results

* `rank_cutMatrix_zero_le`, `rank_cutMatrix_le_one_of_le`: the cut matrix has rank at most
  one across the cut after zero sites and across a cut at or beyond the right end.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 7, Theorem B and
  Proposition 7.1 (sequential truncation).
-/

open Matrix
open ManyBody (interval mem_interval)

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- Across the cut after zero sites the cut matrix has one row, so its rank is at most
one. -/
theorem rank_cutMatrix_zero_le (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    (ManyBody.cutMatrix (interval L 0 0) ψ).rank ≤ 1 := by
  have : IsEmpty {v : Fin L // v ∈ interval L 0 0} :=
    ⟨fun v ↦ absurd (mem_interval.mp v.2).2 (Nat.not_lt_zero _)⟩
  refine (rank_le_card_height _).trans ?_
  rw [Fintype.card_unique]

/-- Across a cut at or beyond the right end the cut matrix has one column, so its rank is
at most one. -/
theorem rank_cutMatrix_le_one_of_le {k : ℕ} (hk : L ≤ k)
    (ψ : EuclideanSpace ℂ (Fin L → Fin q)) :
    (ManyBody.cutMatrix (interval L 0 k) ψ).rank ≤ 1 := by
  have : IsEmpty {v : Fin L // v ∉ interval L 0 k} :=
    ⟨fun v ↦ v.2 (mem_interval.mpr ⟨Nat.zero_le _, lt_of_lt_of_le v.1.2 hk⟩)⟩
  refine (rank_le_card_width _).trans ?_
  rw [Fintype.card_unique]

/-- Explicit open-boundary tensor data representing `ψ`, with singleton endpoint spaces and
internal bond dimensions at most `D`.  This packages the tensor and scalar cap that occur in
the existential predicate `IsOpenMPS`, so an algorithmic construction can retain them as data.
Source: the one-dimensional note, Part IIa, Proposition `prop:VC`, lines 39–62. -/
structure OpenMPSRepresentation (L q D : ℕ) (ψ : (Fin L → Fin q) → ℂ) where
  /-- The varying-bond open-boundary tensor. -/
  tensor : OBCChainTensor q (max 1 D) L
  /-- The scalar cap multiplying the path contraction. -/
  scalar : ℂ
  /-- Every internal virtual bond has dimension at most `D`. -/
  internal_bondDim_le : ∀ k, 0 < k.val → k.val < L → tensor.bondDim k ≤ D
  /-- The represented physical coefficients. -/
  coeff_eq : ∀ x, ψ x = scalar * tensor.coeff x

/-- An open-boundary matrix product state with singleton endpoint spaces and internal
bond dimensions at most `D`. The scalar cap multiplies the rectangular path contraction.
Source: the one-dimensional note, Part IIa, Proposition `prop:VC`, lines 39–62. -/
def IsOpenMPS (L q D : ℕ) (ψ : (Fin L → Fin q) → ℂ) : Prop :=
  ∃ (A : OBCChainTensor q (max 1 D) L) (c : ℂ),
    (∀ k, 0 < k.val → k.val < L → A.bondDim k ≤ D) ∧
      ∀ x, ψ x = c * A.coeff x

/-- The explicit representation type packages exactly the data asserted by `IsOpenMPS`. -/
theorem isOpenMPS_iff_nonempty_representation (L q D : ℕ)
    (ψ : (Fin L → Fin q) → ℂ) :
    IsOpenMPS L q D ψ ↔ Nonempty (OpenMPSRepresentation L q D ψ) := by
  constructor
  · rintro ⟨A, c, hA, hψ⟩
    exact ⟨⟨A, c, hA, hψ⟩⟩
  · rintro ⟨⟨A, c, hA, hψ⟩⟩
    exact ⟨A, c, hA, hψ⟩

namespace OpenMPSRepresentation

/-- Forgetting the packaged tensor data recovers the mathematical MPS predicate. -/
theorem isOpenMPS {L q D : ℕ} {ψ : (Fin L → Fin q) → ℂ}
    (R : OpenMPSRepresentation L q D ψ) : IsOpenMPS L q D ψ :=
  ⟨R.tensor, R.scalar, R.internal_bondDim_le, R.coeff_eq⟩

/-- Scaling a represented state retains the same tensor and scales its scalar cap. -/
def smul {L q D : ℕ} {ψ : (Fin L → Fin q) → ℂ}
    (R : OpenMPSRepresentation L q D ψ) (c : ℂ) :
    OpenMPSRepresentation L q D (fun x ↦ c * ψ x) where
  tensor := R.tensor
  scalar := c * R.scalar
  internal_bondDim_le := R.internal_bondDim_le
  coeff_eq x := by rw [R.coeff_eq x, mul_assoc]

/-- Append a one-site factor to an explicit open-boundary representation. -/
def snoc {L q D : ℕ} {ψ : (Fin L → Fin q) → ℂ}
    (R : OpenMPSRepresentation L q D ψ) (hD : 0 < D) (f : Fin q → ℂ) :
    OpenMPSRepresentation (L + 1) q D
      (fun x ↦ ψ (Fin.init x) * f (x (Fin.last L))) where
  tensor := R.tensor.snoc f
  scalar := R.scalar
  internal_bondDim_le k hk0 hkL := by
    by_cases hk : k.val < L
    · let k' : Fin (L + 1) := ⟨k.val, by omega⟩
      have hk_eq : k = k'.castSucc := by
        apply Fin.ext
        change k.val = k.val
        rfl
      have hdim : (R.tensor.snoc f).bondDim k = R.tensor.bondDim k' := by
        rw [hk_eq]
        simp [OBCChainTensor.snoc]
      rw [hdim]
      exact R.internal_bondDim_le k' (by simpa [k'] using hk0) (by simpa [k'] using hk)
    · have hkval : k.val = L := by omega
      have hk_eq : k = (Fin.last L).castSucc := by
        apply Fin.ext
        simpa using hkval
      have hdim : (R.tensor.snoc f).bondDim k = 1 := by
        rw [hk_eq]
        simp [OBCChainTensor.snoc, R.tensor.right_dim]
      rw [hdim]
      omega
  coeff_eq x := by
    rw [R.coeff_eq, OBCChainTensor.coeff_snoc]
    ring

end OpenMPSRepresentation

/-- Scaling a matrix product state multiplies its scalar endpoint cap. -/
theorem IsOpenMPS.smul {L q D : ℕ} {ψ : (Fin L → Fin q) → ℂ}
    (h : IsOpenMPS L q D ψ) (c : ℂ) :
    IsOpenMPS L q D fun x ↦ c * ψ x := by
  obtain ⟨A, a, hA, hψ⟩ := h
  refine ⟨A, c * a, hA, fun x ↦ ?_⟩
  change c * ψ x = _
  rw [hψ x, mul_assoc]

end TNLean.MPS.AreaLaw

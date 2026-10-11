/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup
import QICLean.Entropy.FiniteProductInformation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Regional entropy of a valid partition move

The entropy of a middle-to-side move is the actual side-dependent regional
conditional mutual information. Its nonnegativity follows from canonical
regional strong subadditivity. For a pure vector, complementary entropies
identify it with the sum of the two conditional entropy differences. These
balanced identities do not require the vector to be normalized.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, display `transport:move-eta`, lines 321–330,
at `openai/math@adc7f124`.
-/

namespace TensorPower.ReplicaTransport

open Entropy (SiteConfig)

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- A valid move has nonnegative conditional mutual information. The receiving
and opposite sides are the actual parts of the old partition. -/
theorem moveEta_nonneg (π : PYF V) (hπ : π.IsPartition) (m : Move V)
    (hm : m.IsValid π) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    0 ≤ moveEta n π m θ := by
  cases m with
  | stay => exact le_rfl
  | toP x =>
    exact FiniteProduct.conditionalMutualInformation_nonneg _ θ x π.F π.P
      (hπ.2.2.1.mono_left hm) (hπ.1.symm.mono_left hm) hπ.2.1.symm
  | toF x =>
    exact FiniteProduct.conditionalMutualInformation_nonneg _ θ x π.P π.F
      (hπ.1.symm.mono_left hm) (hπ.2.2.1.mono_left hm) hπ.2.1

/-- Moving an empty subsystem to the near side has zero entropy, even though
the move constructor is different from a stay. -/
@[simp] theorem moveEta_toP_empty (π : PYF V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : moveEta n π (.toP ∅) θ = 0 := by
  simp only [moveEta, FiniteProduct.conditionalMutualInformation, Finset.empty_union]
  ring

/-- Moving an empty subsystem to the far side has zero entropy. -/
@[simp] theorem moveEta_toF_empty (π : PYF V)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : moveEta n π (.toF ∅) θ = 0 := by
  simp only [moveEta, FiniteProduct.conditionalMutualInformation, Finset.empty_union]
  ring

/-- Purity identifies a near-side move with its two conditional entropy
differences. The complementary region is the whole remaining middle. -/
theorem moveEta_toP_eq_entropy_difference (π : PYF V) (hπ : π.IsPartition)
    (x : Finset V) (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toP x) θ =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ π.P) -
        FiniteProduct.entropy (fun v => Fin (n v)) θ π.P +
      FiniteProduct.entropy (fun v => Fin (n v)) θ π.Y -
        FiniteProduct.entropy (fun v => Fin (n v)) θ (π.Y \ x) := by
  have hcompl : (π.F ∪ π.P)ᶜ = π.Y := by
    ext v
    have hall : v ∈ π.P ∪ π.Y ∪ π.F := by rw [hπ.2.2.2]; exact Finset.mem_univ v
    have hPY : v ∈ π.P → v ∉ π.Y := fun hp hy => Finset.disjoint_left.mp hπ.1 hp hy
    have hYF : v ∈ π.Y → v ∉ π.F := fun hy hf => Finset.disjoint_left.mp hπ.2.2.1 hy hf
    simp only [Finset.mem_compl, Finset.mem_union] at hall ⊢
    tauto
  have hcomplx : (x ∪ π.F ∪ π.P)ᶜ = π.Y \ x := by
    rw [Finset.union_assoc, Finset.compl_union, hcompl]
    rw [← Finset.sdiff_union_of_subset hx]
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    tauto
  have hY := FiniteProduct.entropy_compl (fun v => Fin (n v)) θ (π.F ∪ π.P)
  have hYx := FiniteProduct.entropy_compl (fun v => Fin (n v)) θ (x ∪ π.F ∪ π.P)
  rw [hcompl] at hY
  rw [hcomplx] at hYx
  simp only [moveEta, FiniteProduct.conditionalMutualInformation, ← hY, ← hYx]
  ring

/-- A far-side move uses the far-side conditional entropy difference; it is
not identified with the entropy of the corresponding near-side move. -/
theorem moveEta_toF_eq_entropy_difference (π : PYF V) (hπ : π.IsPartition)
    (x : Finset V) (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (SiteConfig n)) :
    moveEta n π (.toF x) θ =
      FiniteProduct.entropy (fun v => Fin (n v)) θ (x ∪ π.F) -
        FiniteProduct.entropy (fun v => Fin (n v)) θ π.F +
      FiniteProduct.entropy (fun v => Fin (n v)) θ π.Y -
        FiniteProduct.entropy (fun v => Fin (n v)) θ (π.Y \ x) := by
  have hswap : (⟨π.F, π.Y, π.P⟩ : PYF V).IsPartition := by
    refine ⟨hπ.2.2.1.symm, hπ.2.1.symm, hπ.1.symm, ?_⟩
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
      using hπ.2.2.2
  exact moveEta_toP_eq_entropy_difference n ⟨π.F, π.Y, π.P⟩ hswap x hx θ

end TensorPower.ReplicaTransport

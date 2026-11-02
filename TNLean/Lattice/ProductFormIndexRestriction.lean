/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductForm

/-!
# Restricting the index values of a matrix product form

If a coefficient vanishes whenever the index at its own site is outside a specified set,
all other values can be removed from that site's index type. Coefficient neighborhoods are
preserved. This is the restriction to clusters containing a site in Hastings,
arXiv:cond-mat/0508554v3, lines 1259–1279.
-/

open Matrix QuantumCircuit

namespace TNLean.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {near : ι → ι → Prop}

/-- Removing index values that force the coefficient at their site to vanish preserves
the represented operator and the coefficient neighborhoods.
Source: Hastings, arXiv:cond-mat/0508554v3, lines 1259–1279. -/
noncomputable def ProductForm.restrict {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) (s : ∀ i, Finset (P.Index i))
    (hs : ∀ i α, α i ∉ s i → P.coeff i α = 0) : ProductForm q near ρ := by
  classical
  refine {
    Index := fun i ↦ {a : P.Index i // a ∈ s i}
    siteOp := fun i a ↦ P.siteOp i a.1
    coeff := fun i α ↦ P.coeff i (fun j ↦ (α j).1)
    coeff_local := fun i α β h ↦ P.coeff_local i _ _ fun j hj ↦ congrArg Subtype.val (h j hj)
    eq_sum := ?_ }
  refine P.eq_sum.trans ?_
  let f (α : ∀ i, P.Index i) :=
    (∏ i, P.coeff i α) • rectKronecker fun j ↦ P.siteOp j (α j)
  change (∑ α, f α) = ∑ α : (∀ i, {a : P.Index i // a ∈ s i}), f (fun i ↦ (α i).1)
  calc
    (∑ α, f α) = ∑ α ∈ Finset.univ.filter (fun α ↦ ∀ i, α i ∈ s i), f α := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro α _ hα
      have hbad : ¬ ∀ i, α i ∈ s i := by simpa only [Finset.mem_filter, Finset.mem_univ,
        true_and] using hα
      obtain ⟨i, hi⟩ := not_forall.mp hbad
      have hz : ∏ j, P.coeff j α = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hs i α hi)
      simp only [f, hz, zero_smul]
    _ = ∑ α : {α : (∀ i, P.Index i) // ∀ i, α i ∈ s i}, f α.1 :=
      Finset.sum_subtype _ (by simp) f
    _ = _ := Fintype.sum_equiv Equiv.subtypePiEquivPi _ _ fun _ ↦ rfl

/-- The index count after restriction is the cardinality of the allowed set at that site. -/
theorem ProductForm.card_index_restrict {ρ : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (P : ProductForm q near ρ) (s : ∀ i, Finset (P.Index i))
    (hs : ∀ i α, α i ∉ s i → P.coeff i α = 0) (i : ι) :
    Fintype.card ((P.restrict s hs).Index i) = (s i).card := by
  classical
  exact Fintype.card_coe (s i)

end TNLean.Lattice

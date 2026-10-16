/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.RegionalEntropyBridge

/-!
# One-dimensional domains inside the square lattice

A chain is a finite induced lattice domain all of whose sites lie on the horizontal
axis. The finite-range Hamiltonians, gapped ground vectors and regional entropies of
the two-dimensional development apply to it without change; this module only names the
one-row domains, the chain of `L` consecutive sites, and the interval regions of a chain.

## Main definitions

* `IsOneRow`: every site of the domain has second coordinate zero.
* `chainDomain L`: the sites `(0,0), …, (L-1,0)`.
* `interval Λ l r`: the sites of `Λ` with first coordinate in `[l, r]`.
* `chainSiteEquiv L`: the sites of the chain of `L` sites, ordered by position.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 2, the setting.
-/

namespace TNLean.PEPS.AreaLaw.Chain

/-- A one-row domain: every site lies on the horizontal axis. -/
def IsOneRow (Λ : Finset (ℤ × ℤ)) : Prop := ∀ p ∈ Λ, p.2 = 0

/-- The chain of `L` consecutive sites `(0,0), …, (L-1,0)`. -/
def chainDomain (L : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range L).image fun k : ℕ ↦ ((k : ℤ), (0 : ℤ))

/-- Membership in the chain of `L` sites, in coordinates. -/
theorem mem_chainDomain {L : ℕ} {p : ℤ × ℤ} :
    p ∈ chainDomain L ↔ 0 ≤ p.1 ∧ p.1 < L ∧ p.2 = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_range] at hk
    exact ⟨by positivity, by simp only; exact_mod_cast hk, rfl⟩
  · rintro ⟨h0, hL, h2⟩
    refine Finset.mem_image.mpr ⟨p.1.toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have := Int.toNat_of_nonneg h0
      omega
    · ext
      · simp [Int.toNat_of_nonneg h0]
      · simp [h2]

/-- The chain of `L` sites is a one-row domain. -/
theorem isOneRow_chainDomain (L : ℕ) : IsOneRow (chainDomain L) :=
  fun _ hp ↦ (mem_chainDomain.mp hp).2.2

/-- The chain of `L` sites has `L` sites. -/
theorem card_chainDomain (L : ℕ) : (chainDomain L).card = L := by
  rw [chainDomain, Finset.card_image_of_injective _ (fun a b h ↦ by
    have := congrArg Prod.fst h
    simp only at this
    exact_mod_cast this)]
  simp

/-- The interval region of a domain: the sites with first coordinate in `[l, r]`. -/
def interval (Λ : Finset (ℤ × ℤ)) (l r : ℤ) : Finset (Site Λ) :=
  Finset.univ.filter fun v ↦ l ≤ v.1.1 ∧ v.1.1 ≤ r

/-- Membership in an interval region. -/
theorem mem_interval {Λ : Finset (ℤ × ℤ)} {l r : ℤ} {v : Site Λ} :
    v ∈ interval Λ l r ↔ l ≤ v.1.1 ∧ v.1.1 ≤ r := by
  simp [interval]

/-- On a one-row domain, the first coordinate determines the site. -/
theorem fst_injective_of_isOneRow {Λ : Finset (ℤ × ℤ)} (h : IsOneRow Λ) :
    Function.Injective fun v : Site Λ ↦ v.1.1 := by
  intro v w hvw
  apply Subtype.ext
  exact Prod.ext hvw ((h v.1 v.2).trans (h w.1 w.2).symm)

/-- An interval region of a one-row domain has at most `r + 1 - l` sites. -/
theorem card_interval_le {Λ : Finset (ℤ × ℤ)} (h : IsOneRow Λ) (l r : ℤ) :
    (interval Λ l r).card ≤ (r + 1 - l).toNat := by
  have hinj := (fst_injective_of_isOneRow h).injOn (s := (interval Λ l r : Set (Site Λ)))
  have hmaps : ∀ v ∈ interval Λ l r, (fun v : Site Λ ↦ v.1.1) v ∈ Finset.Icc l r := by
    intro v hv
    rw [mem_interval] at hv
    exact Finset.mem_Icc.mpr hv
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Int.card_Icc] at this

/-- The site of the chain of `L` sites at position `k`. -/
def chainSite (L : ℕ) (k : Fin L) : Site (chainDomain L) :=
  ⟨((k : ℤ), 0), mem_chainDomain.mpr ⟨by positivity, by simp only; exact_mod_cast k.2, rfl⟩⟩

/-- The sites of the chain of `L` sites, ordered by position. -/
noncomputable def chainSiteEquiv (L : ℕ) : Fin L ≃ Site (chainDomain L) :=
  Equiv.ofBijective (chainSite L) ⟨fun a b h ↦ by
      have := congrArg (fun v : Site (chainDomain L) ↦ v.1.1) h
      simp only [chainSite] at this
      exact Fin.ext (by exact_mod_cast this), fun v ↦ by
      obtain ⟨h0, hL, h2⟩ := mem_chainDomain.mp v.2
      refine ⟨⟨v.1.1.toNat, by omega⟩, ?_⟩
      apply Subtype.ext
      ext
      · simp [chainSite, Int.toNat_of_nonneg h0]
      · simp [chainSite, h2]⟩

/-- The position of a chain site. -/
@[simp]
theorem chainSiteEquiv_apply_fst (L : ℕ) (k : Fin L) : ((chainSiteEquiv L k).1).1 = k := rfl

end TNLean.PEPS.AreaLaw.Chain

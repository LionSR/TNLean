/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Chain.Basic
import TNLean.PEPS.AreaLaw.EdgeBoundaryCalculus
import TNLean.PEPS.AreaLaw.TwoFamilies
import TNLean.PEPS.AreaLaw.EntropyDimension

/-!
# Entropy inequalities for regions of a chain

Two consequences of subadditivity and purity for the regional entropies of a unit vector
on a finite domain, specialized to the chain of `L` sites.

* The Araki–Lieb inequality `S(X) ≤ S(X ∪ T) + S(T)` for disjoint regions `X` and `T`
  of a pure state: `S(X) = S(Xᶜ)`, the complement `Xᶜ` is the disjoint union of
  `(X ∪ T)ᶜ` and `T`, and `S((X ∪ T)ᶜ) = S(X ∪ T)` again by purity.
* A uniform bound `C` on the entropies of all intervals of the chain gives the area law
  `S(A) ≤ C |∂A|` for every region `A`, where `∂A` is the set of edges of the chain
  with exactly one endpoint in `A`. Every region is a disjoint union of maximal runs
  of consecutive sites, each run contributes at most `C` by subadditivity, and the gap
  just after a run (or an end of the chain, when the run is the whole region) supplies
  a boundary edge of the region that the remaining runs do not share.

## Main results

* `regionalEntropy_le_union_add`: the Araki–Lieb inequality for regional entropies.
* `regionalEntropy_le_mul_card_edgeBoundary_of_intervals`: interval bounds give the
  area law on a chain.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), Section 2, the reduction of the area
  law on a chain to interval regions.
-/

namespace TNLean.PEPS.AreaLaw.Chain

section Purity

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ} {Ω : StateSpace Λ q}

/-- Subadditivity of the regional entropy of a unit vector over disjoint regions. -/
theorem regionalEntropy_union_le (hΩ : ‖Ω‖ = 1) {X T : Finset (Site Λ)}
    (hXT : Disjoint X T) :
    regionalEntropy Λ q Ω (X ∪ T) ≤ regionalEntropy Λ q Ω X + regionalEntropy Λ q Ω T := by
  simp only [regionalEntropy_eq_finiteProduct]
  exact FiniteProduct.entropy_union_le _ Ω hΩ X T hXT

/-- Complementary regions of a pure state have the same regional entropy. -/
theorem regionalEntropy_compl (X : Finset (Site Λ)) :
    regionalEntropy Λ q Ω Xᶜ = regionalEntropy Λ q Ω X := by
  simp only [regionalEntropy_eq_finiteProduct]
  exact FiniteProduct.entropy_compl _ Ω X

/-- The Araki–Lieb inequality for regional entropies of a pure unit vector: for disjoint
regions `X` and `T`, `S(X) ≤ S(X ∪ T) + S(T)`. -/
theorem regionalEntropy_le_union_add (hΩ : ‖Ω‖ = 1) {X T : Finset (Site Λ)}
    (hXT : Disjoint X T) :
    regionalEntropy Λ q Ω X ≤ regionalEntropy Λ q Ω (X ∪ T) + regionalEntropy Λ q Ω T := by
  have hdisj : Disjoint (X ∪ T)ᶜ T :=
    disjoint_compl_left_iff.mpr Finset.subset_union_right
  have hXc : Xᶜ = (X ∪ T)ᶜ ∪ T := by
    ext v
    have hv : v ∈ X → v ∉ T := fun hv ↦ Finset.disjoint_left.mp hXT hv
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    tauto
  calc regionalEntropy Λ q Ω X = regionalEntropy Λ q Ω Xᶜ := (regionalEntropy_compl X).symm
    _ = regionalEntropy Λ q Ω ((X ∪ T)ᶜ ∪ T) := by rw [hXc]
    _ ≤ regionalEntropy Λ q Ω (X ∪ T)ᶜ + regionalEntropy Λ q Ω T :=
        regionalEntropy_union_le hΩ hdisj
    _ = regionalEntropy Λ q Ω (X ∪ T) + regionalEntropy Λ q Ω T := by
        rw [regionalEntropy_compl]

end Purity

section Chain

variable {L : ℕ}

/-- Two sites of the chain are adjacent exactly when their positions differ by one. -/
theorem adj_chainDomain_iff {x y : Site (chainDomain L)} :
    (domainGraph (chainDomain L)).Adj x y ↔ x.1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = x.1.1 := by
  have hx := (mem_chainDomain.mp x.2).2.2
  have hy := (mem_chainDomain.mp y.2).2.2
  simp only [domainGraph]
  omega

/-- A nonempty proper region `A` of the chain contains a nonempty interval `I` (its
leftmost maximal run) such that the boundary of `A \ I` is a proper subset of the boundary
of `A`: the boundary edges of `A \ I` are boundary edges of `A`, and the edge leaving the
right end of the run (or any boundary edge of `A` when `A = I`) is a boundary edge of `A`
alone. -/
theorem exists_interval_subset_edgeBoundary_sdiff_ssubset
    {A : Finset (Site (chainDomain L))} (hne : A.Nonempty) (hA : A ≠ Finset.univ) :
    ∃ l r : ℤ, interval (chainDomain L) l r ⊆ A ∧ (interval (chainDomain L) l r).Nonempty ∧
      edgeBoundary (chainDomain L) (A \ interval (chainDomain L) l r) ⊂
        edgeBoundary (chainDomain L) A := by
  classical
  -- `l` is the least position of a site of `A`.
  obtain ⟨l, hlmem, hlmin⟩ : ∃ l ∈ A.image fun v ↦ v.1.1, ∀ v ∈ A, l ≤ v.1.1 :=
    ⟨_, Finset.min'_mem _ (hne.image _),
      fun v hv ↦ Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv)⟩
  obtain ⟨a₀, ha₀A, ha₀⟩ := Finset.mem_image.mp hlmem
  have ha₀ : a₀.1.1 = l := ha₀
  obtain ⟨ha₀0, ha₀L, -⟩ := mem_chainDomain.mp a₀.2
  -- `g` is the least position `≥ l` that is not the position of a site of `A`.
  obtain ⟨g, ⟨hlg, hgL⟩, hgA, hgmin⟩ : ∃ g : ℤ, (l ≤ g ∧ g ≤ L) ∧ (¬ ∃ v ∈ A, v.1.1 = g) ∧
      ∀ p, l ≤ p → p < g → ∃ v ∈ A, v.1.1 = p := by
    obtain ⟨G, hG⟩ : ∃ G : Finset ℤ, ∀ p, p ∈ G ↔ (l ≤ p ∧ p ≤ L) ∧ ¬ ∃ v ∈ A, v.1.1 = p :=
      ⟨(Finset.Icc l L).filter fun p ↦ ¬ ∃ v ∈ A, v.1.1 = p,
        fun p ↦ by simp only [Finset.mem_filter, Finset.mem_Icc]⟩
    have hLG : (L : ℤ) ∈ G := by
      rw [hG]
      refine ⟨⟨by omega, le_rfl⟩, ?_⟩
      rintro ⟨v, -, hv⟩
      have := (mem_chainDomain.mp v.2).2.1
      omega
    have hGne : G.Nonempty := ⟨_, hLG⟩
    have hgmem := (hG _).mp (Finset.min'_mem G hGne)
    refine ⟨G.min' hGne, hgmem.1, hgmem.2, fun p hlp hpg ↦ ?_⟩
    by_contra h
    have hpG : p ∈ G := (hG p).mpr ⟨⟨hlp, by omega⟩, h⟩
    exact absurd (Finset.min'_le G p hpG) (not_le.mpr hpg)
  have hlg' : l < g := by
    rcases hlg.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨a₀, ha₀A, by omega⟩ hgA
  -- The run `I` is the interval `[l, g - 1]`.
  have hIA : interval (chainDomain L) l (g - 1) ⊆ A := by
    intro v hv
    rw [mem_interval] at hv
    obtain ⟨w, hwA, hw⟩ := hgmin v.1.1 hv.1 (by omega)
    have : w = v := fst_injective_of_isOneRow (isOneRow_chainDomain L) hw
    exact this ▸ hwA
  have hIne : (interval (chainDomain L) l (g - 1)).Nonempty :=
    ⟨a₀, by rw [mem_interval]; omega⟩
  -- Sites of `A` outside the run sit strictly beyond the gap position `g`.
  have hA' : ∀ v ∈ A \ interval (chainDomain L) l (g - 1), g + 1 ≤ v.1.1 := by
    intro v hv
    rw [Finset.mem_sdiff, mem_interval] at hv
    have h1 := hlmin v hv.1
    have h2 : v.1.1 ≠ g := fun h ↦ hgA ⟨v, hv.1, h⟩
    omega
  refine ⟨l, g - 1, hIA, hIne, ?_⟩
  rw [Finset.ssubset_iff_of_subset]
  · -- A boundary edge of `A` that is not a boundary edge of `A \ I`.
    obtain ⟨b, hbA, hb⟩ := hgmin (g - 1) (by omega) (by omega)
    have hbI : b ∈ interval (chainDomain L) l (g - 1) := by rw [mem_interval]; omega
    rcases (A \ interval (chainDomain L) l (g - 1)).eq_empty_or_nonempty with
      hempty | ⟨w, hw⟩
    · rw [hempty, edgeBoundary_empty]
      by_cases hgL' : g < L
      · let c : Site (chainDomain L) := ⟨(g, 0), mem_chainDomain.mpr ⟨by omega, hgL', rfl⟩⟩
        have hc : c.1.1 = g := rfl
        refine ⟨s(b, c), ?_, by simp⟩
        rw [mem_edgeBoundary_pair_iff]
        exact ⟨adj_chainDomain_iff.mpr (Or.inl (by omega)),
          Or.inl ⟨hbA, fun hcA ↦ hgA ⟨c, hcA, hc⟩⟩⟩
      · by_cases hl0 : 0 < l
        · let c : Site (chainDomain L) :=
            ⟨(l - 1, 0), mem_chainDomain.mpr ⟨by omega, by omega, rfl⟩⟩
          have hc : c.1.1 = l - 1 := rfl
          refine ⟨s(a₀, c), ?_, by simp⟩
          rw [mem_edgeBoundary_pair_iff]
          refine ⟨adj_chainDomain_iff.mpr (Or.inr (by omega)),
            Or.inl ⟨ha₀A, fun hcA ↦ ?_⟩⟩
          have := hlmin c hcA
          omega
        · exfalso
          apply hA
          rw [Finset.eq_univ_iff_forall]
          intro v
          obtain ⟨hv0, hvL, -⟩ := mem_chainDomain.mp v.2
          exact hIA (by rw [mem_interval]; omega)
    · have hwg := hA' w hw
      have hwL := (mem_chainDomain.mp w.2).2.1
      let c : Site (chainDomain L) := ⟨(g, 0), mem_chainDomain.mpr ⟨by omega, by omega, rfl⟩⟩
      have hc : c.1.1 = g := rfl
      have hcA : c ∉ A := fun hcA ↦ hgA ⟨c, hcA, hc⟩
      refine ⟨s(b, c), ?_, ?_⟩
      · rw [mem_edgeBoundary_pair_iff]
        exact ⟨adj_chainDomain_iff.mpr (Or.inl (by omega)), Or.inl ⟨hbA, hcA⟩⟩
      · rw [mem_edgeBoundary_pair_iff]
        rintro ⟨-, ⟨hb', -⟩ | ⟨hc', -⟩⟩
        · exact (Finset.mem_sdiff.mp hb').2 hbI
        · exact hcA (Finset.mem_sdiff.mp hc').1
  · -- Every boundary edge of `A \ I` is a boundary edge of `A`.
    have key : ∀ y z : Site (chainDomain L), (domainGraph (chainDomain L)).Adj y z →
        y ∈ A \ interval (chainDomain L) l (g - 1) →
        z ∉ A \ interval (chainDomain L) l (g - 1) → z ∉ A := by
      intro y z hadj hy hz hzA
      have hyg := hA' y hy
      have hadj' := adj_chainDomain_iff.mp hadj
      apply hz
      rw [Finset.mem_sdiff, mem_interval]
      exact ⟨hzA, by omega⟩
    rintro ⟨y, z⟩ hyz
    rw [mem_edgeBoundary_pair_iff] at hyz ⊢
    obtain ⟨hadj, ⟨hy, hz⟩ | ⟨hz, hy⟩⟩ := hyz
    · exact ⟨hadj, Or.inl ⟨(Finset.mem_sdiff.mp hy).1, key y z hadj hy hz⟩⟩
    · exact ⟨hadj, Or.inr ⟨(Finset.mem_sdiff.mp hz).1, key z y hadj.symm hz hy⟩⟩

/-- Interval bounds give the area law on a chain: if every interval region of the chain
of `L` sites has regional entropy at most `C`, then every region `A` has regional entropy
at most `C` times the number of edges of the chain leaving `A`. -/
theorem regionalEntropy_le_mul_card_edgeBoundary_of_intervals {L q : ℕ}
    {Ω : StateSpace (chainDomain L) q} (hΩ : ‖Ω‖ = 1) {C : ℝ} (hC : 0 ≤ C)
    (hI : ∀ l r : ℤ, regionalEntropy (chainDomain L) q Ω (interval (chainDomain L) l r) ≤ C)
    (A : Finset (Site (chainDomain L))) :
    regionalEntropy (chainDomain L) q Ω A ≤ C * (edgeBoundary (chainDomain L) A).card := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hA : A = Finset.univ
    · subst hA
      rw [regionalEntropy_eq_finiteProduct, FiniteProduct.entropy_univ _ Ω hΩ,
        edgeBoundary_univ]
      simp
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [regionalEntropy_eq_finiteProduct, FiniteProduct.entropy_empty _ Ω hΩ,
        edgeBoundary_empty]
      simp
    obtain ⟨l, r, hIA, hIne, hss⟩ :=
      exists_interval_subset_edgeBoundary_sdiff_ssubset hne hA
    have h1 := ih _ (Finset.sdiff_ssubset hIA hIne)
    have h2 : regionalEntropy (chainDomain L) q Ω A ≤
        regionalEntropy (chainDomain L) q Ω (interval (chainDomain L) l r) +
          regionalEntropy (chainDomain L) q Ω (A \ interval (chainDomain L) l r) := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hIA]
      exact regionalEntropy_union_le hΩ Finset.disjoint_sdiff
    have h3 : ((edgeBoundary (chainDomain L) (A \ interval (chainDomain L) l r)).card : ℝ) + 1 ≤
        (edgeBoundary (chainDomain L) A).card := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.card_lt_card hss)
    calc regionalEntropy (chainDomain L) q Ω A
        ≤ C + C * (edgeBoundary (chainDomain L) (A \ interval (chainDomain L) l r)).card := by
          linarith [hI l r]
      _ = C * ((edgeBoundary (chainDomain L) (A \ interval (chainDomain L) l r)).card + 1) := by
          ring
      _ ≤ C * (edgeBoundary (chainDomain L) A).card := by gcongr

end Chain

end TNLean.PEPS.AreaLaw.Chain

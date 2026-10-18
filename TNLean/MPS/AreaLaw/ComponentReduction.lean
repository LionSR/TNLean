/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AreaLaw
import TNLean.Lattice.ZeroEntropy
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The one-dimensional area law on a finite set of integers

Theorem A of the one-dimensional note is stated for every finite set `Λ ⊂ ℤ` with its
induced path graph, whose edges join consecutive integers that both lie in `Λ`. This module
states the model on such a domain and reduces Theorem A to the chain of `|Λ|` sites.

The sites of `Λ` are labelled `0, …, |Λ| - 1` in increasing order (`sitePos`). A support of
range `R` is a nonempty set of sites of diameter at most `R` in the graph distance of the
induced path graph; such a support never contains two sites on opposite sides of a gap of
`Λ`, and its labels span at most `R + 1` consecutive values, so it is also a support of range
`R` of the chain of `|Λ|` sites. An admissible Hamiltonian on `Λ` is therefore a finite-range
Hamiltonian on that chain, with zero terms on the chain supports that straddle a gap.

The chain bound counts the chain edges at the gaps of `Λ`, which are not edges of `Λ`. The
reduction removes them. At a gap no term crosses, so the gapped ground vector has zero
entropy on the prefix of the chain ending at the gap: in cut coordinates the Hamiltonian is
`H₁ ⊗ 1 + 1 ⊗ H₂`, whose gapped ground vector is a product vector. On a region `P` of zero
entropy, the Araki–Lieb inequality and strong subadditivity give `S(A ∆ P) = S(A)` for every
region `A`, and flipping a prefix toggles exactly one boundary edge of the chain. Flipping
the prefixes at the gaps where the region changes leaves a region of the same entropy whose
boundary edges on the chain are the edges of `∂_Λ A`.

This replaces the factorization of the note, under which the ground vector is a product of
component ground vectors and entropy and edge boundary add over components, by the vanishing
entropy of unions of components; only the two-factor product lemma is used.

## Main definitions

* `sitePos`, `domainGraph`: the increasing labelling of `Λ` and its induced path graph.
* `IsDomainSupport`, `DomainHamiltonian`: supports of range `R` and admissible Hamiltonians.
* `domainBoundaryEdges`, `domainRegion`: the edge boundary `∂_Λ A` and the sites in `A`.

## Main results

The zero entropy of a cut that splits no term and the flips of regions of zero entropy are the
site-generic lemmas `TNLean.Lattice.regionEntropy_eq_zero_of_forall_subset_or_disjoint` and
`TNLean.Lattice.regionEntropy_symmDiff_eq_of_eq_zero`.

* `regionEntropy_le_mul_card_domainBoundaryEdges`: Theorem A on `Λ` with the constant
  `C_int(q, R, J, Δ)`.
* `domainAreaLaw`: Theorem A with the constant `C₀(q, R) (1 + J/Δ)`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap* (`docs/notes/one_dimensional_note`), `part0_preamble.tex`, the setting and
  Theorem A (`thm:A`), and `part1_arealaw.tex`, Section 2 (`sec:setting`), first reduction.
-/

open Matrix
open scoped ComplexOrder Kronecker symmDiff Matrix.Norms.L2Operator

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw

section Toggle

variable {L : ℕ}

/-- Position membership in a region of the chain, for an in-range position. -/
theorem exists_mem_val_eq_iff {A : Finset (Fin L)} {r : ℕ} (hr : r < L) :
    (∃ i ∈ A, i.val = r) ↔ (⟨r, hr⟩ : Fin L) ∈ A := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨_, h, rfl⟩

/-- **Flipping a prefix toggles one boundary edge.** Replacing the region `A` by its
symmetric difference with the prefix `[0, p + 1)` of the chain changes its set of boundary
edges exactly at the edge `p`. -/
theorem boundaryEdges_symmDiff_interval {A : Finset (Fin L)} {p : ℕ} (hp : p + 1 < L) :
    boundaryEdges L (A ∆ interval L 0 (p + 1)) = boundaryEdges L A ∆ {p} := by
  ext r
  rw [Finset.mem_symmDiff, mem_boundaryEdges, mem_boundaryEdges, Finset.mem_singleton]
  by_cases hr : r + 1 < L
  · rw [exists_mem_val_eq_iff (by omega), exists_mem_val_eq_iff hr,
      exists_mem_val_eq_iff (A := A) (by omega), exists_mem_val_eq_iff (A := A) hr]
    simp only [Finset.mem_symmDiff, mem_interval]
    rcases lt_trichotomy r p with h | h | h
    · have h1 : r < p + 1 := by omega
      have h2 : r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_true_eq_false, and_false, false_or, hr,
        h.ne, not_false_eq_true]
      tauto
    · subst h
      simp only [zero_le, true_and, lt_add_iff_pos_right, Nat.lt_irrefl, not_true_eq_false,
        and_false, hr, not_false_eq_true, and_true, Nat.lt_add_one]
      tauto
    · have h1 : ¬ r < p + 1 := by omega
      have h2 : ¬ r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_false_eq_true, and_true, or_false, hr,
        h.ne', false_and]
  · have : r ≠ p := by omega
    simp [hr, this]

end Toggle

section FlipInduction

variable {L q : ℕ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}

/-- **Flipping prefixes of zero entropy.** If every prefix `[0, p + 1)` with `p ∈ G` is an
inner edge cut of zero entropy, then every region `A` has a region `A'` of the same entropy
whose boundary edges are those of `A` toggled exactly at the edges of `G`. -/
theorem exists_regionEntropy_eq_boundaryEdges_eq_symmDiff (hΩ : ‖Ω‖ = 1) (G : Finset ℕ)
    (hG : ∀ p ∈ G, p + 1 < L ∧
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (interval L 0 (p + 1)) Ω = 0)
    (A : Finset (Fin L)) :
    ∃ A' : Finset (Fin L), Entropy.regionEntropy (n := fun _ : Fin L ↦ q) A' Ω =
        Entropy.regionEntropy (n := fun _ : Fin L ↦ q) A Ω ∧
      boundaryEdges L A' = boundaryEdges L A ∆ G := by
  induction G using Finset.induction_on with
  | empty => exact ⟨A, rfl, by ext; simp [Finset.mem_symmDiff]⟩
  | insert p G hp ih =>
    obtain ⟨A₁, h1, h2⟩ := ih fun r hr ↦ hG r (Finset.mem_insert_of_mem hr)
    obtain ⟨hp1, hP⟩ := hG p (Finset.mem_insert_self p G)
    refine ⟨A₁ ∆ interval L 0 (p + 1), by rw [regionEntropy_symmDiff_eq_of_eq_zero hΩ hP, h1], ?_⟩
    rw [boundaryEdges_symmDiff_interval hp1, h2, symmDiff_assoc]
    congr 1
    ext r
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases hr : r = p
    · subst hr
      simp [hp]
    · simp [hr]

end FlipInduction

/-! ### Finite domains of the integers -/

section Domain

variable {Λ : Finset ℤ} {q R : ℕ} {J : ℝ}

/-- The sites of a finite set `Λ ⊂ ℤ`, labelled `0, …, |Λ| - 1` in increasing order: site `i`
sits at the integer `sitePos Λ i`. TNLean note, `part0_preamble.tex`, the setting
(`ℋ_Λ = ⊗_{x ∈ Λ} ℂ^q`). -/
noncomputable def sitePos (Λ : Finset ℤ) : Fin Λ.card ↪o ℤ :=
  Λ.orderEmbOfFin rfl

/-- Every site sits at a point of `Λ`. -/
theorem sitePos_mem (i : Fin Λ.card) : sitePos Λ i ∈ Λ :=
  Finset.orderEmbOfFin_mem Λ rfl i

/-- Every point of `Λ` is the position of a site. -/
theorem exists_sitePos_eq {x : ℤ} (hx : x ∈ Λ) : ∃ i, sitePos Λ i = x := by
  have : x ∈ Set.range (sitePos Λ) := by
    rw [sitePos, Finset.range_orderEmbOfFin]
    exact hx
  exact this

/-- Positions grow at least as fast as labels: `j - i ≤ x_j - x_i` for `i ≤ j`. -/
theorem sub_le_sitePos_sub {i j : Fin Λ.card} (hij : i ≤ j) :
    (j.val : ℤ) - i.val ≤ sitePos Λ j - sitePos Λ i := by
  have hij' : i.val ≤ j.val := hij
  obtain ⟨k, hk⟩ : ∃ k, j.val = i.val + k := ⟨j.val - i.val, by omega⟩
  induction k generalizing j with
  | zero =>
    have : j = i := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    have hlt : i.val + k < Λ.card := by have := j.2; omega
    have h1 := ih (j := ⟨i.val + k, hlt⟩) (Fin.mk_le_mk.mpr (by omega)) (by simp) rfl
    have h2 : sitePos Λ ⟨i.val + k, hlt⟩ < sitePos Λ j :=
      (sitePos Λ).strictMono (Fin.mk_lt_of_lt_val (by omega))
    simp only at h1
    push_cast [hk] at h1 ⊢
    omega

/-- Two sites at consecutive integers have consecutive labels. -/
theorem val_eq_add_one_of_sitePos_eq_add_one {i j : Fin Λ.card}
    (h : sitePos Λ j = sitePos Λ i + 1) : j.val = i.val + 1 := by
  have hlt : i < j := (sitePos Λ).lt_iff_lt.mp (by omega)
  have := sub_le_sitePos_sub hlt.le
  have : i.val < j.val := hlt
  omega

/-- The induced path graph of `Λ` on its sites: two sites are adjacent when their positions
are consecutive integers. TNLean note, `part0_preamble.tex`, the setting. -/
def domainGraph (Λ : Finset ℤ) : SimpleGraph (Fin Λ.card) where
  Adj i j := sitePos Λ j = sitePos Λ i + 1 ∨ sitePos Λ i = sitePos Λ j + 1
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ by rcases h with h | h <;> omega⟩

/-- Along a walk of the induced path graph, position minus label is constant, and the
labels move by at most the length of the walk. -/
theorem sitePos_sub_val_of_walk {i j : Fin Λ.card} (w : (domainGraph Λ).Walk i j) :
    sitePos Λ j - j.val = sitePos Λ i - i.val ∧ (j.val : ℤ) - i.val ≤ w.length ∧
      (i.val : ℤ) - j.val ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    have h' : sitePos Λ _ = sitePos Λ _ + 1 ∨ sitePos Λ _ = sitePos Λ _ + 1 := h
    rcases h' with h' | h'
    · have := val_eq_add_one_of_sitePos_eq_add_one h'
      simp only [SimpleGraph.Walk.length_cons]
      push_cast
      omega
    · have := val_eq_add_one_of_sitePos_eq_add_one h'
      simp only [SimpleGraph.Walk.length_cons]
      push_cast
      omega

/-- A support of range `R` in `Λ`: a nonempty set of sites of diameter at most `R` in the
graph distance of the induced path graph. TNLean note, `part0_preamble.tex`, `eq:ham`. -/
def IsDomainSupport (Λ : Finset ℤ) (R : ℕ) (X : Finset (Fin Λ.card)) : Prop :=
  X.Nonempty ∧ ∀ i ∈ X, ∀ j ∈ X, (domainGraph Λ).edist i j ≤ R

noncomputable instance (Λ : Finset ℤ) (R : ℕ) : DecidablePred (IsDomainSupport Λ R) :=
  Classical.decPred _

/-- The supports of range `R` in `Λ`. -/
abbrev DomainSupport (Λ : Finset ℤ) (R : ℕ) := {X : Finset (Fin Λ.card) // IsDomainSupport Λ R X}

/-- Two sites of a support of range `R` are joined by a walk of length at most `R`. -/
theorem IsDomainSupport.exists_walk {X : Finset (Fin Λ.card)} (hX : IsDomainSupport Λ R X)
    {i j : Fin Λ.card} (hi : i ∈ X) (hj : j ∈ X) :
    ∃ w : (domainGraph Λ).Walk i j, w.length ≤ R := by
  have h := hX.2 i hi j hj
  have hne : (domainGraph Λ).edist i j ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top R) h
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  exact ⟨w, by rw [← hw] at h; exact_mod_cast h⟩

/-- A support of range `R` in `Λ` is a support of range `R` of the chain of `|Λ|` sites. -/
theorem IsDomainSupport.isChainSupport {X : Finset (Fin Λ.card)} (hX : IsDomainSupport Λ R X) :
    IsChainSupport Λ.card R X := by
  refine ⟨hX.1, fun i hi j hj ↦ ?_⟩
  obtain ⟨w, hw⟩ := hX.exists_walk hi hj
  have := (sitePos_sub_val_of_walk w).2.1
  have : (w.length : ℤ) ≤ R := by exact_mod_cast hw
  omega

/-- A support of range `R` does not straddle a gap of `Λ`: if the sites `p` and `p + 1` are
not at consecutive integers, every support lies in the prefix `[0, p + 1)` or avoids it. -/
theorem IsDomainSupport.subset_or_disjoint_of_gap {X : Finset (Fin Λ.card)}
    (hX : IsDomainSupport Λ R X) {p : ℕ} (hp : p + 1 < Λ.card)
    (hgap : sitePos Λ ⟨p + 1, hp⟩ ≠ sitePos Λ ⟨p, by omega⟩ + 1) :
    X ⊆ interval Λ.card 0 (p + 1) ∨ Disjoint X (interval Λ.card 0 (p + 1)) := by
  by_cases hsub : X ⊆ interval Λ.card 0 (p + 1)
  · exact Or.inl hsub
  refine Or.inr (Finset.disjoint_right.mpr fun i hiP hiX ↦ ?_)
  obtain ⟨j, hjX, hjP⟩ := Finset.not_subset.mp hsub
  rw [mem_interval] at hiP hjP
  obtain ⟨w, -⟩ := hX.exists_walk hiX hjX
  have hφ := (sitePos_sub_val_of_walk w).1
  have h1 := sub_le_sitePos_sub (i := i) (j := ⟨p, by omega⟩)
    (Fin.le_iff_val_le_val.mpr (by dsimp only; omega))
  have h2 := sub_le_sitePos_sub (i := ⟨p + 1, hp⟩) (j := j)
    (Fin.le_iff_val_le_val.mpr (by dsimp only; omega))
  have h3 : sitePos Λ ⟨p, by omega⟩ < sitePos Λ ⟨p + 1, hp⟩ :=
    (sitePos Λ).strictMono (Fin.mk_lt_mk.mpr (by omega))
  simp only at h1 h2
  omega

/-- An admissible Hamiltonian on a finite set `Λ ⊂ ℤ` with local dimension `q`: one term per
support of range `R`, acting as the identity off its support, Hermitian, and of operator norm
at most `J`. Zero terms are permitted. TNLean note, `part0_preamble.tex`, `eq:ham`. -/
structure DomainHamiltonian (Λ : Finset ℤ) (q R : ℕ) (J : ℝ) where
  /-- The term assigned to each support of range `R`. -/
  term : DomainSupport Λ R → Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ
  /-- Each term acts as the identity off its support. -/
  supported : ∀ X, Entropy.IsSupportedOn (n := fun _ : Fin Λ.card ↦ q) (term X) X.1
  /-- Each term is Hermitian. -/
  hermitian : ∀ X, (term X).IsHermitian
  /-- Each term has operator norm at most `J`. -/
  norm_le : ∀ X, ‖term X‖ ≤ J

/-- The Hamiltonian `H = ∑_X h_X`. TNLean note, `part0_preamble.tex`, `eq:ham`. -/
noncomputable def DomainHamiltonian.operator (h : DomainHamiltonian Λ q R J) :
    Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ :=
  ∑ X, h.term X

/-- An admissible Hamiltonian on `Λ` as a finite-range Hamiltonian on the chain of `|Λ|`
sites, with zero terms on the chain supports that straddle a gap of `Λ`. -/
noncomputable def DomainHamiltonian.toChain (h : DomainHamiltonian Λ q R J) (hJ : 0 ≤ J) :
    ChainHamiltonian Λ.card q R J where
  term Y := if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0
  supported Y := by
    split
    · exact h.supported _
    · exact ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩
  hermitian Y := by
    split
    · exact h.hermitian _
    · exact Matrix.isHermitian_zero
  norm_le Y := by
    split
    · exact h.norm_le _
    · simpa using hJ

/-- The chain Hamiltonian has the same sum. -/
theorem DomainHamiltonian.toChain_operator (h : DomainHamiltonian Λ q R J) (hJ : 0 ≤ J) :
    (h.toChain hJ).operator = h.operator := by
  classical
  refine (Fintype.sum_of_injective (fun X : DomainSupport Λ R ↦
    (⟨X.1, X.2.isChainSupport⟩ : ChainSupport Λ.card R)) (fun X Y hXY ↦ ?_) _ _ ?_ ?_).symm
  · exact Subtype.ext (congrArg (fun Y : ChainSupport Λ.card R ↦ Y.1) hXY)
  · intro Y hY
    change (if hY : IsDomainSupport Λ R Y.1 then h.term ⟨Y.1, hY⟩ else 0) = 0
    split_ifs with hY'
    · exact absurd ⟨⟨Y.1, hY'⟩, rfl⟩ hY
    · rfl
  · intro X
    change h.term X = if hY : IsDomainSupport Λ R X.1 then h.term ⟨X.1, hY⟩ else 0
    simp [X.2]

/-- The edge boundary `∂_Λ A`: the edges `{x, x + 1} ⊆ Λ` with exactly one end in `A`, each
recorded by its left end `x`. TNLean note, `part0_preamble.tex`, the setting. -/
def domainBoundaryEdges (Λ A : Finset ℤ) : Finset ℤ :=
  Λ.filter fun x ↦ x + 1 ∈ Λ ∧ ¬ (x ∈ A ↔ x + 1 ∈ A)

/-- The sites of `Λ` whose positions lie in `A`. -/
noncomputable def domainRegion (Λ A : Finset ℤ) : Finset (Fin Λ.card) :=
  Finset.univ.filter fun i ↦ sitePos Λ i ∈ A

/-- The edge `p` of the chain of `|Λ|` sites joins sites at consecutive integers. -/
def IsDomainEdge (Λ : Finset ℤ) (p : ℕ) : Prop :=
  ∃ hp : p + 1 < Λ.card, sitePos Λ ⟨p + 1, hp⟩ = sitePos Λ ⟨p, by omega⟩ + 1

/-- The boundary edges of `A` in `Λ` correspond to the boundary edges of its sites on the
chain of `|Λ|` sites that join sites at consecutive integers. -/
theorem card_domainBoundaryEdges [DecidablePred (IsDomainEdge Λ)] (A : Finset ℤ) :
    ((boundaryEdges Λ.card (domainRegion Λ A)).filter (IsDomainEdge Λ)).card =
      (domainBoundaryEdges Λ A).card := by
  have hmem : ∀ {r : ℕ} (hr : r < Λ.card),
      (∃ i ∈ domainRegion Λ A, i.val = r) ↔ sitePos Λ ⟨r, hr⟩ ∈ A := fun hr ↦ by
    rw [exists_mem_val_eq_iff hr, domainRegion, Finset.mem_filter]
    simp
  refine Finset.card_bij (fun p hp ↦ sitePos Λ ⟨p, ?_⟩) ?_ ?_ ?_
  · have := (mem_boundaryEdges.mp (Finset.mem_filter.mp hp).1).1
    omega
  · intro p hp
    obtain ⟨hpb, hp1, hcons⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpL, hpA⟩ := mem_boundaryEdges.mp hpb
    rw [hmem (by omega), hmem hpL, hcons] at hpA
    rw [domainBoundaryEdges, Finset.mem_filter]
    refine ⟨sitePos_mem _, ?_, hpA⟩
    rw [← hcons]
    exact sitePos_mem _
  · intro p hp p' hp' h
    have := (sitePos Λ).injective h
    simpa using this
  · intro x hx
    rw [domainBoundaryEdges, Finset.mem_filter] at hx
    obtain ⟨hxΛ, hx1, hxA⟩ := hx
    obtain ⟨i, rfl⟩ := exists_sitePos_eq hxΛ
    obtain ⟨j, hj⟩ := exists_sitePos_eq hx1
    have hji := val_eq_add_one_of_sitePos_eq_add_one hj
    have hpL : i.val + 1 < Λ.card := hji ▸ j.2
    have hjeq : j = ⟨i.val + 1, hpL⟩ := Fin.ext hji
    subst hjeq
    refine ⟨i.val, Finset.mem_filter.mpr ⟨mem_boundaryEdges.mpr ⟨hpL, ?_⟩, hpL, hj⟩, rfl⟩
    rw [hmem (by omega), hmem hpL, hj]
    exact hxA

end Domain

/-! ### Theorem A on a finite set of integers -/

section TheoremA

variable {Λ : Finset ℤ} {q R : ℕ} {J Δ : ℝ}

/-- **Theorem A on a finite set of integers.** For a gapped ground vector `Ω` of an
admissible Hamiltonian on a finite set `Λ ⊂ ℤ`, the entropy of the sites in every `A ⊆ ℤ` is
at most `C_int(q, R, J, Δ)` times the number of edges of `∂_Λ A`.

The proof is the component reduction of the note. At an edge of the chain of `|Λ|` sites
that joins sites at nonconsecutive integers no support crosses, so the prefix ending there
has zero entropy (`regionEntropy_eq_zero_of_forall_subset_or_disjoint`), and flipping the
region on that prefix changes neither its entropy nor any boundary edge but that one. After
the flips at the boundary edges of this kind, the region has exactly `|∂_Λ A|` boundary edges
on the chain, and the chain bound `regionEntropy_le_mul_card_boundaryEdges` applies.
TNLean note, `part0_preamble.tex`, Theorem A (`thm:A`), and `part1_arealaw.tex`, Section 2
(`sec:setting`), first reduction. -/
theorem regionEntropy_le_mul_card_domainBoundaryEdges (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (h : DomainHamiltonian Λ q R J) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q)}
    (hgs : Matrix.IsGappedGroundState h.operator E₀ Ω Δ) (A : Finset ℤ) :
    Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q) (domainRegion Λ A) Ω ≤
      chainIntervalEntropyBound q R J Δ * (domainBoundaryEdges Λ A).card := by
  classical
  set G := (boundaryEdges Λ.card (domainRegion Λ A)).filter fun p ↦ ¬ IsDomainEdge Λ p
  have hG : ∀ p ∈ G, p + 1 < Λ.card ∧ Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q)
      (interval Λ.card 0 (p + 1)) Ω = 0 := by
    intro p hp
    obtain ⟨hpb, hpe⟩ := Finset.mem_filter.mp hp
    have hp1 := (mem_boundaryEdges.mp hpb).1
    refine ⟨hp1, regionEntropy_eq_zero_of_forall_subset_or_disjoint (h := h.term)
      (D := fun X ↦ X.1) h.supported h.hermitian hΔ hgs _ fun X ↦ ?_⟩
    exact X.2.subset_or_disjoint_of_gap hp1 fun he ↦ hpe ⟨hp1, he⟩
  obtain ⟨A', hS, hB⟩ :=
    exists_regionEntropy_eq_boundaryEdges_eq_symmDiff hgs.1 G hG (domainRegion Λ A)
  have hgs' : Matrix.IsGappedGroundState (h.toChain hJ).operator E₀ Ω Δ := by
    rwa [DomainHamiltonian.toChain_operator]
  have hchain := regionEntropy_le_mul_card_boundaryEdges hq hJ hΔ (h.toChain hJ) hgs' A'
  have hsymm : boundaryEdges Λ.card (domainRegion Λ A) ∆ G =
      (boundaryEdges Λ.card (domainRegion Λ A)).filter (IsDomainEdge Λ) := by
    ext p
    simp only [G, Finset.mem_symmDiff, Finset.mem_filter]
    tauto
  rw [hS, hB, hsymm, card_domainBoundaryEdges] at hchain
  exact hchain

/-- **The one-dimensional area law** (Theorem A). For every local dimension `q ≥ 1`, range
`R`, term norm `J ≥ 0` and gap `Δ > 0` there is a constant, namely `C₀(q, R) (1 + J/Δ)`, such
that for every finite set `Λ ⊂ ℤ`, every admissible Hamiltonian on `Λ`, every gapped ground
vector `Ω` and every `A ⊆ ℤ`, the sites of `Λ` in `A` satisfy `S_Ω(A) ≤ C |∂_Λ A|`.
TNLean note, `part0_preamble.tex`, Theorem A (`thm:A`). -/
theorem domainAreaLaw (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C = chainAreaLawConst q R * (1 + J / Δ) ∧
      ∀ Λ : Finset ℤ, ∀ h : DomainHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : EuclideanSpace ℂ (Fin Λ.card → Fin q),
          Matrix.IsGappedGroundState h.operator E₀ Ω Δ → ∀ A : Finset ℤ,
            Entropy.regionEntropy (n := fun _ : Fin Λ.card ↦ q) (domainRegion Λ A) Ω ≤
              C * (domainBoundaryEdges Λ A).card := by
  have hle := chainIntervalEntropyBound_le (q := q) (R := R) hq hJ hΔ
  have h0 := chainIntervalEntropyBound_nonneg (q := q) (R := R) hq hJ hΔ
  refine ⟨chainAreaLawConst q R * (1 + J / Δ), h0.trans hle, rfl, ?_⟩
  intro Λ h E₀ Ω hgs A
  refine (regionEntropy_le_mul_card_domainBoundaryEdges hq hJ hΔ h hgs A).trans ?_
  exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

end TheoremA

end TNLean.MPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
import TNLean.PEPS.AreaLaw.ProductGroundState

/-!
# A cut with no crossing edge

Lemma 2.2 (`lem:zero-boundary`) of the area-law preprint: under the hypotheses of
Theorem 1.1, if no edge of the induced domain graph crosses the cut `A | Aᶜ`,
then the regional entropy `S_Ω(A)` vanishes.

A walk inside the domain cannot leave `A` without crossing an edge of `∂_Λ A`.
Every admissible support is joined by such walks, so it lies in one connected
component and in particular inside `A` or inside `Aᶜ`. In the split
coordinates the Hamiltonian is therefore `H_A ⊗ 1 + 1 ⊗ H_{Aᶜ}`, and the
gapped ground vector is a product vector across the cut
(`exists_eq_mul_of_gap`), whose reduced state has zero entropy.

The same argument covers the degenerate cases of Section 2: range `R = 0`
(every support is a single site, so no cut divides a support and
`H = H_A ⊗ 1 + 1 ⊗ H_{Aᶜ}` for every cut), the
empty and full regions, and every union of connected components of a
disconnected domain. For `q = 1` or an empty domain every regional entropy
vanishes for every unit vector.

## Main results

* `regionalEntropy_eq_zero_of_forall_subset_or_disjoint`: the cut does not
  split any support.
* `regionalEntropy_eq_zero_of_edgeBoundary_eq_empty`: Lemma 2.2.
* `regionalEntropy_eq_zero_of_range_eq_zero`: the range-zero case.
* `regionalEntropy_eq_zero_of_q_eq_one`, `regionalEntropy_eq_zero_of_domain_eq_empty`.
* `IsAdmissibleSupport.reachable`, `edgeBoundary_connectedComponent_eq_empty`:
  supports lie in one component, and components have no crossing edge.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2, `build/sections/01-preliminaries.tex`,
  lines 116–134 (degenerate cases and Lemma 2.2).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder Kronecker

namespace TNLean.PEPS.AreaLaw

/-! ### Splitting supported operators across a cut -/

section Splitting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (p : ι → Prop) [DecidablePred p]

/-- The coordinate splitting of configurations along a predicate on sites. -/
abbrev siteSplit (d : ℕ) : (ι → Fin d) ≃ ({i // p i} → Fin d) × ({i // ¬p i} → Fin d) :=
  Equiv.piEquivPiSubtypeProd p fun _ ↦ Fin d

omit [DecidableEq ι] in
/-- A product operator splits as a Kronecker product across a cut. -/
theorem rectKronecker_submatrix_siteSplit (m : ι → Matrix (Fin d) (Fin d) ℂ) :
    (rectKronecker m).submatrix (siteSplit p d).symm (siteSplit p d).symm =
      rectKronecker (fun i : {i // p i} ↦ m i) ⊗ₖ rectKronecker (fun i : {i // ¬p i} ↦ m i) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [submatrix_apply, rectKronecker_apply, kroneckerMap_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  congr 1
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [siteSplit, Equiv.piEquivPiSubtypeProd, i.2]
  · refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [siteSplit, Equiv.piEquivPiSubtypeProd, i.2]

omit [DecidableEq ι] in
/-- An operator acting on sites satisfying `p` is `K ⊗ 1` in the split
coordinates. -/
theorem exists_submatrix_siteSplit_eq_kronecker_one {S : Set ι} (hS : ∀ i ∈ S, p i)
    {M : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hM : M ∈ QuantumCircuit.supportedOperators d S) :
    ∃ K, M.submatrix (siteSplit p d).symm (siteSplit p d).symm = K ⊗ₖ 1 := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨rectKronecker fun i : {i // p i} ↦ m i, ?_⟩
    rw [rectKronecker_submatrix_siteSplit]
    congr 1
    have : (fun i : {i // ¬p i} ↦ m i) = fun _ ↦ 1 :=
      funext fun i ↦ hm i fun hi ↦ i.2 (hS i hi)
    rw [this, rectKronecker_one]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨K, hK⟩ := hx
    obtain ⟨L, hL⟩ := hy
    exact ⟨K + L, by rw [add_kronecker, ← hK, ← hL]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨K, hK⟩ := hx
    exact ⟨c • K, by rw [smul_kronecker, ← hK]; rfl⟩

omit [DecidableEq ι] in
/-- An operator acting on sites not satisfying `p` is `1 ⊗ K` in the split
coordinates. -/
theorem exists_submatrix_siteSplit_eq_one_kronecker {S : Set ι} (hS : ∀ i ∈ S, ¬p i)
    {M : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hM : M ∈ QuantumCircuit.supportedOperators d S) :
    ∃ K, M.submatrix (siteSplit p d).symm (siteSplit p d).symm = 1 ⊗ₖ K := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨rectKronecker fun i : {i // ¬p i} ↦ m i, ?_⟩
    rw [rectKronecker_submatrix_siteSplit]
    congr 1
    have : (fun i : {i // p i} ↦ m i) = fun _ ↦ 1 :=
      funext fun i ↦ hm i fun hi ↦ hS i hi i.2
    rw [this, rectKronecker_one]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨K, hK⟩ := hx
    obtain ⟨L, hL⟩ := hy
    exact ⟨K + L, by rw [kronecker_add, ← hK, ← hL]; rfl⟩
  | smul c x _ hx =>
    obtain ⟨K, hK⟩ := hx
    exact ⟨c • K, by rw [kronecker_smul, ← hK]; rfl⟩

end Splitting

/-! ### Walks, components and crossing edges -/

section Graph

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}

/-- Without crossing edges, adjacent sites are on the same side of the cut. -/
theorem mem_iff_of_adj_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {x y : Site Λ}
    (hxy : (domainGraph Λ).Adj x y) : x ∈ A ↔ y ∈ A := by
  classical
  have key : ∀ {a b : Site Λ}, (domainGraph Λ).Adj a b → a ∈ A → b ∉ A → False := by
    intro a b hab ha hb
    have hmem : s(a, b) ∈ edgeBoundary Λ A := by
      simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨hab, a, ha, b, hb, rfl⟩
    rw [hA] at hmem
    simp at hmem
  constructor
  · intro hx; by_contra hy; exact key hxy hx hy
  · intro hy; by_contra hx; exact key hxy.symm hy hx

/-- Without crossing edges, the two ends of a walk are on the same side of the
cut. -/
theorem mem_iff_of_walk_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {x y : Site Λ}
    (w : (domainGraph Λ).Walk x y) : x ∈ A ↔ y ∈ A := by
  induction w with
  | nil => rfl
  | cons h _ ih => exact (mem_iff_of_adj_of_edgeBoundary_eq_empty hA h).trans ih

/-- **A cut with no crossing edge splits no support.** Every admissible support
lies inside `A` or is disjoint from it. -/
theorem subset_or_disjoint_of_edgeBoundary_eq_empty (hA : edgeBoundary Λ A = ∅) {R : ℕ}
    (X : AdmissibleSupport Λ R) : X.1 ⊆ A ∨ Disjoint X.1 A := by
  obtain ⟨⟨x₀, hx₀⟩, hwalk⟩ := X.2
  by_cases h : x₀ ∈ A
  · left
    intro y hy
    obtain ⟨w, -⟩ := hwalk x₀ hx₀ y hy
    exact (mem_iff_of_walk_of_edgeBoundary_eq_empty hA w).mp h
  · right
    rw [Finset.disjoint_left]
    intro y hy hyA
    obtain ⟨w, -⟩ := hwalk x₀ hx₀ y hy
    exact h ((mem_iff_of_walk_of_edgeBoundary_eq_empty hA w).mpr hyA)

/-- **Every admissible support lies in one connected component.** -/
theorem IsAdmissibleSupport.reachable {R : ℕ} {X : Finset (Site Λ)}
    (hX : IsAdmissibleSupport Λ R X) {x y : Site Λ} (hx : x ∈ X) (hy : y ∈ X) :
    (domainGraph Λ).Reachable x y :=
  let ⟨w, _⟩ := hX.2 x hx y hy
  ⟨w⟩

open scoped Classical in
/-- **A union of connected components has no crossing edge.** For a set `s` of
components of the induced domain graph, the set of sites in components of `s`
has empty edge boundary. -/
theorem edgeBoundary_connectedComponents_eq_empty
    (s : Set (domainGraph Λ).ConnectedComponent) :
    edgeBoundary Λ (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x ∈ s) =
      ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Finset.mem_univ,
    true_and] at he
  obtain ⟨hadj, x, hx, y, hy, rfl⟩ := he
  rw [SimpleGraph.mem_edgeSet] at hadj
  have hxy : (domainGraph Λ).connectedComponentMk x = (domainGraph Λ).connectedComponentMk y :=
    SimpleGraph.ConnectedComponent.eq.mpr ⟨SimpleGraph.Walk.cons hadj .nil⟩
  exact hy (hxy ▸ hx)

open scoped Classical in
/-- **A connected component has no crossing edge.** -/
theorem edgeBoundary_connectedComponent_eq_empty
    (c : (domainGraph Λ).ConnectedComponent) :
    edgeBoundary Λ (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x = c) =
      ∅ := by
  simpa using edgeBoundary_connectedComponents_eq_empty (Λ := Λ) {c}

end Graph

/-! ### Lemma 2.2 -/

section ZeroBoundary

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

theorem configurationSplit_eq_siteSplit (A : Finset (Site Λ)) :
    configurationSplit Λ q A = siteSplit (· ∈ A) q :=
  rfl

/-- If no admissible support is split by the cut `A | Aᶜ`, the Hamiltonian is a
sum of two commuting factor Hamiltonians in the split coordinates. -/
theorem exists_operator_submatrix_eq (h : LocalHamiltonian Λ q R J) (A : Finset (Site Λ))
    (hsplit : ∀ X : AdmissibleSupport Λ R, X.1 ⊆ A ∨ Disjoint X.1 A) :
    ∃ (HA : Matrix ({x : Site Λ // x ∈ A} → Fin q) ({x : Site Λ // x ∈ A} → Fin q) ℂ)
      (HB : Matrix ({x : Site Λ // x ∉ A} → Fin q) ({x : Site Λ // x ∉ A} → Fin q) ℂ),
      h.operator.submatrix (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm =
        HA ⊗ₖ 1 + 1 ⊗ₖ HB := by
  let P : Matrix (Configuration Λ q) (Configuration Λ q) ℂ → Prop := fun M ↦
    ∃ HA HB, M.submatrix (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm =
      HA ⊗ₖ (1 : Matrix ({x : Site Λ // x ∉ A} → Fin q) _ ℂ) + 1 ⊗ₖ HB
  refine Finset.sum_induction _ P ?_ ?_ ?_
  · rintro M N ⟨HA, HB, hM⟩ ⟨HA', HB', hN⟩
    refine ⟨HA + HA', HB + HB', ?_⟩
    rw [show (M + N).submatrix (configurationSplit Λ q A).symm (configurationSplit Λ q A).symm =
        M.submatrix _ _ + N.submatrix _ _ from rfl, hM, hN, add_kronecker, kronecker_add]
    abel
  · exact ⟨0, 0, by simp⟩
  · intro X _
    rcases hsplit X with hX | hX
    · obtain ⟨K, hK⟩ := exists_submatrix_siteSplit_eq_kronecker_one (· ∈ A)
        (S := (X.1 : Set (Site Λ))) (fun i hi ↦ hX hi) (h.supported X)
      exact ⟨K, 0, by
        rw [configurationSplit_eq_siteSplit, hK, kronecker_zero, add_zero]⟩
    · obtain ⟨K, hK⟩ := exists_submatrix_siteSplit_eq_one_kronecker (· ∈ A)
        (S := (X.1 : Set (Site Λ))) (fun i hi ↦ Finset.disjoint_left.mp hX hi) (h.supported X)
      exact ⟨0, K, by
        rw [configurationSplit_eq_siteSplit, hK, zero_kronecker, zero_add]
        convert rfl⟩

/-- **Zero entropy for a cut that splits no support.** Under the gapped
ground-state hypothesis of Theorem 1.1, if every admissible support lies inside
`A` or is disjoint from it, then `S_Ω(A) = 0`. -/
theorem regionalEntropy_eq_zero_of_forall_subset_or_disjoint (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ))
    (hsplit : ∀ X : AdmissibleSupport Λ R, X.1 ⊆ A ∨ Disjoint X.1 A) :
    regionalEntropy Λ q Ω A = 0 := by
  classical
  obtain ⟨hnorm, hev, hgap⟩ := hΩ
  obtain ⟨HA, HB, hHs⟩ := exists_operator_submatrix_eq h A hsplit
  set e := configurationSplit Λ q A
  set Ωf : Configuration Λ q → ℂ := fun x ↦ Ω x
  set ω : _ → ℂ := Ωf ∘ e.symm with hωdef
  -- The split Hamiltonian is Hermitian; replace `HA`, `HB` by their Hermitian parts.
  have hHerm : (HA ⊗ₖ (1 : Matrix ({x : Site Λ // x ∉ A} → Fin q) _ ℂ) + 1 ⊗ₖ HB).IsHermitian := by
    rw [← hHs]; exact h.operator_isHermitian.submatrix _
  set HA' := (1 / 2 : ℂ) • (HA + HAᴴ)
  set HB' := (1 / 2 : ℂ) • (HB + HBᴴ)
  have hA' : HA'.IsHermitian := by
    simp only [HA', IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  have hB' : HB'.IsHermitian := by
    simp only [HB', IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  have hsum : HA ⊗ₖ (1 : Matrix ({x : Site Λ // x ∉ A} → Fin q) _ ℂ) + 1 ⊗ₖ HB =
      HA' ⊗ₖ 1 + 1 ⊗ₖ HB' := by
    have hc := hHerm.eq
    rw [conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
      conjTranspose_one] at hc
    have hexp : HA' ⊗ₖ (1 : Matrix ({x : Site Λ // x ∉ A} → Fin q) _ ℂ) + 1 ⊗ₖ HB' =
        (1 / 2 : ℂ) • ((HA ⊗ₖ 1 + 1 ⊗ₖ HB) + (HAᴴ ⊗ₖ 1 + 1 ⊗ₖ HBᴴ)) := by
      simp only [HA', HB', add_kronecker, kronecker_add, smul_kronecker, kronecker_smul,
        smul_add]
      abel
    rw [hexp, hc, ← two_smul ℂ, smul_smul]
    norm_num
  -- Transport the ground-state data to the split coordinates.
  have hω1 : star ω ⬝ᵥ ω = 1 := by
    have h1 : (star Ωf ⬝ᵥ Ωf : ℂ) = 1 := by
      have := EuclideanSpace.inner_eq_star_dotProduct Ω Ω
      rw [inner_self_eq_norm_sq_to_K, hnorm] at this
      simpa [dotProduct_comm, Ωf] using this.symm
    rw [← h1, hωdef]
    simp only [dotProduct, Pi.star_apply, Function.comp_apply]
    exact Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl
  have hevω : (HA' ⊗ₖ 1 + 1 ⊗ₖ HB') *ᵥ ω = (E₀ : ℂ) • ω := by
    rw [← hsum, ← hHs, submatrix_mulVec_equiv, Equiv.symm_symm, hωdef]
    have h1 : h.operator *ᵥ Ωf = (E₀ : ℂ) • Ωf := by
      have := congrArg WithLp.ofLp hev
      simpa [Ωf] using this
    funext p
    simp [Function.comp_def, h1, Ωf]
  have hgapω : (HA' ⊗ₖ 1 + 1 ⊗ₖ HB' - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec ω (star ω))).PosSemidef := by
    rw [← hsum, ← hHs]
    convert hgap.submatrix e.symm using 1
    ext p p'
    simp [vecMulVec_apply, one_apply, Ωf, hωdef, e.symm.injective.eq_iff]
  have hred : reducedState Λ q Ω A = partialTraceRight (vecMulVec ω (star ω)) := by
    ext i j; rfl
  rw [regionalEntropy, vonNeumannEntropy_congr hred _
    (partialTraceRight_isHermitian (posSemidef_vecMulVec_self_star ω).isHermitian)]
  exact vonNeumannEntropy_partialTraceRight_eq_zero_of_gap hA' hB' hω1 hΔ hevω hgapω

/-- **A cut with no crossing edge** (area-law preprint, Lemma 2.2,
`lem:zero-boundary`, `01-preliminaries.tex` lines 123–134). Under the
hypotheses of Theorem 1.1, if `∂_Λ A = ∅`, then `S_Ω(A) = 0`.

Only the gapped ground-state hypothesis with `Δ > 0` is used; the bound `J`,
the range `R` and the local dimension `q` are arbitrary. -/
theorem regionalEntropy_eq_zero_of_edgeBoundary_eq_empty (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) {A : Finset (Site Λ)}
    (hA : edgeBoundary Λ A = ∅) : regionalEntropy Λ q Ω A = 0 :=
  regionalEntropy_eq_zero_of_forall_subset_or_disjoint h hΔ hΩ A
    (subset_or_disjoint_of_edgeBoundary_eq_empty hA)

/-- **Range zero** (area-law preprint, `01-preliminaries.tex` lines 118–120). For
`R = 0` the Hamiltonian is a sum of on-site terms and every regional entropy of
the gapped ground vector vanishes. -/
theorem regionalEntropy_eq_zero_of_range_eq_zero (h : LocalHamiltonian Λ q 0 J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A = 0 := by
  refine regionalEntropy_eq_zero_of_forall_subset_or_disjoint h hΔ hΩ A fun X ↦ ?_
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp ((isAdmissibleSupport_zero_iff Λ X.1).mp X.2)
  rw [hx]
  by_cases hxA : x ∈ A
  · exact Or.inl (Finset.singleton_subset_iff.mpr hxA)
  · exact Or.inr (Finset.disjoint_singleton_left.mpr hxA)

/-- The reduced state of a unit vector has unit trace. -/
theorem trace_reducedState (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).trace = 1 := by
  classical
  rw [reducedState, trace_partialTraceRight, trace_submatrix_equiv, trace_vecMulVec]
  have := EuclideanSpace.inner_eq_star_dotProduct Ω Ω
  rw [inner_self_eq_norm_sq_to_K, hΩ] at this
  simpa using this.symm

/-- A regional entropy vanishes when the regional configuration space has at
most one element. -/
theorem regionalEntropy_eq_zero_of_card_le_one (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) (hcard : Fintype.card ({x : Site Λ // x ∈ A} → Fin q) ≤ 1) :
    regionalEntropy Λ q Ω A = 0 := by
  classical
  exact vonNeumannEntropy_eq_zero_of_rank_le_one (reducedState_posSemidef Λ q Ω A)
    (trace_reducedState Ω hΩ A) ((rank_le_card_width _).trans hcard)

/-- **Local dimension one** (area-law preprint, `01-preliminaries.tex`,
line 116): for `q = 1` every regional entropy of every unit vector vanishes. -/
theorem regionalEntropy_eq_zero_of_q_eq_one {Ω : StateSpace Λ 1} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site Λ)) : regionalEntropy Λ 1 Ω A = 0 :=
  regionalEntropy_eq_zero_of_card_le_one Ω hΩ A (by simp)

/-- **Empty domain** (area-law preprint, `01-preliminaries.tex`, line 116): on
the empty domain every regional entropy of every unit vector vanishes. -/
theorem regionalEntropy_eq_zero_of_domain_eq_empty {Ω : StateSpace ∅ q} (hΩ : ‖Ω‖ = 1)
    (A : Finset (Site ∅)) : regionalEntropy ∅ q Ω A = 0 :=
  regionalEntropy_eq_zero_of_card_le_one Ω hΩ A (by
    rw [Fintype.card_fun]
    simp)

open scoped Classical in
/-- **Unions of connected components** (area-law preprint, proof of Lemma 2.2):
the regional entropy of the gapped ground vector vanishes on every union of
connected components of the induced domain graph, in particular on each
component of a disconnected domain. -/
theorem regionalEntropy_connectedComponents_eq_zero (h : LocalHamiltonian Λ q R J)
    {E₀ Δ : ℝ} (hΔ : 0 < Δ) {Ω : StateSpace Λ q}
    (hΩ : IsGappedGroundState Λ q h.operator E₀ Ω Δ)
    (s : Set (domainGraph Λ).ConnectedComponent) :
    regionalEntropy Λ q Ω
      (Finset.univ.filter fun x ↦ (domainGraph Λ).connectedComponentMk x ∈ s) = 0 :=
  regionalEntropy_eq_zero_of_edgeBoundary_eq_empty h hΔ hΩ
    (edgeBoundary_connectedComponents_eq_empty s)

end ZeroBoundary

end TNLean.PEPS.AreaLaw

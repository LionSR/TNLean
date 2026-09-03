/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.CommutingStarSubalgebraKronecker
import TNLean.QCA.SiteIndexedSupportAlgebra

/-!
# Norm-closed generation of the quasi-local algebra by the support algebras

The observable algebras of two disjoint finite regions generate the observable algebra of their
union: in bipartite coordinates the two canonical inclusions are the two Kronecker embeddings, and
products of matrices tensored with the identity span every matrix. Because every site lies in one
of the pairs \(E_x=\{2x,2x+1\}\), the pair algebras therefore generate the whole algebraic local
algebra,
\[
  \bigvee_{x\in\mathbb Z}\mathcal A_{E_x}=\mathcal A_{\mathrm{loc}}.
\]

Applying a nearest-neighbour automorphism \(\omega\) to a pair algebra keeps the result inside the
join
\[
  G=\bigvee_{y\in\mathbb Z}\widehat{\mathcal R}_y
\]
of the site-indexed support algebras, by the two-sided support containment. The algebraic local
algebra is norm dense and \(\omega\) is a surjective isometry, so \(G\) is norm dense. Hence
\(G\) generates the quasi-local algebra in the norm-closed sense.

The algebraic join \(G\) itself is a join of finite-dimensional algebras and is therefore a proper
subalgebra of the quasi-local algebra: the equality asserted here is one of norm closures. Only
the finite local observables are represented on finite regions; a general quasi-local observable
enters through density and continuity.

**Scope restriction (homogeneous chain):** Gross--Nesme--Vogts--Werner allow the one-site matrix
size to depend on the site, and they assume neither a fixed size nor translation covariance. This
file treats the fixed positive size \(d\) of the present quasi-local algebra, so it is reusable
homogeneous infrastructure rather than the unrestricted source statement. See
[the homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf).

No trivial center, matrix-factor presentation, adjacent-block generation equality, or index is
proved here.

## Main definitions

* `SpinChain.PropagatesWithin.supportAlgebraJoin` is the algebraic join
  \(G=\bigvee_y\widehat{\mathcal R}_y\).

## Main results

* `SpinChain.range_localObservable_union` proves that two disjoint finite regions generate their
  union.
* `SpinChain.iSup_range_localObservable_evenPair` is the algebraic local-generation lemma for the
  even pairs.
* `SpinChain.PropagatesWithin.quasiLocalObservable_evenPair_mem_supportAlgebraJoin` places every
  image \(\omega(\mathcal A_{E_x})\) inside \(G\).
* `SpinChain.PropagatesWithin.supportAlgebraJoin_topologicalClosure_eq_top` is the norm-closed
  generation theorem.
* `SpinChain.PropagatesWithin.commute_of_forall_commute_embeddedSupportAlgebra` derives
  commutation with every quasi-local observable from commutation with every support algebra.

## References

* Gross--Nesme--Vogts--Werner, arXiv:0910.3675v2, lines 578--598 and lines 1276--1282.
* Schumacher--Werner, quant-ph/0405174, lines 263--285 and Lemma `lem:localrule`,
  lines 331--365.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2298.
-/

namespace SpinChain

/-! ### Generation of a finite region by disjoint subregions -/

variable {d : ℕ}

/-- Enlarging a finite region enlarges its canonical image in the algebraic local algebra.

Source context: this is the identification of \(\mathcal A_{\Lambda_1}\) with a subalgebra of
\(\mathcal A_{\Lambda_2}\) for \(\Lambda_1\subseteq\Lambda_2\) in GNVW, arXiv:0910.3675v2,
lines 580--584, and in Schumacher--Werner, quant-ph/0405174, lines 270--276. -/
theorem range_localObservable_mono (d : ℕ) {Λ Γ : Finset ℤ} (hΛΓ : Λ ⊆ Γ) :
    (localObservable d Λ).range ≤ (localObservable d Γ).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨localInclusion hΛΓ a, localObservable_localInclusion d hΛΓ a⟩

/-- The two Kronecker embeddings of the full matrix algebras of the two factors generate the full
matrix algebra of the product index type.

Every matrix on the product index type is a linear combination of Kronecker products, and each
Kronecker product is a product of one embedded matrix with one embedded matrix.

Source context: this is the expansion of a local observable into a linear combination of tensor
products in Schumacher--Werner, quant-ph/0405174, Lemma `lem:localrule`, lines 360--364. -/
private theorem kroneckerEmbed_sup_eq_top {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] :
    (⊤ : StarSubalgebra ℂ (Matrix m m ℂ)).map (Matrix.leftKroneckerEmbed (n := n)) ⊔
      (⊤ : StarSubalgebra ℂ (Matrix n n ℂ)).map (Matrix.rightKroneckerEmbed (m := m)) = ⊤ := by
  refine eq_top_iff.mpr fun X _ ↦ ?_
  have hmem : X ∈ Matrix.kroneckerSubmodule
      (⊤ : StarSubalgebra ℂ (Matrix m m ℂ)).toSubmodule
      (⊤ : StarSubalgebra ℂ (Matrix n n ℂ)).toSubmodule := by
    rw [Matrix.mem_kroneckerSubmodule_iff]
    exact ⟨fun _ _ ↦ StarSubalgebra.mem_top (R := ℂ), fun _ _ ↦ StarSubalgebra.mem_top (R := ℂ)⟩
  rwa [← Matrix.leftKroneckerEmbed_sup_rightKroneckerEmbed_toSubmodule] at hmem

/-- The observable algebras of two disjoint finite regions generate the observable algebra of
their union.

In the bipartite coordinates of the union, the two canonical inclusions are the two Kronecker
embeddings, and every matrix on the product index type is a linear combination of Kronecker
products.

This is the algebraic expansion of a local observable into products of observables on disjoint
regions used in GNVW, arXiv:0910.3675v2, lines 592--596, and proved in Schumacher--Werner,
quant-ph/0405174, Lemma `lem:localrule`, lines 341--364. -/
theorem range_localObservable_union (d : ℕ) [NeZero d] {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) :
    (localObservable d (Λ ∪ Γ)).range =
      (localObservable d Λ).range ⊔ (localObservable d Γ).range := by
  refine le_antisymm ?_
    (sup_le (range_localObservable_mono d Finset.subset_union_left)
      (range_localObservable_mono d Finset.subset_union_right))
  rintro _ ⟨a, rfl⟩
  set V : StarSubalgebra ℂ (LocalAlgebra d (Λ ∪ Γ)) :=
    ((localObservable d Λ).range ⊔ (localObservable d Γ).range).comap
      (localObservable d (Λ ∪ Γ)) with hV
  have hleft : (⊤ : StarSubalgebra ℂ (Matrix (Config d Λ) (Config d Λ) ℂ)).map
      (Matrix.leftKroneckerEmbed (n := Config d Γ)) ≤
      V.map (bipartiteLocalAlgebraEquiv hΛΓ).toStarAlgHom := by
    rw [StarSubalgebra.map_le_iff_le_comap]
    intro A _
    rw [StarSubalgebra.mem_comap]
    refine StarSubalgebra.mem_map.mpr
      ⟨localInclusion (d := d) Finset.subset_union_left (CStarMatrix.ofMatrix A), ?_, ?_⟩
    · rw [hV, StarSubalgebra.mem_comap, localObservable_localInclusion]
      exact SetLike.le_def.mp le_sup_left ⟨CStarMatrix.ofMatrix A, rfl⟩
    · exact bipartiteLocalAlgebraEquiv_localInclusion_left hΛΓ (CStarMatrix.ofMatrix A)
  have hright : (⊤ : StarSubalgebra ℂ (Matrix (Config d Γ) (Config d Γ) ℂ)).map
      (Matrix.rightKroneckerEmbed (m := Config d Λ)) ≤
      V.map (bipartiteLocalAlgebraEquiv hΛΓ).toStarAlgHom := by
    rw [StarSubalgebra.map_le_iff_le_comap]
    intro B _
    rw [StarSubalgebra.mem_comap]
    refine StarSubalgebra.mem_map.mpr
      ⟨localInclusion (d := d) Finset.subset_union_right (CStarMatrix.ofMatrix B), ?_, ?_⟩
    · rw [hV, StarSubalgebra.mem_comap, localObservable_localInclusion]
      exact SetLike.le_def.mp le_sup_right ⟨CStarMatrix.ofMatrix B, rfl⟩
    · exact bipartiteLocalAlgebraEquiv_localInclusion_right hΛΓ (CStarMatrix.ofMatrix B)
  have hea : bipartiteLocalAlgebraEquiv hΛΓ a ∈
      (⊤ : StarSubalgebra ℂ (Matrix (Config d Λ) (Config d Λ) ℂ)).map
        (Matrix.leftKroneckerEmbed (n := Config d Γ)) ⊔
      (⊤ : StarSubalgebra ℂ (Matrix (Config d Γ) (Config d Γ) ℂ)).map
        (Matrix.rightKroneckerEmbed (m := Config d Λ)) := by
    rw [kroneckerEmbed_sup_eq_top]
    exact StarSubalgebra.mem_top
  obtain ⟨b, hbV, hb⟩ := StarSubalgebra.mem_map.mp (sup_le hleft hright hea)
  have hba : b = a := (bipartiteLocalAlgebraEquiv hΛΓ).injective hb
  rw [hV, StarSubalgebra.mem_comap] at hbV
  rwa [hba] at hbV

/-- Distinct even pairs are disjoint.

Source context: GNVW, arXiv:0910.3675v2, lines 1252--1256, group the chain into the pairs
\(E_x=\{2x,2x+1\}\). -/
lemma disjoint_evenPair_of_ne {x y : ℤ} (hxy : x ≠ y) :
    Disjoint (evenPair x) (evenPair y) := by
  rw [Finset.disjoint_left]
  intro a hax hay
  simp only [evenPair, Finset.mem_insert, Finset.mem_singleton] at hax hay
  omega

/-- Every site lies in an even pair, so every finite region is covered by finitely many of them.

Source context: GNVW, arXiv:0910.3675v2, lines 1252--1256, where regrouping the chain into the
pairs \(E_x\) covers every site. -/
lemma subset_biUnion_evenPair (Λ : Finset ℤ) :
    Λ ⊆ (Λ.image fun i ↦ i / 2).biUnion evenPair := by
  intro i hi
  refine Finset.mem_biUnion.mpr ⟨i / 2, Finset.mem_image_of_mem _ hi, ?_⟩
  simp only [evenPair, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The even pairs meeting a finite set of pair labels generate no more than the join of all pair
algebras.

Source context: this is the induction over finitely many disjoint groups behind the expansion into
products of one-site observables in GNVW, arXiv:0910.3675v2, lines 592--596. -/
theorem range_localObservable_biUnion_evenPair_le (d : ℕ) [NeZero d] (X : Finset ℤ) :
    (localObservable d (X.biUnion evenPair)).range ≤
      ⨆ x : ℤ, (localObservable d (evenPair x)).range := by
  classical
  induction X using Finset.induction_on with
  | empty =>
      rw [Finset.biUnion_empty]
      exact (range_localObservable_mono d (Finset.empty_subset (evenPair 0))).trans
        (le_iSup (fun x : ℤ ↦ (localObservable d (evenPair x)).range) 0)
  | @insert x₀ X' hx₀ ih =>
      have hdisj : Disjoint (evenPair x₀) (X'.biUnion evenPair) := by
        rw [Finset.disjoint_biUnion_right]
        intro y hy
        exact disjoint_evenPair_of_ne (by rintro rfl; exact hx₀ hy)
      rw [Finset.biUnion_insert, range_localObservable_union d hdisj]
      exact sup_le (le_iSup (fun x : ℤ ↦ (localObservable d (evenPair x)).range) x₀) ih

/-- Algebraic local-generation lemma: the pair algebras \(\mathcal A_{E_x}\) generate the whole
algebraic local algebra.

Every local observable is represented on a finite region, that region is covered by finitely many
even pairs, and disjoint regions generate their union.

Source context: GNVW, arXiv:0910.3675v2, lines 592--596, states that every observable on finitely
many cells expands into products of one-site observables; Schumacher--Werner, quant-ph/0405174,
Lemma `lem:localrule`, lines 341--364, gives the same expansion. The completion is not involved
in this statement. -/
theorem iSup_range_localObservable_evenPair (d : ℕ) [NeZero d] :
    (⨆ x : ℤ, (localObservable d (evenPair x)).range) = ⊤ := by
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨Λ, a, rfl⟩ := exists_supportedIn z
  exact range_localObservable_biUnion_evenPair_le d _
    (range_localObservable_mono d (subset_biUnion_evenPair Λ) ⟨a, rfl⟩)

/-! ### The quasi-local join of the site-indexed support algebras -/

namespace PropagatesWithin

variable [NeZero d] {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- The algebraic join \(G=\bigvee_{y\in\mathbb Z}\widehat{\mathcal R}_y\) of the canonically
embedded site-indexed support algebras.

This is one star-subalgebra of the quasi-local algebra, not a norm-closed one: it is generated by
finite-dimensional algebras, so it does not contain the whole completion.

Source context: GNVW, arXiv:0910.3675v2, lines 1276--1279, form the algebra generated by all
\(\mathcal R_y\); see the homogeneous-chain scope statement in the module docstring. -/
noncomputable def supportAlgebraJoin (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    StarSubalgebra ℂ (QuasiLocalAlgebra d) :=
  ⨆ y : ℤ, embeddedSupportAlgebra hω y

/-- The canonical quasi-local copy of \(\mathcal R_{2x}\) lies in the join.

Source context: GNVW, arXiv:0910.3675v2, lines 1276--1279. -/
theorem embeddedEvenSupportAlgebra_le_supportAlgebraJoin
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    embeddedEvenSupportAlgebra hω x ≤ supportAlgebraJoin hω := by
  rw [supportAlgebraJoin, ← embeddedSupportAlgebra_even hω x]
  exact le_iSup (fun y : ℤ ↦ embeddedSupportAlgebra hω y) (2 * x)

/-- The canonical quasi-local copy of \(\mathcal R_{2x+1}\) lies in the join.

Source context: GNVW, arXiv:0910.3675v2, lines 1276--1279. -/
theorem embeddedOddSupportAlgebra_le_supportAlgebraJoin
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    embeddedOddSupportAlgebra hω x ≤ supportAlgebraJoin hω := by
  rw [supportAlgebraJoin, ← embeddedSupportAlgebra_odd hω x]
  exact le_iSup (fun y : ℤ ↦ embeddedSupportAlgebra hω y) (2 * x + 1)

/-- The image of a pair algebra under the automorphism lies in the join of the support algebras.

The two-sided support containment writes the finite image of \(\mathcal A_{E_x}\) inside the
Kronecker span of \(\mathcal R_{2x}\) and \(\mathcal R_{2x+1}\), and that span is the join of the
two canonically embedded factors.

This is the containment
\(\omega(\mathcal A_{E_x})\subseteq\mathcal R_{2x}\otimes\mathcal R_{2x+1}\)
used in GNVW, arXiv:0910.3675v2, lines 1276--1278; see the homogeneous-chain scope statement in
the module docstring. -/
theorem quasiLocalObservable_evenPair_mem_supportAlgebraJoin
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (A : LocalAlgebra d (evenPair x)) :
    ω (quasiLocalObservable d (evenPair x) A) ∈ supportAlgebraJoin hω := by
  have hΓΔ : Disjoint (leftPair x) (rightPair x) := disjoint_leftPair_rightPair x
  have htarget : regionSumset (evenPair x) (Finset.Icc (-1) 1) =
      leftPair x ∪ rightPair x := regionSumset_evenPair x
  set b : LocalAlgebra d (leftPair x ∪ rightPair x) :=
    htarget ▸ hω.localRestriction (evenPair x) A with hb
  set X : Matrix (Config d (leftPair x) × Config d (rightPair x))
      (Config d (leftPair x) × Config d (rightPair x)) ℂ :=
    bipartiteLocalAlgebraEquiv hΓΔ b with hX
  -- the finite image contains the bipartite representative of the local restriction
  have hXmem : X ∈ evenPairLocalImage hω x := by
    rw [evenPairLocalImage, bipartiteLocalRestrictionRange, StarSubalgebra.bipartiteReindex]
    exact StarSubalgebra.mem_map.mpr
      ⟨b, (mem_transport_localRestrictionRange_iff hω htarget b).mpr ⟨A, hb⟩, rfl⟩
  -- the two-sided support containment, read as membership in the join of the two factors
  have hXjoin : X ∈ (evenSupportAlgebra hω x).map
        (Matrix.leftKroneckerEmbed (n := Config d (rightPair x))) ⊔
      (oddSupportAlgebra hω x).map
        (Matrix.rightKroneckerEmbed (m := Config d (leftPair x))) := by
    have hcontain := evenPairLocalImage_le_support_kroneckerSubmodule hω x hXmem
    rwa [← Matrix.leftKroneckerEmbed_sup_rightKroneckerEmbed_toSubmodule] at hcontain
  -- the canonical quasi-local map in bipartite coordinates
  set φ : Matrix (Config d (leftPair x) × Config d (rightPair x))
      (Config d (leftPair x) × Config d (rightPair x)) ℂ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
    (quasiLocalObservable d (leftPair x ∪ rightPair x)).comp
      (bipartiteLocalAlgebraEquiv hΓΔ).symm.toStarAlgHom with hφ
  have hφ_apply : ∀ Y, φ Y = quasiLocalObservable d (leftPair x ∪ rightPair x)
      ((bipartiteLocalAlgebraEquiv hΓΔ).symm Y) := fun _ ↦ rfl
  have hleft : (evenSupportAlgebra hω x).map
      (Matrix.leftKroneckerEmbed (n := Config d (rightPair x))) ≤
      (supportAlgebraJoin hω).comap φ := by
    rw [StarSubalgebra.map_le_iff_le_comap]
    intro a ha
    rw [StarSubalgebra.mem_comap, StarSubalgebra.mem_comap]
    have hinc : bipartiteLocalAlgebraEquiv hΓΔ
        (localInclusion (d := d) Finset.subset_union_left (CStarMatrix.ofMatrix a)) =
        Matrix.leftKroneckerEmbed (n := Config d (rightPair x)) a :=
      bipartiteLocalAlgebraEquiv_localInclusion_left hΓΔ (CStarMatrix.ofMatrix a)
    change φ (Matrix.leftKroneckerEmbed (n := Config d (rightPair x)) a) ∈
      supportAlgebraJoin hω
    rw [hφ_apply, ← hinc, StarAlgEquiv.symm_apply_apply,
      quasiLocalObservable_localInclusion]
    exact embeddedEvenSupportAlgebra_le_supportAlgebraJoin hω x
      (StarSubalgebra.mem_map.mpr ⟨a, ha, rfl⟩)
  have hright : (oddSupportAlgebra hω x).map
      (Matrix.rightKroneckerEmbed (m := Config d (leftPair x))) ≤
      (supportAlgebraJoin hω).comap φ := by
    rw [StarSubalgebra.map_le_iff_le_comap]
    intro a ha
    rw [StarSubalgebra.mem_comap, StarSubalgebra.mem_comap]
    have hinc : bipartiteLocalAlgebraEquiv hΓΔ
        (localInclusion (d := d) Finset.subset_union_right (CStarMatrix.ofMatrix a)) =
        Matrix.rightKroneckerEmbed (m := Config d (leftPair x)) a :=
      bipartiteLocalAlgebraEquiv_localInclusion_right hΓΔ (CStarMatrix.ofMatrix a)
    change φ (Matrix.rightKroneckerEmbed (m := Config d (leftPair x)) a) ∈
      supportAlgebraJoin hω
    rw [hφ_apply, ← hinc, StarAlgEquiv.symm_apply_apply,
      quasiLocalObservable_localInclusion]
    exact embeddedOddSupportAlgebra_le_supportAlgebraJoin hω x
      (StarSubalgebra.mem_map.mpr ⟨a, ha, rfl⟩)
  have hφX : φ X = ω (quasiLocalObservable d (evenPair x) A) := by
    rw [hφ_apply, hX, StarAlgEquiv.symm_apply_apply, hb]
    exact quasiLocalObservable_transport_localRestriction hω htarget A
  rw [← hφX]
  exact sup_le hleft hright hXjoin

/-- Every image of an algebraic local observable under the automorphism lies in the join of the
support algebras.

The pair algebras generate the algebraic local algebra, and the previous containment covers each
pair.

Source context: GNVW, arXiv:0910.3675v2, lines 1276--1279: the support algebras together generate
an algebra containing the image of every local observable. -/
theorem algebraicToQuasiLocal_mem_supportAlgebraJoin
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (A : AlgebraicLocalAlgebra d) :
    ω (algebraicToQuasiLocal d A) ∈ supportAlgebraJoin hω := by
  have hle : (⨆ x : ℤ, (localObservable d (evenPair x)).range) ≤
      (supportAlgebraJoin hω).comap
        (ω.toStarAlgHom.comp (algebraicToQuasiLocal d)) := by
    refine iSup_le fun x ↦ ?_
    rintro _ ⟨a, rfl⟩
    exact quasiLocalObservable_evenPair_mem_supportAlgebraJoin hω x a
  exact hle (by rw [iSup_range_localObservable_evenPair]; exact StarSubalgebra.mem_top)

/-- Norm-closed generation: the site-indexed support algebras generate the quasi-local algebra
after taking the norm closure.

The algebraic local observables are norm dense, their images under \(\omega\) lie in the join, and
\(\omega\) is a surjective isometry, so the closure of the join is everything.

The generation claim of GNVW, arXiv:0910.3675v2, lines 1276--1279, is read here in the
norm-closed sense: the algebras \(\mathcal R_y\) are finite-dimensional, so their algebraic join
cannot contain the norm completion, while the algebra it generates in the quasi-local sense is
the whole chain algebra. See the homogeneous-chain scope statement in the module docstring. -/
theorem supportAlgebraJoin_topologicalClosure_eq_top
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    (supportAlgebraJoin hω).topologicalClosure = ⊤ := by
  have hcont : Continuous (ω : QuasiLocalAlgebra d → QuasiLocalAlgebra d) :=
    (NonUnitalStarAlgHom.isometry ω.toStarAlgHom ω.injective).continuous
  have hclosed : IsClosed
      ((ω : QuasiLocalAlgebra d → QuasiLocalAlgebra d) ⁻¹'
        closure ((supportAlgebraJoin hω : Set (QuasiLocalAlgebra d)))) :=
    isClosed_closure.preimage hcont
  have hsub : Set.range (algebraicToQuasiLocal d) ⊆
      (ω : QuasiLocalAlgebra d → QuasiLocalAlgebra d) ⁻¹'
        closure ((supportAlgebraJoin hω : Set (QuasiLocalAlgebra d))) := by
    rintro _ ⟨A, rfl⟩
    exact subset_closure (algebraicToQuasiLocal_mem_supportAlgebraJoin hω A)
  have huniv : (Set.univ : Set (QuasiLocalAlgebra d)) ⊆
      (ω : QuasiLocalAlgebra d → QuasiLocalAlgebra d) ⁻¹'
        closure ((supportAlgebraJoin hω : Set (QuasiLocalAlgebra d))) := by
    rw [← (denseRange_algebraicToQuasiLocal d).closure_range]
    exact closure_minimal hsub hclosed
  refine SetLike.coe_injective ?_
  rw [StarSubalgebra.topologicalClosure_coe, StarSubalgebra.coe_top]
  refine Set.eq_univ_of_univ_subset fun z _ ↦ ?_
  simpa using huniv (Set.mem_univ (ω.symm z))

/-- Commutant corollary: an observable commuting with every site-indexed support algebra commutes
with the whole quasi-local algebra.

The elements commuting with a fixed observable and its adjoint form a closed star-subalgebra, so
it contains the norm closure of the join.

Source context: GNVW, arXiv:0910.3675v2, lines 1279--1282, pass from commutation with all
\(\mathcal R_y\) to commutation in the quasi-local algebra before invoking triviality of the
center. See the homogeneous-chain scope statement in the module docstring. -/
theorem commute_of_forall_commute_embeddedSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) {z : QuasiLocalAlgebra d}
    (hz : ∀ y : ℤ, ∀ r ∈ embeddedSupportAlgebra hω y, Commute z r)
    (a : QuasiLocalAlgebra d) : Commute z a := by
  have hle : supportAlgebraJoin hω ≤
      StarSubalgebra.centralizer ℂ ({z} : Set (QuasiLocalAlgebra d)) := by
    rw [supportAlgebraJoin]
    refine iSup_le fun y r hr ↦ ?_
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hstar : r * star g = star g * r := by
      have := congrArg star (hz y (star r) (star_mem hr)).eq
      simpa only [star_mul, star_star] using this
    exact ⟨(hz y r hr).eq, hstar.symm⟩
  have hclosed : IsClosed
      ((StarSubalgebra.centralizer ℂ ({z} : Set (QuasiLocalAlgebra d)) :
        Set (QuasiLocalAlgebra d))) := by
    rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hall := StarSubalgebra.topologicalClosure_minimal hle hclosed
  rw [supportAlgebraJoin_topologicalClosure_eq_top hω] at hall
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp
    (hall (StarSubalgebra.mem_top (x := a))) z rfl).1

end PropagatesWithin

end SpinChain

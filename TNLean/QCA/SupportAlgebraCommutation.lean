/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.DisjointSupport
import TNLean.QCA.OverlappingSupportAlgebra
import TNLean.QCA.SiteIndexedSupportAlgebra

/-!
# Commutation of site-indexed QCA support algebras

For a nearest-neighbour automorphism, the support algebras attached to distinct sites commute.
The only case not already covered by disjoint locality is the common physical pair
\(P_x=L_{x+1}\). For this pair, the two finite local images are included into the common
six-site region in canonical left--middle--right coordinates. Their images commute because the
source pairs are disjoint, and the support-algebra commutation lemma then applies.

**Scope restriction (homogeneous chain):** Gross--Nesme--Vogts--Werner allow the one-site
matrix size to depend on the site. This file treats the fixed positive size \(d\) of the present
quasi-local algebra. See
[the homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf).

## References

* Gross--Nesme--Vogts--Werner, arXiv:0910.3675v2, Lemma `sppcomm`, lines 1221--1246,
  and the consecutive/disjoint argument, lines 1270--1274.
* Schumacher--Werner, quant-ph/0405174, Lemma `sppcomm`, lines 1174--1194.
* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188, Appendix,
  lines 2313--2329.
-/

namespace SpinChain

/-! ### Canonical tripartite coordinates -/

/-- Configurations on three pairwise disjoint regions, in left--middle--right order. -/
def Config.disjointTripleEquiv {d : ℕ} {Λ Γ Δ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ) :
    Config d ((Λ ∪ Γ) ∪ Δ) ≃ (Config d Λ × Config d Γ) × Config d Δ :=
  (Config.disjointUnionEquiv hΛΓΔ).trans
    ((Config.disjointUnionEquiv hΛΓ).prodCongr (Equiv.refl (Config d Δ)))

/-- Local observables on three pairwise disjoint regions, in left--middle--right matrix
coordinates. -/
noncomputable def tripartiteLocalAlgebraEquiv {d : ℕ} {Λ Γ Δ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ) :
    LocalAlgebra d ((Λ ∪ Γ) ∪ Δ) ≃⋆ₐ[ℂ]
      Matrix ((Config d Λ × Config d Γ) × Config d Δ)
        ((Config d Λ × Config d Γ) × Config d Δ) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (Config.disjointTripleEquiv hΛΓ hΛΓΔ)).trans
    CStarMatrix.ofMatrixStarAlgEquiv.symm

/-- Equality on the complement of the last two regions is equality on the first region. -/
private lemma Config.restrict_sdiff_union_right_eq_iff {d : ℕ} {Λ Γ Δ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ)
    (u v : Config d ((Λ ∪ Γ) ∪ Δ)) :
    restrict (Finset.sdiff_subset : ((Λ ∪ Γ) ∪ Δ) \ (Γ ∪ Δ) ⊆ (Λ ∪ Γ) ∪ Δ) u =
        restrict Finset.sdiff_subset v ↔
      restrict (show Λ ⊆ (Λ ∪ Γ) ∪ Δ by simp) u =
        restrict (show Λ ⊆ (Λ ∪ Γ) ∪ Δ by simp) v := by
  constructor
  · intro h
    funext i
    have hiΓ : (i : ℤ) ∉ Γ := hΛΓ.notMem_of_mem_left_finset i.2
    have hiΔ : (i : ℤ) ∉ Δ := hΛΓΔ.notMem_of_mem_left_finset
      (Finset.mem_union_left Γ i.2)
    exact congrFun h ⟨i, Finset.mem_sdiff.mpr ⟨by simp [i.2], by simp [hiΓ, hiΔ]⟩⟩
  · intro h
    funext i
    have hiNot : (i : ℤ) ∉ Γ ∪ Δ := (Finset.mem_sdiff.mp i.2).2
    have hiAB : (i : ℤ) ∈ Λ ∪ Γ :=
      (Finset.mem_union.mp (Finset.mem_sdiff.mp i.2).1).resolve_right
        (fun hiΔ ↦ hiNot (Finset.mem_union_right Γ hiΔ))
    have hiΛ : (i : ℤ) ∈ Λ :=
      (Finset.mem_union.mp hiAB).resolve_right
        (fun hiΓ ↦ hiNot (Finset.mem_union_left Δ hiΓ))
    exact congrFun h ⟨i, hiΛ⟩

/-- Restriction of reconstructed tripartite coordinates to the first region recovers the left
coordinate. -/
@[simp]
private lemma Config.restrict_disjointTripleEquiv_symm_left {d : ℕ} {Λ Γ Δ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ)
    (x : (Config d Λ × Config d Γ) × Config d Δ) :
    restrict (show Λ ⊆ (Λ ∪ Γ) ∪ Δ by simp)
        ((disjointTripleEquiv hΛΓ hΛΓΔ).symm x) = x.1.1 := by
  calc
    _ = restrict (show Λ ⊆ Λ ∪ Γ by simp)
        (restrict (show Λ ∪ Γ ⊆ (Λ ∪ Γ) ∪ Δ from
          fun _ h ↦ Finset.mem_union_left Δ h)
          ((disjointTripleEquiv hΛΓ hΛΓΔ).symm x)) :=
      (restrict_trans (show Λ ⊆ Λ ∪ Γ by simp)
        (show Λ ∪ Γ ⊆ (Λ ∪ Γ) ∪ Δ from
          fun _ h ↦ Finset.mem_union_left Δ h) _).symm
    _ = x.1.1 := by simp [disjointTripleEquiv]

/-- Restriction of reconstructed tripartite coordinates to the last two regions recovers the
middle--right pair. -/
private lemma Config.restrict_disjointTripleEquiv_symm_right {d : ℕ} {Λ Γ Δ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ)
    (x : (Config d Λ × Config d Γ) × Config d Δ) :
    restrict (show Γ ∪ Δ ⊆ (Λ ∪ Γ) ∪ Δ by simp)
        ((disjointTripleEquiv hΛΓ hΛΓΔ).symm x) =
      (disjointUnionEquiv
        (hΛΓΔ.mono Finset.subset_union_right (fun _ h ↦ h))).symm (x.1.2, x.2) := by
  let hΓΔ : Disjoint Γ Δ :=
    hΛΓΔ.mono Finset.subset_union_right (fun _ h ↦ h)
  apply (disjointUnionEquiv hΓΔ).injective
  apply Prod.ext
  · simp only [disjointUnionEquiv_apply_fst,
      restrict_disjointUnionEquiv_symm_left]
    rw [restrict_trans]
    change restrict Finset.subset_union_right
        (restrict Finset.subset_union_left
          ((disjointTripleEquiv hΛΓ hΛΓΔ).symm x)) = x.1.2
    simp [disjointTripleEquiv]
  · simp only [disjointUnionEquiv_apply_snd,
      restrict_disjointUnionEquiv_symm_right]
    rw [restrict_trans]
    simp [disjointTripleEquiv]

/-- In canonical tripartite coordinates, inclusion from the first two regions is the natural
left overlapping lift. -/
theorem tripartiteLocalAlgebraEquiv_localInclusion_left {d : ℕ}
    {Λ Γ Δ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ)
    (A : LocalAlgebra d (Λ ∪ Γ)) :
    tripartiteLocalAlgebraEquiv hΛΓ hΛΓΔ
        (localInclusion (d := d) Finset.subset_union_left A) =
      Matrix.leftOverlappingLift (bipartiteLocalAlgebraEquiv hΛΓ A) := by
  ext x y
  change localInclusion (d := d) Finset.subset_union_left A
      ((Config.disjointTripleEquiv hΛΓ hΛΓΔ).symm x)
      ((Config.disjointTripleEquiv hΛΓ hΛΓΔ).symm y) = _
  rw [localInclusion_apply]
  simp only [Config.splitEquiv_snd_eq_iff_restrict_right hΛΓΔ]
  simp [Config.disjointTripleEquiv, Matrix.leftOverlappingLift,
    bipartiteLocalAlgebraEquiv_apply, Matrix.one_apply]

/-- In canonical tripartite coordinates, inclusion from the last two regions is the natural
right overlapping lift. -/
theorem tripartiteLocalAlgebraEquiv_localInclusion_right {d : ℕ}
    {Λ Γ Δ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) (hΛΓΔ : Disjoint (Λ ∪ Γ) Δ)
    (A : LocalAlgebra d (Γ ∪ Δ)) :
    tripartiteLocalAlgebraEquiv hΛΓ hΛΓΔ
        (localInclusion (d := d) (by intro i hi; simp only [Finset.mem_union] at hi ⊢; aesop) A) =
      Matrix.rightOverlappingLift (bipartiteLocalAlgebraEquiv
        (hΛΓΔ.mono Finset.subset_union_right (fun _ h ↦ h)) A) := by
  ext x y
  change localInclusion (d := d) _ A
      ((Config.disjointTripleEquiv hΛΓ hΛΓΔ).symm x)
      ((Config.disjointTripleEquiv hΛΓ hΛΓΔ).symm y) = _
  rw [localInclusion_apply]
  simp only [Config.splitEquiv_snd_eq_iff_restrict_sdiff]
  simp only [Config.restrict_sdiff_union_right_eq_iff hΛΓ hΛΓΔ]
  rw [Config.restrict_disjointTripleEquiv_symm_right hΛΓ hΛΓΔ x,
    Config.restrict_disjointTripleEquiv_symm_right hΛΓ hΛΓΔ y,
    Config.restrict_disjointTripleEquiv_symm_left hΛΓ hΛΓΔ x,
    Config.restrict_disjointTripleEquiv_symm_left hΛΓ hΛΓΔ y]
  simp [Matrix.rightOverlappingLift, bipartiteLocalAlgebraEquiv_apply,
    Matrix.one_apply]

/-! ### Consecutive finite images -/

/-- The source pairs for consecutive blocks are disjoint. -/
private lemma disjoint_evenPair_evenPair_add_one (x : ℤ) :
    Disjoint (evenPair x) (evenPair (x + 1)) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [evenPair, Finset.mem_insert, Finset.mem_singleton] at hi hj
  omega

/-- The three target pairs \(L_x,P_x,P_{x+1}\) are pairwise disjoint. -/
lemma disjoint_leftPair_union_rightPair_rightPair_add_one (x : ℤ) :
    Disjoint (leftPair x ∪ rightPair x) (rightPair (x + 1)) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  simp only [leftPair, rightPair, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton] at hi hj
  omega

/-- The common target of the two consecutive finite images is the six-site region displayed by
GNVW in the consecutive-pair argument. -/
lemma leftPair_union_rightPair_union_rightPair_add_one (x : ℤ) :
    (leftPair x ∪ rightPair x) ∪ rightPair (x + 1) =
      {2 * x - 1, 2 * x, 2 * x + 1, 2 * x + 2, 2 * x + 3, 2 * x + 4} := by
  ext i
  simp only [leftPair, rightPair, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  omega

namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- The defining finite-restriction equality after transporting along a target-region
identity. -/
private lemma quasiLocalObservable_transport_localRestriction
    {𝓝 Λ T : Finset ℤ} (hω : PropagatesWithin ω 𝓝)
    (hT : regionSumset Λ 𝓝 = T) (A : LocalAlgebra d Λ) :
    quasiLocalObservable d T (hT ▸ hω.localRestriction Λ A) =
      ω (quasiLocalObservable d Λ A) := by
  subst T
  exact hω.quasiLocalObservable_localRestriction Λ A

/-- Membership in a finite local image transported along its target-region equality. -/
private lemma mem_transport_localRestrictionRange_iff
    {𝓝 Λ T : Finset ℤ} (hω : PropagatesWithin ω 𝓝)
    (hT : regionSumset Λ 𝓝 = T) (A : LocalAlgebra d T) :
    A ∈ hT ▸ hω.localRestrictionRange Λ ↔
      ∃ A₀, A = hT ▸ hω.localRestriction Λ A₀ := by
  subst T
  change (∃ A₀, hω.localRestriction Λ A₀ = A) ↔
    ∃ A₀, A = hω.localRestriction Λ A₀
  constructor <;> rintro ⟨A₀, hA₀⟩
  · exact ⟨A₀, hA₀.symm⟩
  · exact ⟨A₀, hA₀.symm⟩

/-- Bipartite finite-image coordinates respect equality of the left finite region. -/
private lemma transport_bipartiteLocalRestrictionRange_left
    {𝓝 Λ Γ Γ' Δ : Finset ℤ} (hω : PropagatesWithin ω 𝓝) (q : Γ = Γ')
    (hΓΔ : Disjoint Γ Δ) (hΓ'Δ : Disjoint Γ' Δ)
    (hT : regionSumset Λ 𝓝 = Γ ∪ Δ) (hT' : regionSumset Λ 𝓝 = Γ' ∪ Δ) :
    q.symm ▸ hω.bipartiteLocalRestrictionRange Λ Γ' Δ hΓ'Δ hT' =
      hω.bipartiteLocalRestrictionRange Λ Γ Δ hΓΔ hT := by
  subst Γ'
  rfl

/-- The finite image of the next source pair, using the canonical equality
\(L_{x+1}=P_x\) so its left coordinate is literally the common physical pair. -/
private noncomputable def consecutiveEvenPairLocalImage
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ
      (Matrix (Config d (rightPair x) × Config d (rightPair (x + 1)))
        (Config d (rightPair x) × Config d (rightPair (x + 1))) ℂ) :=
  hω.bipartiteLocalRestrictionRange (evenPair (x + 1)) (rightPair x)
    (rightPair (x + 1))
    (by rw [rightPair_eq_leftPair_add_one]; exact disjoint_leftPair_rightPair (x + 1))
    (by rw [regionSumset_evenPair, ← rightPair_eq_leftPair_add_one x])

/-- Transporting the next block's canonical image along \(P_x=L_{x+1}\) gives the
consecutively aligned image. -/
private lemma transport_evenPairLocalImage_add_one
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (rightPair_eq_leftPair_add_one x).symm ▸ evenPairLocalImage hω (x + 1) =
      consecutiveEvenPairLocalImage hω x := by
  unfold evenPairLocalImage consecutiveEvenPairLocalImage
  apply transport_bipartiteLocalRestrictionRange_left hω
    (rightPair_eq_leftPair_add_one x)

section

set_option maxHeartbeats 800000

/-- The canonical lifts of two consecutive finite images commute in the common six-site
left--middle--right coordinates.

This is the disjoint-source step in GNVW, arXiv:0910.3675v2, lines 1270--1274. -/
private theorem evenPairLocalImages_overlappingLifts_commute
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∀ ⦃X⦄, X ∈ evenPairLocalImage hω x →
      ∀ ⦃Y⦄, Y ∈ consecutiveEvenPairLocalImage hω x →
        Matrix.leftOverlappingLift X * Matrix.rightOverlappingLift Y =
          Matrix.rightOverlappingLift Y * Matrix.leftOverlappingLift X := by
  intro X hX Y hY
  rw [evenPairLocalImage, bipartiteLocalRestrictionRange,
    StarSubalgebra.bipartiteReindex, StarSubalgebra.mem_map] at hX
  rw [consecutiveEvenPairLocalImage, bipartiteLocalRestrictionRange,
    StarSubalgebra.bipartiteReindex, StarSubalgebra.mem_map] at hY
  rcases hX with ⟨A, hA, rfl⟩
  rcases hY with ⟨B, hB, rfl⟩
  rw [mem_transport_localRestrictionRange_iff hω (regionSumset_evenPair x)] at hA
  have hNextTarget : regionSumset (evenPair (x + 1)) (Finset.Icc (-1) 1) =
      rightPair x ∪ rightPair (x + 1) := by
    rw [regionSumset_evenPair, ← rightPair_eq_leftPair_add_one x]
  rw [mem_transport_localRestrictionRange_iff hω hNextTarget] at hB
  rcases hA with ⟨A₀, rfl⟩
  rcases hB with ⟨B₀, rfl⟩
  let hLP := disjoint_leftPair_rightPair x
  let hT := disjoint_leftPair_union_rightPair_rightPair_add_one x
  let hPR : Disjoint (rightPair x) (rightPair (x + 1)) :=
    hT.mono Finset.subset_union_right (fun _ h ↦ h)
  change Matrix.leftOverlappingLift
      (bipartiteLocalAlgebraEquiv hLP
        (regionSumset_evenPair x ▸ hω.localRestriction (evenPair x) A₀)) *
      Matrix.rightOverlappingLift
        (bipartiteLocalAlgebraEquiv hPR
          (hNextTarget ▸ hω.localRestriction (evenPair (x + 1)) B₀)) =
      Matrix.rightOverlappingLift
          (bipartiteLocalAlgebraEquiv hPR
            (hNextTarget ▸ hω.localRestriction (evenPair (x + 1)) B₀)) *
        Matrix.leftOverlappingLift
          (bipartiteLocalAlgebraEquiv hLP
            (regionSumset_evenPair x ▸ hω.localRestriction (evenPair x) A₀))
  have hLeft := tripartiteLocalAlgebraEquiv_localInclusion_left hLP hT
    (regionSumset_evenPair x ▸ hω.localRestriction (evenPair x) A₀)
  have hRight := tripartiteLocalAlgebraEquiv_localInclusion_right hLP hT
    (hNextTarget ▸ hω.localRestriction (evenPair (x + 1)) B₀)
  rw [← hLeft, ← hRight]
  rw [← map_mul, ← map_mul]
  congr 1
  apply quasiLocalObservable_injective d ((leftPair x ∪ rightPair x) ∪ rightPair (x + 1))
  rw [map_mul, map_mul, quasiLocalObservable_localInclusion,
    quasiLocalObservable_localInclusion,
    quasiLocalObservable_transport_localRestriction hω (regionSumset_evenPair x),
    quasiLocalObservable_transport_localRestriction hω hNextTarget]
  rw [← map_mul, (quasiLocalObservable_commute_of_disjoint
    (disjoint_evenPair_evenPair_add_one x) A₀ B₀).eq, map_mul]

end

/-- Left support algebras respect equality of their left finite region. -/
private lemma transport_leftSupportAlgebra {d : ℕ} {Λ Γ Δ : Finset ℤ} (h : Λ = Γ)
    (S : StarSubalgebra ℂ
      (Matrix (Config d Γ × Config d Δ) (Config d Γ × Config d Δ) ℂ)) :
    h.symm ▸ Matrix.leftSupportAlgebra S =
      Matrix.leftSupportAlgebra (h.symm ▸ S) := by
  subst Γ
  rfl

/-- Membership in a matrix star-subalgebra transports along equality of the finite region. -/
private lemma matrix_mem_transport {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ = Γ)
    (S : StarSubalgebra ℂ (Matrix (Config d Γ) (Config d Γ) ℂ))
    {A : Matrix (Config d Γ) (Config d Γ) ℂ} (hA : A ∈ S) :
    h.symm ▸ A ∈ h.symm ▸ S := by
  subst Γ
  exact hA

/-- Canonical quasi-local matrix embeddings respect equality of their finite regions. -/
private lemma matrixToQuasiLocalObservable_transport {d : ℕ} [NeZero d]
    {Λ Γ : Finset ℤ} (h : Λ = Γ)
    (A : Matrix (Config d Γ) (Config d Γ) ℂ) :
    matrixToQuasiLocalObservable d Λ (h.symm ▸ A) =
      matrixToQuasiLocalObservable d Γ A := by
  subst Γ
  rfl

/-- Consecutive support algebras in the load-bearing odd--even order commute on their common
physical pair.

This applies Schumacher--Werner/GNVW Lemma `sppcomm` in the order
\(\operatorname{Spp}_{\mathrm R}(S_x),\operatorname{Spp}_{\mathrm L}(S_{x+1})\). -/
private theorem oddSupportAlgebra_commute_consecutiveLeftSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∀ R ∈ oddSupportAlgebra hω x,
      ∀ L ∈ Matrix.leftSupportAlgebra (consecutiveEvenPairLocalImage hω x),
        Commute R L := by
  intro R hR L hL
  rw [commute_iff_eq]
  exact Matrix.supportAlgebras_commute_of_overlappingLifts_commute
    (evenPairLocalImage hω x) (consecutiveEvenPairLocalImage hω x)
    (evenPairLocalImages_overlappingLifts_commute hω x) R hR L hL

/-- The two embedded support algebras in the unique overlapping odd--even configuration commute. -/
theorem embeddedOddSupportAlgebra_commute_embeddedEvenSupportAlgebra_add_one
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∀ X ∈ embeddedOddSupportAlgebra hω x,
      ∀ Y ∈ embeddedEvenSupportAlgebra hω (x + 1), Commute X Y := by
  intro X hX Y hY
  rw [embeddedOddSupportAlgebra, StarSubalgebra.mem_map] at hX
  rw [embeddedEvenSupportAlgebra, StarSubalgebra.mem_map] at hY
  rcases hX with ⟨R, hR, rfl⟩
  rcases hY with ⟨L, hL, rfl⟩
  let L' : Matrix (Config d (rightPair x)) (Config d (rightPair x)) ℂ :=
    (rightPair_eq_leftPair_add_one x).symm ▸ L
  have hLcast : (rightPair_eq_leftPair_add_one x).symm ▸ L ∈
      (rightPair_eq_leftPair_add_one x).symm ▸ evenSupportAlgebra hω (x + 1) :=
    matrix_mem_transport (rightPair_eq_leftPair_add_one x)
      (evenSupportAlgebra hω (x + 1)) hL
  rw [evenSupportAlgebra,
    transport_leftSupportAlgebra (rightPair_eq_leftPair_add_one x)] at hLcast
  have hL' : L' ∈ Matrix.leftSupportAlgebra (consecutiveEvenPairLocalImage hω x) := by
    change (rightPair_eq_leftPair_add_one x).symm ▸ L ∈ _
    rw [← transport_evenPairLocalImage_add_one hω x]
    exact hLcast
  have hComm := oddSupportAlgebra_commute_consecutiveLeftSupportAlgebra hω x R hR L' hL'
  rw [← matrixToQuasiLocalObservable_transport
    (rightPair_eq_leftPair_add_one x) L]
  exact hComm.map (matrixToQuasiLocalObservable d (rightPair x))

end PropagatesWithin

/-! ### Physical support regions and pairwise assembly -/

/-- The physical two-site region of the embedded support algebra \(\mathcal R_y\). -/
def supportRegion (y : ℤ) : Finset ℤ :=
  if y % 2 = 0 then leftPair (y / 2) else rightPair (y / 2)

@[simp]
lemma supportRegion_even (x : ℤ) : supportRegion (2 * x) = leftPair x := by
  simp [supportRegion]

@[simp]
lemma supportRegion_odd (x : ℤ) : supportRegion (2 * x + 1) = rightPair x := by
  rw [supportRegion]
  simp only [Int.mul_add_emod_self_left, Int.one_emod_two, one_ne_zero, ↓reduceIte]
  congr 1
  rw [show 2 * x + 1 = 1 + x * 2 by ring, Int.add_mul_ediv_right]
  all_goals norm_num

private lemma disjoint_leftPair_leftPair_of_ne {x z : ℤ} (h : x ≠ z) :
    Disjoint (leftPair x) (leftPair z) := by
  rw [Finset.disjoint_left]
  intro i hix hiz
  simp only [leftPair, Finset.mem_insert, Finset.mem_singleton] at hix hiz
  omega

private lemma disjoint_rightPair_rightPair_of_ne {x z : ℤ} (h : x ≠ z) :
    Disjoint (rightPair x) (rightPair z) := by
  rw [Finset.disjoint_left]
  intro i hix hiz
  simp only [rightPair, Finset.mem_insert, Finset.mem_singleton] at hix hiz
  omega

private lemma disjoint_leftPair_rightPair_of_ne_add_one {x z : ℤ} (h : x ≠ z + 1) :
    Disjoint (leftPair x) (rightPair z) := by
  rw [Finset.disjoint_left]
  intro i hix hiz
  simp only [leftPair, rightPair, Finset.mem_insert, Finset.mem_singleton] at hix hiz
  omega

private lemma disjoint_rightPair_leftPair_of_ne_add_one {x z : ℤ} (h : z ≠ x + 1) :
    Disjoint (rightPair x) (leftPair z) := by
  exact (disjoint_leftPair_rightPair_of_ne_add_one h).symm

namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- Every element of the site-indexed family is supported in its parity-selected physical
region. -/
theorem embeddedSupportAlgebra_supportedIn
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (y : ℤ)
    {R : QuasiLocalAlgebra d} (hR : R ∈ embeddedSupportAlgebra hω y) :
    QuasiLocalSupportedIn R (supportRegion y) := by
  by_cases hy : y % 2 = 0
  · have hrepl : y = 2 * (y / 2) := by
      have hdiv := Int.ediv_mul_add_emod y 2
      omega
    rw [hrepl, supportRegion_even]
    exact embeddedSupportAlgebra_even_supportedIn hω (y / 2) (hrepl ▸ hR)
  · have hmod : y % 2 = 1 := by
      have hnonneg := Int.emod_nonneg y (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 2)
      omega
    have hrepl : y = 2 * (y / 2) + 1 := by
      have hdiv := Int.ediv_mul_add_emod y 2
      omega
    rw [hrepl, supportRegion_odd]
    exact embeddedSupportAlgebra_odd_supportedIn hω (y / 2) (hrepl ▸ hR)

/-- For distinct indices, physical support regions are disjoint except for the consecutive
odd--even pair, in either order. -/
theorem supportRegion_disjoint_or_consecutive {y z : ℤ} (hyz : y ≠ z) :
    Disjoint (supportRegion y) (supportRegion z) ∨
      (∃ x, y = 2 * x + 1 ∧ z = 2 * x + 2) ∨
      ∃ x, z = 2 * x + 1 ∧ y = 2 * x + 2 := by
  by_cases hy : y % 2 = 0 <;> by_cases hz : z % 2 = 0
  · have hy' : y = 2 * (y / 2) := by
      have := Int.ediv_mul_add_emod y 2
      omega
    have hz' : z = 2 * (z / 2) := by
      have := Int.ediv_mul_add_emod z 2
      omega
    left
    rw [hy', hz', supportRegion_even, supportRegion_even]
    apply disjoint_leftPair_leftPair_of_ne
    omega
  · have hy' : y = 2 * (y / 2) := by
      have := Int.ediv_mul_add_emod y 2
      omega
    have hzmod : z % 2 = 1 := by
      have hnonneg := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
      omega
    have hz' : z = 2 * (z / 2) + 1 := by
      have := Int.ediv_mul_add_emod z 2
      omega
    by_cases h : y / 2 = z / 2 + 1
    · right; right
      exact ⟨z / 2, hz', by omega⟩
    · left
      rw [hy', hz', supportRegion_even, supportRegion_odd]
      exact disjoint_leftPair_rightPair_of_ne_add_one h
  · have hymod : y % 2 = 1 := by
      have hnonneg := Int.emod_nonneg y (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 2)
      omega
    have hy' : y = 2 * (y / 2) + 1 := by
      have := Int.ediv_mul_add_emod y 2
      omega
    have hz' : z = 2 * (z / 2) := by
      have := Int.ediv_mul_add_emod z 2
      omega
    by_cases h : z / 2 = y / 2 + 1
    · right; left
      exact ⟨y / 2, hy', by omega⟩
    · left
      rw [hy', hz', supportRegion_odd, supportRegion_even]
      exact disjoint_rightPair_leftPair_of_ne_add_one h
  · have hymod : y % 2 = 1 := by
      have hnonneg := Int.emod_nonneg y (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos y (by norm_num : (0 : ℤ) < 2)
      omega
    have hzmod : z % 2 = 1 := by
      have hnonneg := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
      omega
    have hy' : y = 2 * (y / 2) + 1 := by
      have := Int.ediv_mul_add_emod y 2
      omega
    have hz' : z = 2 * (z / 2) + 1 := by
      have := Int.ediv_mul_add_emod z 2
      omega
    left
    rw [hy', hz', supportRegion_odd, supportRegion_odd]
    apply disjoint_rightPair_rightPair_of_ne
    omega

/-- Distinct members of the site-indexed support-algebra family commute elementwise.

This is the homogeneous-chain specialization of the consecutive/disjoint commutation argument
in GNVW, arXiv:0910.3675v2, lines 1270--1274. -/
theorem embeddedSupportAlgebra_pairwise_commute
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    Pairwise fun y z : ℤ ↦
      ∀ X ∈ embeddedSupportAlgebra hω y,
        ∀ Y ∈ embeddedSupportAlgebra hω z, Commute X Y := by
  intro y z hyz X hX Y hY
  rcases supportRegion_disjoint_or_consecutive hyz with hdisj | hover | hover
  · exact (embeddedSupportAlgebra_supportedIn hω y hX).commute_of_disjoint
      (embeddedSupportAlgebra_supportedIn hω z hY) hdisj
  · rcases hover with ⟨x, rfl, rfl⟩
    rw [embeddedSupportAlgebra_odd] at hX
    rw [show 2 * x + 2 = 2 * (x + 1) by ring, embeddedSupportAlgebra_even] at hY
    exact embeddedOddSupportAlgebra_commute_embeddedEvenSupportAlgebra_add_one hω x X hX Y hY
  · rcases hover with ⟨x, rfl, rfl⟩
    rw [show 2 * x + 2 = 2 * (x + 1) by ring, embeddedSupportAlgebra_even] at hX
    rw [embeddedSupportAlgebra_odd] at hY
    exact (embeddedOddSupportAlgebra_commute_embeddedEvenSupportAlgebra_add_one
      hω x Y hY X hX).symm

end PropagatesWithin

end SpinChain

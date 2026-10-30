/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SupportAlgebraFactors
import TNLean.Algebra.CommutingStarSubalgebraProduct
import TNLean.Algebra.StarSubalgebraEquiv
import QICLean.Algebra.MatrixAlgHomCentralizer
import Mathlib.Data.Fintype.BigOperators

/-!
# Both adjacent-generation equalities and matrix-size identities

The actual image of each even-pair algebra equals the join of its two
support factors. The factors have already been proved to be full matrix
algebras, so their commuting join is a full matrix algebra. Its relative
commutant of the image is scalar by image-pair generation. The accepted
finite matrix relative-commutant theorem then forces surjectivity.
For the physical-pair equality, disjoint locality derives the scalar
relative commutant inside the physical pair instead. Both equalities give
their matrix-size identities for one coherent positive site-indexed family.

Source: GNVW, arXiv:0910.3675v2, equations AARReven and AARRodd,
source lines 1276--1318.

**Scope restriction (homogeneous chain):** The on-site matrix size is one
fixed positive integer; the source also permits site-dependent sizes.
See `docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
No translation-covariance hypothesis is used.
-/

open scoped Kronecker

namespace SpinChain
namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

private noncomputable def localAlgebraMatrixEquiv (Λ : Finset ℤ) :
    LocalAlgebra d Λ ≃⋆ₐ[ℂ]
      Matrix (Fin (Fintype.card (Config d Λ))) (Fin (Fintype.card (Config d Λ))) ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans
    (Matrix.matrixReindexStarAlgEquiv (Fintype.equivFin (Config d Λ)))

/-- The actual finite support algebra is identified with its faithful
quasi-local image without changing prescribed matrix coordinates.
Source: GNVW RR2x, lines 1251–1274. -/
noncomputable def supportEmbeddingEquiv (Λ : Finset ℤ)
    (S : StarSubalgebra ℂ (Matrix (Config d Λ) (Config d Λ) ℂ)) :
    ↥S ≃⋆ₐ[ℂ] ↥(S.map (matrixToQuasiLocalObservable d Λ)) :=
  S.equivMapOfInjective (matrixToQuasiLocalObservable d Λ)
    ((quasiLocalObservable_injective d Λ).comp CStarMatrix.ofMatrixStarAlgEquiv.injective)

/-- The prescribed presentations of the actual even and odd support
factors present their join, in that order. Source: GNVW AARReven,
lines 1276–1287; Schumacher–Werner bruleU, lines 980–1001. -/
noncomputable def adjacentSupportJoinMatrixEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    ↥(embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x)
      ≃⋆ₐ[ℂ] Matrix (Fin (r * s)) (Fin (r * s)) ℂ := by
  letI : Nontrivial (QuasiLocalAlgebra d) :=
    (quasiLocalObservable_injective d ∅).nontrivial
  let eE : ↥(embeddedEvenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ :=
    (supportEmbeddingEquiv (leftPair x) (evenSupportAlgebra hω x)).symm.trans eR
  let eO : ↥(embeddedOddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ :=
    (supportEmbeddingEquiv (rightPair x) (oddSupportAlgebra hω x)).symm.trans eS
  have hEO : ∀ a : embeddedEvenSupportAlgebra hω x,
      ∀ b : embeddedOddSupportAlgebra hω x,
      Commute (a : QuasiLocalAlgebra d) (b : QuasiLocalAlgebra d) := by
    intro a b
    exact embeddedSupportAlgebra_pairwise_commute hω
      (show 2 * x ≠ 2 * x + 1 by omega) a
      (by simpa only [embeddedSupportAlgebra_even] using a.2) b
      (by simpa only [embeddedSupportAlgebra_odd] using b.2)
  exact StarSubalgebra.commutingSupEquivMatrix _ _ hEO eE eO

/-- The even and odd support presentations send an actual product to the
Kronecker product of the prescribed factor coordinates.
Source: Schumacher–Werner, bruleU/bruleV, lines 980–1001. -/
theorem adjacentSupportJoinMatrixEquiv_apply_product
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ)
    (a : evenSupportAlgebra hω x) (b : oddSupportAlgebra hω x) :
    adjacentSupportJoinMatrixEquiv hω x eR eS
      ⟨matrixToQuasiLocalObservable d (leftPair x) a *
          matrixToQuasiLocalObservable d (rightPair x) b,
        (embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x).mul_mem
          ((le_sup_left : embeddedEvenSupportAlgebra hω x ≤
              embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x)
            (StarSubalgebra.mem_map.mpr ⟨a, a.2, rfl⟩))
          ((le_sup_right : embeddedOddSupportAlgebra hω x ≤
              embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x)
            (StarSubalgebra.mem_map.mpr ⟨b, b.2, rfl⟩))⟩ =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (eR a ⊗ₖ eS b) := by
  unfold adjacentSupportJoinMatrixEquiv
  rw [StarSubalgebra.commutingSupEquivMatrix_apply_mul]
  simp only [StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply]

/-- The join of the actual adjacent support factors is a full matrix
algebra of positive size. This derives its matrix presentation, rather
than assuming it; GNVW, arXiv:0910.3675v2, lines 1276--1282. -/
theorem exists_adjacentSupportJoin_matrix
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    ∃ (q : ℕ) (_ : NeZero q),
      Nonempty (↥(embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x)
        ≃⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ) := by
  obtain ⟨r, hr, ⟨eR⟩⟩ := exists_evenSupportAlgebra_matrix hω x
  obtain ⟨s, hs, ⟨eS⟩⟩ := exists_oddSupportAlgebra_matrix hω x
  let : NeZero r := hr
  let : NeZero s := hs
  exact ⟨r * s, inferInstance, ⟨adjacentSupportJoinMatrixEquiv hω x eR eS⟩⟩

/-- The actual image of the even-pair algebra equals the join of its two
adjacent support factors. The scalar relative commutant is derived from
global image-pair generation, and the finite matrix theorem forces the
inclusion to be onto. This is GNVW, arXiv:0910.3675v2, equation AARReven,
source lines 1276--1287, in the homogeneous-chain domain. -/
theorem range_image_evenPair_eq_adjacentSupportJoin
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (ω.toStarAlgHom.comp (quasiLocalObservable d (evenPair x))).range =
      embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x := by
  classical
  let J := embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x
  obtain ⟨q, hq, ⟨eJ⟩⟩ := exists_adjacentSupportJoin_matrix hω x
  let : NeZero q := hq
  let p := Fintype.card (Config d (evenPair x))
  let : NeZero p := inferInstance
  let eA : LocalAlgebra d (evenPair x) ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
    localAlgebraMatrixEquiv (evenPair x)
  let f := (ω.toStarAlgHom.comp (quasiLocalObservable d (evenPair x))).codRestrict J
    (quasiLocalObservable_evenPair_mem_adjacentSupportJoin hω x)
  let Φ := eJ.toStarAlgHom.comp (f.comp eA.symm.toStarAlgHom)
  have hcentral : Subalgebra.centralizer ℂ (Set.range Φ) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro T hT
    let z : J := eJ.symm T
    have hcomm (A : LocalAlgebra d (evenPair x)) :
        Commute (z : QuasiLocalAlgebra d)
          (ω (quasiLocalObservable d (evenPair x) A)) := by
      have hΦA : Φ (eA A) = eJ (f A) := by
        change eJ (f (eA.symm (eA A))) = eJ (f A)
        rw [StarAlgEquiv.symm_apply_apply]
      have hc := ((Subalgebra.mem_centralizer_iff ℂ).mp hT
        (Φ (eA A)) ⟨eA A, rfl⟩).symm
      rw [hΦA] at hc
      have hsub : z * f A = f A * z := by
        apply eJ.injective
        rw [map_mul, map_mul]
        change eJ (eJ.symm T) * eJ (f A) = eJ (f A) * eJ (eJ.symm T)
        rw [StarAlgEquiv.apply_symm_apply]
        exact hc
      exact congrArg Subtype.val hsub
    obtain ⟨c, hc, _⟩ :=
      existsUnique_eq_smul_one_of_mem_adjacentSupportJoin_commute_image hω x z z.2 hcomm
    have hz : z = c • (1 : J) := Subtype.ext hc
    have hTc : T = c • (1 : Matrix (Fin q) (Fin q) ℂ) := by
      simpa only [z, StarAlgEquiv.apply_symm_apply, map_smul, map_one] using congrArg eJ hz
    rw [Algebra.mem_bot]
    exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hTc.symm⟩
  have hΦ := Matrix.StarAlgHom.surjective_of_centralizer_range_eq_bot Φ hcentral
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨M, hM⟩ := hΦ (eJ z)
    exact ⟨eA.symm M, eJ.injective hM⟩
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact quasiLocalObservable_evenPair_mem_adjacentSupportJoin hω x A
  · intro z hz
    obtain ⟨A, hA⟩ := hf ⟨z, hz⟩
    exact ⟨A, congrArg Subtype.val hA⟩

/-- The matrix sizes of the two actual support factors of an image pair
multiply to the physical pair size. The matrix sizes are specified by
star-algebra presentations, and are not vector-space dimensions; GNVW,
arXiv:0910.3675v2, lines 1287--1290, immediately after AARReven. -/
theorem evenSupportAlgebra_matrixSize_mul_odd
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    r * s = d * d := by
  classical
  let eJ := adjacentSupportJoinMatrixEquiv hω x eR eS
  let f := ω.toStarAlgHom.comp (quasiLocalObservable d (evenPair x))
  let eImage : LocalAlgebra d (evenPair x) ≃⋆ₐ[ℂ]
      ↥(embeddedEvenSupportAlgebra hω x ⊔ embeddedOddSupportAlgebra hω x) := by
    rw [← range_image_evenPair_eq_adjacentSupportJoin hω x]
    exact StarAlgEquiv.ofInjective f
      (ω.injective.comp (quasiLocalObservable_injective d (evenPair x)))
  let eA : LocalAlgebra d (evenPair x) ≃⋆ₐ[ℂ]
      Matrix (Fin (Fintype.card (Config d (evenPair x))))
        (Fin (Fintype.card (Config d (evenPair x)))) ℂ :=
    localAlgebraMatrixEquiv (evenPair x)
  have hsize : Fintype.card (Config d (evenPair x)) = r * s :=
    Matrix.matrixAlgEquiv_fin_eq (eA.symm.trans (eImage.trans eJ)).toAlgEquiv
  have hcard : Fintype.card (Config d (evenPair x)) = d * d := by
    change Fintype.card (↥(evenPair x) → Fin d) = d * d
    rw [Fintype.card_fun, Fintype.card_coe]
    have hne : 2 * x ≠ 2 * x + 1 := by omega
    simp [evenPair, hne, pow_two]
  exact hsize.symm.trans hcard

/-- A coherent positive site-indexed matrix-size family satisfies the
first source size identity, with no presentation or size assertion supplied
as a premise. Source: GNVW, arXiv:0910.3675v2, lines 1287--1290. -/
theorem exists_supportAlgebra_matrixSizes_even_mul
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    ∃ r : ℤ → ℕ, (∀ y, NeZero (r y)) ∧
      (∀ x, Nonempty (↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x))) (Fin (r (2 * x))) ℂ)) ∧
      (∀ x, Nonempty (↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x + 1))) (Fin (r (2 * x + 1))) ℂ)) ∧
      (∀ x, r (2 * x) * r (2 * x + 1) = d * d) := by
  obtain ⟨r, hr, eE, eO⟩ := exists_supportAlgebra_matrixSizes hω
  refine ⟨r, hr, eE, eO, ?_⟩
  intro x
  let : NeZero (r (2 * x)) := hr (2 * x)
  let : NeZero (r (2 * x + 1)) := hr (2 * x + 1)
  obtain ⟨eR⟩ := eE x
  obtain ⟨eS⟩ := eO x
  exact evenSupportAlgebra_matrixSize_mul_odd hω x eR eS

/-- The prescribed presentations of the actual odd factor and next
even factor present their join on a physical pair, in that order.
Source: GNVW AARRodd, lines 1306–1315; Schumacher–Werner bruleV. -/
noncomputable def physicalPairSupportJoinMatrixEquiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(evenSupportAlgebra hω (x + 1)) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    ↥(embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1))
      ≃⋆ₐ[ℂ] Matrix (Fin (r * s)) (Fin (r * s)) ℂ := by
  letI : Nontrivial (QuasiLocalAlgebra d) :=
    (quasiLocalObservable_injective d ∅).nontrivial
  let eO := (supportEmbeddingEquiv (rightPair x) (oddSupportAlgebra hω x)).symm.trans eR
  let eE := (supportEmbeddingEquiv (leftPair (x + 1))
    (evenSupportAlgebra hω (x + 1))).symm.trans eS
  have hOE : ∀ a : embeddedOddSupportAlgebra hω x,
      ∀ b : embeddedEvenSupportAlgebra hω (x + 1),
      Commute (a : QuasiLocalAlgebra d) (b : QuasiLocalAlgebra d) := by
    intro a b
    exact embeddedSupportAlgebra_pairwise_commute hω
      (show 2 * x + 1 ≠ 2 * (x + 1) by omega) a
      (by simpa only [embeddedSupportAlgebra_odd] using a.2) b
      (by simpa only [embeddedSupportAlgebra_even] using b.2)
  exact StarSubalgebra.commutingSupEquivMatrix _ _ hOE eO eE

/-- The odd and next even support presentations send an actual product to the
Kronecker product of the prescribed factor coordinates.
Source: Schumacher–Werner, bruleU/bruleV, lines 980–1001. -/
theorem physicalPairSupportJoinMatrixEquiv_apply_product
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(evenSupportAlgebra hω (x + 1)) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ)
    (a : oddSupportAlgebra hω x) (b : evenSupportAlgebra hω (x + 1)) :
    physicalPairSupportJoinMatrixEquiv hω x eR eS
      ⟨matrixToQuasiLocalObservable d (rightPair x) a *
          matrixToQuasiLocalObservable d (leftPair (x + 1)) b,
        (embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1)).mul_mem
          ((le_sup_left : embeddedOddSupportAlgebra hω x ≤
              embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1))
            (StarSubalgebra.mem_map.mpr ⟨a, a.2, rfl⟩))
          ((le_sup_right : embeddedEvenSupportAlgebra hω (x + 1) ≤
              embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1))
            (StarSubalgebra.mem_map.mpr ⟨b, b.2, rfl⟩))⟩ =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (eR a ⊗ₖ eS b) := by
  unfold physicalPairSupportJoinMatrixEquiv
  rw [StarSubalgebra.commutingSupEquivMatrix_apply_mul]
  simp only [StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply]

/-- A physical-pair observable commuting with its two support factors is
scalar. All other support factors are disjoint from the pair; global
support generation then applies. This is the second strict-inclusion
argument of GNVW, arXiv:0910.3675v2, equation AARRodd, lines 1306--1315. -/
theorem existsUnique_eq_smul_one_of_supported_rightPair_commute_supports
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    (z : QuasiLocalAlgebra d) (hz : QuasiLocalSupportedIn z (rightPair x))
    (hO : ∀ r ∈ embeddedOddSupportAlgebra hω x, Commute z r)
    (hE : ∀ r ∈ embeddedEvenSupportAlgebra hω (x + 1), Commute z r) :
    ∃! c : ℂ, z = c • (1 : QuasiLocalAlgebra d) := by
  apply existsUnique_eq_smul_one_of_commute z
  intro a
  apply commute_of_forall_commute_embeddedSupportAlgebra hω
  intro y r hr
  by_cases hyO : y = 2 * x + 1
  · subst y
    exact hO r (by simpa only [embeddedSupportAlgebra_odd] using hr)
  by_cases hyE : y = 2 * (x + 1)
  · subst y
    exact hE r (by simpa only [embeddedSupportAlgebra_even] using hr)
  have hdisj : Disjoint (rightPair x) (supportRegion y) := by
    rcases supportRegion_disjoint_or_consecutive (Ne.symm hyO) with
      h | ⟨u, hu, huy⟩ | ⟨u, huy, hu⟩
    · simpa only [supportRegion_odd] using h
    · omega
    · omega
  exact hz.commute_of_disjoint (embeddedSupportAlgebra_supportedIn hω y hr) hdisj

/-- The two support factors on a physical pair generate its entire
observable algebra. Their scalar relative commutant is derived using
disjoint locality and global support generation, so strict inclusion is
excluded by the accepted finite matrix theorem. This is GNVW,
arXiv:0910.3675v2, equation AARRodd, source lines 1306--1315. -/
theorem adjacentSupportJoin_eq_range_rightPair
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1) =
      (quasiLocalObservable d (rightPair x)).range := by
  classical
  let J := embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1)
  let P := (quasiLocalObservable d (rightPair x)).range
  have hJP : J ≤ P := by
    apply sup_le
    · intro z hz
      exact embeddedSupportAlgebra_odd_supportedIn hω x
        (by simpa only [embeddedSupportAlgebra_odd] using hz)
    · intro z hz
      have hs := embeddedSupportAlgebra_even_supportedIn hω (x + 1)
        (by simpa only [embeddedSupportAlgebra_even] using hz)
      rw [← rightPair_eq_leftPair_add_one x] at hs
      exact hs
  obtain ⟨r, hr, ⟨eR⟩⟩ := exists_oddSupportAlgebra_matrix hω x
  obtain ⟨s, hs, ⟨eS⟩⟩ := exists_evenSupportAlgebra_matrix hω (x + 1)
  let : NeZero r := hr
  let : NeZero s := hs
  let eJ := physicalPairSupportJoinMatrixEquiv hω x eR eS
  let eP := StarAlgEquiv.ofInjective (quasiLocalObservable d (rightPair x))
    (quasiLocalObservable_injective d (rightPair x))
  let p := Fintype.card (Config d (rightPair x))
  let : NeZero p := inferInstance
  let eA : LocalAlgebra d (rightPair x) ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
    localAlgebraMatrixEquiv (rightPair x)
  let eAmbient : ↥P ≃⋆ₐ[ℂ] Matrix (Fin p) (Fin p) ℂ := eP.symm.trans eA
  let j := J.subtype.codRestrict P (fun z ↦ hJP z.2)
  let Φ := eAmbient.toStarAlgHom.comp (j.comp eJ.symm.toStarAlgHom)
  have hcentral : Subalgebra.centralizer ℂ (Set.range Φ) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro T hT
    let z : P := eAmbient.symm T
    have hcomm (w : J) : Commute (z : QuasiLocalAlgebra d) (w : QuasiLocalAlgebra d) := by
      have hΦw : Φ (eJ w) = eAmbient (j w) := by
        change eAmbient (j (eJ.symm (eJ w))) = eAmbient (j w)
        rw [StarAlgEquiv.symm_apply_apply]
      have hc := ((Subalgebra.mem_centralizer_iff ℂ).mp hT
        (Φ (eJ w)) ⟨eJ w, rfl⟩).symm
      rw [hΦw] at hc
      have hsub : z * j w = j w * z := by
        apply eAmbient.injective
        rw [map_mul, map_mul]
        change eAmbient (eAmbient.symm T) * eAmbient (j w) =
          eAmbient (j w) * eAmbient (eAmbient.symm T)
        rw [StarAlgEquiv.apply_symm_apply]
        exact hc
      exact congrArg Subtype.val hsub
    obtain ⟨c, hc, _⟩ :=
      existsUnique_eq_smul_one_of_supported_rightPair_commute_supports hω x z z.2
        (fun w hw ↦ hcomm ⟨w, (show embeddedOddSupportAlgebra hω x ≤ J from le_sup_left) hw⟩)
        (fun w hw ↦ hcomm ⟨w, (show embeddedEvenSupportAlgebra hω (x + 1) ≤ J
          from le_sup_right) hw⟩)
    have hz : z = c • (1 : P) := Subtype.ext hc
    have hTc : T = c • (1 : Matrix (Fin p) (Fin p) ℂ) := by
      simpa only [z, StarAlgEquiv.apply_symm_apply, map_smul, map_one]
        using congrArg eAmbient hz
    rw [Algebra.mem_bot]
    exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hTc.symm⟩
  have hΦ := Matrix.StarAlgHom.surjective_of_centralizer_range_eq_bot Φ hcentral
  have hj : Function.Surjective j := by
    intro z
    obtain ⟨M, hM⟩ := hΦ (eAmbient z)
    exact ⟨eJ.symm M, eAmbient.injective hM⟩
  apply le_antisymm hJP
  intro z hz
  obtain ⟨w, hw⟩ := hj ⟨z, hz⟩
  have hval : (w : QuasiLocalAlgebra d) = z := congrArg Subtype.val hw
  exact hval ▸ w.2

/-- The matrix sizes of the two support factors on the same physical
pair multiply to its physical matrix size. This is the second size
identity in GNVW, arXiv:0910.3675v2, following AARRodd, lines 1314--1318. -/
theorem oddSupportAlgebra_matrixSize_mul_even_add_one
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r s : ℕ} [NeZero r] [NeZero s]
    (eR : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (eS : ↥(evenSupportAlgebra hω (x + 1)) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    r * s = d * d := by
  classical
  let eJ := physicalPairSupportJoinMatrixEquiv hω x eR eS
  let eImage : LocalAlgebra d (rightPair x) ≃⋆ₐ[ℂ]
      ↥(embeddedOddSupportAlgebra hω x ⊔ embeddedEvenSupportAlgebra hω (x + 1)) := by
    rw [adjacentSupportJoin_eq_range_rightPair hω x]
    exact StarAlgEquiv.ofInjective (quasiLocalObservable d (rightPair x))
      (quasiLocalObservable_injective d (rightPair x))
  have hsize : Fintype.card (Config d (rightPair x)) = r * s :=
    Matrix.matrixAlgEquiv_fin_eq
      ((localAlgebraMatrixEquiv (rightPair x)).symm.trans (eImage.trans eJ)).toAlgEquiv
  have hcard : Fintype.card (Config d (rightPair x)) = d * d := by
    change Fintype.card (↥(rightPair x) → Fin d) = d * d
    rw [Fintype.card_fun, Fintype.card_coe]
    have hne : 2 * x + 1 ≠ 2 * x + 2 := by omega
    simp [rightPair, hne, pow_two]
  exact hsize.symm.trans hcard

/-- The actual homogeneous support factors admit one coherent positive
matrix-size family satisfying both source size identities. The factor
presentations and identities are derived from the nearest-neighbour
automorphism alone. Source: GNVW, arXiv:0910.3675v2, equations AARReven
and AARRodd with their size consequences, lines 1276--1318. -/
theorem exists_supportAlgebra_matrixSizes_mul
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    ∃ r : ℤ → ℕ, (∀ y, NeZero (r y)) ∧
      (∀ x, Nonempty (↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x))) (Fin (r (2 * x))) ℂ)) ∧
      (∀ x, Nonempty (↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (r (2 * x + 1))) (Fin (r (2 * x + 1))) ℂ)) ∧
      (∀ x, r (2 * x) * r (2 * x + 1) = d * d) ∧
      (∀ x, r (2 * x + 1) * r (2 * x + 2) = d * d) := by
  obtain ⟨r, hr, eE, eO, hEven⟩ := exists_supportAlgebra_matrixSizes_even_mul hω
  refine ⟨r, hr, eE, eO, hEven, ?_⟩
  intro x
  let : NeZero (r (2 * x + 1)) := hr (2 * x + 1)
  let : NeZero (r (2 * x + 2)) := hr (2 * x + 2)
  obtain ⟨eR⟩ := eO x
  have he := eE (x + 1)
  rw [show 2 * (x + 1) = 2 * x + 2 by ring] at he
  obtain ⟨eS⟩ := he
  exact oddSupportAlgebra_matrixSize_mul_even_add_one hω x eR eS

end PropagatesWithin
end SpinChain

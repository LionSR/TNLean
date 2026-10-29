/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SupportAlgebraFactors
import TNLean.Algebra.CommutingStarSubalgebraProduct
import QICLean.Algebra.MatrixAlgHomCentralizer

/-!
# Generation by the two support factors of an image pair

The actual image of each even-pair algebra equals the join of its two
support factors. The factors have already been proved to be full matrix
algebras, so their commuting join is a full matrix algebra. Its relative
commutant of the image is scalar by image-pair generation. The accepted
finite matrix relative-commutant theorem then forces surjectivity.

Source: GNVW, arXiv:0910.3675v2, equation AARReven, source lines 1276--1287.

**Scope restriction (homogeneous chain):** The on-site matrix size is one
fixed positive integer; the source also permits site-dependent sizes.
See `docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
No translation-covariance hypothesis is used.
-/

namespace SpinChain
namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

private noncomputable def supportEmbeddingEquiv (Λ : Finset ℤ)
    (S : StarSubalgebra ℂ (Matrix (Config d Λ) (Config d Λ) ℂ)) :
    ↥S ≃⋆ₐ[ℂ] ↥(S.map (matrixToQuasiLocalObservable d Λ)) := by
  let f := matrixToQuasiLocalObservable d Λ
  let g := (f.comp S.subtype).codRestrict (S.map f)
    (fun x ↦ StarSubalgebra.mem_map.mpr ⟨x, x.2, rfl⟩)
  apply StarAlgEquiv.ofBijective g
  constructor
  · intro x y h
    apply Subtype.ext
    exact ((quasiLocalObservable_injective d Λ).comp
      CStarMatrix.ofMatrixStarAlgEquiv.injective) (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    obtain ⟨a, ha, rfl⟩ := StarSubalgebra.mem_map.mp hz
    exact ⟨⟨a, ha⟩, rfl⟩

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
  exact ⟨r * s, inferInstance,
    ⟨StarSubalgebra.commutingSupEquivMatrix _ _ hEO eE eO⟩⟩

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
    CStarMatrix.ofMatrixStarAlgEquiv.symm.trans
      (Matrix.matrixReindexStarAlgEquiv (Fintype.equivFin (Config d (evenPair x))))
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
        simp only [Φ, StarAlgHom.comp_apply, StarAlgEquiv.symm_apply_apply]
      have hc := ((Subalgebra.mem_centralizer_iff ℂ).mp hT
        (Φ (eA A)) ⟨eA A, rfl⟩).symm
      rw [hΦA] at hc
      have hsub : z * f A = f A * z := by
        apply eJ.injective
        simpa only [map_mul, z, StarAlgEquiv.apply_symm_apply] using hc
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

end PropagatesWithin
end SpinChain

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixKroneckerEmbed
import TNLean.QCA.LocalAlgebra

/-!
# Bipartite coordinates for finite-region observable algebras

For disjoint finite regions \(\Lambda\) and \(\Gamma\), restriction to the two regions identifies
configurations on \(\Lambda\cup\Gamma\) with pairs of configurations. Reindexing rows and columns
along this identification gives a star-algebra equivalence
\[
  \mathcal A_{\Lambda\cup\Gamma}\simeq
  M_{\operatorname{Config}(\Lambda)\times\operatorname{Config}(\Gamma)}(\mathbb C).
\]
The canonical inclusions from the two regions become the left and right Kronecker embeddings in
this order. This is the finite-dimensional coordinate boundary used before applying matrix support
algebras; no support algebra is defined here.

## Main definitions

* `SpinChain.Config.disjointUnionEquiv` — configurations on a disjoint union as pairs.
* `SpinChain.bipartiteLocalAlgebraEquiv` — the associated matrix star-algebra equivalence.
* `SpinChain.StarSubalgebra.bipartiteReindex` — a local star-subalgebra in the resulting fixed
  left/right matrix coordinates.

## Main results

* `SpinChain.bipartiteLocalAlgebraEquiv_localInclusion_left` — the left local inclusion is
  \(A\mapsto A\otimes 1\).
* `SpinChain.bipartiteLocalAlgebraEquiv_localInclusion_right` — the right local inclusion is
  \(B\mapsto 1\otimes B\).

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2298.
* Schumacher--Werner, quant-ph/0405174, lines 270--293 and Definition 1.
* Gross--Nesme--Vogts--Werner, arXiv:0910.3675v2, lines 1249--1266.
-/

open scoped Kronecker

namespace SpinChain

namespace Config

/-- The complementary sites of the left region in a disjoint union are the sites of the right
region.

Source context: this is the site identification underlying GNVW, arXiv:0910.3675v2,
equation `RR2x`, lines 1249--1266. -/
private def leftComplementSiteEquiv {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    ↥((Λ ∪ Γ) \ Λ) ≃ ↥Γ where
  toFun i := ⟨i, (Finset.mem_union.mp (Finset.mem_sdiff.mp i.2).1).resolve_left
    (Finset.mem_sdiff.mp i.2).2⟩
  invFun i := ⟨i, Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_right Λ i.2, hΛΓ.notMem_of_mem_right_finset i.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexing complementary configurations from the left split by the right-region sites.

Source context: this is the configuration identification underlying GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
private def leftComplementEquiv (d : ℕ) {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    Config d ((Λ ∪ Γ) \ Λ) ≃ Config d Γ :=
  (leftComplementSiteEquiv hΛΓ).arrowCongr (Equiv.refl (Fin d))

/-- The complementary sites of the right region in a disjoint union are the sites of the left
region.

Source context: this is the site identification underlying GNVW, arXiv:0910.3675v2,
equation `RR2x`, lines 1249--1266. -/
private def rightComplementSiteEquiv {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    ↥((Λ ∪ Γ) \ Γ) ≃ ↥Λ where
  toFun i := ⟨i, (Finset.mem_union.mp (Finset.mem_sdiff.mp i.2).1).resolve_right
    (Finset.mem_sdiff.mp i.2).2⟩
  invFun i := ⟨i, Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_left Γ i.2, hΛΓ.notMem_of_mem_left_finset i.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexing complementary configurations from the right split by the left-region sites.

Source context: this is the configuration identification underlying GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
private def rightComplementEquiv (d : ℕ) {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    Config d ((Λ ∪ Γ) \ Γ) ≃ Config d Λ :=
  (rightComplementSiteEquiv hΛΓ).arrowCongr (Equiv.refl (Fin d))

/-- Reindexing restriction to the left complement agrees with restriction to the right region.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
private lemma leftComplementEquiv_restrict {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x : Config d (Λ ∪ Γ)) :
    leftComplementEquiv d hΛΓ
        (restrict (Finset.sdiff_subset : (Λ ∪ Γ) \ Λ ⊆ Λ ∪ Γ) x) =
      restrict Finset.subset_union_right x := by
  funext i
  rfl

/-- Reindexing restriction to the right complement agrees with restriction to the left region.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
private lemma rightComplementEquiv_restrict {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x : Config d (Λ ∪ Γ)) :
    rightComplementEquiv d hΛΓ
        (restrict (Finset.sdiff_subset : (Λ ∪ Γ) \ Γ ⊆ Λ ∪ Γ) x) =
      restrict Finset.subset_union_left x := by
  funext i
  rfl

/-- Splitting configurations on a union of disjoint regions into the two restrictions.

The first component is the configuration on `Λ` and the second is the configuration on `Γ`.
Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
def disjointUnionEquiv {d : ℕ} {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ) :
    Config d (Λ ∪ Γ) ≃ Config d Λ × Config d Γ :=
  (splitEquiv (d := d) (Finset.subset_union_left : Λ ⊆ Λ ∪ Γ)).trans
    ((Equiv.refl (Config d Λ)).prodCongr (leftComplementEquiv d hΛΓ))

/-- The first component of the disjoint-union equivalence is restriction to the left region.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
lemma disjointUnionEquiv_apply_fst {d : ℕ} {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ)
    (x : Config d (Λ ∪ Γ)) :
    (disjointUnionEquiv hΛΓ x).1 = restrict Finset.subset_union_left x :=
  rfl

/-- The second component of the disjoint-union equivalence is restriction to the right region.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
lemma disjointUnionEquiv_apply_snd {d : ℕ} {Λ Γ : Finset ℤ} (hΛΓ : Disjoint Λ Γ)
    (x : Config d (Λ ∪ Γ)) :
    (disjointUnionEquiv hΛΓ x).2 = restrict Finset.subset_union_right x := by
  exact leftComplementEquiv_restrict hΛΓ x

/-- Restricting a reconstructed pair to the left region recovers its first component.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
lemma restrict_disjointUnionEquiv_symm_left {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x : Config d Λ × Config d Γ) :
    restrict Finset.subset_union_left ((disjointUnionEquiv hΛΓ).symm x) = x.1 :=
  by simpa only [disjointUnionEquiv_apply_fst] using
    congrArg Prod.fst ((disjointUnionEquiv hΛΓ).apply_symm_apply x)

/-- Restricting a reconstructed pair to the right region recovers its second component.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
lemma restrict_disjointUnionEquiv_symm_right {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x : Config d Λ × Config d Γ) :
    restrict Finset.subset_union_right ((disjointUnionEquiv hΛΓ).symm x) = x.2 :=
  by simpa only [disjointUnionEquiv_apply_snd] using
    congrArg Prod.snd ((disjointUnionEquiv hΛΓ).apply_symm_apply x)

/-- Equality of the complementary coordinates for the left split is equality after restriction to
the right region.

Source context: this coordinate identity underlies the left tensor factor in GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266; it is not stated separately there. -/
lemma splitEquiv_snd_eq_iff_restrict_right {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x y : Config d (Λ ∪ Γ)) :
    (splitEquiv Finset.subset_union_left x).2 =
        (splitEquiv Finset.subset_union_left y).2 ↔
      restrict Finset.subset_union_right x = restrict Finset.subset_union_right y := by
  rw [splitEquiv_snd_eq_iff_restrict_sdiff]
  constructor
  · intro h
    simpa only [leftComplementEquiv_restrict] using
      congrArg (leftComplementEquiv d hΛΓ) h
  · intro h
    apply (leftComplementEquiv d hΛΓ).injective
    simpa only [leftComplementEquiv_restrict] using h

/-- Equality of the complementary coordinates for the right split is equality after restriction
to the left region.

Source context: this coordinate identity underlies the right tensor factor in GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266; it is not stated separately there. -/
lemma splitEquiv_snd_eq_iff_restrict_left {d : ℕ} {Λ Γ : Finset ℤ}
    (hΛΓ : Disjoint Λ Γ) (x y : Config d (Λ ∪ Γ)) :
    (splitEquiv Finset.subset_union_right x).2 =
        (splitEquiv Finset.subset_union_right y).2 ↔
      restrict Finset.subset_union_left x = restrict Finset.subset_union_left y := by
  rw [splitEquiv_snd_eq_iff_restrict_sdiff]
  constructor
  · intro h
    simpa only [rightComplementEquiv_restrict] using
      congrArg (rightComplementEquiv d hΛΓ) h
  · intro h
    apply (rightComplementEquiv d hΛΓ).injective
    simpa only [rightComplementEquiv_restrict] using h

end Config

variable {d : ℕ} {Λ Γ : Finset ℤ}

/-- Bipartite matrix coordinates for the observable algebra on a disjoint union.

The left matrix factor corresponds to `Λ` and the right matrix factor corresponds to `Γ`.
Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
noncomputable def bipartiteLocalAlgebraEquiv (hΛΓ : Disjoint Λ Γ) :
    LocalAlgebra d (Λ ∪ Γ) ≃⋆ₐ[ℂ]
      Matrix (Config d Λ × Config d Γ) (Config d Λ × Config d Γ) ℂ :=
  (CStarMatrix.reindexₐ ℂ ℂ (Config.disjointUnionEquiv hΛΓ)).trans
    CStarMatrix.ofMatrixStarAlgEquiv.symm

/-- Evaluation of the bipartite equivalence is simultaneous reindexing by the reconstructed left
and right configurations.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
@[simp]
lemma bipartiteLocalAlgebraEquiv_apply (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d (Λ ∪ Γ)) (x y : Config d Λ × Config d Γ) :
    bipartiteLocalAlgebraEquiv hΛΓ A x y =
      A ((Config.disjointUnionEquiv hΛΓ).symm x)
        ((Config.disjointUnionEquiv hΛΓ).symm y) :=
  rfl

/-- In bipartite coordinates, inclusion from the left region is tensoring on the right by the
identity matrix.

This fixes the tensor-factor orientation used by the support algebra in GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
theorem bipartiteLocalAlgebraEquiv_localInclusion_left (hΛΓ : Disjoint Λ Γ)
    (A : LocalAlgebra d Λ) :
    bipartiteLocalAlgebraEquiv hΛΓ
        (localInclusion (d := d) Finset.subset_union_left A) =
      Matrix.leftKroneckerEmbed (n := Config d Γ) (CStarMatrix.ofMatrix.symm A) := by
  ext x y
  rw [bipartiteLocalAlgebraEquiv_apply, localInclusion_apply]
  simp only [Config.splitEquiv_snd_eq_iff_restrict_right hΛΓ]
  simp only [Config.restrict_disjointUnionEquiv_symm_left,
    Config.restrict_disjointUnionEquiv_symm_right]
  simp [Matrix.leftKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- In bipartite coordinates, inclusion from the right region is tensoring on the left by the
identity matrix.

This fixes the tensor-factor orientation used by the support algebra in GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. -/
theorem bipartiteLocalAlgebraEquiv_localInclusion_right (hΛΓ : Disjoint Λ Γ)
    (B : LocalAlgebra d Γ) :
    bipartiteLocalAlgebraEquiv hΛΓ
        (localInclusion (d := d) Finset.subset_union_right B) =
      Matrix.rightKroneckerEmbed (m := Config d Λ) (CStarMatrix.ofMatrix.symm B) := by
  ext x y
  rw [bipartiteLocalAlgebraEquiv_apply, localInclusion_apply]
  simp only [Config.splitEquiv_snd_eq_iff_restrict_left hΛΓ]
  simp only [Config.restrict_disjointUnionEquiv_symm_left,
    Config.restrict_disjointUnionEquiv_symm_right]
  simp [Matrix.rightKroneckerEmbed_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    mul_comm]

/-- A finite-region star-subalgebra written in the bipartite matrix coordinates of two disjoint
regions.

The result is a star-subalgebra of the bipartite matrix algebra on which the left and right support
algebras are defined. No support algebra is formed here.

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. This is the canonical
finite-dimensional coordinate construction determined by that decomposition, not a separately
stated source definition. -/
noncomputable def StarSubalgebra.bipartiteReindex (hΛΓ : Disjoint Λ Γ)
    (S : StarSubalgebra ℂ (LocalAlgebra d (Λ ∪ Γ))) :
    StarSubalgebra ℂ
      (Matrix (Config d Λ × Config d Γ) (Config d Λ × Config d Γ) ℂ) :=
  S.map (bipartiteLocalAlgebraEquiv hΛΓ).toStarAlgHom

end SpinChain

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.SiteIndexedSupportAlgebra

/-!
# Two-site translation covariance of the site-indexed support algebras

For a translation-covariant star-automorphism of the homogeneous quasi-local observable algebra
with nearest-neighbour propagation, the site-indexed support algebras
\((\mathcal R_y)_{y\in\mathbb Z}\) of `TNLean.QCA.SiteIndexedSupportAlgebra` satisfy
\[
  \tau_2(\mathcal R_y)=\mathcal R_{y+2},
\]
where \(\tau_2\) is translation by two sites of the original chain, that is, by one blocked cell.
In the two parities this reads
\[
  \tau_2(\mathcal R_{2x})=\mathcal R_{2x+2},\qquad
  \tau_2(\mathcal R_{2x+1})=\mathcal R_{2x+3}.
\]
Translation covariance is used only here; the construction of the family itself uses the
star-automorphism and its propagation region alone.

The corresponding one-site formula \(\tau_1(\mathcal R_y)=\mathcal R_{y+1}\) is false in general
and is not asserted anywhere in this file: the even source pair \(E_x=\{2x,2x+1\}\) is carried to
\(E_{x+1}\) by translation by two, while translation by one does not preserve the even pairing at
all. Gross--Nesme--Vogts--Werner give the shift automorphism as an explicit counterexample at
arXiv:0910.3675v2, lines 1267--1268: there the even algebra is a two-site full matrix algebra
while the odd algebra is the scalars, and no translation carries one onto the other. That example
repeats the even subscript on line 1268 where the odd one is meant; the intended reading is used
in this sentence only, and no declaration below refers to the example.

The proof replaces the finite matrix coefficients by their quasi-local compressions. Writing
\(\Gamma\) and \(\Delta\) for the two ordered target regions, the left coefficient of an element
\(V\) of the image algebra at a pair of \(\Delta\)-configurations is
\[
  \sum_{k}\, e_{k i}^{\Delta}\, V\, e_{j k}^{\Delta},
\]
a sum of products taken entirely inside the quasi-local algebra. Both matrix coefficient families
therefore become families of quasi-local elements to which lattice translation applies directly.

**Scope restriction (homogeneous chain):** as in `TNLean.QCA.SiteIndexedSupportAlgebra`, the
one-site matrix size is the fixed positive size \(d\) of the present quasi-local algebra, whereas
Gross--Nesme--Vogts--Werner allow it to depend on the site. Their cellular automata are moreover
not assumed translation covariant, so the theorems below are not covariance theorems of that
paper: covariance under translation of the support algebras is supplied by Schumacher--Werner,
quant-ph/0405174, lines 1199--1206 and 1218--1226, and the translation-covariant fixed-\(d\)
setting by Cirac et al., arXiv:1703.09188, lines 2292--2298. Schumacher--Werner state the
translated-support identity for the cube lattice in arbitrary dimension with the cubic
nearest-neighbour scheme, quant-ph/0405174, lines 920--941; the theorems below are its
one-dimensional instance. See the
[Schumacher--Werner covariance scope note](https://sirui-lu.com/TNLean/paper-gaps/sw04_support_covariance_scope.pdf)
and the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf).

No commutation theorem, matrix-factor classification, adjacent-block generation equality, or
index is proved here.

## Main results

* `Matrix.leftKroneckerEmbed_bipartiteSlice_eq_sum` and
  `Matrix.rightKroneckerEmbed_operatorBlock_eq_sum` express a matrix coefficient of a bipartite
  matrix through compressions by matrix units of the complementary factor.
* `SpinChain.matrixToQuasiLocalObservable_bipartiteSlice_eq_sum` and
  `SpinChain.matrixToQuasiLocalObservable_operatorBlock_eq_sum` are the quasi-local forms of
  those two expressions.
* `SpinChain.translateRegion_evenPair`, `SpinChain.translateRegion_leftPair`, and
  `SpinChain.translateRegion_rightPair` translate the three two-site regions by two sites.
* `SpinChain.PropagatesWithin.embeddedEvenSupportAlgebra_map_quasiLocalTranslation_two` and
  `SpinChain.PropagatesWithin.embeddedOddSupportAlgebra_map_quasiLocalTranslation_two` are the two
  parity formulas.
* `SpinChain.PropagatesWithin.embeddedSupportAlgebra_map_quasiLocalTranslation_two` is the unified
  formula \(\tau_2(\mathcal R_y)=\mathcal R_{y+2}\).

## References

* Schumacher--Werner, quant-ph/0405174, definition `defBBq`, lines 1199--1206, and the
  translated-support calculation, lines 1218--1226.
* Gross--Nesme--Vogts--Werner, arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266, and the shift
  example, lines 1267--1268.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, lines 2292--2298 and 2313--2328.
-/

open scoped BigOperators Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A first-factor coefficient of a bipartite matrix, tensored with the identity of the second
factor, is the sum of the compressions of that matrix by the matrix units of the second factor:
\[
  X_{ij}\otimes\mathbf 1=\sum_k(\mathbf 1\otimes e_{ki})\,X\,(\mathbf 1\otimes e_{jk}).
\]

This is the coefficient family of Schumacher--Werner, quant-ph/0405174, lines 1137--1169,
rewritten so that each coefficient is a sum of products inside the ambient algebra. Neither that
paper nor GNVW, arXiv:0910.3675v2, lines 1188--1191, displays the identity separately. -/
theorem leftKroneckerEmbed_bipartiteSlice_eq_sum
    (X : Matrix (m × n) (m × n) ℂ) (i j : n) :
    leftKroneckerEmbed (n := n) (bipartiteSlice X i j) =
      ∑ k : n, rightKroneckerEmbed (m := m) (single k i (1 : ℂ)) * X *
        rightKroneckerEmbed (m := m) (single j k (1 : ℂ)) := by
  ext p q
  obtain ⟨a, u⟩ := p
  obtain ⟨b, v⟩ := q
  rw [Matrix.sum_apply]
  simp only [leftKroneckerEmbed_apply, rightKroneckerEmbed_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.single_apply,
    bipartiteSlice_apply]
  simp [ite_and, eq_comm, mul_comm]

/-- A second-factor coefficient of a bipartite matrix, tensored with the identity of the first
factor, is the sum of the compressions of that matrix by the matrix units of the first factor:
\[
  \mathbf 1\otimes X_{ij}=\sum_k(e_{ki}\otimes\mathbf 1)\,X\,(e_{jk}\otimes\mathbf 1).
\]

This is the symmetric counterpart of `Matrix.leftKroneckerEmbed_bipartiteSlice_eq_sum` for the
coefficient family of GNVW, arXiv:0910.3675v2, lines 1211--1219. -/
theorem rightKroneckerEmbed_operatorBlock_eq_sum
    (X : Matrix (m × n) (m × n) ℂ) (i j : m) :
    rightKroneckerEmbed (m := m) (operatorBlock X i j) =
      ∑ k : m, leftKroneckerEmbed (n := n) (single k i (1 : ℂ)) * X *
        leftKroneckerEmbed (n := n) (single j k (1 : ℂ)) := by
  ext p q
  obtain ⟨a, u⟩ := p
  obtain ⟨b, v⟩ := q
  rw [Matrix.sum_apply]
  simp only [leftKroneckerEmbed_apply, rightKroneckerEmbed_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.single_apply,
    operatorBlock_apply]
  simp [ite_and, eq_comm, mul_comm]

end Matrix

namespace SpinChain

/-! ### Translation of the three two-site regions -/

/-- Translating the even source pair by two sites advances its index:
\(E_x+2=E_{x+1}\).

Source context: this is the blocked-cell shift used by GNVW, arXiv:0910.3675v2,
lines 1251--1266, and by Cirac et al., arXiv:1703.09188, lines 2313--2318. -/
lemma translateRegion_evenPair (x : ℤ) :
    translateRegion 2 (evenPair x) = evenPair (x + 1) := by
  ext y
  simp only [mem_translateRegion, evenPair, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Translating the left target pair by two sites advances its index:
\(L_x+2=L_{x+1}\).

Source context: GNVW, arXiv:0910.3675v2, lines 1251--1266. -/
lemma translateRegion_leftPair (x : ℤ) :
    translateRegion 2 (leftPair x) = leftPair (x + 1) := by
  ext y
  simp only [mem_translateRegion, leftPair, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Translating the right target pair by two sites advances its index:
\(P_x+2=P_{x+1}\).

Source context: GNVW, arXiv:0910.3675v2, lines 1251--1266. -/
lemma translateRegion_rightPair (x : ℤ) :
    translateRegion 2 (rightPair x) = rightPair (x + 1) := by
  ext y
  simp only [mem_translateRegion, rightPair, Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ### Quasi-local compressions of the matrix coefficients -/

variable {d : ℕ} [NeZero d]

/-- Transporting a finite-region observable along an equality of regions does not change the
quasi-local observable it represents. -/
private lemma quasiLocalObservable_cast {U V : Finset ℤ} (h : U = V) (A : LocalAlgebra d U) :
    quasiLocalObservable d V (h ▸ A) = quasiLocalObservable d U A := by
  subst h
  rfl

omit [NeZero d] in
/-- Reading the left Kronecker embedding back in the observable algebra of the union gives the
canonical inclusion from the first region. -/
private lemma bipartiteLocalAlgebraEquiv_symm_leftKroneckerEmbed {Γ Δ : Finset ℤ}
    (hΓΔ : Disjoint Γ Δ) (M : Matrix (Config d Γ) (Config d Γ) ℂ) :
    (bipartiteLocalAlgebraEquiv hΓΔ).symm (Matrix.leftKroneckerEmbed M) =
      localInclusion (d := d) Finset.subset_union_left
        (CStarMatrix.ofMatrixStarAlgEquiv M) := by
  rw [StarAlgEquiv.symm_apply_eq]
  exact (bipartiteLocalAlgebraEquiv_localInclusion_left hΓΔ
    (CStarMatrix.ofMatrixStarAlgEquiv M)).symm

omit [NeZero d] in
/-- Reading the right Kronecker embedding back in the observable algebra of the union gives the
canonical inclusion from the second region. -/
private lemma bipartiteLocalAlgebraEquiv_symm_rightKroneckerEmbed {Γ Δ : Finset ℤ}
    (hΓΔ : Disjoint Γ Δ) (M : Matrix (Config d Δ) (Config d Δ) ℂ) :
    (bipartiteLocalAlgebraEquiv hΓΔ).symm (Matrix.rightKroneckerEmbed M) =
      localInclusion (d := d) Finset.subset_union_right
        (CStarMatrix.ofMatrixStarAlgEquiv M) := by
  rw [StarAlgEquiv.symm_apply_eq]
  exact (bipartiteLocalAlgebraEquiv_localInclusion_right hΓΔ
    (CStarMatrix.ofMatrixStarAlgEquiv M)).symm

/-- In bipartite coordinates for two disjoint regions, the canonical quasi-local copy of a
first-factor matrix coefficient is a sum of compressions by matrix units of the second region.

The first region supplies the left tensor factor and the second the right one, as in GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1249--1266. The identity itself is the quasi-local form
of the coefficient family of Schumacher--Werner, quant-ph/0405174, lines 1137--1169; it is not
displayed separately in either source. -/
theorem matrixToQuasiLocalObservable_bipartiteSlice_eq_sum
    {Γ Δ : Finset ℤ} (hΓΔ : Disjoint Γ Δ) (A : LocalAlgebra d (Γ ∪ Δ))
    (i j : Config d Δ) :
    matrixToQuasiLocalObservable d Γ
        (Matrix.bipartiteSlice (bipartiteLocalAlgebraEquiv hΓΔ A) i j) =
      ∑ k : Config d Δ,
        matrixToQuasiLocalObservable d Δ (Matrix.single k i (1 : ℂ)) *
          quasiLocalObservable d (Γ ∪ Δ) A *
          matrixToQuasiLocalObservable d Δ (Matrix.single j k (1 : ℂ)) := by
  have hlocal :
      localInclusion (d := d) Finset.subset_union_left
          (CStarMatrix.ofMatrixStarAlgEquiv
            (Matrix.bipartiteSlice (bipartiteLocalAlgebraEquiv hΓΔ A) i j)) =
        ∑ k : Config d Δ,
          localInclusion (d := d) Finset.subset_union_right
              (CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single k i (1 : ℂ))) * A *
            localInclusion (d := d) Finset.subset_union_right
              (CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single j k (1 : ℂ))) := by
    rw [← bipartiteLocalAlgebraEquiv_symm_leftKroneckerEmbed hΓΔ,
      Matrix.leftKroneckerEmbed_bipartiteSlice_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_mul, bipartiteLocalAlgebraEquiv_symm_rightKroneckerEmbed,
      bipartiteLocalAlgebraEquiv_symm_rightKroneckerEmbed, StarAlgEquiv.symm_apply_apply]
  have hstart : matrixToQuasiLocalObservable d Γ
      (Matrix.bipartiteSlice (bipartiteLocalAlgebraEquiv hΓΔ A) i j) =
      quasiLocalObservable d Γ (CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.bipartiteSlice (bipartiteLocalAlgebraEquiv hΓΔ A) i j)) := rfl
  rw [hstart,
    ← quasiLocalObservable_localInclusion d (show Γ ⊆ Γ ∪ Δ from Finset.subset_union_left),
    hlocal, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_mul, quasiLocalObservable_localInclusion,
    quasiLocalObservable_localInclusion]
  rfl

/-- In bipartite coordinates for two disjoint regions, the canonical quasi-local copy of a
second-factor matrix coefficient is a sum of compressions by matrix units of the first region.

This is the symmetric counterpart of
`SpinChain.matrixToQuasiLocalObservable_bipartiteSlice_eq_sum` for the coefficient family of GNVW,
arXiv:0910.3675v2, lines 1211--1219. -/
theorem matrixToQuasiLocalObservable_operatorBlock_eq_sum
    {Γ Δ : Finset ℤ} (hΓΔ : Disjoint Γ Δ) (A : LocalAlgebra d (Γ ∪ Δ))
    (i j : Config d Γ) :
    matrixToQuasiLocalObservable d Δ
        (Matrix.operatorBlock (bipartiteLocalAlgebraEquiv hΓΔ A) i j) =
      ∑ k : Config d Γ,
        matrixToQuasiLocalObservable d Γ (Matrix.single k i (1 : ℂ)) *
          quasiLocalObservable d (Γ ∪ Δ) A *
          matrixToQuasiLocalObservable d Γ (Matrix.single j k (1 : ℂ)) := by
  have hlocal :
      localInclusion (d := d) Finset.subset_union_right
          (CStarMatrix.ofMatrixStarAlgEquiv
            (Matrix.operatorBlock (bipartiteLocalAlgebraEquiv hΓΔ A) i j)) =
        ∑ k : Config d Γ,
          localInclusion (d := d) Finset.subset_union_left
              (CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single k i (1 : ℂ))) * A *
            localInclusion (d := d) Finset.subset_union_left
              (CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single j k (1 : ℂ))) := by
    rw [← bipartiteLocalAlgebraEquiv_symm_rightKroneckerEmbed hΓΔ,
      Matrix.rightKroneckerEmbed_operatorBlock_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_mul, bipartiteLocalAlgebraEquiv_symm_leftKroneckerEmbed,
      bipartiteLocalAlgebraEquiv_symm_leftKroneckerEmbed, StarAlgEquiv.symm_apply_apply]
  have hstart : matrixToQuasiLocalObservable d Δ
      (Matrix.operatorBlock (bipartiteLocalAlgebraEquiv hΓΔ A) i j) =
      quasiLocalObservable d Δ (CStarMatrix.ofMatrixStarAlgEquiv
        (Matrix.operatorBlock (bipartiteLocalAlgebraEquiv hΓΔ A) i j)) := rfl
  rw [hstart,
    ← quasiLocalObservable_localInclusion d (show Δ ⊆ Γ ∪ Δ from Finset.subset_union_right),
    hlocal, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_mul, quasiLocalObservable_localInclusion,
    quasiLocalObservable_localInclusion]
  rfl

/-- Translation of a quasi-local observable presented by an ordinary matrix in finite-region
coordinates reindexes that matrix by the configuration translation. -/
private lemma quasiLocalTranslation_matrixToQuasiLocalObservable (a : ℤ) (Θ : Finset ℤ)
    (M : Matrix (Config d Θ) (Config d Θ) ℂ) :
    quasiLocalTranslation d a (matrixToQuasiLocalObservable d Θ M) =
      matrixToQuasiLocalObservable d (translateRegion a Θ)
        (Matrix.reindex (Config.translation d a Θ) (Config.translation d a Θ) M) := by
  rw [matrixToQuasiLocalObservable, StarAlgHom.comp_apply,
    quasiLocalTranslation_quasiLocalObservable, matrixToQuasiLocalObservable,
    StarAlgHom.comp_apply]
  rfl

/-- Translation of a quasi-local matrix unit in finite-region coordinates is the matrix unit at
the translated configurations. -/
private lemma quasiLocalTranslation_matrixToQuasiLocalObservable_single (a : ℤ) (Θ : Finset ℤ)
    (p q : Config d Θ) :
    quasiLocalTranslation d a (matrixToQuasiLocalObservable d Θ (Matrix.single p q (1 : ℂ))) =
      matrixToQuasiLocalObservable d (translateRegion a Θ)
        (Matrix.single (Config.translation d a Θ p) (Config.translation d a Θ q) (1 : ℂ)) := by
  rw [quasiLocalTranslation_matrixToQuasiLocalObservable, Matrix.reindex_apply,
    Matrix.submatrix_single_equiv, Equiv.symm_symm]

/-! ### The quasi-local generator families -/

namespace PropagatesWithin

variable {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d} {𝓝 : Finset ℤ}

/-- The compressions of the image of the observable algebra on a source region by the matrix
units of a second region.

Taking the second region to be the right target pair gives the generators of the even support
algebra, and taking it to be the left target pair gives those of the odd support algebra. The
remaining target region never enters. -/
private noncomputable def compressionGenerators
    (ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d) (Λ Θ : Finset ℤ) :
    Set (QuasiLocalAlgebra d) :=
  {g | ∃ (B : LocalAlgebra d Λ) (i j : Config d Θ),
    g = ∑ k : Config d Θ,
      matrixToQuasiLocalObservable d Θ (Matrix.single k i (1 : ℂ)) *
        ω (quasiLocalObservable d Λ B) *
        matrixToQuasiLocalObservable d Θ (Matrix.single j k (1 : ℂ))}

/-- The transported finite local image consists of the finite-region observables whose quasi-local
copies are the images of the source observable algebra. -/
private lemma mem_localRestrictionRange_cast (hω : PropagatesWithin ω 𝓝) {Λ U : Finset ℤ}
    (h : regionSumset Λ 𝓝 = U) (A : LocalAlgebra d U) :
    A ∈ h ▸ hω.localRestrictionRange Λ ↔
      ∃ B : LocalAlgebra d Λ,
        ω (quasiLocalObservable d Λ B) = quasiLocalObservable d U A := by
  subst h
  have hmem : A ∈ hω.localRestrictionRange Λ ↔
      ∃ B : LocalAlgebra d Λ, hω.localRestriction Λ B = A := Iff.rfl
  rw [hmem]
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B, (hω.quasiLocalObservable_localRestriction Λ B).symm⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, ?_⟩
    apply quasiLocalObservable_injective d (regionSumset Λ 𝓝)
    rw [hω.quasiLocalObservable_localRestriction, hB]

/-- The canonical quasi-local copy of the left support algebra is generated by the quasi-local
compressions of the first-factor coefficients. -/
private theorem map_leftSupportAlgebra_eq_adjoin (hω : PropagatesWithin ω 𝓝)
    (Λ Γ Δ : Finset ℤ) (hΓΔ : Disjoint Γ Δ) (htarget : regionSumset Λ 𝓝 = Γ ∪ Δ) :
    (Matrix.leftSupportAlgebra (hω.bipartiteLocalRestrictionRange Λ Γ Δ hΓΔ htarget)).map
        (matrixToQuasiLocalObservable d Γ) =
      StarAlgebra.adjoin ℂ (compressionGenerators ω Λ Δ) := by
  rw [Matrix.leftSupportAlgebra, StarAlgHom.map_adjoin]
  congr 1
  ext g
  simp only [Set.mem_image, Matrix.leftCoefficientSet, Set.mem_ofPred_eq,
    compressionGenerators, bipartiteLocalRestrictionRange, StarSubalgebra.bipartiteReindex,
    StarSubalgebra.mem_map]
  constructor
  · rintro ⟨M, ⟨X, ⟨A, hA, rfl⟩, i, j, rfl⟩, rfl⟩
    obtain ⟨B, hB⟩ := (hω.mem_localRestrictionRange_cast htarget A).mp hA
    refine ⟨B, i, j, ?_⟩
    rw [show (bipartiteLocalAlgebraEquiv hΓΔ).toStarAlgHom A =
      bipartiteLocalAlgebraEquiv hΓΔ A from rfl,
      matrixToQuasiLocalObservable_bipartiteSlice_eq_sum hΓΔ A i j, hB]
  · rintro ⟨B, i, j, rfl⟩
    refine ⟨Matrix.bipartiteSlice
      (bipartiteLocalAlgebraEquiv hΓΔ (htarget ▸ hω.localRestriction Λ B)) i j,
      ⟨_, ⟨htarget ▸ hω.localRestriction Λ B, ?_, rfl⟩, i, j, rfl⟩, ?_⟩
    · refine (hω.mem_localRestrictionRange_cast htarget _).mpr ⟨B, ?_⟩
      rw [quasiLocalObservable_cast, hω.quasiLocalObservable_localRestriction]
    · rw [matrixToQuasiLocalObservable_bipartiteSlice_eq_sum hΓΔ _ i j,
        quasiLocalObservable_cast, hω.quasiLocalObservable_localRestriction]

/-- The canonical quasi-local copy of the right support algebra is generated by the quasi-local
compressions of the second-factor coefficients. -/
private theorem map_rightSupportAlgebra_eq_adjoin (hω : PropagatesWithin ω 𝓝)
    (Λ Γ Δ : Finset ℤ) (hΓΔ : Disjoint Γ Δ) (htarget : regionSumset Λ 𝓝 = Γ ∪ Δ) :
    (Matrix.rightSupportAlgebra (hω.bipartiteLocalRestrictionRange Λ Γ Δ hΓΔ htarget)).map
        (matrixToQuasiLocalObservable d Δ) =
      StarAlgebra.adjoin ℂ (compressionGenerators ω Λ Γ) := by
  rw [Matrix.rightSupportAlgebra, StarAlgHom.map_adjoin]
  congr 1
  ext g
  simp only [Set.mem_image, Matrix.rightCoefficientSet, Set.mem_ofPred_eq,
    compressionGenerators, bipartiteLocalRestrictionRange, StarSubalgebra.bipartiteReindex,
    StarSubalgebra.mem_map]
  constructor
  · rintro ⟨M, ⟨X, ⟨A, hA, rfl⟩, i, j, rfl⟩, rfl⟩
    obtain ⟨B, hB⟩ := (hω.mem_localRestrictionRange_cast htarget A).mp hA
    refine ⟨B, i, j, ?_⟩
    rw [show (bipartiteLocalAlgebraEquiv hΓΔ).toStarAlgHom A =
      bipartiteLocalAlgebraEquiv hΓΔ A from rfl,
      matrixToQuasiLocalObservable_operatorBlock_eq_sum hΓΔ A i j, hB]
  · rintro ⟨B, i, j, rfl⟩
    refine ⟨Matrix.operatorBlock
      (bipartiteLocalAlgebraEquiv hΓΔ (htarget ▸ hω.localRestriction Λ B)) i j,
      ⟨_, ⟨htarget ▸ hω.localRestriction Λ B, ?_, rfl⟩, i, j, rfl⟩, ?_⟩
    · refine (hω.mem_localRestrictionRange_cast htarget _).mpr ⟨B, ?_⟩
      rw [quasiLocalObservable_cast, hω.quasiLocalObservable_localRestriction]
    · rw [matrixToQuasiLocalObservable_operatorBlock_eq_sum hΓΔ _ i j,
        quasiLocalObservable_cast, hω.quasiLocalObservable_localRestriction]

/-! ### Translation of the generator families -/

/-- A star-automorphism commuting with one lattice translation commutes with it pointwise. -/
private lemma apply_quasiLocalTranslation_of_commute {a : ℤ}
    (hcomm : Commute ω (quasiLocalTranslation d a)) (A : QuasiLocalAlgebra d) :
    ω (quasiLocalTranslation d a A) = quasiLocalTranslation d a (ω A) := by
  simpa only [StarAlgEquiv.mul_apply] using DFunLike.congr_fun hcomm.eq A

/-- Translating one compression produces the corresponding compression for the translated source
and compressing regions. -/
private lemma quasiLocalTranslation_compressionGenerator {a : ℤ}
    (hcomm : Commute ω (quasiLocalTranslation d a)) (Λ Δ : Finset ℤ)
    (B : LocalAlgebra d Λ) (i j : Config d Δ) :
    quasiLocalTranslation d a
        (∑ k : Config d Δ,
          matrixToQuasiLocalObservable d Δ (Matrix.single k i (1 : ℂ)) *
            ω (quasiLocalObservable d Λ B) *
            matrixToQuasiLocalObservable d Δ (Matrix.single j k (1 : ℂ))) =
      ∑ k : Config d (translateRegion a Δ),
        matrixToQuasiLocalObservable d (translateRegion a Δ)
            (Matrix.single k (Config.translation d a Δ i) (1 : ℂ)) *
          ω (quasiLocalObservable d (translateRegion a Λ) (localTranslation d a Λ B)) *
          matrixToQuasiLocalObservable d (translateRegion a Δ)
            (Matrix.single (Config.translation d a Δ j) k (1 : ℂ)) := by
  rw [map_sum, ← Equiv.sum_comp (Config.translation d a Δ)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, map_mul, quasiLocalTranslation_matrixToQuasiLocalObservable_single,
    quasiLocalTranslation_matrixToQuasiLocalObservable_single,
    ← apply_quasiLocalTranslation_of_commute hcomm,
    quasiLocalTranslation_quasiLocalObservable]

/-- Translation carries the compressions of a source region by a second region to the
compressions of the two translated regions. -/
private theorem image_compressionGenerators {a : ℤ}
    (hcomm : Commute ω (quasiLocalTranslation d a)) (Λ Θ : Finset ℤ) :
    quasiLocalTranslation d a '' compressionGenerators ω Λ Θ =
      compressionGenerators ω (translateRegion a Λ) (translateRegion a Θ) := by
  ext g
  simp only [Set.mem_image, compressionGenerators, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, ⟨B, i, j, rfl⟩, rfl⟩
    exact ⟨localTranslation d a Λ B, Config.translation d a Θ i, Config.translation d a Θ j,
      quasiLocalTranslation_compressionGenerator hcomm Λ Θ B i j⟩
  · rintro ⟨B, i, j, rfl⟩
    refine ⟨_, ⟨(localTranslation d a Λ).symm B, (Config.translation d a Θ).symm i,
      (Config.translation d a Θ).symm j, rfl⟩, ?_⟩
    rw [quasiLocalTranslation_compressionGenerator hcomm Λ Θ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply]

/-! ### Two-site covariance -/

/-- Translation by two sites advances the even support algebra by one blocked cell:
\[
  \tau_2(\mathcal R_{2x})=\mathcal R_{2x+2}.
\]

The shift is by two sites of the original chain, that is, by one blocked cell; the corresponding
one-site formula is false in general, as the module docstring records.

Source: Schumacher--Werner, quant-ph/0405174, definition `defBBq`, lines 1199--1206, and the
translated-support calculation, lines 1218--1226, in the fixed-\(d\) translation-covariant setting
of Cirac et al., arXiv:1703.09188, lines 2292--2298, for the support algebras of GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266. See the homogeneous-chain scope statement in
the module docstring. -/
theorem embeddedEvenSupportAlgebra_map_quasiLocalTranslation_two
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω) (x : ℤ) :
    (embeddedEvenSupportAlgebra hω x).map (quasiLocalTranslation d 2).toStarAlgHom =
      embeddedEvenSupportAlgebra hω (x + 1) := by
  rw [embeddedEvenSupportAlgebra, evenSupportAlgebra, evenPairLocalImage,
    hω.map_leftSupportAlgebra_eq_adjoin, StarAlgHom.map_adjoin,
    show ((quasiLocalTranslation d 2).toStarAlgHom : QuasiLocalAlgebra d → QuasiLocalAlgebra d) =
      quasiLocalTranslation d 2 from rfl,
    image_compressionGenerators (hcov 2), translateRegion_evenPair, translateRegion_rightPair,
    embeddedEvenSupportAlgebra, evenSupportAlgebra, evenPairLocalImage,
    hω.map_leftSupportAlgebra_eq_adjoin]

/-- Translation by two sites advances the odd support algebra by one blocked cell:
\[
  \tau_2(\mathcal R_{2x+1})=\mathcal R_{2x+3}.
\]

The shift is by two sites of the original chain, that is, by one blocked cell; the corresponding
one-site formula is false in general, as the module docstring records.

Source: Schumacher--Werner, quant-ph/0405174, definition `defBBq`, lines 1199--1206, and the
translated-support calculation, lines 1218--1226, in the fixed-\(d\) translation-covariant setting
of Cirac et al., arXiv:1703.09188, lines 2292--2298, for the support algebras of GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266. See the homogeneous-chain scope statement in
the module docstring. -/
theorem embeddedOddSupportAlgebra_map_quasiLocalTranslation_two
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω) (x : ℤ) :
    (embeddedOddSupportAlgebra hω x).map (quasiLocalTranslation d 2).toStarAlgHom =
      embeddedOddSupportAlgebra hω (x + 1) := by
  rw [embeddedOddSupportAlgebra, oddSupportAlgebra, evenPairLocalImage,
    hω.map_rightSupportAlgebra_eq_adjoin, StarAlgHom.map_adjoin,
    show ((quasiLocalTranslation d 2).toStarAlgHom : QuasiLocalAlgebra d → QuasiLocalAlgebra d) =
      quasiLocalTranslation d 2 from rfl,
    image_compressionGenerators (hcov 2), translateRegion_evenPair, translateRegion_leftPair,
    embeddedOddSupportAlgebra, oddSupportAlgebra, evenPairLocalImage,
    hω.map_rightSupportAlgebra_eq_adjoin]

/-- Two-site translation covariance of the unified site-indexed support-algebra family:
\[
  \tau_2(\mathcal R_y)=\mathcal R_{y+2}\qquad(y\in\mathbb Z).
\]

The displacement is two sites of the original chain, that is, one blocked cell. The one-site
formula \(\tau_1(\mathcal R_y)=\mathcal R_{y+1}\) is false in general and is not asserted; see the
module docstring.

Source: Schumacher--Werner, quant-ph/0405174, definition `defBBq`, lines 1199--1206, and the
translated-support calculation, lines 1218--1226, in the fixed-\(d\) translation-covariant setting
of Cirac et al., arXiv:1703.09188, lines 2292--2298, for the support algebras of GNVW,
arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266. GNVW allow site-dependent cell algebras and
assume no translation covariance, so this is not a covariance theorem of that paper. See the
homogeneous-chain scope statement in the module docstring. -/
theorem embeddedSupportAlgebra_map_quasiLocalTranslation_two
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω) (y : ℤ) :
    (embeddedSupportAlgebra hω y).map (quasiLocalTranslation d 2).toStarAlgHom =
      embeddedSupportAlgebra hω (y + 2) := by
  obtain ⟨x, hx | hx⟩ := Int.even_or_odd' y
  · subst hx
    rw [embeddedSupportAlgebra_even, show 2 * x + 2 = 2 * (x + 1) by ring,
      embeddedSupportAlgebra_even, embeddedEvenSupportAlgebra_map_quasiLocalTranslation_two hω hcov]
  · subst hx
    rw [embeddedSupportAlgebra_odd, show 2 * x + 1 + 2 = 2 * (x + 1) + 1 by ring,
      embeddedSupportAlgebra_odd, embeddedOddSupportAlgebra_map_quasiLocalTranslation_two hω hcov]

/-- The even parity formula for the unified family:
\[
  \tau_2(\mathcal R_{2x})=\mathcal R_{2x+2}.
\]

Source: as for `SpinChain.PropagatesWithin.embeddedSupportAlgebra_map_quasiLocalTranslation_two`,
with the even index of GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1261--1266. -/
theorem embeddedSupportAlgebra_map_quasiLocalTranslation_two_even
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω) (x : ℤ) :
    (embeddedSupportAlgebra hω (2 * x)).map (quasiLocalTranslation d 2).toStarAlgHom =
      embeddedSupportAlgebra hω (2 * x + 2) :=
  embeddedSupportAlgebra_map_quasiLocalTranslation_two hω hcov (2 * x)

/-- The odd parity formula for the unified family:
\[
  \tau_2(\mathcal R_{2x+1})=\mathcal R_{2x+3}.
\]

Source: as for `SpinChain.PropagatesWithin.embeddedSupportAlgebra_map_quasiLocalTranslation_two`,
with the odd index of GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1261--1266. -/
theorem embeddedSupportAlgebra_map_quasiLocalTranslation_two_odd
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (hcov : TranslationCovariant ω) (x : ℤ) :
    (embeddedSupportAlgebra hω (2 * x + 1)).map (quasiLocalTranslation d 2).toStarAlgHom =
      embeddedSupportAlgebra hω (2 * x + 3) := by
  have h := embeddedSupportAlgebra_map_quasiLocalTranslation_two hω hcov (2 * x + 1)
  rwa [show 2 * x + 1 + 2 = 2 * x + 3 by ring] at h

end PropagatesWithin

end SpinChain

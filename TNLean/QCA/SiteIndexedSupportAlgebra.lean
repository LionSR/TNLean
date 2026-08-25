/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.BipartiteSupportAlgebra
import TNLean.QCA.FiniteLocalRestriction

/-!
# Site-indexed support algebras of a nearest-neighbour QCA

For
\[
  E_x=\{2x,2x+1\},\qquad
  L_x=\{2x-1,2x\},\qquad
  P_x=\{2x+1,2x+2\},
\]
nearest-neighbour propagation places the image of the observable algebra on \(E_x\) in the
observable algebra on \(L_x\cup P_x\). The canonical bipartite coordinates put \(L_x\) first and
\(P_x\) second. The left and right support algebras of this image are therefore, in the notation
of Gross--Nesme--Vogts--Werner,
\[
  \mathcal R_{2x}=\operatorname{Spp}_{\mathrm L}(S_x),\qquad
  \mathcal R_{2x+1}=\operatorname{Spp}_{\mathrm R}(S_x).
\]
They are embedded into the quasi-local algebra as one family indexed by \(\mathbb Z\).

**Scope restriction (homogeneous chain):** Gross--Nesme--Vogts--Werner allow the one-site
matrix size to depend on the site. This file treats the fixed positive size \(d\) of the present
quasi-local algebra. The unrestricted construction requires a site-dependent spin-chain
observable algebra. See
[the homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf).

No translation covariance, commutation theorem, matrix-factor classification, adjacent-block
generation equality, or index is proved here.

## Main definitions

* `SpinChain.evenPair`, `SpinChain.leftPair`, and `SpinChain.rightPair` are \(E_x,L_x,P_x\).
* `SpinChain.matrixToQuasiLocalObservable` is the canonical star-algebra homomorphism from
  ordinary finite-region matrices to quasi-local observables.
* `SpinChain.PropagatesWithin.evenPairLocalImage` is \(S_x\) in the ordered
  \(L_x\times P_x\) coordinates.
* `SpinChain.PropagatesWithin.evenSupportAlgebra` and
  `SpinChain.PropagatesWithin.oddSupportAlgebra` are
  \(\mathcal R_{2x}\) and \(\mathcal R_{2x+1}\).
* `SpinChain.PropagatesWithin.embeddedSupportAlgebra` is the unified quasi-local family
  \((\mathcal R_y)_{y\in\mathbb Z}\).

## Main results

* `SpinChain.regionSumset_evenPair` identifies the four-site target as \(L_x\cup P_x\).
* `SpinChain.rightPair_eq_leftPair_add_one` identifies \(P_x=L_{x+1}\).
* `SpinChain.matrixToQuasiLocalObservable_supportedIn` records the finite-region support of this
  canonical homomorphism.
* `SpinChain.PropagatesWithin.evenPairLocalImage_le_support_kroneckerSubmodule` is the
  site-specific two-sided support containment.
* `SpinChain.PropagatesWithin.embeddedSupportAlgebra_even_supportedIn` and
  `SpinChain.PropagatesWithin.embeddedSupportAlgebra_odd_supportedIn` place the two parity
  families in their physical two-site regions.

## References

* Gross--Nesme--Vogts--Werner, arXiv:0910.3675v2, equation `RR2x`, lines 1251--1278.
* Schumacher--Werner, quant-ph/0405174, Section 4.3, lines 1137--1194.
* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2329.
-/

namespace SpinChain

/-! ### Adjacent two-site regions -/

/-- The even source pair \(E_x=\{2x,2x+1\}\).

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266; Cirac et al.,
arXiv:1703.09188, Appendix, lines 2313--2318. -/
def evenPair (x : ℤ) : Finset ℤ :=
  {2 * x, 2 * x + 1}

/-- The left target pair \(L_x=\{2x-1,2x\}\).

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266. -/
def leftPair (x : ℤ) : Finset ℤ :=
  {2 * x - 1, 2 * x}

/-- The right target pair \(P_x=\{2x+1,2x+2\}\).

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1251--1266. -/
def rightPair (x : ℤ) : Finset ℤ :=
  {2 * x + 1, 2 * x + 2}

/-- The nearest-neighbour enlargement of \(E_x\) is the ordered union \(L_x\cup P_x\).

Source context: GNVW, arXiv:0910.3675v2, lines 1251--1258; Cirac et al.,
arXiv:1703.09188, Appendix, lines 2313--2318. -/
lemma regionSumset_evenPair (x : ℤ) :
    regionSumset (evenPair x) (Finset.Icc (-1) 1) = leftPair x ∪ rightPair x := by
  ext y
  simp only [mem_regionSumset, evenPair, leftPair, rightPair, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, a, ha, rfl⟩
    rcases hj with rfl | rfl <;> omega
  · rintro ((rfl | rfl) | rfl | rfl)
    · exact ⟨2 * x, Or.inl rfl, -1, by omega⟩
    · exact ⟨2 * x, Or.inl rfl, 0, by omega⟩
    · exact ⟨2 * x, Or.inl rfl, 1, by omega⟩
    · exact ⟨2 * x + 1, Or.inr rfl, 1, by omega⟩

/-- The two target pairs \(L_x\) and \(P_x\) are disjoint.

Source context: GNVW, arXiv:0910.3675v2, lines 1251--1258. -/
lemma disjoint_leftPair_rightPair (x : ℤ) : Disjoint (leftPair x) (rightPair x) := by
  rw [Finset.disjoint_left]
  intro a haL haR
  simp only [leftPair, rightPair, Finset.mem_insert, Finset.mem_singleton] at haL haR
  omega

/-- The right target pair of \(E_x\) is the left target pair of \(E_{x+1}\):
\(P_x=L_{x+1}\).

Source context: this is the common two-site region in the consecutive-pair argument of GNVW,
arXiv:0910.3675v2, lines 1270--1278. -/
lemma rightPair_eq_leftPair_add_one (x : ℤ) : rightPair x = leftPair (x + 1) := by
  ext y
  simp only [rightPair, leftPair, Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ### Canonical matrix observables -/

/-- The canonical star-algebra homomorphism from ordinary matrices in finite-region coordinates
to the quasi-local algebra.

It first identifies a matrix with the corresponding element of the finite local C*-algebra and
then applies the canonical quasi-local inclusion. Under this identification, it is the
finite-region inclusion used by Cirac et al., arXiv:1703.09188, lines 2292--2298. It also realizes
the finite-cell inclusions surrounding GNVW equation `RR2x`, arXiv:0910.3675v2,
lines 1251--1274; neither source names the composition separately. -/
noncomputable def matrixToQuasiLocalObservable (d : ℕ) [NeZero d] (Λ : Finset ℤ) :
    Matrix (Config d Λ) (Config d Λ) ℂ →⋆ₐ[ℂ] QuasiLocalAlgebra d :=
  (quasiLocalObservable d Λ).comp CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom

/-- A matrix embedded by `matrixToQuasiLocalObservable` is supported in its defining finite
region.

This is the support property of the canonical finite-region inclusion used by Cirac et al.,
arXiv:1703.09188, lines 2292--2298; it is not a separately stated source theorem. -/
theorem matrixToQuasiLocalObservable_supportedIn (d : ℕ) [NeZero d] (Λ : Finset ℤ)
    (a : Matrix (Config d Λ) (Config d Λ) ℂ) :
    QuasiLocalSupportedIn (matrixToQuasiLocalObservable d Λ a) Λ := by
  change QuasiLocalSupportedIn
    (quasiLocalObservable d Λ (CStarMatrix.ofMatrixStarAlgEquiv a)) Λ
  exact QuasiLocalSupportedIn.quasiLocalObservable _

/-! ### Finite support algebras -/

namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- The finite image \(S_x=\omega(\mathcal A_{E_x})\) in the canonical ordered
\(L_x\times P_x\) matrix coordinates.

The first matrix coordinate is `Config d (leftPair x)` and the second is
`Config d (rightPair x)`.

This is the fixed-\(d\) specialization of the site-dependent local image in GNVW,
arXiv:0910.3675v2, lines 1251--1266, under the homogeneous-chain scope stated in the module
docstring. Cirac et al. use the homogeneous image at arXiv:1703.09188, lines 2313--2318.
See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def evenPairLocalImage
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ
      (Matrix (Config d (leftPair x) × Config d (rightPair x))
        (Config d (leftPair x) × Config d (rightPair x)) ℂ) :=
  hω.bipartiteLocalRestrictionRange (evenPair x) (leftPair x) (rightPair x)
    (disjoint_leftPair_rightPair x) (regionSumset_evenPair x)

/-- The even support algebra
\(\mathcal R_{2x}=\operatorname{Spp}_{\mathrm L}(S_x)\) on \(L_x\).

This is the fixed-\(d\) instance of GNVW equation `RR2x`, arXiv:0910.3675v2,
lines 1261--1266, under the homogeneous-chain scope stated in the module docstring. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def evenSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ (Matrix (Config d (leftPair x)) (Config d (leftPair x)) ℂ) :=
  Matrix.leftSupportAlgebra (evenPairLocalImage hω x)

/-- The odd support algebra
\(\mathcal R_{2x+1}=\operatorname{Spp}_{\mathrm R}(S_x)\) on \(P_x\).

This is the fixed-\(d\) instance of GNVW equation `RR2x`, arXiv:0910.3675v2,
lines 1261--1266, under the homogeneous-chain scope stated in the module docstring. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def oddSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ (Matrix (Config d (rightPair x)) (Config d (rightPair x)) ℂ) :=
  Matrix.rightSupportAlgebra (evenPairLocalImage hω x)

/-- The site-specific two-sided support containment
\[
  S_x\subseteq
  \operatorname{Spp}_{\mathrm L}(S_x)\boxtimes
  \operatorname{Spp}_{\mathrm R}(S_x).
\]

This is obtained from the general full-matrix support containment after inserting the canonical
\(L_x\times P_x\) coordinates.

This is the fixed-\(d\) instance of GNVW equation `a2Supp`, arXiv:0910.3675v2,
lines 1211--1219, used for the adjacent pair at lines 1276--1278. Cirac et al.,
arXiv:1703.09188, lines 2322--2328, state only the weaker containment in the left support
algebra tensored with the unrestricted right physical factor. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
theorem evenPairLocalImage_le_support_kroneckerSubmodule
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (evenPairLocalImage hω x).toSubmodule ≤
      Matrix.kroneckerSubmodule (evenSupportAlgebra hω x).toSubmodule
        (oddSupportAlgebra hω x).toSubmodule := by
  simpa only [evenSupportAlgebra, oddSupportAlgebra] using
    Matrix.le_support_kroneckerSubmodule (evenPairLocalImage hω x)

/-! ### Canonical quasi-local embeddings -/

/-- The canonical quasi-local copy of \(\mathcal R_{2x}\subseteq\mathcal A_{L_x}\).

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1261--1278; the canonical
finite-region embedding is the homogeneous quasi-local inclusion in Cirac et al.,
arXiv:1703.09188, lines 2292--2298. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def embeddedEvenSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ (QuasiLocalAlgebra d) :=
  (evenSupportAlgebra hω x).map (matrixToQuasiLocalObservable d (leftPair x))

/-- The canonical quasi-local copy of \(\mathcal R_{2x+1}\subseteq\mathcal A_{P_x}\).

Source context: GNVW, arXiv:0910.3675v2, equation `RR2x`, lines 1261--1278; the canonical
finite-region embedding is the homogeneous quasi-local inclusion in Cirac et al.,
arXiv:1703.09188, lines 2292--2298. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def embeddedOddSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    StarSubalgebra ℂ (QuasiLocalAlgebra d) :=
  (oddSupportAlgebra hω x).map (matrixToQuasiLocalObservable d (rightPair x))

/-- The unified embedded support-algebra family \((\mathcal R_y)_{y\in\mathbb Z}\).

Even indices select the left support of \(S_x\), and odd indices select its right support.

This family is the fixed-\(d\) specialization of GNVW equation `RR2x`, arXiv:0910.3675v2,
lines 1261--1266, under the homogeneous-chain scope stated in the module docstring. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
noncomputable def embeddedSupportAlgebra
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (y : ℤ) :
    StarSubalgebra ℂ (QuasiLocalAlgebra d) :=
  if y % 2 = 0 then embeddedEvenSupportAlgebra hω (y / 2)
  else embeddedOddSupportAlgebra hω (y / 2)

/-- At an even index, the unified family is the embedded left support algebra.

This is the even parity formula in the fixed-\(d\) specialization of GNVW equation `RR2x`,
arXiv:0910.3675v2, lines 1261--1266. See the homogeneous-chain scope statement in the module
docstring. -/
@[simp]
theorem embeddedSupportAlgebra_even
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    embeddedSupportAlgebra hω (2 * x) = embeddedEvenSupportAlgebra hω x := by
  rw [embeddedSupportAlgebra]
  simp

/-- At an odd index, the unified family is the embedded right support algebra.

This is the odd parity formula in the fixed-\(d\) specialization of GNVW equation `RR2x`,
arXiv:0910.3675v2, lines 1261--1266. See the homogeneous-chain scope statement in the module
docstring. -/
@[simp]
theorem embeddedSupportAlgebra_odd
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    embeddedSupportAlgebra hω (2 * x + 1) = embeddedOddSupportAlgebra hω x := by
  rw [embeddedSupportAlgebra]
  simp only [Int.mul_add_emod_self_left, Int.one_emod_two, one_ne_zero, ↓reduceIte]
  congr 1
  rw [show 2 * x + 1 = 1 + x * 2 by ring, Int.add_mul_ediv_right]
  all_goals norm_num

/-- Every element of the unified family at an even index is supported in \(L_x\).

This is the physical localization accompanying the even algebra in GNVW equation `RR2x`,
arXiv:0910.3675v2, lines 1261--1274. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
theorem embeddedSupportAlgebra_even_supportedIn
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r : QuasiLocalAlgebra d} (hr : r ∈ embeddedSupportAlgebra hω (2 * x)) :
    QuasiLocalSupportedIn r (leftPair x) := by
  rw [embeddedSupportAlgebra_even] at hr
  rw [embeddedEvenSupportAlgebra, StarSubalgebra.mem_map] at hr
  rcases hr with ⟨a, _ha, rfl⟩
  exact matrixToQuasiLocalObservable_supportedIn d (leftPair x) a

/-- Every element of the unified family at an odd index is supported in \(P_x\).

This is the physical localization accompanying the odd algebra in GNVW equation `RR2x`,
arXiv:0910.3675v2, lines 1261--1274. See the
[homogeneous-chain scope note](https://sirui-lu.com/TNLean/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.pdf). -/
theorem embeddedSupportAlgebra_odd_supportedIn
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ)
    {r : QuasiLocalAlgebra d} (hr : r ∈ embeddedSupportAlgebra hω (2 * x + 1)) :
    QuasiLocalSupportedIn r (rightPair x) := by
  rw [embeddedSupportAlgebra_odd] at hr
  rw [embeddedOddSupportAlgebra, StarSubalgebra.mem_map] at hr
  rcases hr with ⟨a, _ha, rfl⟩
  exact matrixToQuasiLocalObservable_supportedIn d (rightPair x) a

end PropagatesWithin

end SpinChain

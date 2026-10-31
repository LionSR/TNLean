/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.InverseCompatibleFamilyProperties
import TNLean.MPS.MPU.InverseCompatibleGates
import TNLean.MPS.MPU.InverseCompatibleMovement
import TNLean.MPS.MPU.InverseCompatiblePeriodicComposition
import TNLean.MPS.MPU.ThreeLeggedDecomposition

/-!
# The pleasant properties of the inverse-compatible source decomposition

The second proposition of Appendix `app:Z2` of arXiv:2502.20257
(`main.tex`, lines 5342--5487) asserts that a time-reversal invariant MPU
tensor $\mathcal U$ with sign $\sigma$ admits decompositions
$\mathcal U=X_1Y_1=X_2Y_2$ satisfying the modified compatibility relations
`eq:modif_XY`,
$$
  X_1=(I_d\otimes T^*)Y_2^\dagger,\qquad Y_1=X_2^\dagger(T^T\otimes I_d),
$$
such that "the pleasant properties" `eq:3-leg`--`eq:thm1c`,
`eq:wLR`--`eq:MPUnice2` and `eq:MPUnice3`--`eq:MPUnice4` hold.  This file
turns that collective phrase into the explicit list
`MPOTensor.SourceFactors.PleasantProperties`, with one field (or one field of
`MPOTensor.SourceFactors`) for each displayed equation:

* `eq:3-leg`, $\mathcal M_1=X_1Y_1$ and $\mathcal M_2=X_2Y_2$: the fields
  `sourceCutM₁_eq` and `sourceCutM₂_eq` of `MPOTensor.SourceFactors`;
* `eq:uv`, unitarity of $u$ and $v$: `sourceU_isUnitaryBetween` and
  `sourceV_isUnitaryBetween` of `MPOTensor.SourceFactors.IsThreeLegged`;
* `eq:thm1c`, $X_2^\dagger X_2=\Id$ and $X_1^\dagger(I_d\otimes\rho)X_1=\Id$:
  the fields `X₂_isometry` and `X₁_weighted_isometry` of `MPOTensor.SourceFactors`;
* line 809, $d_ld_r=d^2$: `leftRank_mul_rightRank`;
* `eq:wLR`, unitarity of $w_L$ and $w_R$: `sourceWL_isUnitaryBetween` and
  `sourceWR_isUnitaryBetween`;
* `eq:MPUnice2`, the two physical $Y$ closures: `Y₁_physical_contraction` and
  `Y₂_physical_contraction`;
* `eq:MPUnice3`, $Y_1Y_1^\dagger=\frac d{d_r}\Id$ and
  $Y_2(I_d\otimes\rho)Y_2^\dagger=\frac d{d_l}\Id$: `Y₁_mul_conjTranspose` and
  `Y₂_weighted_mul_conjTranspose`;
* `eq:MPUnice4`, the two physical $X$ closures: `X₁_physical_contraction` and
  `X₂_physical_contraction`.

The chosen compact-SVD factors of a simple MPU in canonical form II satisfy
the list (arXiv:2502.20257, Theorem `thm:mpu`, Corollary `cor:mpu` and
Proposition `prop:MPUsplus`), and so do the inverse-compatible factors of the
appendix.  The adjoint-simplicity premise of `prop:MPUsplus` and of the appendix
is not added: in canonical form II it follows from simplicity
(`MPOTensor.IsMPUCanonicalFormII.isMPUSimple_physicalAdjointTensor`).

The same proposition asserts the truncated-chain identity `eq:UUU`,
$U^LU^\infty=\sigma U^{\infty-L}$.  On a ring of $n+m+2$ sites in the order
$(a,p,b,q)$, with $p$ of length $n$ and $q$ of length $m$, the truncated
symmetry $U^L$ of `eq:truncsym` has total length $L=n+2$ and endpoint sites
$a,b$.  The product $U^LU^\infty$ acts trivially on $p$ and outputs endpoint
legs at $a$ and $b$, so the complementary truncated symmetry has bulk $q$ and
the same two endpoint sites, traversed from $b$ to $a$: its total length is
$m+2$, two more than the printed $\infty-L$
(`docs/paper-gaps/fbc25_complementary_truncation_shared_endpoints.tex`).
**Local fix (complementary length):** the equation is stated with this
complementary truncated symmetry
(`MPOTensor.SourceFactors.complementaryTruncatedSymmetry`); the leg of $U^L$ at
$a$ (dimension $d_l$) is matched with the leg of the complement at $a$
(dimension $d_r$) along the proved equality $d_l=d_r$.

## Main definitions

* `MPOTensor.SourceFactors.PleasantProperties`: the pleasant properties of
  supplied source factors.
* `MPOTensor.SourceFactors.complementaryTruncatedSymmetry`: the truncated
  symmetry on the complementary arc of a ring, as an operator on the whole ring.

## Main results

* `MPOTensor.IsMPUCanonicalFormII.sourceFactors_pleasantProperties`: the chosen source
  factors of a simple MPU in canonical form II have the pleasant properties.
* `MPOTensor.inverseCompatibleSourceFactors_pleasantProperties`: the inverse-compatible
  source factors have the pleasant properties.
* `MPOTensor.inverseCompatibleSourceFactors_truncatedSymmetry_mul_groupedMPO`:
  `eq:UUU` for the inverse-compatible source factors.
* `MPOTensor.exists_inverseCompatible_pleasantProperties`: the appendix
  proposition, including `eq:UUU`, for a tensor whose physical adjoint is
  carried by a unitary gauge $T$ with $T\overline T=\sigma\Id$.
* `MPOTensor.GroupFamily.IsRepresentation.exists_inverseCompatible_pleasantProperties_of_inv_eq`:
  the same at an involutive element of a canonical representation, with the chosen
  dagger-inverse gauge and sign.
-/

open scoped ComplexOrder Matrix Kronecker BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}

namespace SourceFactors

/-- **The pleasant properties** of supplied source factors $X_1,Y_1,X_2,Y_2$,
the collective hypothesis named in the second proposition of Appendix `app:Z2`
of arXiv:2502.20257 (lines 5342--5350).

The equations `eq:3-leg` and `eq:thm1c` and the one-sided inverses are fields
of `MPOTensor.SourceFactors`; `eq:uv` and the dimension identity of line 809 are
the fields of `MPOTensor.SourceFactors.IsThreeLegged`.  The remaining fields
are, in order:

* `eq:wLR` (Corollary `cor:mpu`(a), lines 811--869): the gates
  $w_L=Y_2\mathbin{-}X_2$ and $w_R=X_1\mathbin{-}Y_1$ are unitary;
* `eq:MPUnice2` (Corollary `cor:mpu`(b), lines 870--914): the physical
  closures of $Y_1$ and of $Y_2$ weighted by $\rho$ are the identity;
* `eq:MPUnice3` (Proposition `prop:MPUsplus`, lines 1067--1116):
  $Y_1Y_1^\dagger=\frac{d}{d_r}\Id$ and
  $Y_2(I_d\otimes\rho)Y_2^\dagger=\frac{d}{d_l}\Id$;
* `eq:MPUnice4` (Proposition `prop:MPUsplus`, lines 1117--1160): the physical
  closures of $X_1$ weighted by $\rho$ and of $X_2$ are $\frac{d_r}{d}\Id$ and
  $\frac{d_l}{d}\Id$. -/
structure PleasantProperties (S : SourceFactors U ρ) : Prop extends S.IsThreeLegged where
  /-- The left staircase gate $w_L$ is unitary (`eq:wLR`). -/
  sourceWL_isUnitaryBetween : (sourceWL U S).IsUnitaryBetween
  /-- The right staircase gate $w_R$ is unitary (`eq:wLR`). -/
  sourceWR_isUnitaryBetween : (sourceWR U S).IsUnitaryBetween
  /-- The physical closure of $Y_1$ is the identity (`eq:MPUnice2`). -/
  Y₁_physical_contraction : ∀ p q : Fin d,
    (∑ r : Fin r[U], ∑ α : Fin D, star (S.Y₁ r (α, p)) * S.Y₁ r (α, q)) =
      if p = q then 1 else 0
  /-- The physical closure of $Y_2$ weighted by $\rho$ is the identity (`eq:MPUnice2`). -/
  Y₂_physical_contraction : ∀ p q : Fin d,
    (∑ l : Fin ℓ[U], ∑ α : Fin D, ∑ β : Fin D,
      star (S.Y₂ l (p, α)) * S.Y₂ l (q, β) * ρ β α) = if p = q then 1 else 0
  /-- The curly-leg normalization $Y_1Y_1^\dagger=\frac d{d_r}\Id$ (`eq:MPUnice3`). -/
  Y₁_mul_conjTranspose : S.Y₁ * S.Y₁ᴴ = ((d : ℂ) / (r[U] : ℂ)) • 1
  /-- The thick-leg normalization $Y_2(I_d\otimes\rho)Y_2^\dagger=\frac d{d_l}\Id$
  (`eq:MPUnice3`). -/
  Y₂_weighted_mul_conjTranspose :
    S.Y₂ * sourceWeight (d := d) ρ * S.Y₂ᴴ = ((d : ℂ) / (ℓ[U] : ℂ)) • 1
  /-- The physical closure of $X_1$ weighted by $\rho$ is $\frac{d_r}{d}\Id$
  (`eq:MPUnice4`). -/
  X₁_physical_contraction : ∀ i j : Fin d,
    (∑ r : Fin r[U], ∑ α : Fin D, ∑ β : Fin D,
      S.X₁ (i, α) r * ρ β α * star (S.X₁ (j, β) r)) =
        ((r[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0)
  /-- The physical closure of $X_2$ is $\frac{d_l}{d}\Id$ (`eq:MPUnice4`). -/
  X₂_physical_contraction : ∀ i j : Fin d,
    (∑ l : Fin ℓ[U], ∑ x : Fin D, S.X₂ (x, i) l * star (S.X₂ (x, j) l)) =
      ((ℓ[U] : ℂ) / (d : ℂ)) * (if i = j then 1 else 0)

/-- **The complementary truncated symmetry** $U^{\infty-L}$ of `eq:UUU`, as an
operator on a ring of $n+m+2$ sites grouped as $((a,p,b),q)$, with $p$ of
length $n$ and $q$ of length $m$.  It is the identity on $p$ and the truncated
symmetry of `eq:truncsym` with bulk $q$ and endpoint sites $b$ (thick leg) and
$a$ (curly leg).  Its rows are grouped as those of $U^L\otimes I_q$, where
$U^L$ has endpoint sites $a$ (thick leg) and $b$ (curly leg); the two legs at
each endpoint site are matched along `e`.

The printed length $\infty-L$ is two short: the complementary truncated
symmetry shares both endpoint sites with $U^L$, and has total length $m+2$
(`docs/paper-gaps/fbc25_complementary_truncation_shared_endpoints.tex`).

Source: arXiv:2502.20257, `eq:complementary` (lines 2175--2181) and `eq:UUU`
(lines 5344--5348). -/
noncomputable def complementaryTruncatedSymmetry (S : SourceFactors U ρ)
    (e : Fin ℓ[U] ≃ Fin r[U]) (n m : ℕ) :
    Matrix ((Fin ℓ[U] × ((Fin n → Fin d) × Fin r[U])) × (Fin m → Fin d))
      ((Fin d × ((Fin n → Fin d) × Fin d)) × (Fin m → Fin d)) ℂ :=
  fun ((l, p, t), q) ((a, p', b), q') ↦
    (if p = p' then 1 else 0) * S.truncatedSymmetry m (e.symm t, q, e l) (b, q', a)

end SourceFactors

/-- **The pleasant properties of the chosen source factors.** For a simple MPU
tensor in canonical form II, the compact-SVD source factors at the recorded fixed
point $\rho$ satisfy every pleasant property.

This collects arXiv:2502.20257, Theorem `thm:mpu`, Corollary `cor:mpu` and
Proposition `prop:MPUsplus` (lines 657--1160).  The adjoint-simplicity premise of
`prop:MPUsplus` is derived from canonical form II, not assumed. -/
theorem IsMPUCanonicalFormII.sourceFactors_pleasantProperties
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) :
    (sourceFactors U hU.ρ hU.ρ_posDef).PleasantProperties := by
  have hadjoint := hU.isMPUSimple_physicalAdjointTensor hsimple
  obtain ⟨hL, hR⟩ := hU.sourceWL_sourceWR_isUnitaryBetween hsimple
  exact
    { toIsThreeLegged := hU.sourceFactors_isThreeLegged hsimple
      sourceWL_isUnitaryBetween := hL
      sourceWR_isUnitaryBetween := hR
      Y₁_physical_contraction := hU.sourceY₁_physical_contraction hsimple
      Y₂_physical_contraction := hU.sourceY₂_physical_contraction hsimple
      Y₁_mul_conjTranspose := hU.sourceY₁_mul_conjTranspose hsimple hadjoint
      Y₂_weighted_mul_conjTranspose :=
        hU.sourceY₂_weighted_mul_conjTranspose hsimple hadjoint
      X₁_physical_contraction := hU.sourceX₁_physical_contraction hsimple hadjoint
      X₂_physical_contraction := hU.sourceX₂_physical_contraction hsimple hadjoint }

variable (U) (T : Matrix.unitaryGroup (Fin D) ℂ)
  (hT : ∀ i j, physicalAdjointTensor U i j =
    (T : Matrix (Fin D) (Fin D) ℂ)ᴴ * U i j * T)

/-- The gate $u$ of the inverse-compatible record is the literal new gate
$Y_2\mathbin{-}Y$ with its first-rank coordinate transported along the rank
equivalence. Source: arXiv:2502.20257, lines 5390--5432 and 5486--5487. -/
theorem sourceU_inverseCompatibleSourceFactors (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    SourceFactors.sourceU U (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ) =
      Matrix.reindex ((Equiv.refl _).prodCongr (inverseCompatibleRankEquiv U T hT))
        (Equiv.refl _) (inverseCompatibleU U T) := by
  ext ⟨l, r⟩ ⟨i, j⟩
  rfl

/-- The gate $v$ of the inverse-compatible record is the literal new gate
$X\mathbin{-}X_2$ with its first-rank coordinate transported along the rank
equivalence. Source: arXiv:2502.20257, lines 5390--5432 and 5486--5487. -/
theorem sourceV_inverseCompatibleSourceFactors (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    SourceFactors.sourceV U (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ) =
      Matrix.reindex (Equiv.refl _)
        ((inverseCompatibleRankEquiv U T hT).prodCongr (Equiv.refl _))
        (inverseCompatibleV U T) := by
  ext ⟨i, j⟩ ⟨r, l⟩
  rfl

/-- **`eq:UUU`** (arXiv:2502.20257, Appendix `app:Z2`, second proposition,
lines 5344--5348): $U^LU^\infty=\sigma\,U^{\infty-L}$ for the inverse-compatible
source factors.  Let $\mathcal U$ be a simple tensor in canonical form II whose
physical adjoint is $T^\dagger\mathcal U T$ for a unitary $T$ with
$T\overline T=\sigma\Id$.  On the ring of $n+m+2$ sites in the order
$(a,p,b,q)$, the truncated symmetry $U^{n+2}$ on the sites $(a,p,b)$, extended
by the identity on $q$, composed with the periodic operator $U^\infty$ on the
whole ring, is $\sigma$ times the complementary truncated symmetry, the
identity on $p$ and the truncated symmetry on the sites $(b,q,a)$.  Here
$\mathcal U=\mathcal U^\dagger$ up to the gauge, so $U^\infty_{g^{-1}}=U^\infty_g$.

**Local fix (complementary length):** the complementary truncated symmetry
shares the endpoint sites $a,b$ with $U^{n+2}$, so its total length is $m+2$,
not the printed $\infty-L=m$
(`docs/paper-gaps/fbc25_complementary_truncation_shared_endpoints.tex`).

The proof is the contraction the source leaves to the reader: the periodic
operator factors through the two arcs
(`MPOTensor.inverseCompatibleGroupedMPO_eq_wordB_mul_complementaryArc`), and the
endpoint words cancel to $\sigma$
(`MPOTensor.inverseCompatibleFirstArcEmbedding_mul_groupedMPO`). -/
theorem inverseCompatibleSourceFactors_truncatedSymmetry_mul_groupedMPO
    (hU : IsMPUCanonicalFormII U) (hsimple : IsMPUSimple U) (σ : ℂ)
    (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) (n m : ℕ) :
    ((inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).truncatedSymmetry n ⊗ₖ
        (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) * inverseCompatibleGroupedMPO U n m =
      σ • (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).complementaryTruncatedSymmetry
        (inverseCompatibleRankEquiv U T hT) n m := by
  classical
  set S := inverseCompatibleSourceFactors U T hU hsimple hT σ hσ
  set e := inverseCompatibleRankEquiv U T hT
  have hA (N : ℕ) (l : Fin ℓ[U]) (p : Fin N → Fin d) (s : Fin ℓ[U])
      (x : Fin d × ((Fin N → Fin d) × Fin d)) :
      inverseCompatibleWordA U T N (l, p, s) x = S.truncatedSymmetry N (l, p, e s) x := by
    have h := congrFun (congrFun
      (inverseCompatibleWordA_eq_reindex_truncatedSymmetry U T hU hsimple hT σ hσ N)
      (l, p, s)) x
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h
  have key := inverseCompatibleFirstArcEmbedding_mul_groupedMPO U T hU hsimple hT σ hσ n m
  ext ⟨⟨l, p, t⟩, q⟩ ⟨⟨a, p', b⟩, q'⟩
  calc _ = (inverseCompatibleFirstArcEmbedding U T n m * inverseCompatibleGroupedMPO U n m)
        ((l, p, e.symm t), q) ((a, p', b), q') := by
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨x₁, x₂⟩ := x
        simp only [inverseCompatibleFirstArcEmbedding, Matrix.kroneckerMap_apply, hA,
          Equiv.apply_symm_apply]
    _ = _ := by
        rw [key]
        simp only [Matrix.smul_apply, inverseCompatibleComplementaryArc,
          SourceFactors.complementaryTruncatedSymmetry, hA, smul_eq_mul]

/-- **The pleasant properties of the inverse-compatible source factors.** Let
$\mathcal U$ be a simple tensor in canonical form II whose physical adjoint is
$T^\dagger\mathcal U T$ for a unitary $T$ with $T\overline T=\sigma\Id$.  The
inverse-compatible factors $X_1=(I_d\otimes T^*)Y_2^\dagger$,
$Y_1=X_2^\dagger(T^T\otimes I_d)$, $X_2$, $Y_2$ have every pleasant property.

The proof is the transport of arXiv:2502.20257, lines 5486--5487: the new gates
are unitary (`MPOTensor.inverseCompatibleGates_unitary_and_phase`), the staircase
gates and the closures are transported by the unitary comparison, and the second
factors are unchanged. -/
theorem inverseCompatibleSourceFactors_pleasantProperties (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    (inverseCompatibleSourceFactors U T hU hsimple hT σ hσ).PleasantProperties := by
  have hadjoint := hU.isMPUSimple_physicalAdjointTensor hsimple
  obtain ⟨hu, hv, -⟩ := inverseCompatibleGates_unitary_and_phase U T hU hsimple hT σ hσ
  obtain ⟨hL, hR⟩ :=
    inverseCompatibleSourceFactors_movement_isUnitaryBetween U T hU hsimple hT σ hσ
  have hY := inverseCompatibleSourceFactors_Y_physical_contractions U T hU hsimple hT σ hσ
  have hYrank :=
    inverseCompatibleSourceFactors_Y_rank_normalizations U T hU hsimple hT σ hσ hadjoint
  have hX :=
    inverseCompatibleSourceFactors_X_physical_contractions U T hU hsimple hT σ hσ hadjoint
  exact
    { leftRank_mul_rightRank := (hU.sourceFactors_isThreeLegged hsimple).leftRank_mul_rightRank
      sourceU_isUnitaryBetween := by
        rw [sourceU_inverseCompatibleSourceFactors]
        exact hu.reindex _ _ _
      sourceV_isUnitaryBetween := by
        rw [sourceV_inverseCompatibleSourceFactors]
        exact hv.reindex _ _ _
      sourceWL_isUnitaryBetween := hL
      sourceWR_isUnitaryBetween := hR
      Y₁_physical_contraction := fun p q ↦ (hY p q).1
      Y₂_physical_contraction := fun p q ↦ (hY p q).2
      Y₁_mul_conjTranspose := hYrank.1
      Y₂_weighted_mul_conjTranspose := hYrank.2
      X₁_physical_contraction := fun i j ↦ (hX i j).1
      X₂_physical_contraction := fun i j ↦ (hX i j).2 }

/-- **The inverse-compatible decomposition** (arXiv:2502.20257, Appendix `app:Z2`,
second proposition, lines 5342--5350).  Let $\mathcal U$ be a
simple tensor in canonical form II whose physical adjoint is
$T^\dagger\mathcal U T$ for a unitary $T$ with $T\overline T=\sigma\Id$.  Then
there are source factors $X_1,Y_1,X_2,Y_2$ with all the pleasant properties that
satisfy the modified compatibility relations `eq:modif_XY`,
$$
  X_1=(I_d\otimes T^*)Y_2^\dagger,\qquad Y_1=X_2^\dagger(T^T\otimes I_d),
$$
where the intermediate space of the right-hand sides, of dimension $d_l$, is
identified with that of $X_1,Y_1$, of dimension $d_r$, along the proved
equality $d_r=d_l$.  Moreover the truncated symmetries of these factors satisfy
`eq:UUU`, $U^LU^\infty=\sigma U^{\infty-L}$, on every ring, in the form of
`MPOTensor.inverseCompatibleSourceFactors_truncatedSymmetry_mul_groupedMPO`.

The adjoint-simplicity premise of the source is derived from canonical form II.
The right dressing is written $T^T\otimes I_d$ because the first source cut
carries its column index in (virtual, physical) order; see
`docs/paper-gaps/mpu_source_cut_orientation.tex`.  **Local fix (complementary
length):** the complementary truncated symmetry of `eq:UUU` shares its two
endpoint sites with $U^L$
(`docs/paper-gaps/fbc25_complementary_truncation_shared_endpoints.tex`). -/
theorem exists_inverseCompatible_pleasantProperties (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (σ : ℂ) (hσ : (T : Matrix (Fin D) (Fin D) ℂ) *
      (T : Matrix (Fin D) (Fin D) ℂ).map (starRingEnd ℂ) = σ • 1) :
    ∃ S : SourceFactors U hU.ρ, S.PleasantProperties ∧
      S.X₁ = Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv U T hT)
        (inverseCompatibleLeftGauge (d := d) T * S.Y₂ᴴ) ∧
      S.Y₁ = Matrix.reindex (inverseCompatibleRankEquiv U T hT) (Equiv.refl _)
        (S.X₂ᴴ * inverseCompatibleRightGauge (d := d) T) ∧
      ∀ n m : ℕ, (S.truncatedSymmetry n ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) *
          inverseCompatibleGroupedMPO U n m =
        σ • S.complementaryTruncatedSymmetry (inverseCompatibleRankEquiv U T hT) n m :=
  ⟨inverseCompatibleSourceFactors U T hU hsimple hT σ hσ,
    inverseCompatibleSourceFactors_pleasantProperties U T hT hU hsimple σ hσ, rfl, rfl,
    inverseCompatibleSourceFactors_truncatedSymmetry_mul_groupedMPO U T hT hU hsimple σ hσ⟩

namespace GroupFamily

/-- **The inverse-compatible decomposition at an involutive element**
(arXiv:2502.20257, Appendix `app:Z2`, second proposition, lines 5342--5350).
For an element $g=g^{-1}$ of a representation whose tensors have left-canonical
normalized flattenings, and whose tensor $\mathcal U_g$ is in canonical form II,
the chosen dagger-inverse gauge $T_g$ and sign $\sigma_g$ of `eq:defT` and
`eq:intro_sigma` give source factors with all the pleasant properties satisfying
`eq:modif_XY` and `eq:UUU`.

Simplicity is part of the representation; simplicity of the adjoint is derived
from canonical form II.  **Local fix (complementary length):** as in
`MPOTensor.exists_inverseCompatible_pleasantProperties`
(`docs/paper-gaps/fbc25_complementary_truncation_shared_endpoints.tex`). -/
theorem IsRepresentation.exists_inverseCompatible_pleasantProperties_of_inv_eq
    {G : Type*} [Group G] {d : ℕ} (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) (hU : IsMPUCanonicalFormII (F.tensor g)) :
    let T := hF.daggerInverseGauge F hcanonical g
    let hT := hF.physicalAdjointTensor_eq_daggerInverseGauge_of_inv_eq F hcanonical g hg
    ∃ S : SourceFactors (F.tensor g) hU.ρ, S.PleasantProperties ∧
      S.X₁ = Matrix.reindex (Equiv.refl _) (inverseCompatibleRankEquiv (F.tensor g) T hT)
        (inverseCompatibleLeftGauge (d := d) T * S.Y₂ᴴ) ∧
      S.Y₁ = Matrix.reindex (inverseCompatibleRankEquiv (F.tensor g) T hT) (Equiv.refl _)
        (S.X₂ᴴ * inverseCompatibleRightGauge (d := d) T) ∧
      ∀ n m : ℕ, (S.truncatedSymmetry n ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ)) *
          inverseCompatibleGroupedMPO (F.tensor g) n m =
        hF.daggerInverseScalar F hcanonical g •
          S.complementaryTruncatedSymmetry (inverseCompatibleRankEquiv (F.tensor g) T hT) n m :=
  exists_inverseCompatible_pleasantProperties (F.tensor g) _ _ hU (hF.isSimple g) _
    (hF.daggerInverseGauge_mul_mapStar_self_eq_smul_one_of_inv_eq F hcanonical g hg)

end GroupFamily

end MPOTensor

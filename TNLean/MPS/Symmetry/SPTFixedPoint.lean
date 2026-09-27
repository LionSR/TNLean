/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import TNLean.Algebra.ComplexSqrt
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.RFP.Defs
import TNLean.MPS.Symmetry.CocycleCoboundary
import TNLean.MPS.Symmetry.VirtualRepresentation

/-!
# SPT fixed points: the zero-correlation-length MPS of a projective representation

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
paragraph "Symmetry protected topological order",
`Papers/2011.12127/TN-Review-main.tex` lines 1147–1157: within each SPT phase "a
representative MPS with zero correlation length can be constructed starting from any
solution of the 1- and 2-cocycle condition"; the source then prints such a tensor on
the physical space `ℂ^G ⊗ ℂ^G` and the bond space `ℂ^G`, states that its symmetry
relation `S_g(A) = e^{iφ(g)} X_g† A X_g` is equivalent to the 2-cocycle equation, and
that its transfer matrix is a rank-one projector.

**Formalized here.** For a projective representation `ρ` of `G` on `ℂ^D` with factor
system `ω` and a character `φ : G →* ℂ`, the tensor with physical space `ℂ^D ⊗ ℂ^D`
and letters `A^{(a,b)} = D^{-1/2} |a⟩⟨b|` is the renormalization fixed point in the
phase of `[ω]`:
* its transfer map is `X ↦ D⁻¹ tr(X) · 1`, a rank-one projector, so the tensor has
  zero correlation length; the tensor is injective, hence normal;
* the linear representation `U(g) = φ(g) (W_gᵀ ⊗ W_g⁻¹)`, `W_g = ρ(g⁻¹)`, of `G` on
  the physical space satisfies `∑ⱼ U(g)ᵢⱼ Aʲ = φ(g) W_g Aⁱ W_g⁻¹`; the phases of `ρ`
  cancel in `U` exactly because they obey the 2-cocycle equation;
* for `φ = 1` the tensor is on-site symmetric, and every virtual representation it
  induces has factor system cohomologous to `ω`.

**Local fix (fixed-point tensor):** the printed tensor
`A^{ab}_{xy} = e^{i(ω(a,x) + φ(b))} δ_{y,ax}` has letters proportional to the twisted
left-regular matrices, which commute with the printed gauges; it is not normal and its
transfer map is not of rank one for nontrivial `G`.  The construction here is the
dimer fixed point that the printed claims describe; documented in
`docs/paper-gaps/rmp_spt_fixed_point_tensor.tex`.

**Scope restriction (supplied projective representation):** the source starts from a
2-cocycle `ω` alone, while the symmetry results here (`sptFixedPointAction`,
`twistedTensor_sptFixedPointTensor`, `sptFixedPointTensor_isOnSiteSymmetric`,
`cohomologousTo_of_sptFixedPointTensor`, `exists_virtualRep_sptFixedPointTensor`) take a
projective representation `ρ` with factor system `ω` as input; the transfer, injectivity
and normality results do not involve `ρ`. The existence of such a `ρ` for finite `G`, for
instance the twisted regular representation on `ℂ^G`, is not formalized; documented in
`docs/paper-gaps/rmp_spt_fixed_point_supplied_representation.tex`.

**Scope restriction (trivial character):** the source's symmetry
`S_g(A) = e^{iφ(g)} X_g† A X_g` carries the phase of a 1-cocycle `φ`, while
`sptFixedPointTensor_isOnSiteSymmetric`, `cohomologousTo_of_sptFixedPointTensor` and
`exists_virtualRep_sptFixedPointTensor` are stated for `φ = 1`; for nontrivial `φ` only
the twist identity `twistedTensor_sptFixedPointTensor` is proved, since
`IsOnSiteSymmetric` asks for equal matrix product vectors and the twist multiplies the
vector on `N` sites by `φ(g)^N`. Documented in
`docs/paper-gaps/rmp_spt_fixed_point_trivial_character.tex`.

## Main definitions

* `MPSTensor.sptFixedPointTensor` : the letters `D^{-1/2} |a⟩⟨b|`
* `MPSTensor.sptFixedPointAction` : the physical representation `φ(g) (W_gᵀ ⊗ W_g⁻¹)`

## Main results

* `MPSTensor.transferMap_sptFixedPointTensor`
* `MPSTensor.sptFixedPointTensor_isTransferIdempotent`
* `MPSTensor.finrank_range_transferMap_sptFixedPointTensor`
* `MPSTensor.sptFixedPointTensor_isInjective`, `MPSTensor.sptFixedPointTensor_isNormal`
* `MPSTensor.eq_of_sum_smul_sptFixedPointTensor_eq`
* `MPSTensor.twistedTensor_sptFixedPointTensor`
* `MPSTensor.sptFixedPointTensor_isOnSiteSymmetric`
* `MPSTensor.cohomologousTo_of_sptFixedPointTensor`
* `MPSTensor.exists_virtualRep_sptFixedPointTensor`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPSTensor

open TNLean.Algebra

variable {D : ℕ}

/-- The pair of bond labels `(a, b)` encoded by a physical index of `ℂ^D ⊗ ℂ^D`. -/
abbrev sptPair (i : Fin (D * D)) : Fin D × Fin D := finProdFinEquiv.symm i

/-- The normalization `D^{-1/2}` of the letters. -/
abbrev sptScale (D : ℕ) : ℂ := ((Real.sqrt D : ℂ))⁻¹

lemma star_sptScale_mul_sptScale : star (sptScale D) * sptScale D = (D : ℂ)⁻¹ := by
  rw [sptScale, star_inv₀, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg D), Complex.ofReal_natCast]

private lemma sptScale_ne_zero [NeZero D] : sptScale D ≠ 0 := by
  refine inv_ne_zero (Complex.ofReal_ne_zero.mpr ((Real.sqrt_ne_zero').mpr ?_))
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)

/-- **The SPT fixed-point tensor.** The letter at the physical index `(a, b)` is
`D^{-1/2} |a⟩⟨b|`.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1149–1150), with the local fix of the
module docstring. -/
def sptFixedPointTensor (D : ℕ) : MPSTensor (D * D) D := fun i =>
  sptScale D • Matrix.single (sptPair i).1 (sptPair i).2 1

private lemma sum_pair {M : Type*} [AddCommMonoid M] (f : Fin D × Fin D → M) :
    ∑ i : Fin (D * D), f (sptPair i) = ∑ a : Fin D, ∑ b : Fin D, f (a, b) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)

/-- **The transfer map is `X ↦ D⁻¹ tr(X) · 1`.** Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157): the transfer matrix is a
rank-one projector. -/
theorem transferMap_sptFixedPointTensor (X : Matrix (Fin D) (Fin D) ℂ) :
    Kraus.transferMap (sptFixedPointTensor D) X = ((D : ℂ)⁻¹ * X.trace) • 1 := by
  classical
  rw [Kraus.transferMap_apply]
  ext x y
  simp only [sptFixedPointTensor, Matrix.conjTranspose_smul, Matrix.conjTranspose_single,
    star_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.single_mul_mul_single,
    one_mul, mul_one, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [sum_pair (fun p => star (sptScale D) * sptScale D * Matrix.single p.1 p.1 (X p.2 p.2) x y)]
  simp only [star_sptScale_mul_sptScale, Matrix.single_apply, Matrix.one_apply, Matrix.trace,
    Matrix.diag_apply]
  by_cases hxy : x = y
  · subst hxy
    simp [Finset.mul_sum]
  · simp only [hxy, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff.mpr fun ha => absurd (ha.1.symm.trans ha.2) hxy, mul_zero]

/-- **The transfer map is idempotent.** Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157). -/
theorem sptFixedPointTensor_isTransferIdempotent :
    IsTransferIdempotent (sptFixedPointTensor D) := by
  rcases eq_or_ne D 0 with rfl | hD
  · ext X : 1; exact Subsingleton.elim _ _
  ext X : 1
  simp only [LinearMap.comp_apply, transferMap_sptFixedPointTensor, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  congr 1
  field_simp

/-- **The transfer map has rank one.** For `D > 0` its range is the line spanned by
the identity.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` line 1157). -/
theorem finrank_range_transferMap_sptFixedPointTensor [NeZero D] :
    Module.finrank ℂ (LinearMap.range (Kraus.transferMap (sptFixedPointTensor D))) = 1 := by
  have hrange : LinearMap.range (Kraus.transferMap (sptFixedPointTensor D)) =
      Submodule.span ℂ {(1 : Matrix (Fin D) (Fin D) ℂ)} := by
    apply le_antisymm
    · rintro _ ⟨X, rfl⟩
      rw [transferMap_sptFixedPointTensor]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨1, ?_⟩
      rw [transferMap_sptFixedPointTensor, Matrix.trace_one, Fintype.card_fin,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne D)), one_smul]
  rw [hrange, finrank_span_singleton one_ne_zero]

/-- **The fixed-point tensor is injective**: its letters are nonzero multiples of
the matrix units.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1149–1157), the fixed point whose
transfer matrix is a rank-one projector. -/
theorem sptFixedPointTensor_isInjective [NeZero D] :
    Kraus.IsInjective (sptFixedPointTensor D) := by
  classical
  have hc : sptScale D ≠ 0 := sptScale_ne_zero
  refine Submodule.eq_top_of_forall_single_mem _ fun a b => ?_
  have hmem : sptFixedPointTensor D (finProdFinEquiv (a, b)) ∈
      Submodule.span ℂ (Set.range (sptFixedPointTensor D)) := Submodule.subset_span ⟨_, rfl⟩
  have := Submodule.smul_mem _ (sptScale D)⁻¹ hmem
  rw [show sptFixedPointTensor D (finProdFinEquiv (a, b)) =
      sptScale D • Matrix.single a b 1 by simp [sptFixedPointTensor], smul_smul,
    inv_mul_cancel₀ hc, one_smul] at this
  exact this

/-- **The fixed-point tensor is normal.**  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1149–1157). -/
theorem sptFixedPointTensor_isNormal [NeZero D] : Kraus.IsNormal (sptFixedPointTensor D) :=
  sptFixedPointTensor_isInjective.isNormal

/-- The entry `(a, b)` of a linear combination of the letters is `D^{-1/2}` times the
coefficient of the letter `(a, b)`. -/
theorem sum_smul_sptFixedPointTensor_apply (c : Fin (D * D) → ℂ) (a b : Fin D) :
    (∑ j, c j • sptFixedPointTensor D j) a b = sptScale D * c (finProdFinEquiv (a, b)) := by
  classical
  rw [← finProdFinEquiv.sum_comp]
  simp [Matrix.sum_apply, sptFixedPointTensor, Matrix.single_apply, Fintype.sum_prod_type,
    ite_and, mul_comm]

/-- **The letters are linearly independent**: for `D > 0` a linear combination of the
letters determines its coefficients. -/
theorem eq_of_sum_smul_sptFixedPointTensor_eq [NeZero D] {c c' : Fin (D * D) → ℂ}
    (h : ∑ j, c j • sptFixedPointTensor D j = ∑ j, c' j • sptFixedPointTensor D j) :
    c = c' := by
  have hc : sptScale D ≠ 0 := sptScale_ne_zero
  funext j
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective j
  have hab := congrFun (congrFun h a) b
  rw [sum_smul_sptFixedPointTensor_apply, sum_smul_sptFixedPointTensor_apply] at hab
  exact mul_left_cancel₀ hc hab

/-! ### The physical symmetry -/

section Symmetry

variable {G : Type*} [Group G] {ω : ScalarCocycle G}

/-- The virtual gauge `W_g = ρ(g⁻¹)` of the physical symmetry `g`.  Source:
arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` lines 1152–1155), the
gauge matrices `X_g` of the fixed-point construction. -/
abbrev sptGauge (ρ : ProjectiveRepresentation (D := D) ω) (g : G) : GL (Fin D) ℂ :=
  ρ.X g⁻¹

/-- The operator `W_gᵀ ⊗ W_g⁻¹` on `ℂ^D ⊗ ℂ^D`, the factor of the physical action
`U(g) = φ(g) (W_gᵀ ⊗ W_g⁻¹)`.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1149–1157), with the local fix of the
module docstring. -/
def sptKron (W : GL (Fin D) ℂ) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (W : Matrix (Fin D) (Fin D) ℂ)ᵀ ⊗ₖ ((W⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)

/-- Scalars cancel in `W ↦ Wᵀ ⊗ W⁻¹`. -/
private lemma sptKron_eq_of_eq_smul {W V : GL (Fin D) ℂ} {c : ℂ}
    (h : (W : Matrix (Fin D) (Fin D) ℂ) = c • (V : Matrix (Fin D) (Fin D) ℂ)) :
    sptKron W = sptKron V := by
  classical
  rcases eq_or_ne D 0 with rfl | hD
  · exact Subsingleton.elim _ _
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 := congrArg (· * ((W⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) h
    simp only [Units.mul_inv, zero_smul, Matrix.zero_mul] at h1
    have : NeZero D := ⟨hD⟩
    exact one_ne_zero h1
  have hinv : ((W⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      c⁻¹ • ((V⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    have h1 : (c⁻¹ • ((V⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
        (W : Matrix (Fin D) (Fin D) ℂ) = 1 := by
      rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
        Units.inv_mul]
    calc ((W⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
        = (c⁻¹ • ((V⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
            (W : Matrix (Fin D) (Fin D) ℂ) * ((W⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ) := by
          rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [sptKron, sptKron, h, hinv, Matrix.transpose_smul, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

private lemma sptKron_mul (W V : GL (Fin D) ℂ) : sptKron W * sptKron V = sptKron (V * W) := by
  rw [sptKron, sptKron, sptKron, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
    mul_inv_rev]
  rfl

private lemma sptKron_one : sptKron (1 : GL (Fin D) ℂ) = 1 := by
  simp [sptKron]

/-- The physical representation `U(g) = φ(g) (W_gᵀ ⊗ W_g⁻¹)` on `ℂ^D ⊗ ℂ^D`.  The factor
system of `ρ` cancels between the two tensor factors, so `U` is a linear
representation.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1149–1157), with the local fix of the
module docstring. -/
def sptFixedPointAction (ρ : ProjectiveRepresentation (D := D) ω) (φ : G →* ℂ) :
    G →* Matrix (Fin (D * D)) (Fin (D * D)) ℂ where
  toFun g := φ g • Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv (sptKron (sptGauge ρ g))
  map_one' := by
    have h1 : (ρ.X 1 : Matrix (Fin D) (Fin D) ℂ) =
        (ω 1 1 : ℂ) • ((1 : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
      have := congrArg (· * (((ρ.X 1)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
        (ρ.map_mul 1 1)
      simpa [Matrix.mul_assoc, Matrix.smul_mul] using this
    rw [map_one, one_smul, sptGauge, inv_one, sptKron_eq_of_eq_smul h1, sptKron_one, map_one]
  map_mul' g h := by
    rw [smul_mul_smul_comm, ← map_mul (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv),
      sptKron_mul, map_mul φ]
    congr 2
    refine (sptKron_eq_of_eq_smul (c := (ω h⁻¹ g⁻¹ : ℂ)) ?_).symm
    rw [sptGauge, sptGauge, sptGauge, mul_inv_rev, Units.val_mul]
    exact ρ.map_mul _ _

/-- **Symmetry relation of the fixed-point tensor.**
`∑ⱼ U(g)ᵢⱼ Aʲ = φ(g) W_g Aⁱ W_g⁻¹`, the relation `S_g(A) = e^{iφ(g)} X_g† A X_g` of
arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` line 1157). -/
theorem twistedTensor_sptFixedPointTensor (ρ : ProjectiveRepresentation (D := D) ω)
    (φ : G →* ℂ) (g : G) (i : Fin (D * D)) :
    twistedTensor (sptFixedPointTensor D) (sptFixedPointAction ρ φ) g i =
      φ g • ((sptGauge ρ g : Matrix (Fin D) (Fin D) ℂ) * sptFixedPointTensor D i *
        (((sptGauge ρ g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  classical
  ext x y
  simp only [twistedTensor, sptFixedPointAction, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.sum_apply, sptFixedPointTensor, smul_eq_mul, sptKron,
    Matrix.single_apply,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, ite_and, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, sptPair]
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  simp only [ite_true]
  ring

/-- **On-site symmetry of the fixed-point tensor.** With the trivial character, the
fixed-point tensor has the same matrix product vectors as each of its twists by
`sptFixedPointAction ρ 1`.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1155–1157), for the trivial character
(scope restriction of the module docstring). -/
theorem sptFixedPointTensor_isOnSiteSymmetric (ρ : ProjectiveRepresentation (D := D) ω) :
    IsOnSiteSymmetric (sptFixedPointTensor D) (sptFixedPointAction ρ 1) := fun g =>
  GaugeEquiv.sameMPV ⟨sptGauge ρ g, fun i => by
    simpa using twistedTensor_sptFixedPointTensor ρ 1 g i⟩

/-- **The virtual cocycle class of the fixed-point tensor is `[ω]`.**
Every virtual projective representation of the on-site symmetry
`sptFixedPointAction ρ 1` has a factor system cohomologous to `ω`.  Source:
arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` lines 1147–1149):
the fixed point "transforms according to" the prescribed 2-cocycle. -/
theorem cohomologousTo_of_sptFixedPointTensor [NeZero D]
    (ρ : ProjectiveRepresentation (D := D) ω) {ω' : ScalarCocycle G}
    (ρ' : ProjectiveRepresentation (D := D) ω')
    (hρ' : ∀ g i, twistedTensor (sptFixedPointTensor D) (sptFixedPointAction ρ 1) g i =
      (ρ'.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * sptFixedPointTensor D i *
        (((ρ'.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ScalarCocycle.CohomologousTo ω' ω :=
  cohomologousTo_of_isInjective _ sptFixedPointTensor_isInjective _
    (Nat.pos_of_ne_zero (NeZero.ne D)) (ρ₁ := ρ) (ρ₂ := ρ')
    (fun g i => by simpa using twistedTensor_sptFixedPointTensor ρ 1 g i) hρ'

/-- **The fixed-point tensor realizes the class `[ω]`.**  The virtual representation
theorem applies to the fixed-point tensor, and the factor system it produces is
cohomologous to `ω`.  Source: arXiv:2011.12127, §III.A
(`Papers/2011.12127/TN-Review-main.tex` lines 1147–1157), for the trivial character
(scope restriction of the module docstring). -/
theorem exists_virtualRep_sptFixedPointTensor [NeZero D]
    (ρ : ProjectiveRepresentation (D := D) ω) :
    ∃ ω' : ScalarCocycle G, ∃ ρ' : ProjectiveRepresentation (D := D) ω',
      (∀ g i, twistedTensor (sptFixedPointTensor D) (sptFixedPointAction ρ 1) g i =
        (ρ'.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * sptFixedPointTensor D i *
          (((ρ'.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ∧
      ScalarCocycle.CohomologousTo ω' ω := by
  obtain ⟨ω', ρ', hρ'⟩ := virtual_rep_of_symmetric_injective _
    sptFixedPointTensor_isInjective _ (sptFixedPointTensor_isOnSiteSymmetric ρ)
  exact ⟨ω', ρ', hρ', cohomologousTo_of_sptFixedPointTensor ρ ρ' hρ'⟩

end Symmetry

end MPSTensor

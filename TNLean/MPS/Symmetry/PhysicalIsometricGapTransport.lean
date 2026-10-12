/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IsometricGapTransfer
import TNLean.MPS.Symmetry.IsometricParentInteraction
import TNLean.MPS.Symmetry.PhysicalInteractionGroundSpace

/-!
# Noncommuting Hamiltonians under physical isometries

For a positive two-site interaction \(h\) and a one-site isometry \(J\), the
extension \(h'=(J\otimes J)h(J\otimes J)^\dagger+1-(JJ^\dagger)^{\otimes2}\)
has exactly the isometric image of the original periodic ground space.
A gap \(\delta\) transfers to the lower bound \(\min(\delta,1)\).
No commutativity of the translates of \(h\) or \(h'\) is assumed.

The auxiliary interaction obtained by setting \(h=0\) has commuting
support penalties and kernel equal to the included whole-chain space.
Its gap is at least one. Positivity of \(h\) gives the same lower bound on the
orthogonal complement for the actual extension; intertwining handles
the included subspace.

Source context: arXiv:2203.12563, Section 5, physical-space enlargement;
arXiv:1010.3732, Section II.F.2, isometric physical embeddings.
-/

open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace

namespace MPSTensor

/-- The unused-space penalties commute on every periodic chain. This
statement concerns only the extension of zero, not an arbitrary interaction. -/
theorem isometricInteractionExtension_zero_translate_commute {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hN : 2 ≤ N) (i j : Fin N) :
    Commute
      (MPOTensor.embedLocalOperator 2 N hN i (isometricInteractionExtension E 0))
      (MPOTensor.embedLocalOperator 2 N hN j (isometricInteractionExtension E 0)) := by
  have heq (k : Fin N) :
      MPOTensor.embedLocalOperator 2 N hN k (isometricInteractionExtension E 0) =
        1 - MPOTensor.embedLocalOperator 2 N hN k
          (MPOTensor.twoSiteSectorProjection (E * Eᴴ)) := by
    change (MPOTensor.embedLocalOperatorAlgHom (d := m) 2 N hN k)
      (1 - singleKrausMap (MPOTensor.sitewisePhysicalMatrix E 2) (1 - 0)) = _
    simp only [sub_zero, singleKrausMap_apply, Matrix.mul_one,
      MPOTensor.sitewisePhysicalMatrix_two_mul_conjTranspose, map_sub, map_one]
    rfl
  rw [heq, heq]
  exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right
    (MPOTensor.embed_twoSiteSectorProjection_commute (E * Eᴴ) hN i j))

/-- The sum of the unused-space penalties has kernel exactly the range of
the tensor power of the physical inclusion. -/
theorem isometricInteractionExtension_zero_ker_eq_range {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E 0) hN)) =
        LinearMap.range (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)) := by
  have hzero : interactionHamiltonian (0 : MPOTensor.ChainOperator d 2) hN = 0 := by
    unfold interactionHamiltonian
    apply Finset.sum_eq_zero
    intro i _
    exact (MPOTensor.embedLocalOperatorAlgHom (d := d) 2 N hN i).map_zero
  have hcomm (i j : Fin N) :
      Commute (MPOTensor.embedLocalOperator 2 N hN i (0 : MPOTensor.ChainOperator d 2))
        (MPOTensor.embedLocalOperator 2 N hN j (0 : MPOTensor.ChainOperator d 2)) := by
    change Commute ((MPOTensor.embedLocalOperatorAlgHom 2 N hN i) 0)
      ((MPOTensor.embedLocalOperatorAlgHom 2 N hN j) 0)
    simp only [map_zero]
    exact Commute.zero_left _
  simpa only [hzero, map_zero, LinearMap.ker_zero, Submodule.map_top] using
    isometricInteractionExtension_ker_eq_map E hE 0 (IsStarProjection.zero _) hN hcomm
      (isometricInteractionExtension_zero_translate_commute E hN)

/-- Extending a positive local interaction and penalizing the unused
physical space gives another positive local interaction. -/
theorem isometricInteractionExtension_posSemidef {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) :
    (isometricInteractionExtension E A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact (isometricInteractionExtension_isStarProjection E hE 0
    (IsStarProjection.zero _)).nonneg.trans
      (isometricInteractionExtension_mono E (Matrix.nonneg_iff_posSemidef.mpr hA))

private theorem normSq_sum_eq {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℂ ι) :
    (∑ i, Complex.normSq (v i)) = ‖v‖ ^ 2 := by
  simp_rw [Complex.normSq_eq_norm_sq]
  exact (EuclideanSpace.norm_sq_eq v).symm

private theorem re_dotProduct_eq_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).re =
      (⟪Matrix.toEuclideanLin M v, v⟫_ℂ).re := by
  rw [← RCLike.re_eq_complex_re, inner_re_symm, RCLike.re_eq_complex_re,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (star v.ofLp ⬝ᵥ (M *ᵥ v.ofLp)).re =
    ((M *ᵥ v.ofLp) ⬝ᵥ star v.ofLp).re
  rw [dotProduct_comm]

/-- Every vector perpendicular to the included chain has energy at least
its squared norm under the extended Hamiltonian. Only local positivity is
needed; the actual local terms may fail to commute. -/
theorem isometricInteractionExtension_inactive_energy_lower_bound {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg m N))
    (hv : v ∈ (LinearMap.range
      (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)))ᗮ) :
    ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN) v, v⟫_ℂ).re := by
  let P := interactionHamiltonian (isometricInteractionExtension E 0) hN
  let H := interactionHamiltonian (isometricInteractionExtension E A) hN
  have hProjection := isometricInteractionExtension_isStarProjection E hE 0
    (IsStarProjection.zero _)
  have hP : P.PosSemidef := interactionHamiltonian_posSemidef
    (Matrix.nonneg_iff_posSemidef.mp hProjection.nonneg) hN
  have hSpec := interactionHamiltonian_spectrum_gap_one_of_commuting_projection _
    hProjection hN (isometricInteractionExtension_zero_translate_commute E hN)
  have hvP : v ∈ (LinearMap.ker (Matrix.toEuclideanLin P))ᗮ := by
    rwa [isometricInteractionExtension_zero_ker_eq_range E hE hN]
  have hGap := Matrix.orthogonal_quadratic_gap_of_spectrum_separated P hP.isHermitian
    (fun z hz => (hSpec z hz).2) v hvP
  have hEnergy : ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin P v, v⟫_ℂ).re := by
    simpa only [one_mul, normSq_sum_eq, re_dotProduct_eq_re_inner] using hGap
  have hOrder : P ≤ H := interactionHamiltonian_mono
    (isometricInteractionExtension_mono E (Matrix.nonneg_iff_posSemidef.mpr hA)) hN
  have hPositive := Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hOrder)
  have hEnergyOrder : (⟪Matrix.toEuclideanLin P v, v⟫_ℂ).re ≤
      (⟪Matrix.toEuclideanLin H v, v⟫_ℂ).re := by
    simpa only [map_sub, LinearMap.sub_apply, inner_sub_left,
      RCLike.re_eq_complex_re, Complex.sub_re, sub_nonneg] using
      hPositive.re_inner_nonneg_left v
  exact hEnergy.trans hEnergyOrder

private noncomputable def physicalChainLinearIsometry {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1) (N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Cfg m N) := by
  let T := Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)
  have hT : T.adjoint ∘ₗ T = LinearMap.id := by
    simpa only [T, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix_isometry E hE N)
  exact T.isometryOfInner fun x y => by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hT, LinearMap.id_apply]

private theorem physicalChainLinearIsometry_toLinearMap {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1) (N : ℕ) :
    (physicalChainLinearIsometry E hE N).toLinearMap =
      Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) := rfl

private theorem physicalChainLinearIsometry_intertwines {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.IsHermitian) (hN : 2 ≤ N)
    (x : EuclideanSpace ℂ (Cfg d N)) :
    Matrix.toEuclideanLin (interactionHamiltonian (isometricInteractionExtension E A) hN)
        (physicalChainLinearIsometry E hE N x) =
      physicalChainLinearIsometry E hE N
        (Matrix.toEuclideanLin (interactionHamiltonian A hN) x) := by
  have h := congrArg (fun M => Matrix.toEuclideanLin M x)
    (interactionHamiltonian_isometricInteractionExtension_intertwiner E hE A hA hN)
  change Matrix.toEuclideanLin _
      ((physicalChainLinearIsometry E hE N).toLinearMap x) =
    (physicalChainLinearIsometry E hE N).toLinearMap (Matrix.toEuclideanLin _ x)
  simpa only [physicalChainLinearIsometry_toLinearMap, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h

private theorem physicalChainLinearIsometry_inactive_bound {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg m N))
    (hv : (physicalChainLinearIsometry E hE N).toLinearMap.adjoint v = 0) :
    (1 : ℝ) * ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN) v, v⟫_ℂ).re := by
  rw [one_mul]
  apply isometricInteractionExtension_inactive_energy_lower_bound E hE hA hN v
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨x, rfl⟩
  change ⟪(physicalChainLinearIsometry E hE N).toLinearMap x, v⟫_ℂ = 0
  rw [← LinearMap.adjoint_inner_right, hv, inner_zero_right]

/-- For every positive local interaction, the enlarged periodic kernel is
exactly the physical isometric image of the original kernel. No translated
terms are assumed to commute. -/
theorem isometricInteractionExtension_ker_eq_map_of_posSemidef {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) =
      (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN))).map
        (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)) := by
  simpa only [physicalChainLinearIsometry_toLinearMap] using
    (physicalChainLinearIsometry E hE N).ker_eq_map_of_intertwines_of_inactive_bound
      (physicalChainLinearIsometry_intertwines E hE hA.isHermitian hN)
      (by norm_num : (0 : ℝ) < 1)
      (physicalChainLinearIsometry_inactive_bound E hE hA hN)

/-- A one-dimensional periodic ground space is carried to the line of the
physically included vector for arbitrary positive local interactions. -/
theorem isometricInteractionExtension_ker_eq_span_of_posSemidef {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N)
    (ψ : EuclideanSpace ℂ (Cfg d N))
    (hground : LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)) =
      Submodule.span ℂ {ψ}) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) =
      Submodule.span ℂ {Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N) ψ} := by
  rw [isometricInteractionExtension_ker_eq_map_of_posSemidef E hE hA hN,
    hground, Submodule.map_span, Set.image_singleton]

/-- A lower quadratic-form gap transfers through a physical inclusion with
the minimum of the original gap and the unit unused-state penalty. -/
theorem isometricInteractionExtension_quadratic_gap {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N) {δ : ℝ}
    (hGap : ∀ x ∈ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)))ᗮ,
      δ * ‖x‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin (interactionHamiltonian A hN) x, x⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)))ᗮ,
      min δ 1 * ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin
        (interactionHamiltonian (isometricInteractionExtension E A) hN) v, v⟫_ℂ).re := by
  exact (physicalChainLinearIsometry E hE N).re_inner_ge_of_intertwines
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (interactionHamiltonian_posSemidef
        (isometricInteractionExtension_posSemidef E hE hA) hN).isHermitian)
    (physicalChainLinearIsometry_intertwines E hE hA.isHermitian hN)
    hGap (physicalChainLinearIsometry_inactive_bound E hE hA hN)

/-- A norm gap on the original periodic kernel complement gives the gap
\(\min(\delta,1)\) on the full enlarged chain, without commutativity. -/
theorem isometricInteractionExtension_norm_gap {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)))ᗮ,
      δ * ‖x‖ ≤ ‖Matrix.toEuclideanLin (interactionHamiltonian A hN) x‖) :
    ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)))ᗮ,
      min δ 1 * ‖v‖ ≤ ‖Matrix.toEuclideanLin
        (interactionHamiltonian (isometricInteractionExtension E A) hN) v‖ := by
  exact (physicalChainLinearIsometry E hE N).norm_gap_of_intertwines
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (interactionHamiltonian_posSemidef (isometricInteractionExtension_posSemidef E hE hA) hN))
    (Matrix.isPositive_toEuclideanLin_iff.mpr (interactionHamiltonian_posSemidef hA hN))
    (physicalChainLinearIsometry_intertwines E hE hA.isHermitian hN)
    hδ hGap (physicalChainLinearIsometry_inactive_bound E hE hA hN)

/-- A spectral gap above zero transfers through an isometric physical
inclusion with the bound \(\min(\delta,1)\). This does not assert a zero
mode when the original Hamiltonian has trivial kernel. -/
theorem isometricInteractionExtension_spectrum_gap {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N) {δ : ℝ}
    (hGap : ∀ z ∈ spectrum ℂ (interactionHamiltonian A hN), z.re = 0 ∨ δ ≤ z.re) :
    ∀ z ∈ spectrum ℂ (interactionHamiltonian (isometricInteractionExtension E A) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ min δ 1 ≤ z.re) := by
  have hQuad : ∀ x ∈ (LinearMap.ker
      (Matrix.toEuclideanLin (interactionHamiltonian A hN)))ᗮ,
      δ * ‖x‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin (interactionHamiltonian A hN) x, x⟫_ℂ).re := by
    intro x hx
    simpa only [normSq_sum_eq, re_dotProduct_eq_re_inner] using
      Matrix.orthogonal_quadratic_gap_of_spectrum_separated _
        (interactionHamiltonian_posSemidef hA hN).isHermitian hGap x hx
  apply Matrix.spectrum_separated_of_orthogonal_quadratic_gap _
    (interactionHamiltonian_posSemidef (isometricInteractionExtension_posSemidef E hE hA) hN)
  intro v hv
  simpa only [normSq_sum_eq, re_dotProduct_eq_re_inner] using
    isometricInteractionExtension_quadratic_gap E hE hA hN hQuad v hv

end MPSTensor

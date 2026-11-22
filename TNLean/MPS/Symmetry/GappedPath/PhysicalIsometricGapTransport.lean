/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Gap.IsometricGapTransfer
import QICLean.ManyBody.Hamiltonian.KernelGap
import TNLean.MPS.Symmetry.GappedPath.PhysicalInteractionGap
import TNLean.MPS.Symmetry.GappedPath.PhysicalInteractionGroundSpace

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

open ManyBody

namespace MPSTensor

/-- The unused-space penalties commute on every periodic chain. This
statement concerns only the extension of zero, not an arbitrary interaction. -/
theorem isometricInteractionExtension_zero_translate_commute {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hN : 2 ≤ N) (i j : Fin N) :
    Commute
      (placeAlong (X := fun _ ↦ Fin m) (ringWindow hN i) (isometricInteractionExtension E 0))
      (placeAlong (X := fun _ ↦ Fin m) (ringWindow hN j)
        (isometricInteractionExtension E 0)) := by
  have heq (k : Fin N) :
      placeAlong (X := fun _ ↦ Fin m) (ringWindow hN k) (isometricInteractionExtension E 0) =
        1 - placeAlong (X := fun _ ↦ Fin m) (ringWindow hN k)
          (MPOTensor.twoSiteSectorProjection (E * Eᴴ)) := by
    change placeAlong (X := fun _ ↦ Fin m) (ringWindow hN k)
      (1 - singleKrausMap (Matrix.tensorPower 2 E) (1 - 0)) = _
    simp only [sub_zero, singleKrausMap_apply, Matrix.mul_one,
      MPOTensor.tensorPower_two_mul_conjTranspose, placeAlong_sub, placeAlong_one]
  rw [heq, heq]
  exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right
    (MPOTensor.embed_twoSiteSectorProjection_commute (E * Eᴴ) hN i j))

/-- The sum of the unused-space penalties has kernel exactly the range of
the tensor power of the physical inclusion. -/
theorem isometricInteractionExtension_zero_ker_eq_range {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1) (hN : 2 ≤ N) :
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (isometricInteractionExtension E 0)).hamiltonian) =
        LinearMap.range (Matrix.toEuclideanLin (Matrix.tensorPower N E)) := by
  have : NeZero N := ⟨by omega⟩
  have hzero : (Interaction.translationInvariant N
      (0 : MPOTensor.ChainOperator d 2)).hamiltonian = 0 := by
    simp only [Interaction.hamiltonian_translationInvariant_of_le _ hN, placeAlong_zero,
      Finset.sum_const_zero]
  have hcomm (i j : Fin N) :
      Commute (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i)
          (0 : MPOTensor.ChainOperator d 2))
        (placeAlong (X := fun _ ↦ Fin d) (ringWindow hN j)
          (0 : MPOTensor.ChainOperator d 2)) := by
    simp only [placeAlong_zero]
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

/-- Every vector perpendicular to the included chain has energy at least
its squared norm under the extended Hamiltonian. Only local positivity is
needed; the actual local terms may fail to commute. -/
theorem isometricInteractionExtension_inactive_energy_lower_bound {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ (Cfg m N))
    (hv : v ∈ (LinearMap.range
      (Matrix.toEuclideanLin (Matrix.tensorPower N E)))ᗮ) :
    haveI : NeZero N := ⟨by omega⟩; ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian v,
        v⟫_ℂ).re := by
  have : NeZero N := ⟨by omega⟩
  let P := (Interaction.translationInvariant N (isometricInteractionExtension E 0)).hamiltonian
  let H := (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian
  have hProjection := isometricInteractionExtension_isStarProjection E hE 0
    (IsStarProjection.zero _)
  have hP : P.PosSemidef := Interaction.posSemidef_hamiltonian fun _ ↦
      Matrix.LE.le.posSemidef (Interaction.translationInvariant_term_nonneg hProjection.nonneg _)
  have hSpec := hamiltonian_translationInvariant_eigenvalue_gap_one_of_commuting_projection _
    hProjection hN (isometricInteractionExtension_zero_translate_commute E hN)
  have hvP : v ∈ (LinearMap.ker (Matrix.toEuclideanLin P))ᗮ := by
    rwa [isometricInteractionExtension_zero_ker_eq_range E hE hN]
  have hGap := (forall_hasEigenvalue_iff_re_inner (Δ := 1) hP).mp
    (by simpa only [Complex.ofReal_one] using hSpec) v hvP
  have hEnergy : ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin P v, v⟫_ℂ).re := by
    rwa [one_mul, ← RCLike.re_eq_complex_re, inner_re_symm, RCLike.re_eq_complex_re] at hGap
  have hOrder : P ≤ H := by
    simp only [P, H, Interaction.hamiltonian_translationInvariant_of_le _ hN]
    exact Finset.sum_le_sum fun _ _ ↦ placeAlong_le_placeAlong _
      (isometricInteractionExtension_mono E (Matrix.nonneg_iff_posSemidef.mpr hA))
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
  let T := Matrix.toEuclideanLin (Matrix.tensorPower N E)
  have hT : T.adjoint ∘ₗ T = LinearMap.id := by
    simpa only [T, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one] using
      congrArg Matrix.toEuclideanLin (MPOTensor.tensorPower_isometry E hE N)
  exact T.isometryOfInner fun x y => by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hT, LinearMap.id_apply]

private theorem physicalChainLinearIsometry_toLinearMap {d m : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1) (N : ℕ) :
    (physicalChainLinearIsometry E hE N).toLinearMap =
      Matrix.toEuclideanLin (Matrix.tensorPower N E) := rfl

private theorem physicalChainLinearIsometry_intertwines {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.IsHermitian) (hN : 2 ≤ N)
    (x : EuclideanSpace ℂ (Cfg d N)) :
    haveI : NeZero N := ⟨by omega⟩; Matrix.toEuclideanLin
        (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian
        (physicalChainLinearIsometry E hE N x) =
      physicalChainLinearIsometry E hE N
        (Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian x) := by
  have : NeZero N := ⟨by omega⟩
  have h := congrArg (fun M => Matrix.toEuclideanLin M x)
    (hamiltonian_translationInvariant_isometricInteractionExtension_intertwiner E hE A hA hN)
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
    haveI : NeZero N := ⟨by omega⟩; (1 : ℝ) * ‖v‖ ^ 2 ≤ (⟪Matrix.toEuclideanLin
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian v,
        v⟫_ℂ).re := by
  have : NeZero N := ⟨by omega⟩
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
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian) =
      (LinearMap.ker
        (Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian)).map
        (Matrix.toEuclideanLin (Matrix.tensorPower N E)) := by
  have : NeZero N := ⟨by omega⟩
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
    (hground : haveI : NeZero N := ⟨by omega⟩; LinearMap.ker
        (Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian) =
      Submodule.span ℂ {ψ}) :
    haveI : NeZero N := ⟨by omega⟩; LinearMap.ker (Matrix.toEuclideanLin
      (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian) =
      Submodule.span ℂ {Matrix.toEuclideanLin (Matrix.tensorPower N E) ψ} := by
  have : NeZero N := ⟨by omega⟩
  rw [isometricInteractionExtension_ker_eq_map_of_posSemidef E hE hA hN,
    hground, Submodule.map_span, Set.image_singleton]

/-- **Gap transfer through a physical inclusion.** If every eigenvalue of the original periodic
Hamiltonian is `0` or at least `δ`, then every eigenvalue of the enlarged one is `0` or at least
\(\min(\delta,1)\), without commutativity. This does not assert a zero mode when the original
Hamiltonian has trivial kernel, and no sign of `δ` is assumed. -/
theorem isometricInteractionExtension_eigenvalue_gap {d m N : ℕ}
    (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
    {A : MPOTensor.ChainOperator d 2} (hA : A.PosSemidef) (hN : 2 ≤ N) {δ : ℝ}
    (hGap : haveI : NeZero N := ⟨by omega⟩; ∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (Interaction.translationInvariant N A).hamiltonian) μ →
      μ = 0 ∨ (δ : ℂ) ≤ μ) :
    haveI : NeZero N := ⟨by omega⟩;
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toEuclideanLin
        (Interaction.translationInvariant N (isometricInteractionExtension E A)).hamiltonian) μ →
      μ = 0 ∨ ((min δ 1 : ℝ) : ℂ) ≤ μ := by
  have : NeZero N := ⟨by omega⟩
  have hPA : (Interaction.translationInvariant N A).hamiltonian.PosSemidef :=
    Interaction.posSemidef_hamiltonian fun _ ↦
      Matrix.LE.le.posSemidef (Interaction.translationInvariant_term_nonneg hA.nonneg _)
  have hPE : (Interaction.translationInvariant N
      (isometricInteractionExtension E A)).hamiltonian.PosSemidef :=
    Interaction.posSemidef_hamiltonian fun _ ↦
      Matrix.LE.le.posSemidef (Interaction.translationInvariant_term_nonneg
        (isometricInteractionExtension_posSemidef E hE hA).nonneg _)
  rw [forall_hasEigenvalue_iff_re_inner hPA] at hGap
  rw [forall_hasEigenvalue_iff_re_inner hPE]
  intro v hv
  rw [← RCLike.re_eq_complex_re, inner_re_symm, RCLike.re_eq_complex_re]
  refine (physicalChainLinearIsometry E hE N).re_inner_ge_of_intertwines
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hPE.isHermitian)
    (physicalChainLinearIsometry_intertwines E hE hA.isHermitian hN)
    (fun x hx ↦ ?_) (physicalChainLinearIsometry_inactive_bound E hE hA hN) v hv
  rw [← RCLike.re_eq_complex_re, inner_re_symm, RCLike.re_eq_complex_re]
  exact hGap x hx

end MPSTensor

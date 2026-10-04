/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith
import QICLean.Algebra.MatrixAux
import TNLean.MPS.Symmetry.LocalSpectralSupport
import TNLean.MPS.Symmetry.ProjectiveGaugeTransport
import TNLean.MPS.Symmetry.NearbyInjectiveAdjointActions
import TNLean.MPS.Symmetry.ProjectiveHomConjugation
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Uniform rigidity of unitary projective classes

A dimension-dependent neighborhood of a unitary adjoint action determines its
projective cohomology class. The proof averages the orbit of the identity line
in the space of intertwiners, extracts a nearby invariant line, and obtains an
invertible projective intertwiner. No topology on the group or continuity of
its representatives is required.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. This module proves
an auxiliary finite-dimensional rigidity statement, and does not construct the
virtual data needed for the Hamiltonian converse.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder InnerProductSpace Kronecker Topology

private theorem exists_common_fixedPoint_of_closed_convex_isometries
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (f : ι → E →ₗᵢ[ℝ] E)
    (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconv : Convex ℝ S)
    (hmap : ∀ i, Set.MapsTo (f i) S S) :
    ∃ v ∈ S, ∀ i, f i v = v := by
  obtain ⟨v, hv, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv (0 : E)
  refine ⟨v, hv, ?_⟩
  intro i
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin
    (f i v) (hmap i hv)
  simp only [zero_sub, inner_neg_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at hinner
  have hnorm : ‖f i v‖ = ‖v‖ := (f i).norm_map v
  have hzero : ‖v - f i v‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hnorm]
    linarith
  have heq : v - f i v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (v - f i v)])
  exact (sub_eq_zero.mp heq).symm

/-- An invariant orbit contained in a closed ball has a common fixed point in that ball. -/
private theorem exists_common_fixedPoint_in_closedConvexHull
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (f : ι → E →ₗᵢ[ℝ] E)
    (O : Set E) (hne : O.Nonempty) (hmap : ∀ i, Set.MapsTo (f i) O O)
    (x : E) (ε : ℝ) (hnear : O ⊆ Metric.closedBall x ε) :
    ∃ v ∈ closedConvexHull ℝ O,
      (∀ i, f i v = v) ∧ dist v x ≤ ε := by
  let S := closedConvexHull ℝ O
  have hSmap : ∀ i, Set.MapsTo (f i) S S := by
    intro i
    exact closedConvexHull_min
      (fun y hy => subset_closedConvexHull (hmap i hy))
      (convex_closedConvexHull.linear_preimage (f i).toLinearMap)
      (isClosed_closedConvexHull.preimage (f i).continuous)
  obtain ⟨v, hv, hfixed⟩ := exists_common_fixedPoint_of_closed_convex_isometries
    f S (hne.mono subset_closedConvexHull) isClosed_closedConvexHull
    convex_closedConvexHull hSmap
  refine ⟨v, hv, hfixed, ?_⟩
  exact Metric.mem_closedBall.mp
    (closedConvexHull_min hnear (convex_closedBall x ε) Metric.isClosed_closedBall hv)


namespace Matrix

private theorem frobenius_norm_unitary_conjugation
    {n : Type*} [Fintype n] [DecidableEq n]
    (U A : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    ‖U * A * Uᴴ‖ = ‖A‖ := by
  have hU'U : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    ← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
  congr 1
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  calc
    trace ((U * (Aᴴ * Uᴴ)) * (U * A * Uᴴ)) = trace (U * (Aᴴ * A) * Uᴴ) := by
      congr 1
      simp only [mul_assoc]
      rw [← mul_assoc Uᴴ U, hU'U, one_mul]
    _ = trace (Aᴴ * A) := by
      rw [trace_mul_cycle, hU'U, one_mul]

private noncomputable def unitaryConjugationFrobeniusIsometry
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    EuclideanSpace ℂ (n × n) →ₗᵢ[ℝ] EuclideanSpace ℂ (n × n) where
  toLinearMap := (frobeniusEuclideanMap
    ((LinearMap.mulRight ℂ Uᴴ).comp (LinearMap.mulLeft ℂ U))).restrictScalars ℝ
  norm_map' x := by
    let A := (frobeniusEquivEuclidean n n).symm x
    have hx : x = frobeniusEquivEuclidean n n A := by simp [A]
    rw [hx]
    change ‖frobeniusEuclideanMap
      ((LinearMap.mulRight ℂ Uᴴ).comp (LinearMap.mulLeft ℂ U))
      (frobeniusEquivEuclidean n n A)‖ = ‖frobeniusEquivEuclidean n n A‖
    rw [frobeniusEuclideanMap_apply, LinearIsometryEquiv.norm_map,
      LinearIsometryEquiv.norm_map]
    exact frobenius_norm_unitary_conjugation U A hU

private theorem exists_fixed_hermitian_near_unitary_orbit
    {n ι : Type*} [Fintype n] [DecidableEq n]
    (U : ι → Matrix n n ℂ) (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    (O : Set (Matrix n n ℂ)) (hne : O.Nonempty)
    (hHerm : ∀ A ∈ O, A.IsHermitian)
    (hmap : ∀ i A, A ∈ O → U i * A * (U i)ᴴ ∈ O)
    (P : Matrix n n ℂ) (ε : ℝ) (hnear : ∀ A ∈ O, ‖A - P‖ ≤ ε) :
    ∃ R : Matrix n n ℂ, R.IsHermitian ∧ ‖R - P‖ ≤ ε ∧
      ∀ i, U i * R * (U i)ᴴ = R := by
  let e := frobeniusEquivEuclidean n n
  let eR := e.toLinearEquiv.restrictScalars ℝ
  let H := (selfAdjoint.submodule ℝ (Matrix n n ℂ)).map eR.toLinearMap
  have hsub : e '' O ⊆ (H : Set (EuclideanSpace ℂ (n × n))) := by
    rintro _ ⟨A, hA, rfl⟩
    exact Submodule.mem_map.mpr ⟨A, hHerm A hA, rfl⟩
  have hhull : closedConvexHull ℝ (e '' O) ⊆ H :=
    closedConvexHull_min hsub H.convex H.closed_of_finiteDimensional
  obtain ⟨v, hv, hfix, hdist⟩ := exists_common_fixedPoint_in_closedConvexHull
    (fun i => unitaryConjugationFrobeniusIsometry (U i) (hU i))
    (e '' O) (hne.image e) (by
      intro i
      rintro _ ⟨A, hA, rfl⟩
      exact ⟨U i * A * (U i)ᴴ, hmap i A hA, rfl⟩)
    (e P) ε (by
      rintro _ ⟨A, hA, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, ← e.map_sub, e.norm_map]
      exact hnear A hA)
  refine ⟨e.symm v, ?_, ?_, ?_⟩
  · obtain ⟨A, hA, hAv⟩ := Submodule.mem_map.mp (hhull hv)
    change e A = v at hAv
    have heq : e.symm v = A := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hAv.symm
    exact heq ▸ hA
  · rw [← e.norm_map, e.map_sub, e.apply_symm_apply]
    exact (dist_eq_norm v (e P)) ▸ hdist
  · intro i
    apply e.injective
    rw [e.apply_symm_apply]
    have hi := hfix i
    change e (U i * e.symm v * (U i)ᴴ) = v at hi
    exact hi

private theorem supportProj_eq_of_isHermitian_idempotent
    {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.PosSemidef) (hid : P * P = P) : hP.supportProj = P := by
  obtain ⟨W, hW⟩ := hP.exists_supportProj_eq_mul
  have hPS : P * hP.supportProj = hP.supportProj := by
    rw [hW, ← mul_assoc, hid]
  have hPS' : P * hP.supportProj = P := by
    simpa only [conjTranspose_mul, hP.isHermitian.eq,
      hP.supportProj_isHermitian.eq] using congrArg conjTranspose hP.supportProj_mul_self
  exact hPS.symm.trans hPS'

end Matrix

namespace Matrix

private theorem exists_radius_invertible_spectral_line
    {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (J₀ : Matrix n (Fin 1) ℂ) (hJ₀ : J₀.IsIsometry)
    (decode : (n → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hdecode : IsUnit (decode (fun i => J₀ i 0))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ R : Matrix n n ℂ, R.IsHermitian →
      ‖R - J₀ * J₀ᴴ‖ < ε → ∃ J : Matrix n (Fin 1) ℂ,
        J.IsIsometry ∧ IsUnit (decode (fun i => J i 0)) ∧
        ∀ U : Matrix n n ℂ, Commute U R →
          U * J = (J * (Jᴴ * U * J)) := by
  let P := J₀ * J₀ᴴ
  have hP : P.PosSemidef := posSemidef_self_mul_conjTranspose J₀
  have hid : P * P = P := by
    change J₀ * J₀ᴴ * (J₀ * J₀ᴴ) = J₀ * J₀ᴴ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J₀ᴴ, hJ₀, Matrix.one_mul]
  let e := frobeniusEquivEuclidean n n
  let T := EuclideanSpace ℂ (n × n)
  let A : T → Matrix n n ℂ := fun t =>
    (selfAdjointPart ℝ (e.symm t) : Matrix n n ℂ)
  let t₀ : T := e P
  have hA : Continuous A := by
    change Continuous fun t => (⅟ (2 : ℝ)) • (e.symm t + star (e.symm t))
    exact (e.symm.continuous.add e.symm.continuous.star).const_smul (⅟ (2 : ℝ))
  have hAt₀ : A t₀ = P := by
    simp only [A, t₀, e.symm_apply_apply]
    exact (show IsSelfAdjoint P from hP.isHermitian).coe_selfAdjointPart_apply ℝ
  have hbase : (A t₀).PosSemidef := hAt₀.symm ▸ hP
  obtain ⟨a, b, S, _, _, hS, ht₀, hcont, hbase, hframe⟩ :=
    exists_local_continuous_spectral_frame A hA
      (fun t => (selfAdjointPart ℝ (e.symm t)).property) t₀
      hbase J₀ hJ₀ ((hbase.supportProj_congr hP hAt₀).trans
        (supportProj_eq_of_isHermitian_idempotent hP hid))
  let J : T → Matrix n (Fin 1) ℂ := fun t =>
    polarIso (spectralCorner a b (A t) * J₀)
  have hJcont : ContinuousAt J t₀ := hcont.continuousAt (hS.mem_nhds ht₀)
  have hdcont : ContinuousAt (fun t => decode (fun i => J t i 0)) t₀ := by
    exact decode.continuous_of_finiteDimensional.continuousAt.comp
      (continuousAt_pi.mpr fun i => (continuous_apply 0).continuousAt.comp
        ((continuous_apply i).continuousAt.comp hJcont))
  have hunit : ∀ᶠ t in 𝓝 t₀, IsUnit (decode (fun i => J t i 0)) :=
    hdcont.eventually (Units.isOpen.mem_nhds (by
      change IsUnit (decode (fun i => J t₀ i 0))
      simpa only [J, hbase] using hdecode))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    ((show ∀ᶠ t in 𝓝 t₀, t ∈ S from hS.mem_nhds ht₀).and hunit)
  refine ⟨ε, hε, fun R hR hnear => ?_⟩
  let t : T := e R
  have hAt : A t = R := by
    simp only [A, t, e.symm_apply_apply]
    exact (show IsSelfAdjoint R from hR).coe_selfAdjointPart_apply ℝ
  have ht : dist t t₀ < ε := by
    change dist (e R) (e P) < ε
    rw [e.isometry.dist_eq, dist_eq_norm]
    exact hnear
  have hSunit := hball ht
  obtain ⟨hIso, hCorner⟩ := hframe t hSunit.1
  refine ⟨J t, hIso, hSunit.2, fun U hUR => ?_⟩
  have hComm : Commute U (J t * (J t)ᴴ) := by
    rw [hCorner, hAt]
    exact commute_spectralCorner_of_commute a b U R hUR
  have hPJ : (J t * (J t)ᴴ) * J t = J t := by
    rw [Matrix.mul_assoc, hIso, Matrix.mul_one]
  calc
    U * J t = U * ((J t * (J t)ᴴ) * J t) := by rw [hPJ]
    _ = (J t * (J t)ᴴ) * U * J t := by rw [← Matrix.mul_assoc, hComm.eq]
    _ = J t * ((J t)ᴴ * U * J t) := by simp only [Matrix.mul_assoc]

end Matrix

open TNLean.Algebra
private theorem cohomologous_of_projective_intertwiner
    {G : Type} [Group G] {D : ℕ} [NeZero D]
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (W : Matrix (Fin D) (Fin D) ℂ) (hW : IsUnit W)
    (c : G → ℂ)
    (hInter : ∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) * W =
      c g • (W * (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ))) :
    ω₁.CohomologousTo ω₀ := by
  have hne : ∀ g, c g ≠ 0 := by
    intro g hz
    have hprod : IsUnit ((ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) * W) :=
      (ρ₁.X g).isUnit.mul hW
    exact hprod.ne_zero (by simpa only [hz, zero_smul] using hInter g)
  let f : G → Units ℂ := fun g => Units.mk0 (c g) (hne g)
  let Y : GL (Fin D) ℂ := hW.unit
  let ρ₂ := ρ₀.conjugate Y
  have hEq : ∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) =
      (f g : ℂ) • (ρ₂.X g : Matrix (Fin D) (Fin D) ℂ) := by
    intro g
    have hh := congrArg
      (fun X => X * ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) (hInter g)
    have hY : (Y : Matrix (Fin D) (Fin D) ℂ) = W := hW.unit_spec
    simpa only [← hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.smul_mul, ρ₂, ProjectiveRepresentation.conjugate,
      Matrix.GeneralLinearGroup.coe_mul, f, Units.val_mk0] using hh
  refine ⟨f, fun g h => ?_⟩
  have hm := ρ₁.map_mul g h
  rw [hEq g, hEq h, hEq (g * h), smul_mul_smul_comm,
    ρ₂.map_mul, smul_smul, smul_smul] at hm
  have hs : (f g : ℂ) * (f h : ℂ) * (ω₀ g h : ℂ) =
      (ω₁ g h : ℂ) * (f (g * h) : ℂ) :=
    ProjectiveRepresentation.smul_eq_smul_cancel (NeZero.pos D)
      (ρ₂.X (g * h)).isUnit hm
  apply Units.val_injective
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [← mul_inv_cancel_right₀ (Units.ne_zero (f (g * h))) (ω₁ g h : ℂ), ← hs]
  ring


open TNLean.Algebra

private theorem cohomologous_of_uniformly_near_intertwiner_orbit
    {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ} [NeZero D]
    (J₀ : Matrix n (Fin 1) ℂ) (hJ₀ : J₀.IsIsometry)
    (decode : (n → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hdecode : IsUnit (decode (fun i => J₀ i 0))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (G : Type) [Group G]
      (ω₀ ω₁ : ScalarCocycle G)
      (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
      (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
      (S : G → Matrix n n ℂ),
      (∀ g, S g ∈ Matrix.unitaryGroup n ℂ) →
      (∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup (Fin D) ℂ) →
      (∀ g h M, S g * (S h * M * (S h)ᴴ) * (S g)ᴴ =
        S (g * h) * M * (S (g * h))ᴴ) →
      (∀ g v, decode (S g *ᵥ v) =
        (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) * decode v *
          (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ) →
      (∀ g, ‖S g * (J₀ * J₀ᴴ) * (S g)ᴴ - J₀ * J₀ᴴ‖ < ε) →
      ω₁.CohomologousTo ω₀ := by
  obtain ⟨δ, hδ, hline⟩ := Matrix.exists_radius_invertible_spectral_line
    J₀ hJ₀ decode hdecode
  refine ⟨δ / 2, half_pos hδ, fun G _ ω₀ ω₁ ρ₀ ρ₁ S hS hρ₀ hmul hdec hnear => ?_⟩
  let P := J₀ * J₀ᴴ
  let O := Set.range fun g => S g * P * (S g)ᴴ
  obtain ⟨R, hR, hdist, hfixed⟩ := Matrix.exists_fixed_hermitian_near_unitary_orbit
    S hS O (Set.range_nonempty _) (by
      rintro A ⟨g, rfl⟩
      exact ((Matrix.posSemidef_self_mul_conjTranspose J₀).mul_mul_conjTranspose_same
        (S g)).isHermitian) (by
      intro g A hA
      obtain ⟨h, rfl⟩ := hA
      exact ⟨g * h, (hmul g h P).symm⟩)
    P (δ / 2) (by rintro A ⟨g, rfl⟩; exact (hnear g).le)
  obtain ⟨J, _, hW, hJ⟩ := hline R hR (hdist.trans_lt (half_lt_self hδ))
  let W := decode (fun i => J i 0)
  let c : G → ℂ := fun g => (Jᴴ * S g * J) 0 0
  apply cohomologous_of_projective_intertwiner ρ₀ ρ₁ W hW c
  intro g
  have hComm : Commute (S g) R := by
    have hg := congrArg (fun X => X * S g) (hfixed g)
    have hSS : (S g)ᴴ * S g = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hS g)
    change S g * R = R * S g
    simpa only [Matrix.mul_assoc, hSS, Matrix.mul_one] using hg
  have heig : S g *ᵥ (fun i => J i 0) = c g • (fun i => J i 0) := by
    have hSJ := hJ (S g) hComm
    ext i
    have hi := congrFun (congrFun hSJ i) 0
    simpa only [Matrix.mul_apply, Fin.sum_univ_one, Pi.smul_apply,
      smul_eq_mul, mul_comm, c, Matrix.mulVec, dotProduct] using hi
  have hd := congrArg decode heig
  rw [hdec, decode.map_smul] at hd
  have hρ : (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hρ₀ g)
  have hh := congrArg
    (fun X => X * (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)) hd
  simpa only [Matrix.mul_assoc, hρ, Matrix.mul_one, Matrix.smul_mul] using hh


open scoped InnerProductSpace Kronecker
namespace Matrix

private noncomputable def fromColumnVector {D : ℕ} :
    ((Fin D × Fin D) → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun v := fun i j => v (j, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem exists_identity_intertwiner_frame {D : ℕ} [NeZero D] :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ J : Matrix (Fin D × Fin D) (Fin 1) ℂ,
      J.IsIsometry ∧ (∀ i, J i 0 = a * (1 : Matrix (Fin D) (Fin D) ℂ).vec i) ∧
      IsUnit (((a⁻¹ : ℂ) • fromColumnVector) (fun i => J i 0)) := by
  let e := frobeniusEquivEuclidean (Fin D) (Fin D)
  let x := e (1 : Matrix (Fin D) (Fin D) ℂ)
  have hxne : x ≠ 0 := by
    intro hx
    exact one_ne_zero (e.injective (by simpa only [x, e.map_zero] using hx))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  let v : EuclideanSpace ℂ (Fin D × Fin D) := ‖x‖⁻¹ • x
  have hvnorm : ‖v‖ = 1 := by
    change ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
  let a : ℂ := (‖x‖ : ℂ)⁻¹
  have ha : a ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hxpos.ne')
  let J : Matrix (Fin D × Fin D) (Fin 1) ℂ := fun i _ => WithLp.ofLp v i
  have hJa : ∀ i, J i 0 = a * (1 : Matrix (Fin D) (Fin D) ℂ).vec i := by
    intro i
    change ‖x‖⁻¹ • WithLp.ofLp x i = a * (1 : Matrix (Fin D) (Fin D) ℂ).vec i
    have hxvec : WithLp.ofLp x = (1 : Matrix (Fin D) (Fin D) ℂ).vec := rfl
    rw [hxvec]
    change (↑(‖x‖⁻¹) : ℂ) * _ = _
    rw [Complex.ofReal_inv]
  have hJIso : J.IsIsometry := by
    change Jᴴ * J = 1
    ext i j
    fin_cases i
    fin_cases j
    change (∑ i, star (WithLp.ofLp v i) * WithLp.ofLp v i) = 1
    have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v
    rw [hvnorm] at hi
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
    simpa [dotProduct, mul_comm] using hi
  refine ⟨a, ha, J, hJIso, hJa, ?_⟩
  have hdecode : ((a⁻¹ : ℂ) • fromColumnVector) (fun i => J i 0) = 1 := by
    ext i j
    change a⁻¹ * J (j, i) 0 = (1 : Matrix (Fin D) (Fin D) ℂ) i j
    rw [hJa]
    exact inv_mul_cancel_left₀ ha _
  rw [hdecode]
  exact isUnit_one

end Matrix

namespace Matrix
private noncomputable def choiEuclideanLinearMap {D : ℕ} (a : ℂ) :
    (EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D × Fin D)) →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ where
  toFun B := fun ji kl => (a * star a) * WithLp.ofLp
    (B (frobeniusEquivEuclidean (Fin D) (Fin D) (single ji.1 kl.1 1))) (kl.2, ji.2)
  map_add' B C := by
    ext ji kl
    change (a * star a) * ((B + C)
      (frobeniusEquivEuclidean (Fin D) (Fin D) (single ji.1 kl.1 1))).ofLp
      (kl.2, ji.2) = _ + _
    simp only [_root_.add_apply, PiLp.add_apply, mul_add]
  map_smul' c B := by
    ext ji kl
    change (a * star a) * ((c • B)
      (frobeniusEquivEuclidean (Fin D) (Fin D) (single ji.1 kl.1 1))).ofLp
      (kl.2, ji.2) = c * _
    simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul]
    ring

private theorem choi_conjugationEuclideanCLM {D : ℕ}
    (a : ℂ) (V : Matrix (Fin D) (Fin D) ℂ) :
    choiEuclideanLinearMap a (conjugationEuclideanCLM V) =
      (a * star a) • vecMulVec V.vec (star V.vec) := by
  ext ⟨j, i⟩ ⟨k, l⟩
  change (a * star a) * (V * single j k 1 * Vᴴ : Matrix (Fin D) (Fin D) ℂ) i l =
    (a * star a) * (V i j * star (V l k))
  congr 1
  rw [single_eq_single_vecMulVec_single, mul_vecMulVec, vecMulVec_mul]
  simp [vecMulVec_apply]


private theorem conjugationEuclideanCLM_comp {D : ℕ}
    (V W : Matrix (Fin D) (Fin D) ℂ) :
    (conjugationEuclideanCLM V).comp (conjugationEuclideanCLM W) =
      conjugationEuclideanCLM (V * W) := by
  ext x
  obtain ⟨X, rfl⟩ := (frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  simp only [ContinuousLinearMap.comp_apply, conjugationEuclideanCLM_apply,
    conjTranspose_mul, Matrix.mul_assoc]

private theorem conjugationEuclideanCLM_one {D : ℕ} :
    conjugationEuclideanCLM (1 : Matrix (Fin D) (Fin D) ℂ) = .id ℂ _ := by
  ext x
  obtain ⟨X, rfl⟩ := (frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  simp only [conjugationEuclideanCLM_apply, conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one, ContinuousLinearMap.id_apply]

private theorem norm_conjugationEuclideanCLM_le_one {D : ℕ}
    (V : Matrix (Fin D) (Fin D) ℂ) (hV : V ∈ unitaryGroup (Fin D) ℂ) :
    ‖conjugationEuclideanCLM V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  obtain ⟨X, rfl⟩ := (frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  rw [conjugationEuclideanCLM_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, frobenius_norm_unitary_conjugation V X hV, one_mul]

private theorem choi_intertwiner_orbit_difference {D : ℕ}
    (a : ℂ) (J₀ : Matrix (Fin D × Fin D) (Fin 1) ℂ)
    (hJ : ∀ i, J₀ i 0 = a * (1 : Matrix (Fin D) (Fin D) ℂ).vec i)
    (V W : Matrix (Fin D) (Fin D) ℂ) (hW : W ∈ unitaryGroup (Fin D) ℂ) :
    let S := W.map star ⊗ₖ V
    S * (J₀ * J₀ᴴ) * Sᴴ - J₀ * J₀ᴴ =
      choiEuclideanLinearMap a
        ((conjugationEuclideanCLM V - conjugationEuclideanCLM W).comp
          (conjugationEuclideanCLM Wᴴ)) := by
  let S := W.map star ⊗ₖ V
  let Z := V * Wᴴ
  have hW' : W * Wᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hW
  have hOp : (conjugationEuclideanCLM V - conjugationEuclideanCLM W).comp
      (conjugationEuclideanCLM Wᴴ) = conjugationEuclideanCLM Z - .id ℂ _ := by
    rw [ContinuousLinearMap.sub_comp, conjugationEuclideanCLM_comp,
      conjugationEuclideanCLM_comp, hW', conjugationEuclideanCLM_one]
  rw [hOp, LinearMap.map_sub, ← conjugationEuclideanCLM_one,
    choi_conjugationEuclideanCLM, choi_conjugationEuclideanCLM]
  have hcol : ∀ i, (S * J₀) i 0 = a * Z.vec i := by
    intro i
    have hj : (fun i => J₀ i 0) = a • (1 : Matrix (Fin D) (Fin D) ℂ).vec := by
      ext i
      exact hJ i
    change (S *ᵥ (fun i => J₀ i 0)) i = _
    rw [hj, Matrix.mulVec_smul, kronecker_mulVec_vec]
    simp only [Matrix.mul_one]
    rfl
  have hleft : S * (J₀ * J₀ᴴ) * Sᴴ =
      (a * star a) • vecMulVec Z.vec (star Z.vec) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (S * J₀), ← conjTranspose_mul]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change (S * J₀) i 0 * star ((S * J₀) j 0) =
      (a * star a) * (Z.vec i * star (Z.vec j))
    rw [hcol, hcol, star_mul]
    ring
  have hright : J₀ * J₀ᴴ =
      (a * star a) • vecMulVec (1 : Matrix (Fin D) (Fin D) ℂ).vec
        (star (1 : Matrix (Fin D) (Fin D) ℂ).vec) := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change J₀ i 0 * star (J₀ j 0) =
      (a * star a) * ((1 : Matrix (Fin D) (Fin D) ℂ).vec i *
        star ((1 : Matrix (Fin D) (Fin D) ℂ).vec j))
    rw [hJ, hJ, star_mul]
    ring
  exact congrArg₂ (· - ·) hleft hright


private theorem exists_adjoint_radius_for_intertwiner_orbit
    {D : ℕ} (a : ℂ) (J₀ : Matrix (Fin D × Fin D) (Fin 1) ℂ)
    (hJ : ∀ i, J₀ i 0 = a * (1 : Matrix (Fin D) (Fin D) ℂ).vec i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V W : Matrix (Fin D) (Fin D) ℂ,
      W ∈ unitaryGroup (Fin D) ℂ →
      ‖conjugationEuclideanCLM V - conjugationEuclideanCLM W‖ < δ →
      let S := W.map star ⊗ₖ V
      ‖S * (J₀ * J₀ᴴ) * Sᴴ - J₀ * J₀ᴴ‖ < ε := by
  let K := choiEuclideanLinearMap (D := D) a
  have hcont : Continuous fun B => ‖K B‖ :=
    continuous_norm.comp K.continuous_of_finiteDimensional
  have hevent : ∀ᶠ B in 𝓝 (0 : EuclideanSpace ℂ (Fin D × Fin D) →L[ℂ]
      EuclideanSpace ℂ (Fin D × Fin D)), ‖K B‖ < ε :=
    hcont.continuousAt.eventually (Iio_mem_nhds (by simpa only [map_zero, norm_zero] using hε))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ, hδ, fun V W hW hnear => ?_⟩
  dsimp only
  rw [choi_intertwiner_orbit_difference a J₀ hJ V W hW]
  apply hball
  rw [dist_zero_right]
  have hW' : Wᴴ ∈ unitaryGroup (Fin D) ℂ := by
    simpa only [star_eq_conjTranspose] using Unitary.star_mem hW
  have hN := norm_conjugationEuclideanCLM_le_one Wᴴ hW'
  calc
    _ ≤ ‖conjugationEuclideanCLM V - conjugationEuclideanCLM W‖ *
        ‖conjugationEuclideanCLM Wᴴ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖conjugationEuclideanCLM V - conjugationEuclideanCLM W‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hN
        (norm_nonneg (conjugationEuclideanCLM V - conjugationEuclideanCLM W))
    _ < δ := hnear


end Matrix

namespace TNLean.Algebra.ProjectiveRepresentation

/-- Uniformly close unitary adjoint actions have cohomologous factor systems.
This finite-dimensional rigidity statement requires no topology on the group and
no continuous choice of projective representatives. It is an auxiliary result for
the varying-support argument in arXiv:1010.3732, Appendix C, lines 2653–2717;
it does not derive virtual data from a physical Hamiltonian path. -/
theorem exists_uniform_adjoint_rigidity_radius {D : ℕ} [NeZero D] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (G : Type) [Group G] (ω₀ ω₁ : ScalarCocycle G)
      (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
      (ρ₁ : ProjectiveRepresentation (D := D) ω₁),
      (∀ g, (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) →
      (∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) →
      (∀ g, ‖Matrix.conjugationEuclideanCLM (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) -
        Matrix.conjugationEuclideanCLM (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)‖ < δ) →
      ω₁.CohomologousTo ω₀ := by
  obtain ⟨a, _, J₀, hJ₀, hJa, hdecode⟩ :=
    Matrix.exists_identity_intertwiner_frame (D := D)
  obtain ⟨ε, hε, hOrbit⟩ := cohomologous_of_uniformly_near_intertwiner_orbit
    J₀ hJ₀ ((a⁻¹ : ℂ) • Matrix.fromColumnVector) hdecode
  obtain ⟨δ, hδ, hNear⟩ :=
    Matrix.exists_adjoint_radius_for_intertwiner_orbit a J₀ hJa ε hε
  refine ⟨δ, hδ, ?_⟩
  intro G _ ω₀ ω₁ ρ₀ ρ₁ h₀ h₁ hclose
  apply hOrbit G ω₀ ω₁ ρ₀ ρ₁ (homMatrix ρ₀ ρ₁)
  · exact fun g => homMatrix_mem_unitaryGroup ρ₀ ρ₁ h₀ h₁ g
  · exact h₀
  · exact homMatrix_conjugation_mul ρ₀ ρ₁ h₀ h₁
  · intro g v
    let X : Matrix (Fin D) (Fin D) ℂ := Matrix.fromColumnVector v
    have hv : X.vec = v := rfl
    change a⁻¹ • Matrix.fromColumnVector (homMatrix ρ₀ ρ₁ g *ᵥ v) =
      (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) *
        (a⁻¹ • Matrix.fromColumnVector v) * (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ
    rw [← hv, homMatrix, Matrix.kronecker_mulVec_vec]
    change a⁻¹ • ((ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) * X *
      (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ)ᴴ) = _
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  · intro g
    exact hNear (ρ₁.X g) (ρ₀.X g) (h₀ g) (hclose g)

end TNLean.Algebra.ProjectiveRepresentation

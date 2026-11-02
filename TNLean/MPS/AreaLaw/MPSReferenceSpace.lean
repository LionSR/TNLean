/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OpenMPSSpan
import QICLean.Analysis.ViableSubspace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reference spaces from finite matrix product approximations

Approximants to an orthonormal basis define a linear map close to the
inclusion of the original subspace. A small total squared error gives an
image of the same dimension, mutually close to the original space.
The finite-span theorem gives a uniform exact matrix product bond bound
for every vector of this one image space.

This is a finite-dimensional auxiliary to the reference-space step in
ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805.
The approximating vectors and their matrix product representations are
explicit inputs here; the physical ground-space construction supplies
them separately.
-/

open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The finite coefficient estimate used when approximants to basis vectors
are combined, supporting ALVV, arXiv:1602.08828v2, proof of `t:alg1`,
lines 1801–1805. -/
private theorem norm_sum_smul_sq_le
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (v : ι → E) :
    ‖∑ i, c i • v i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have hnorm := norm_sum_le (s := Finset.univ) (f := fun i ↦ c i • v i)
  simp only [norm_smul] at hnorm
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ ‖c i‖) (fun i ↦ ‖v i‖))

/-- The map defined by approximants to an orthonormal basis differs from
inclusion by the sum of their squared errors. This supports the reference
space in ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805. -/
private theorem basis_approximation_error_sq_le
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : Submodule ℂ E) (b : OrthonormalBasis ι ℂ T) (phi : ι → E)
    (eta : ℝ) (herror : ∑ i, ‖phi i - (b i : E)‖ ^ 2 ≤ eta) (x : T) :
    ‖b.toBasis.constr ℂ phi x - (x : E)‖ ^ 2 ≤ eta * ‖x‖ ^ 2 := by
  have hsum : ∑ i, b.repr x i • (b i : E) = (x : E) := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using congrArg T.subtype (b.sum_repr x)
  have hexpand : b.toBasis.constr ℂ phi x - (x : E) =
      ∑ i, b.repr x i • (phi i - (b i : E)) := by
    rw [Module.Basis.constr_apply_fintype]
    simp only [Module.Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [← hsum]
    simp only [smul_sub, Finset.sum_sub_distrib]
  have hparseval : ∑ i, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
    simp_rw [b.repr_apply_apply]
    exact b.sum_sq_norm_inner_right x
  rw [hexpand]
  calc
    _ ≤ (∑ i, ‖b.repr x i‖ ^ 2) * ∑ i, ‖phi i - (b i : E)‖ ^ 2 :=
      norm_sum_smul_sq_le (fun i ↦ b.repr x i) (fun i ↦ phi i - (b i : E))
    _ ≤ (∑ i, ‖b.repr x i‖ ^ 2) * eta :=
      mul_le_mul_of_nonneg_left herror (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    _ = eta * ‖x‖ ^ 2 := by rw [hparseval, mul_comm]

/-- Best approximation by orthogonal projection, used in the two directions
of the reference-space comparison in ALVV, arXiv:1602.08828v2, proof of
`t:alg1`, lines 1801–1805. -/
private theorem norm_sub_starProjection_le_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : Submodule ℂ E) (x y : E) (hy : y ∈ T) :
    ‖x - T.starProjection x‖ ≤ ‖x - y‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ (⟨y, hy⟩ : T)

/-- A linear approximation to inclusion with squared error at most
`epsilon/4` has the same dimension and gives mutual `epsilon`-closeness.
This supports the reference-space step in ALVV, arXiv:1602.08828v2,
proof of `t:alg1`, lines 1801–1805. -/
private theorem range_close_of_subtype_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : Submodule ℂ E) (F : T →ₗ[ℂ] E)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (herror : ∀ x : T, ‖F x - (x : E)‖ ^ 2 ≤ epsilon / 4 * ‖x‖ ^ 2) :
    Module.finrank ℂ F.range = Module.finrank ℂ T ∧
      Submodule.IsCloseTo epsilon F.range T ∧
      Submodule.IsCloseTo epsilon T F.range := by
  have hsmall (x : T) : ‖F x - (x : E)‖ ^ 2 ≤ ‖x‖ ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_right
      (by linarith only [hepsilon1] : epsilon / 4 ≤ 1 / 4) (sq_nonneg ‖x‖)
    exact (herror x).trans (by nlinarith only [h])
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := hsmall x
    rw [hx, zero_sub, norm_neg] at h
    change ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 / 4 at h
    have hs : ‖x‖ ^ 2 = 0 := by nlinarith only [h, sq_nonneg ‖x‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hforward : Submodule.IsCloseTo epsilon F.range T := by
    rw [Submodule.isCloseTo_iff]
    intro x hx
    let v : T := ⟨x, hx⟩
    have hbest := norm_sub_starProjection_le_of_mem F.range x (F v) ⟨v, rfl⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbest 2
    have herr := herror v
    change ‖F v - x‖ ^ 2 ≤ epsilon / 4 * ‖x‖ ^ 2 at herr
    rw [norm_sub_rev] at herr
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x F.range
    rw [Submodule.starProjection_orthogonal_val] at hpy
    nlinarith only [hsq, herr, hpy, mul_nonneg hepsilon (sq_nonneg ‖x‖)]
  refine ⟨LinearMap.finrank_range_of_inj hinj, hforward, ?_⟩
  rw [Submodule.isCloseTo_iff]
  rintro _ ⟨x, rfl⟩
  have hhalf : ‖F x - (x : E)‖ ≤ ‖x‖ / 2 := by
    nlinarith only [hsmall x, norm_nonneg (F x - (x : E)), norm_nonneg x]
  have htriangle : ‖x‖ ≤ ‖F x‖ + ‖F x - (x : E)‖ := by
    simpa only [sub_sub_cancel, Submodule.norm_coe] using norm_sub_le (F x) (F x - (x : E))
  have hnorm : ‖x‖ ≤ 2 * ‖F x‖ := by linarith only [hhalf, htriangle]
  have hsq := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
  have hscale := mul_le_mul_of_nonneg_left hsq hepsilon
  have herr : ‖F x - (x : E)‖ ^ 2 ≤ epsilon * ‖F x‖ ^ 2 := by
    nlinarith only [herror x, hscale]
  have hbest := norm_sub_starProjection_le_of_mem T (F x) (x : E) x.property
  have hproj := pow_le_pow_left₀ (norm_nonneg _) hbest 2
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection (F x) T
  rw [Submodule.starProjection_orthogonal_val] at hpy
  nlinarith only [hproj, herr, hpy]

/-- Matrix product approximants to an orthonormal basis span one nearby
subspace of the same dimension. Every vector of that fixed subspace has
bond dimension at most the basis cardinality times the individual bound.
This is an auxiliary with explicit approximating vectors, supporting ALVV,
arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1805; it does not
construct those vectors from a physical Hamiltonian. -/
theorem exists_reference_subspace_of_isOpenMPS_basis_approximations
    {L q D : ℕ}
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (b : OrthonormalBasis (Fin (Module.finrank ℂ T)) ℂ T)
    (phi : Fin (Module.finrank ℂ T) → EuclideanSpace ℂ (Fin L → Fin q))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (herror : ∑ i, ‖phi i - (b i : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤ epsilon / 4)
    (hphi : ∀ i, IsOpenMPS L q D (fun x ↦ phi i x)) :
    ∃ U : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)),
      Module.finrank ℂ U = Module.finrank ℂ T ∧
      Submodule.IsCloseTo epsilon U T ∧ Submodule.IsCloseTo epsilon T U ∧
      ∀ v ∈ U, IsOpenMPS L q (Module.finrank ℂ T * D) (fun x ↦ v x) := by
  classical
  let F : T →ₗ[ℂ] EuclideanSpace ℂ (Fin L → Fin q) := b.toBasis.constr ℂ phi
  have hF (x : T) : ‖F x - (x : EuclideanSpace ℂ (Fin L → Fin q))‖ ^ 2 ≤
      epsilon / 4 * ‖x‖ ^ 2 :=
    basis_approximation_error_sq_le T b phi (epsilon / 4) herror x
  obtain ⟨hdim, hUT, hTU⟩ := range_close_of_subtype_error T F epsilon hepsilon hepsilon1 hF
  refine ⟨F.range, hdim, hUT, hTU, ?_⟩
  intro v hv
  let raw := WithLp.linearEquiv 2 ℂ (((Fin L → Fin q) → ℂ))
  let S : Finset ((Fin L → Fin q) → ℂ) := Finset.univ.image (fun i ↦ raw (phi i))
  have hspan : v ∈ Submodule.span ℂ (Set.range phi) := by
    simpa only [F, Module.Basis.constr_range] using hv
  have hvraw : raw v ∈ Submodule.span ℂ (S : Set ((Fin L → Fin q) → ℂ)) := by
    have h := Submodule.apply_mem_span_image_of_mem_span raw.toLinearMap hspan
    change raw v ∈ Submodule.span ℂ (raw '' Set.range phi) at h
    simpa only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp']
      using h
  have hS : ∀ w ∈ S, IsOpenMPS L q D w := by
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact hphi i
  have hcard : S.card ≤ Module.finrank ℂ T := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (f := fun i ↦ raw (phi i))
        (s := (Finset.univ : Finset (Fin (Module.finrank ℂ T)))))
  have hmps := isOpenMPS_of_mem_span S hS hvraw
  exact hmps.mono (Nat.mul_le_mul_right D hcard)

end TNLean.MPS.AreaLaw

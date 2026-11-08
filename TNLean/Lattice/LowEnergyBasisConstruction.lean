/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.LowEnergyCommutatorSum
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Construction of a basis for low-energy compressions

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, chooses a basis of a
degenerate ground space to control the sum of the off-diagonal parts of the local terms.
Scalar compressions on a multidimensional subspace require no further diagonalization.
The construction below uses the commuting centre of the real span of the compressions.

**Scope restriction (geometric growth):** only the physical summed theorem in the
graph section assumes polynomial sphere growth with size-independent constants.
Source lines 169–190 do not supply that hypothesis; the unrestricted version of eq.
`oibu` is false, as shown mathematically in
`docs/paper-gaps/hastings05_tree_basis_counterexample.tex`. See also
`docs/paper-gaps/hastings05_geometric_growth_scope.tex`.
The finite-dimensional basis construction and its system-dependent conditioning
estimate are unaffected.
-/

open scoped InnerProductSpace

namespace TNLean.Lattice

section NormComparison

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ F]

/-- The norm of the inverse of the commutator map on the quotient by its kernel. With the
quotient norm this is the reciprocal of its lower norm. It records the conditioning that
replaces the spectral denominators in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1683–1708. It need not be bounded uniformly along a sequence of systems. -/
noncomputable def quotientConditionNumber (T : F →ₗ[ℝ] G) : ℝ :=
  letI : IsClosed (T.ker : Set F) := T.ker.closed_of_finiteDimensional
  ‖T.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap‖

theorem quotientConditionNumber_nonneg (T : F →ₗ[ℝ] G) :
    0 ≤ quotientConditionNumber T := by
  let : IsClosed (T.ker : Set F) := T.ker.closed_of_finiteDimensional
  change 0 ≤ ‖T.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap‖
  exact norm_nonneg (T.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap :
    T.range →L[ℝ] F ⧸ T.ker)

/-- A contraction vanishing on the kernel of `T` is bounded by the explicit quotient
conditioning of `T`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_le_quotientConditionNumber_mul (T : F →ₗ[ℝ] G) (S : F →ₗ[ℝ] H)
    (hker : T.ker ≤ S.ker) (hS : ∀ x, ‖S x‖ ≤ ‖x‖) (x : F) :
    ‖S x‖ ≤ quotientConditionNumber T * ‖T x‖ := by
  let : IsClosed (T.ker : Set F) := T.ker.closed_of_finiteDimensional
  let U := T.ker.liftQ S hker
  have hU (q : F ⧸ T.ker) : ‖U q‖ ≤ ‖q‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt q hε
    calc ‖U q‖ = ‖S y‖ := by rw [← hy]; rfl
      _ ≤ ‖q‖ + ε := (hS y).trans hnorm.le
  calc ‖S x‖ = ‖U (T.ker.mkQ x)‖ := rfl
    _ ≤ ‖T.ker.mkQ x‖ := hU _
    _ = ‖T.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap
        ⟨T x, T.mem_range_self x⟩‖ := by
      congr 1
      exact (T.quotKerEquivRange_symm_apply_image x _).symm
    _ ≤ quotientConditionNumber T * ‖T x‖ :=
      T.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap.le_opNorm _

end NormComparison

section JointBasis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Every commuting family of self-adjoint operators on a finite-dimensional complex inner
product space has a common orthonormal eigenbasis. No simplicity of the joint eigenvalues is
required. This supplies the terminal scalar subspaces in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_joint_eigenvectors (T : ι → E →L[ℂ] E)
    (hT : ∀ i, IsSelfAdjoint (T i)) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∀ i a, ∃ c : ℂ, T i (b a) = c • b a := by
  classical
  let A : ι → Module.End ℂ E := fun i => (T i).toLinearMap
  have hA : ∀ i, (A i).IsSymmetric := fun i => (hT i).isSymmetric
  have hAA : Pairwise fun i j => Commute (A i) (A j) := fun i j _ => by
    ext x
    exact congrArg (fun U : E →L[ℂ] E => U x) (hcomm i j).eq
  let V : (ι → ℂ) → Submodule ℂ E := fun c => ⨅ i, Module.End.eigenspace (A i) (c i)
  have hOrth : OrthogonalFamily ℂ (fun c => V c) fun c => (V c).subtypeₗᵢ :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hA
  have hTop : (⨆ c, V c) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hA hAA
  have hInt : DirectSum.IsInternal V := hOrth.isInternal_iff.mpr (by
    rw [hTop, Submodule.top_orthogonal_eq_bot])
  let := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hInt' := (DirectSum.isInternal_ne_bot_iff (A := V)).mpr hInt
  have hOrth' := hOrth.comp (Subtype.val_injective (p := fun c => V c ≠ ⊥))
  let b := hInt'.subordinateOrthonormalBasis rfl hOrth'
  refine ⟨b, fun i a => ?_⟩
  let c := hInt'.subordinateOrthonormalBasisIndex rfl a hOrth'
  have hm : b a ∈ V c.val := hInt'.subordinateOrthonormalBasis_subordinate rfl a hOrth'
  exact ⟨c.val i, Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hm i)⟩

end JointBasis

section CompressionSpan

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable local instance {m : ℕ} : NormedSpace ℝ (Fin m → E →L[ℂ] E) := Pi.normedSpace

/-- The real dimension of the self-adjoint endomorphisms of an `n`-dimensional complex inner
product space is `n²`. Thus at most `n²` original compressions suffice in the construction of
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem finrank_selfAdjoint_continuousLinearMap :
    Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) = (Module.finrank ℂ E) ^ 2 := by
  have h := (imaginaryPart (A := E →L[ℂ] E)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr imaginaryPart_surjective, finrank_top,
    ker_imaginaryPart] at h
  have hd : Module.finrank ℝ (E →L[ℂ] E) = 2 * (Module.finrank ℂ E) ^ 2 := by
    rw [finrank_real_of_complex,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).finrank_eq,
      Module.finrank_linearMap]
    ring
  change Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) +
    Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) = _ at h
  omega

/-- The commutator map of a selected finite family, restricted to a real subspace of
endomorphisms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1708. -/
def compressionCommutatorMap {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : V →ₗ[ℝ] (Fin m → E →L[ℂ] E) where
  toFun x i := A i * x.val - x.val * A i
  map_add' x y := by ext i u; simp [mul_add, add_mul]; abel
  map_smul' c x := by ext i u; simp [smul_sub]

set_option backward.isDefEq.respectTransparency false in
/-- The quotient conditioning of the selected compression commutator map, with the
operator norm on the real compression span and the maximum norm on the commutators.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def compressionConditionNumber {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : ℝ :=
  letI : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.complexToReal
  letI : NormedSpace ℝ V := V.normedSpace
  letI : NormedSpace ℝ (Fin m → E →L[ℂ] E) := Pi.normedSpace
  quotientConditionNumber (F := V) (G := Fin m → E →L[ℂ] E) (compressionCommutatorMap V A)

set_option backward.isDefEq.respectTransparency false in
theorem compressionConditionNumber_nonneg {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : 0 ≤ compressionConditionNumber V A := by
  unfold compressionConditionNumber
  exact quotientConditionNumber_nonneg (compressionCommutatorMap V A)

set_option backward.isDefEq.respectTransparency false in
/-- A real span of self-adjoint operators has an orthonormal basis in which every
off-diagonal entry is controlled by its commutators with any finite spanning family.
The kernel consists of the centre of this span, whose members commute and hence have a
common orthonormal eigenbasis. This replaces the final separation assertion in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_norm_inner_le_compressionCommutatorMap
    (V : Submodule ℝ (E →L[ℂ] E)) (hV : ∀ x ∈ V, IsSelfAdjoint x) {m : ℕ}
    (A : Fin m → E →L[ℂ] E) (hspan : Submodule.span ℝ (Set.range A) = V) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∀ (x : V) a c, a ≠ c →
        ‖⟪b a, x.val (b c)⟫_ℂ‖ ≤
          quotientConditionNumber (compressionCommutatorMap V A) *
            ∑ i, ‖A i * x.val - x.val * A i‖ := by
  classical
  let T := compressionCommutatorMap V A
  have hcentral (x : T.ker) (y : V) : Commute x.val.val y.val := by
    have hy : y.val ∈ Submodule.span ℝ (Set.range A) := hspan.symm ▸ y.property
    suffices ∀ z ∈ Submodule.span ℝ (Set.range A), Commute x.val.val z from this y.val hy
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      have hx := congrFun (LinearMap.mem_ker.mp x.property) i
      exact (sub_eq_zero.mp hx).symm
    | zero => exact Commute.zero_right _
    | add y z _ _ hy hz => exact hy.add_right hz
    | smul c y _ hy => exact hy.smul_right c
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_joint_eigenvectors
    (fun z : T.ker => z.val.val)
    (fun z => hV _ z.val.property) (fun z w => hcentral z w.val)
  refine ⟨b, fun x a c hac => ?_⟩
  let S : V →ₗ[ℝ] ℂ :=
    (((innerSL ℂ (b a)).comp (ContinuousLinearMap.apply ℂ E (b c))).restrictScalars ℝ).toLinearMap
      |>.comp V.subtype
  have hker : T.ker ≤ S.ker := by
    intro y hy
    obtain ⟨r, hr⟩ := hb ⟨y, hy⟩ c
    change ⟪b a, y.val (b c)⟫_ℂ = 0
    rw [hr, inner_smul_right, b.orthonormal.inner_eq_zero hac, mul_zero]
  have hS (y : V) : ‖S y‖ ≤ ‖y‖ := by
    change ‖⟪b a, y.val (b c)⟫_ℂ‖ ≤ ‖y.val‖
    calc _ ≤ ‖b a‖ * ‖y.val (b c)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y.val‖ := by simpa only [b.orthonormal.1 a, b.orthonormal.1 c, one_mul, mul_one]
          using y.val.le_opNorm (b c)
  have hcomp : ‖S x‖ ≤ quotientConditionNumber T * ‖T x‖ :=
    norm_le_quotientConditionNumber_mul (F := V) (G := Fin m → E →L[ℂ] E) (H := ℂ)
      T S hker hS x
  have hTx : ‖T x‖ ≤ ∑ i, ‖A i * x.val - x.val * A i‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr
    intro i
    exact Finset.single_le_sum (f := fun j => ‖A j * x.val - x.val * A j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  change ‖S x‖ ≤ quotientConditionNumber T * _
  exact hcomp.trans (mul_le_mul_of_nonneg_left hTx (quotientConditionNumber_nonneg T))

/-- The real span of the original Hermitian compressions. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable abbrev realCompressionSpan (B : ι → E →L[ℂ] E) : Submodule ℝ (E →L[ℂ] E) :=
  Submodule.span ℝ (Set.range B)

set_option backward.isDefEq.respectTransparency false in
/-- Construction of the basis and of at most `n²` original compressions controlling every
off-diagonal entry. The coefficient is the explicit inverse lower norm of the commutator
map modulo its kernel; no spectral separation or chosen basis is assumed.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_norm_inner_le_commutators (B : ι → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) :
    ∃ (m : ℕ) (j : Fin m → ι)
      (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E),
      m ≤ (Module.finrank ℂ E) ^ 2 ∧
      Submodule.span ℝ (Set.range (B ∘ j)) = realCompressionSpan B ∧
      ∀ i a c, a ≠ c →
        ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
          compressionConditionNumber (realCompressionSpan B) (B ∘ j) *
            ∑ k, ‖B (j k) * B i - B i * B (j k)‖ := by
  classical
  let V := realCompressionSpan B
  have hV : V ≤ selfAdjoint.submodule ℝ (E →L[ℂ] E) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hB i)
  obtain ⟨A, hA, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range B)
  choose j hj using hA
  have hAj : B ∘ j = A := funext hj
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_norm_inner_le_compressionCommutatorMap V
    (fun x hx => hV hx) A hspan
  refine ⟨Module.finrank ℝ V, j, b, ?_, hAj.symm ▸ hspan, fun i a c hac => ?_⟩
  · exact (Submodule.finrank_mono hV).trans_eq finrank_selfAdjoint_continuousLinearMap
  · rw [hAj]
    simpa only [compressionConditionNumber, hj] using
      hb ⟨B i, Submodule.subset_span (Set.mem_range_self i)⟩ a c hac

end CompressionSpan

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundEigenspace H E₀) :=
  (groundEigenspace H E₀).innerProductSpace

section GroundSpace

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

local instance (H : Matrix ν ν ℂ) (E₀ : ℝ) : CompleteSpace (groundEigenspace H E₀) :=
  FiniteDimensional.complete ℂ (groundEigenspace H E₀)

/-- The compression `P W P`, acting on the ground eigenspace itself. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
noncomputable def groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    groundEigenspace H E₀ →L[ℂ] groundEigenspace H E₀ :=
  ((groundCompression H E₀ W).codRestrict (groundEigenspace H E₀)
    (fun _ => (groundEigenspace H E₀).starProjection_apply_mem _)).comp
      (groundEigenspace H E₀).subtypeL

@[simp]
theorem coe_groundSpaceCompression_apply (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ)
    (x : groundEigenspace H E₀) :
    (groundSpaceCompression H E₀ W x : EuclideanSpace ℂ ν) = groundCompression H E₀ W x := rfl

theorem isSelfAdjoint_groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ)
    {W : Matrix ν ν ℂ} (hW : W.IsHermitian) : IsSelfAdjoint (groundSpaceCompression H E₀ W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact (isSelfAdjoint_groundCompression H E₀ hW).isSymmetric x.val y.val

/-- The norm of a ground-space compression does not exceed the original term norm.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
theorem norm_groundSpaceCompression_le (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ ≤ ‖W‖ := by
  refine (show ‖groundSpaceCompression H E₀ W‖ ≤ ‖groundCompression H E₀ W‖ from ?_).trans
    (norm_groundCompression_le H E₀ W)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (groundCompression H E₀ W).le_opNorm x.val

/-- Restriction to the ground space does not increase the norm of the commutator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1683–1708. -/
theorem norm_groundSpaceCompression_commutator_le (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ ≤
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  exact (groundCompression H E₀ W * groundCompression H E₀ B -
    groundCompression H E₀ B * groundCompression H E₀ W).le_opNorm x.val

/-- The ambient compression has exactly the operator norm of its restriction to the
actual ground eigenspace. Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601. -/
theorem norm_groundSpaceCompression_eq (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ = ‖groundCompression H E₀ W‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦
      (groundCompression H E₀ W).le_opNorm x.val
  · refine ContinuousLinearMap.opNorm_le_bound (groundCompression H E₀ W)
      (norm_nonneg (groundSpaceCompression H E₀ W)) ?_
    intro x
    let y : groundEigenspace H E₀ :=
      ⟨(groundEigenspace H E₀).starProjection x,
        (groundEigenspace H E₀).starProjection_apply_mem x⟩
    have hCx : groundCompression H E₀ W x =
        (groundSpaceCompression H E₀ W y : EuclideanSpace ℂ ν) := by
      have hp : (groundEigenspace H E₀).starProjection
          ((groundEigenspace H E₀).starProjection x) =
          (groundEigenspace H E₀).starProjection x :=
        (groundEigenspace H E₀).starProjection_eq_self_iff.mpr
          ((groundEigenspace H E₀).starProjection_apply_mem x)
      simp only [y, coe_groundSpaceCompression_apply, groundCompression,
        mul_apply_eq_comp, hp]
    rw [hCx]
    exact ((groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left
        ((groundEigenspace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W)))

/-- Restricting a compressed commutator to the ground eigenspace preserves its norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601 and 1644–1654. -/
theorem norm_groundSpaceCompression_commutator_eq (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ =
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  apply le_antisymm (norm_groundSpaceCompression_commutator_le H E₀ W B)
  refine ContinuousLinearMap.opNorm_le_bound
    (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W)
    (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
      groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)) ?_
  intro x
  let y : groundEigenspace H E₀ :=
    ⟨(groundEigenspace H E₀).starProjection x,
      (groundEigenspace H E₀).starProjection_apply_mem x⟩
  have hp : (groundEigenspace H E₀).starProjection
      ((groundEigenspace H E₀).starProjection x) =
      (groundEigenspace H E₀).starProjection x :=
    (groundEigenspace H E₀).starProjection_eq_self_iff.mpr
      ((groundEigenspace H E₀).starProjection_apply_mem x)
  have hCx : (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W) x =
      ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W) y :
          EuclideanSpace ℂ ν) := by
    simp only [_root_.sub_apply, mul_apply_eq_comp, Submodule.coe_sub,
      coe_groundSpaceCompression_apply, y, groundCompression, hp]
  rw [hCx]
  exact ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
    groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left ((groundEigenspace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
          groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)))


end GroundSpace

section Graph

open GaussianFilter Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- A constructed orthonormal basis of the nonzero ground space satisfies a summed
off-diagonal estimate using at most `n²` actual local terms. The geometric constant is that
of the commutator row sum, and the additional factor is the explicitly displayed quotient
conditioning of the selected ground-space commutator map. This conditioning is not asserted
to be uniform in the system size. No basis, spectral refinement or separation hypothesis is
supplied. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu` and lines 1695–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le [NeZero d]
    (G : SimpleGraph ι) (X : κ → Finset ι) (a : κ → ι) (ha : ∀ k, a k ∈ X k)
    (h : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (hHerm : ∀ k, (h k).IsHermitian)
    (hSupport : ∀ k, h k ∈ supportedOperators d (X k : Set ι))
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ X k, ∀ z ∈ X k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (X k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ X j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : (∑ k, h k).IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    [NeZero (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀))] :
    let B : κ → groundEigenspace (∑ k, h k) E₀ →L[ℂ]
        groundEigenspace (∑ k, h k) E₀ :=
      fun i => groundSpaceCompression (∑ k, h k) E₀ (h i)
    ∃ (m : ℕ) (j : Fin m → κ)
      (b : OrthonormalBasis
        (Fin (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀))) ℂ
          (groundEigenspace (∑ k, h k) E₀)),
      m ≤ (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀)) ^ 2 ∧
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ k, h k) E₀ (gaussianFilteredTerm q ΔE (∑ k, h k) (h i)))‖ ≤
        (Module.finrank ℂ (groundEigenspace (∑ k, h k) E₀) - 1 : ℕ) *
          compressionConditionNumber (realCompressionSpan B) (B ∘ j) *
          ∑ k, commutatorConst R vR b₀ Kg kg *
            Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖h (j k)‖ *
              (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  classical
  let K := groundEigenspace (∑ k, h k) E₀
  let B := fun i => groundSpaceCompression (∑ k, h k) E₀ (h i)
  obtain ⟨m, j, b, hm, _, hb⟩ := exists_orthonormalBasis_norm_inner_le_commutators B
    (fun i => isSelfAdjoint_groundSpaceCompression _ _ (hHerm i))
  refine ⟨m, j, b, hm, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  let C := compressionConditionNumber (realCompressionSpan B) (B ∘ j)
  have hC : 0 ≤ C := compressionConditionNumber_nonneg _ _
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (ι → Fin d))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hent (i : κ) :
      ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (ι → Fin d)))
        (groundCompression (∑ k, h k) E₀ (h i))‖ ≤
        (Module.finrank ℂ K - 1 : ℕ) * (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) := by
    exact norm_offDiagonalPartFamily_le hv _ (by positivity) fun c e hce => hb i c e hce
  calc _ ≤ ∑ i, (Module.finrank ℂ K - 1 : ℕ) *
        (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) :=
      Finset.sum_le_sum fun i _ => hent i
    _ = (Module.finrank ℂ K - 1 : ℕ) * C *
        ∑ k, ∑ i, ‖B (j k) * B i - B i * B (j k)‖ := by
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hC)
      refine Finset.sum_le_sum fun k _ => ?_
      refine (Finset.sum_le_sum fun i _ => norm_groundSpaceCompression_commutator_le
        (∑ k, h k) E₀ (h (j k)) (h i)).trans ?_
      exact sum_norm_groundCompression_commutator_le G X a ha h hHerm hSupport R hDiam vR
        hCard b₀ hBudget Kg kg hGrowth hΔE hH hgap (j k)

end Graph

end TNLean.Lattice

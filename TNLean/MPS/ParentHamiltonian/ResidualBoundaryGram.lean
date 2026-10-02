/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualBoundaryOverlap
import TNLean.MPS.ParentHamiltonian.GramConvergence
import TNLean.MPS.ParentHamiltonian.PeriodicPrimitiveGroundSpace
import TNLean.MPS.Periodic.SectorLift
import QICLean.Channel.FixedPoint.LimitingGramMetric

/-!
# Gram operators of correlated residual boundaries

For a rectangular boundary \(Y\in M_{D\times E}(\mathbb C)\), the
correlated tail map has fibers \(V^\dagger A^\tau Y\).
Its Gram form is determined by
\(Q_r=\sum_\tau A^{\tau\dagger}VV^\dagger A^\tau\).
Under trace-preserving normalization and the cyclic shift
\(P_aA_i=A_iP_{a+1}\), the support condition \(VV^\dagger=P_a\)
gives \(Q_r=P_{a+r}\). Thus the tail map is a contraction and is
isometric on the row corner \(P_{a+r}Y=Y\).

The residual Gram operator is the pullback of the ordinary blocked-prefix
Gram operator through this correlated map. Its limiting metric is
\(Y\mapsto(\operatorname{tr}\rho)^{-1}Q_rY\rho\).
The norm of the residual error is at most the ordinary prefix Gram error,
with no factor depending on the original tail length. Primitive prefix
convergence therefore gives geometric convergence uniformly in that length.

These are finite-dimensional intermediate estimates. They do not assert a
three-interval projection defect, an intersection property, or a spectral gap
for every original chain length. The tail and virtual boundary remain
correlated; no independent spectator condition is assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i),
lines 2442--2531; the cyclic word transport and compressed sectors are those
of DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D E L : ℕ}

/-- The correlated original tail has square virtual fibers \(V^\dagger A^\tau Y\)
and a rectangular boundary domain, with column index before row index.
This is the virtual factor of the residual boundary contraction in DCCSP17,
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. -/
noncomputable def correlatedTailMapES (A : MPSTensor d D)
    (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] BoundaryFamilySpace (D := E) (Cfg d r) :=
  LinearMap.toContinuousLinearMap
    ((boundaryFamilyEquiv (D := E) (Cfg d r)).symm.toLinearMap.comp
      ({ toFun := fun x τ => Vᴴ * Kraus.evalWord A (List.ofFn τ) *
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm x
         map_add' := by intros; funext τ; simp [Matrix.mul_add]
         map_smul' := by intros; funext τ; simp } :
        EuclideanSpace ℂ (Fin E × Fin D) →ₗ[ℂ]
          (Cfg d r → Matrix (Fin E) (Fin E) ℂ)))

/-- Each fiber of the correlated tail map is the literal matrix
\(V^\dagger A^\tau Y\), including an empty tail. -/
@[simp] theorem boundaryFamilyEquiv_correlatedTailMapES_apply
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Y : Matrix (Fin D) (Fin E) ℂ) (τ : Cfg d r) :
    boundaryFamilyEquiv (D := E) (Cfg d r)
      (correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)) τ =
      Vᴴ * Kraus.evalWord A (List.ofFn τ) * Y := by
  change boundaryFamilyEquiv (D := E) (Cfg d r)
    ((boundaryFamilyEquiv (D := E) (Cfg d r)).symm
      (fun τ => Vᴴ * Kraus.evalWord A (List.ofFn τ) *
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm
          (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y))) τ = _
  rw [(boundaryFamilyEquiv (D := E) (Cfg d r)).apply_symm_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).symm_apply_apply]

/-- The correlated tail Gram form is \(\operatorname{tr}(Y^\dagger Q_r Z)\),
where \(Q_r=\sum_\tau A^{\tau\dagger}VV^\dagger A^\tau\). -/
theorem inner_correlatedTailMapES
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Y Z : Matrix (Fin D) (Fin E) ℂ) :
    ⟪correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y),
      correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Z)⟫_ℂ =
      Matrix.trace (Yᴴ * (∑ τ : Cfg d r,
        (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
          Kraus.evalWord A (List.ofFn τ)) * Z) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  change (∑ τ : Cfg d r,
    inner ℂ (boundaryFamilyFiber (D := E)
      (correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)) τ)
    (boundaryFamilyFiber (D := E)
      (correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Z)) τ)) = _
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyEquiv_correlatedTailMapES_apply, Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]

/-- Trace-preserving normalization and the cyclic letter shift derive the
exact row corner \(\sum_\tau A^{\tau\dagger}P_aA^\tau=P_{a+r}\).
Source: DCCSP17, arXiv:1708.00029, the off-diagonal cyclic equation iterated
in Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem sum_word_conjTranspose_cyclic_projection_mul_word
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hShift : ∀ a i, P a * A i = A i * P (a + 1)) (a : Fin m) (r : ℕ) :
    ∑ τ : Cfg d r,
      (Kraus.evalWord A (List.ofFn τ))ᴴ * P a * Kraus.evalWord A (List.ofFn τ) =
      P (a + r • (1 : Fin m)) := by
  simp_rw [Matrix.mul_assoc,
    projector_mul_evalWord_eq_evalWord_mul_projector P A hShift,
    List.length_ofFn]
  simp_rw [← Matrix.mul_assoc]
  rw [← Matrix.sum_mul,
    sum_evalWord_conjTranspose_mul_evalWord A hTP r, Matrix.one_mul]

/-- If the exact tail Gram matrix is an orthogonal projection, the
correlated tail map is a contraction on the ambient rectangular space. -/
theorem norm_correlatedTailMapES_le_one_of_wordGram_eq_projection
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : IsOrthogonalProjection Q)
    (hGram : ∑ τ : Cfg d r,
      (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
        Kraus.evalWord A (List.ofFn τ) = Q) :
    ‖correlatedTailMapES A V r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  have hi := congrArg (RCLike.re : ℂ →+ ℝ) (inner_correlatedTailMapES A V r Y Y)
  rw [← norm_sq_eq_re_inner, hGram] at hi
  have hn := (Matrix.PosSemidef.conjTranspose_mul_mul_same
    (isOrthogonalProjection_posSemidef hQ.one_sub) Y).trace_nonneg
  have hn' := (Complex.nonneg_iff.mp hn).1
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub,
    Complex.sub_re, Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq] at hn'
  rw [one_mul, LinearIsometryEquiv.norm_map,
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hi]
  exact sub_nonneg.mp hn'

/-- The residual Gram operator is the correlated pullback of the ordinary
prefix Gram operator. This exact factorization requires no normalization
or letter intertwining. -/
theorem blockedResidualBoundaryMapES_adjoint_comp_self
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (N r : ℕ) :
    (blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r) =
      (correlatedTailMapES A V r).adjoint.comp
        ((boundaryFiberwiseMap (Cfg d r) (groundSpaceGram B N)).comp
          (correlatedTailMapES A V r)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  obtain ⟨X, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective x
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective y
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_boundaryFiberwiseMap, boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyEquiv_correlatedTailMapES_apply, groundSpaceGram] using
      inner_blockedResidualBoundaryMapES_eq_sum_groundSpaceMapES A B V N r Y X

/-- Pull back the primitive prefix limiting metric through the correlated
tail map. Its rectangular action is \(Y\mapsto(\operatorname{tr}\rho)^{-1}Q_rY\rho\).
This is the limiting form used in the residual estimate underlying
Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (i). -/
noncomputable def residualBoundaryGramLimit (A : MPSTensor d D)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (r : ℕ) :
    EuclideanSpace ℂ (Fin E × Fin D) →L[ℂ] EuclideanSpace ℂ (Fin E × Fin D) :=
  (correlatedTailMapES A V r).adjoint.comp
    ((boundaryFiberwiseMap (Cfg d r) (Matrix.gramReshuffle (fixedPointProj ρ htr))).comp
      (correlatedTailMapES A V r))

private theorem boundaryFiberwiseMap_sub (S : Type*) [Fintype S]
    (G H : EuclideanSpace ℂ (Fin E × Fin E) →L[ℂ]
      EuclideanSpace ℂ (Fin E × Fin E)) :
    boundaryFiberwiseMap S (G - H) = boundaryFiberwiseMap S G - boundaryFiberwiseMap S H := by
  ext x p
  rfl

/-- A contractive correlated tail does not increase the prefix Gram error.
The coefficient is one, independently of the tail length. -/
theorem norm_blockedResidualBoundaryMapES_gram_sub_limit_le
    (A : MPSTensor d D) (B : MPSTensor (blockPhysDim d L) E)
    (V : Matrix (Fin D) (Fin E) ℂ) (ρ : Matrix (Fin E) (Fin E) ℂ)
    (htr : Matrix.trace ρ ≠ 0) (N r : ℕ)
    (hC : ‖correlatedTailMapES A V r‖ ≤ 1) :
    ‖(blockedResidualBoundaryMapES A L B V N r).adjoint.comp
        (blockedResidualBoundaryMapES A L B V N r) - residualBoundaryGramLimit A V ρ htr r‖ ≤
      ‖groundSpaceGram B N - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ := by
  rw [blockedResidualBoundaryMapES_adjoint_comp_self, residualBoundaryGramLimit,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ← boundaryFiberwiseMap_sub]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
    (norm_nonneg _)).trans ?_
  have hb := norm_boundaryFiberwiseMap_le (Cfg d r)
    (groundSpaceGram B N - Matrix.gramReshuffle (fixedPointProj ρ htr))
  calc
    _ ≤ 1 * (‖groundSpaceGram B N - Matrix.gramReshuffle (fixedPointProj ρ htr)‖ * 1) := by
      gcongr
      · simpa only [LinearIsometryEquiv.norm_map] using hC
    _ = _ := by simp only [one_mul, mul_one]

/-- The adjoint recombines the correlated tail fibers as
\(\sum_\tau A^{\tau\dagger}Vx_\tau\). -/
theorem correlatedTailMapES_adjoint_apply
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ) (r : ℕ)
    (x : BoundaryFamilySpace (D := E) (Cfg d r)) :
    (correlatedTailMapES A V r).adjoint x =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        (∑ τ : Cfg d r, (Kraus.evalWord A (List.ofFn τ))ᴴ * V *
          boundaryFamilyEquiv (D := E) (Cfg d r) x τ) := by
  refine ext_inner_left ℂ fun y => ?_
  obtain ⟨Y, rfl⟩ := (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)).surjective y
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply, Fintype.sum_prod_type]
  change (∑ τ : Cfg d r,
    inner ℂ (boundaryFamilyFiber (D := E)
      (correlatedTailMapES A V r (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y)) τ)
      (boundaryFamilyFiber (D := E) x τ)) = _
  simp_rw [boundaryFamilyFiber_eq_frobeniusEquivEuclidean,
    boundaryFamilyEquiv_correlatedTailMapES_apply, Matrix.inner_frobeniusEquivEuclidean,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  simp only [Matrix.mul_sum, Matrix.trace_sum]

/-- The pulled-back limiting metric acts by right multiplication by
\(\rho/\operatorname{tr}\rho\), after the exact tail Gram matrix on the left. -/
theorem residualBoundaryGramLimit_frobeniusEquivEuclidean_apply
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin E) ℂ)
    (ρ : Matrix (Fin E) (Fin E) ℂ) (htr : Matrix.trace ρ ≠ 0) (r : ℕ)
    (Y : Matrix (Fin D) (Fin E) ℂ) :
    residualBoundaryGramLimit A V ρ htr r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        ((Matrix.trace ρ)⁻¹ • ((∑ τ : Cfg d r,
          (Kraus.evalWord A (List.ofFn τ))ᴴ * (V * Vᴴ) *
            Kraus.evalWord A (List.ofFn τ)) * Y * ρ)) := by
  rw [residualBoundaryGramLimit, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, correlatedTailMapES_adjoint_apply]
  simp_rw [boundaryFamilyEquiv_boundaryFiberwiseMap_apply,
    boundaryFamilyEquiv_correlatedTailMapES_apply,
    Matrix.gramReshuffle_fixedPointProj_frobeniusEquivEuclidean_apply,
    LinearIsometryEquiv.symm_apply_apply]
  simp only [Matrix.mul_smul, Matrix.sum_mul, ← Finset.smul_sum, Matrix.mul_assoc]

/-- The cyclic row corner derived from the original tensor makes every
correlated tail map contractive, uniformly in the tail length.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`. -/
theorem norm_correlatedTailMapES_le_one_of_cyclic_support
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ a, IsOrthogonalProjection (P a))
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hShift : ∀ a i, P a * A i = A i * P (a + 1))
    (a : Fin m) (V : Matrix (Fin D) (Fin E) ℂ) (hV : V * Vᴴ = P a) (r : ℕ) :
    ‖correlatedTailMapES A V r‖ ≤ 1 := by
  refine norm_correlatedTailMapES_le_one_of_wordGram_eq_projection
    A V r (P (a + r • (1 : Fin m))) (hP _) ?_
  simpa only [hV] using
    sum_word_conjTranspose_cyclic_projection_mul_word A P hTP hShift a r

/-- The derived cyclic limiting metric is
\(Y\mapsto(\operatorname{tr}\rho)^{-1}P_{a+r}Y\rho\).
On the row corner \(P_{a+r}Y=Y\), this is simply right multiplication.
Source: the cyclic compression of DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, and Nachtergaele, Lemma `commutation` (i). -/
theorem residualBoundaryGramLimit_apply_of_cyclic_support
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hShift : ∀ a i, P a * A i = A i * P (a + 1))
    (a : Fin m) (V : Matrix (Fin D) (Fin E) ℂ) (hV : V * Vᴴ = P a)
    (ρ : Matrix (Fin E) (Fin E) ℂ) (htr : Matrix.trace ρ ≠ 0)
    (r : ℕ) (Y : Matrix (Fin D) (Fin E) ℂ) :
    residualBoundaryGramLimit A V ρ htr r
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin E) Y) =
      Matrix.frobeniusEquivEuclidean (Fin D) (Fin E)
        ((Matrix.trace ρ)⁻¹ • (P (a + r • (1 : Fin m)) * Y * ρ)) := by
  simpa only [hV, sum_word_conjTranspose_cyclic_projection_mul_word A P hTP hShift] using
    residualBoundaryGramLimit_frobeniusEquivEuclidean_apply A V ρ htr r Y

/-- Primitive prefix convergence bounds the residual Gram error
geometrically, uniformly over every original tail length. The cyclic corner
and contraction are derived from the original trace-preserving tensor.
This is a quantitative intermediate estimate for Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (i), lines 2442--2531. -/
theorem IsPrimitiveMPS.residualBoundaryGram_sub_limit_norm_sq_le_geometric
    [NeZero E] {B : MPSTensor (blockPhysDim d L) E}
    {ρ : Matrix (Fin E) (Fin E) ℂ} (hB : IsPrimitiveMPS B ρ)
    {m : ℕ} [NeZero m] (A : MPSTensor d D)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hProj : ∀ a, IsOrthogonalProjection (P a))
    (hTP : ∑ i, (A i)ᴴ * A i = 1)
    (hShift : ∀ a i, P a * A i = A i * P (a + 1))
    (a : Fin m) (V : Matrix (Fin D) (Fin E) ℂ) (hV : V * Vᴴ = P a) :
    let htr : Matrix.trace ρ ≠ 0 := by
      intro h
      exact hB.fixedPoint_ne_zero
        ((Matrix.PosSemidef.trace_eq_zero_iff hB.fixedPoint_psd).1 h)
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N, 1 ≤ N → ∀ r,
      ‖(blockedResidualBoundaryMapES A L B V N r).adjoint.comp
          (blockedResidualBoundaryMapES A L B V N r) - residualBoundaryGramLimit A V ρ htr r‖ ^ 2 ≤
        (E : ℝ) ^ 3 * (C * q ^ N) ^ 2 := by
  obtain ⟨C, q, hC, hq, hq1, hBound⟩ :=
    hB.groundSpaceGram_sub_fixedPointProj_norm_sq_le_geometric
  refine ⟨C, q, hC, hq, hq1, fun N hN r => ?_⟩
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (norm_blockedResidualBoundaryMapES_gram_sub_limit_le A B V ρ _ N r
      (norm_correlatedTailMapES_le_one_of_cyclic_support A P hProj hTP hShift a V hV r)) 2).trans
    (hBound N hN)

/-- Blocking by the period leaves each individual cyclic projection as
its own step-orbit projection. Source: DCCSP17, arXiv:1708.00029,
Lemma `lem:blocking-arbitrary`, with \(p=m\). -/
theorem stepOrbitProjection_self {m : ℕ} [NeZero m]
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ) (a : Fin (m.gcd m)) :
    stepOrbitProjection P m a = P (Fin.cast (Nat.gcd_self m) a) := by
  have hOrbit (k : Fin (m / m.gcd m)) :
      Fin.stepOrbitEquiv m m (Nat.pos_of_ne_zero (NeZero.ne m)) (a, k) =
        Fin.cast (Nat.gcd_self m) a := by
    apply Fin.ext
    have ha : a.val < m := by simpa only [Nat.gcd_self] using a.isLt
    simp [Fin.stepOrbitEquiv, Nat.add_mod, Nat.mod_eq_of_lt ha]
  simp only [stepOrbitProjection, hOrbit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.gcd_self, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne m)), one_smul]

/-- Periodicity derives primitive compressed sectors, faithful invariant
matrices, the cyclic support isometries and exact blocked ground spaces.
Their correlated residual Gram operators have the derived row metric
\(Y\mapsto(\operatorname{tr}\rho_a)^{-1}P_{a+r}Y\rho_a\)
and converge geometrically uniformly over every original tail length.
No primitive presentation, invariant matrix, or boundary-corner condition
is supplied as a hypothesis.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (i), lines 2442--2531. -/
theorem IsPeriodic.exists_cyclic_residualBoundaryGram_bound
    {m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (dim : Fin (m.gcd m) → ℕ) (hdim : ∀ a, 0 < dim a),
      let _ : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
      ∃ (B : (a : Fin (m.gcd m)) → MPSTensor (blockPhysDim d m) (dim a))
        (V : (a : Fin (m.gcd m)) → Matrix (Fin D) (Fin (dim a)) ℂ)
        (ρ : (a : Fin (m.gcd m)) → Matrix (Fin (dim a)) (Fin (dim a)) ℂ)
        (hPrimitive : ∀ a, IsPrimitiveMPS (B a) (ρ a)),
        (∀ a, (ρ a).PosDef) ∧ (∀ u, IsOrthogonalProjection (P u)) ∧ (∑ u, P u) = 1 ∧
        (∀ u i, P u * A i = A i * P (u + 1)) ∧ (∑ a, dim a) = D ∧
        (∀ a, (V a)ᴴ * V a = 1) ∧
        (∀ a, V a * (V a)ᴴ = P (Fin.cast (Nat.gcd_self m) a)) ∧
        (∀ a i, B a i = (V a)ᴴ * blockTensor A m i * V a) ∧
        (∀ a i, blockTensor A m i * V a = V a * B a i) ∧
        (∀ N, groundSpaceES (blockTensor A m) N =
          groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) ∧
        ∀ a,
          let htr : Matrix.trace (ρ a) ≠ 0 := by
            intro h
            exact (hPrimitive a).fixedPoint_ne_zero
              ((Matrix.PosSemidef.trace_eq_zero_iff (hPrimitive a).fixedPoint_psd).1 h)
          (∀ r Y, residualBoundaryGramLimit A (V a) (ρ a) htr r
              (Matrix.frobeniusEquivEuclidean (Fin D) (Fin (dim a)) Y) =
            Matrix.frobeniusEquivEuclidean (Fin D) (Fin (dim a))
              ((Matrix.trace (ρ a))⁻¹ •
                (P (Fin.cast (Nat.gcd_self m) a + r • (1 : Fin m)) * Y * ρ a))) ∧
          ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧ ∀ N, 1 ≤ N → ∀ r,
            ‖(blockedResidualBoundaryMapES A m (B a) (V a) N r).adjoint.comp
                (blockedResidualBoundaryMapES A m (B a) (V a) N r) -
                  residualBoundaryGramLimit A (V a) (ρ a) htr r‖ ^ 2 ≤
              (dim a : ℝ) ^ 3 * (C * q ^ N) ^ 2 := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨P, dim, B, V, hProj, hSum, _hNe, hShift, hdim, hTotal, _hCan,
    hIso, hV, hCompression, hIntertwine, hGround, hPeriod⟩ :=
    hA.exists_stepOrbit_groundSpaceDecomposition m hA.period_pos
  let : ∀ a, NeZero (dim a) := fun a => ⟨Nat.ne_of_gt (hdim a)⟩
  have hOne (a : Fin (m.gcd m)) : IsPeriodic 1 (B a) := by
    simpa only [Nat.gcd_self, Nat.div_self hA.period_pos] using hPeriod a
  choose ρ hPrimitive hFaithful using fun a => exists_isPrimitiveMPS_of_isPeriodic_one (hOne a)
  have hV' (a : Fin (m.gcd m)) : V a * (V a)ᴴ = P (Fin.cast (Nat.gcd_self m) a) := by
    simpa only [stepOrbitProjection_self] using hV a
  refine ⟨P, dim, hdim, B, V, ρ, hPrimitive, hFaithful, hProj, hSum, hShift,
    hTotal, hIso, hV', hCompression, hIntertwine, hGround, fun a => ⟨?_, ?_⟩⟩
  · exact fun r Y => residualBoundaryGramLimit_apply_of_cyclic_support
      A P hA.leftCanonical hShift _ (V a) (hV' a) (ρ a) _ r Y
  · exact (hPrimitive a).residualBoundaryGram_sub_limit_norm_sq_le_geometric
      A P hProj hA.leftCanonical hShift _ (V a) (hV' a)
end MPSTensor

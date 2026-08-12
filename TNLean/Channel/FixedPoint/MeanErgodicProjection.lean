/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MeanErgodic
import TNLean.Channel.Basic
import TNLean.Channel.Semigroup.CPClosure

/-!
# Positive trace-nonincreasing mean-ergodic projections

A positive trace-nonincreasing endomorphism of a finite-dimensional complex
matrix algebra has bounded forward orbits.  Its finite-dimensional
mean-ergodic projection is therefore defined and positive.  For a
trace-preserving map, the projection is trace-preserving and fixes the identity
whenever the original map fixes the identity.  A completely positive map has a
completely positive mean-ergodic projection: each Cesàro average is a
nonnegative multiple of a finite sum of powers, hence completely positive, and
the set of completely positive maps is closed in finite dimension.

The bounded-orbit estimate is proved directly.  A positive semidefinite orbit
remains in a bounded trace section of the positive cone.  Hermitian matrices are
differences of their positive and negative parts, and arbitrary matrices are
complex linear combinations of two Hermitian matrices.

## Main statements

* `IsPositiveMap.hasBoundedOrbits_of_posSemidef_orbit_bounded`: the
  Hermitian-decomposition reduction from a positive-semidefinite orbit bound
  to a bound on every matrix, shared by every hypothesis (trace-nonincreasing,
  trace-preserving, or unital) under which Wolf's uniform bound applies.
* `IsPositiveMap.hasBoundedOrbits_of_traceNonincreasing`: positivity and trace
  nonincrease imply bounded forward orbits on every matrix.
* `IsPositiveMap.hasBoundedOrbits_of_tracePreserving`: the trace-preserving
  specialization.
* `IsPositiveMap.meanErgodicProjection_isPositiveMap`: the mean-ergodic
  projection of a positive map is positive.
* `IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap`: the
  mean-ergodic projection of a trace-preserving map is trace-preserving.
* `LinearMap.HasBoundedOrbits.meanErgodicProjection_one`: a fixed identity is
  fixed by the mean-ergodic projection.
* `IsPositiveMap.range_meanErgodicProjection_of_tracePreserving`: the range of
  the resulting projection is exactly the fixed-point space.
* `IsCPMap.meanErgodicProjection_isCPMap`: the mean-ergodic projection of a
  completely positive map is completely positive.
* `IsChannel.meanErgodicProjection`: the mean-ergodic projection of a quantum
  channel is again a quantum channel.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.3 and
  Equation (6.14); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256.
-/

open Filter Function Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {D : ℕ}

/-- The forward orbit of a positive semidefinite matrix under a positive
trace-nonincreasing endomorphism is bounded.

Indeed, every iterate remains positive semidefinite and its trace does not
increase, so the orbit lies in a bounded trace section of the positive cone.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
private theorem IsPositiveMap.isBounded_orbit_of_posSemidef_of_traceNonincreasing
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.PosSemidef) :
    Bornology.IsBounded (Set.range fun n : ℕ ↦ T^[n] X) := by
  have hiter_pos : ∀ n : ℕ, (T^[n] X).PosSemidef := by
    intro n
    induction n with
    | zero => simpa using hX
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hT _ ih
  have hiter_trace : ∀ n : ℕ, Matrix.trace (T^[n] X) ≤ Matrix.trace X := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hTNI _ (hiter_pos n)).trans ih
  have hiter_trace_norm : ∀ n : ℕ,
      ‖Matrix.trace (T^[n] X)‖ ≤ ‖Matrix.trace X‖ := by
    intro n
    rw [show ‖Matrix.trace (T^[n] X)‖ = (Matrix.trace (T^[n] X)).re from by
        simpa using congrArg Complex.re
          (Complex.norm_of_nonneg' (hiter_pos n).trace_nonneg),
      show ‖Matrix.trace X‖ = (Matrix.trace X).re from by
        simpa using congrArg Complex.re (Complex.norm_of_nonneg' hX.trace_nonneg)]
    rw [← sub_nonneg]
    simpa using (RCLike.nonneg_iff.mp (sub_nonneg.mpr (hiter_trace n))).1
  apply (posSemidef_trace_bounded_isBounded ‖Matrix.trace X‖).subset
  intro Y hY
  obtain ⟨n, rfl⟩ := hY
  exact ⟨hiter_pos n, hiter_trace_norm n⟩

/-- The forward orbit of a Hermitian matrix under a positive endomorphism is
bounded, assuming the forward orbit of every positive semidefinite matrix is
bounded.

The matrix is the difference of its positive and negative parts.  Each part
has a bounded positive semidefinite orbit by hypothesis, and linearity gives
the stated bound.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
private theorem IsPositiveMap.isBounded_orbit_of_isHermitian_of_posSemidef_orbit_bounded
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (_hT : IsPositiveMap T)
    (hpsd : ∀ {X : Matrix (Fin D) (Fin D) ℂ}, X.PosSemidef →
      Bornology.IsBounded (Set.range fun n : ℕ ↦ T^[n] X))
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X.IsHermitian) :
    Bornology.IsBounded (Set.range fun n : ℕ ↦ T^[n] X) := by
  let Q₁ : Matrix (Fin D) (Fin D) ℂ := X⁺
  let Q₂ : Matrix (Fin D) (Fin D) ℂ := X⁻
  have hQ₁ : Q₁.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have hQ₂ : Q₂.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  have hdecomp : X = Q₁ - Q₂ := by
    simpa only [Q₁, Q₂] using
      (CFC.posPart_sub_negPart X (isSelfAdjoint_iff.mpr hX)).symm
  have hb₁ := hpsd hQ₁
  have hb₂ := hpsd hQ₂
  rw [isBounded_iff_forall_norm_le] at hb₁ hb₂ ⊢
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  refine ⟨C₁ + C₂, ?_⟩
  intro Y hY
  obtain ⟨n, rfl⟩ := hY
  change ‖T^[n] X‖ ≤ C₁ + C₂
  rw [hdecomp, iterate_map_sub]
  calc
    ‖T^[n] Q₁ - T^[n] Q₂‖ ≤ ‖T^[n] Q₁‖ + ‖T^[n] Q₂‖ := norm_sub_le _ _
    _ ≤ C₁ + C₂ := add_le_add (hC₁ _ ⟨n, rfl⟩) (hC₂ _ ⟨n, rfl⟩)

/-- A positive matrix endomorphism whose forward orbits are bounded on every
positive semidefinite matrix has bounded forward orbits on every matrix.

For an arbitrary matrix `X`, the matrices `X + Xᴴ` and `i(X - Xᴴ)` are
Hermitian, and each Hermitian matrix is the difference of its positive and
negative parts, so the assumed bounds combine linearly.

This packages the reduction step of Wolf, Proposition 6.3 and Equation (6.14):
a hypothesis on the map (trace-nonincreasing, trace-preserving, or unital)
only has to supply the positive semidefinite orbit bound.  Local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem IsPositiveMap.hasBoundedOrbits_of_posSemidef_orbit_bounded
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    (hpsd : ∀ {X : Matrix (Fin D) (Fin D) ℂ}, X.PosSemidef →
      Bornology.IsBounded (Set.range fun n : ℕ ↦ T^[n] X)) :
    T.HasBoundedOrbits := by
  intro X
  let H₁ : Matrix (Fin D) (Fin D) ℂ := X + Xᴴ
  let H₂ : Matrix (Fin D) (Fin D) ℂ := Complex.I • (X - Xᴴ)
  have hH₁ : H₁.IsHermitian := by
    ext i j
    simp [H₁, add_comm]
  have hH₂ : H₂.IsHermitian := by
    ext i j
    simp [H₂, sub_eq_add_neg, add_comm]
  have hdecomp : X = (2 : ℂ)⁻¹ • (H₁ - Complex.I • H₂) := by
    ext i j
    simp only [H₁, H₂, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb₁ := hT.isBounded_orbit_of_isHermitian_of_posSemidef_orbit_bounded hpsd hH₁
  have hb₂ := hT.isBounded_orbit_of_isHermitian_of_posSemidef_orbit_bounded hpsd hH₂
  rw [isBounded_iff_forall_norm_le] at hb₁ hb₂ ⊢
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  refine ⟨‖(2 : ℂ)⁻¹‖ * (C₁ + C₂), ?_⟩
  intro Y hY
  obtain ⟨n, rfl⟩ := hY
  change ‖T^[n] X‖ ≤ ‖(2 : ℂ)⁻¹‖ * (C₁ + C₂)
  rw [hdecomp, ← Module.End.coe_pow]
  simp only [map_smul, map_sub]
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖(T ^ n) H₁ - Complex.I • (T ^ n) H₂‖ ≤
        ‖(T ^ n) H₁‖ + ‖Complex.I • (T ^ n) H₂‖ := norm_sub_le _ _
    _ = ‖T^[n] H₁‖ + ‖T^[n] H₂‖ := by
      simp only [norm_smul, Complex.norm_I, one_mul, Module.End.coe_pow]
    _ ≤ C₁ + C₂ := add_le_add (hC₁ _ ⟨n, rfl⟩) (hC₂ _ ⟨n, rfl⟩)

/-- A positive trace-nonincreasing matrix endomorphism has bounded forward
orbits. Positive orbits remain in the bounded trace section determined by
their initial trace; Hermitian decomposition gives the general case.

This is the trace-nonincreasing form of Wolf, Proposition 6.3. -/
theorem IsPositiveMap.hasBoundedOrbits_of_traceNonincreasing
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTNI : IsTraceNonincreasingMap T) :
    T.HasBoundedOrbits :=
  hT.hasBoundedOrbits_of_posSemidef_orbit_bounded fun hX =>
    hT.isBounded_orbit_of_posSemidef_of_traceNonincreasing hTNI hX

/-- A positive trace-preserving endomorphism of a finite-dimensional complex
matrix algebra has bounded forward orbits on every matrix.

For an arbitrary matrix (X), the matrices (X+X^*) and
\(i(X-X^*)\) are Hermitian and
\[
  X=\frac12\bigl((X+X^*)-i\,i(X-X^*)\bigr).
\]
The Hermitian-orbit estimate and linearity then give a uniform bound for the
orbit of (X).  No contractivity hypothesis is used.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem IsPositiveMap.hasBoundedOrbits_of_tracePreserving
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    T.HasBoundedOrbits :=
  hT.hasBoundedOrbits_of_traceNonincreasing hTP.isTraceNonincreasingMap

/-- The finite-dimensional mean-ergodic projection of a positive matrix
endomorphism is positive.

Every Cesàro average is positive on a positive semidefinite input.  The
positive semidefinite cone is closed, so the pointwise mean-ergodic limit is
positive as well.

Source: Wolf, Proposition 6.3(iii) and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem IsPositiveMap.meanErgodicProjection_isPositiveMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hbounded : T.HasBoundedOrbits) :
    IsPositiveMap (LinearMap.meanErgodicProjection T hbounded) := by
  intro X hX
  have hiter_pos : ∀ n : ℕ, (T^[n] X).PosSemidef := by
    intro n
    induction n with
    | zero => simpa using hX
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hT _ ih
  have havg_pos : ∀ n : ℕ,
      (birkhoffAverage ℂ T _root_.id n X).PosSemidef := by
    intro n
    rw [birkhoffAverage, birkhoffSum]
    exact (Matrix.posSemidef_sum _ fun k _ ↦ hiter_pos k).smul (by positivity)
  exact isClosed_posSemidef.mem_of_tendsto
    (hbounded.tendsto_birkhoffAverage_meanErgodicProjection X)
    (Filter.Eventually.of_forall havg_pos)

/-- The finite-dimensional mean-ergodic projection of a trace-preserving
matrix endomorphism is trace-preserving.

The trace of every nonempty Cesàro average equals the trace of the input.
Continuity of the trace and pointwise mean-ergodic convergence pass this
identity to the limit.

Source: Wolf, Proposition 6.3(iii) and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hTP : IsTracePreservingMap T) (hbounded : T.HasBoundedOrbits) :
    IsTracePreservingMap (LinearMap.meanErgodicProjection T hbounded) := by
  intro X
  have hiter_trace : ∀ n : ℕ, Matrix.trace (T^[n] X) = Matrix.trace X := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', hTP, ih]
  have havg_trace : ∀ n : ℕ, n ≠ 0 →
      Matrix.trace (birkhoffAverage ℂ T _root_.id n X) = Matrix.trace X := by
    intro n hn
    simp only [birkhoffAverage, birkhoffSum, id_eq, Matrix.trace_smul,
      Matrix.trace_sum, hiter_trace, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (show (n : ℂ) ≠ 0 by exact_mod_cast hn),
      one_mul]
  have hlimit := hbounded.tendsto_birkhoffAverage_meanErgodicProjection X
  have htrace_limit : Tendsto
      (fun n ↦ Matrix.trace (birkhoffAverage ℂ T _root_.id n X)) atTop
      (𝓝 (Matrix.trace (LinearMap.meanErgodicProjection T hbounded X))) :=
    ((Matrix.traceLinearMap (Fin D) ℂ ℂ).continuous_of_finiteDimensional.tendsto
      (LinearMap.meanErgodicProjection T hbounded X)).comp hlimit
  have heventually : ∀ᶠ n : ℕ in atTop,
      Matrix.trace (birkhoffAverage ℂ T _root_.id n X) = Matrix.trace X :=
    (Filter.eventually_ne_atTop 0).mono fun n hn ↦ havg_trace n hn
  have htrace_constant : Tendsto
      (fun n : ℕ ↦ Matrix.trace (birkhoffAverage ℂ T _root_.id n X)) atTop
      (𝓝 (Matrix.trace X)) :=
    tendsto_const_nhds.congr' (heventually.mono fun _ h ↦ h.symm)
  exact tendsto_nhds_unique htrace_limit htrace_constant

/-- If a matrix endomorphism fixes the identity, then its mean-ergodic
projection fixes the identity.

Source: Wolf, Proposition 6.3(iii) and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--256. -/
theorem LinearMap.HasBoundedOrbits.meanErgodicProjection_one
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hbounded : T.HasBoundedOrbits) (hOne : T 1 = 1) :
    LinearMap.meanErgodicProjection T hbounded 1 = 1 := by
  exact hbounded.meanErgodicProjection_apply_eq_self_iff 1 |>.2 hOne

/-- The range of the mean-ergodic projection of a positive trace-preserving
matrix endomorphism is exactly its fixed-point space.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269. -/
@[simp]
theorem IsPositiveMap.range_meanErgodicProjection_of_tracePreserving
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    LinearMap.range
        (LinearMap.meanErgodicProjection T
          (hT.hasBoundedOrbits_of_tracePreserving hTP)) =
      LinearMap.ker (T - 1) := by
  exact (hT.hasBoundedOrbits_of_tracePreserving hTP).range_meanErgodicProjection

/-- The mean-ergodic projection of a positive trace-preserving matrix
endomorphism fixes precisely the fixed points of the original endomorphism.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--269. -/
@[simp]
theorem IsPositiveMap.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    LinearMap.meanErgodicProjection T
        (hT.hasBoundedOrbits_of_tracePreserving hTP) X = X ↔
      T X = X := by
  exact (hT.hasBoundedOrbits_of_tracePreserving hTP)
    |>.meanErgodicProjection_apply_eq_self_iff X

/-! ### Pointwise convergence implies operator-norm convergence in finite dimension -/

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- In finite dimension, pointwise convergence of continuous linear
endomorphisms implies convergence in the operator norm: evaluation on a finite
basis is a linear isomorphism onto a finite product, hence a homeomorphism. -/
theorem tendsto_of_tendsto_apply_of_finiteDimensional {S : ℕ → E →L[ℂ] E} {P : E →L[ℂ] E}
    (h : ∀ x : E, Tendsto (fun n : ℕ ↦ S n x) atTop (𝓝 (P x))) :
    Tendsto S atTop (𝓝 P) := by
  classical
  let ι := Fin (Module.finrank ℂ E)
  let b := Module.finBasis ℂ E
  -- Evaluation on the basis, as a continuous linear map into a finite product.
  let Φ : (E →L[ℂ] E) →L[ℂ] (ι → E) :=
    ContinuousLinearMap.pi fun i ↦ (ContinuousLinearMap.apply ℂ E) (b i)
  have hΦ : ∀ (f : E →L[ℂ] E) (i : ι), Φ f i = f (b i) := fun f i ↦
    ContinuousLinearMap.pi_apply _ f i
  -- `Φ` is bijective: maps are determined by their values on the basis.
  have hinj : Function.Injective Φ.toLinearMap := by
    intro f g hfg
    have hfg' : ∀ i : ι, f (b i) = g (b i) := fun i ↦
      calc f (b i) = Φ f i := (hΦ f i).symm
        _ = Φ g i := congrFun hfg i
        _ = g (b i) := hΦ g i
    have hlin : f.toLinearMap = g.toLinearMap := b.ext hfg'
    exact ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun hlin x
  have hsurj : Function.Surjective Φ.toLinearMap := by
    intro w
    refine ⟨LinearMap.toContinuousLinearMap (b.constr ℂ w), ?_⟩
    ext i
    change Φ (LinearMap.toContinuousLinearMap (b.constr ℂ w)) i = w i
    rw [hΦ]
    exact b.constr_basis (M' := E) ℂ w i
  let e := LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩
  -- Both directions are continuous in finite dimension.
  have hfwd : Continuous e := Φ.toLinearMap.continuous_of_finiteDimensional
  have hbwd : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  -- Convergence of the evaluations, then transport back.
  have hEval : Tendsto (fun n : ℕ ↦ e (S n)) atTop (𝓝 (e P)) := by
    rw [tendsto_pi_nhds]
    intro i
    have hS : ∀ n : ℕ, e (S n) i = S n (b i) := fun n ↦ hΦ (S n) i
    have hP : e P i = P (b i) := hΦ P i
    simp_rw [hS, hP]
    exact h (b i)
  have hb := (hbwd.tendsto (e P)).comp hEval
  have heq : e.symm ∘ (fun n : ℕ ↦ e (S n)) = S := by
    funext n
    exact e.symm_apply_apply (S n)
  rw [heq] at hb
  simpa only [LinearEquiv.symm_apply_apply] using hb

end ContinuousLinearMap

/-! ### Complete positivity of the mean-ergodic projection -/

/-- The finite-dimensional mean-ergodic projection of a completely positive
matrix endomorphism is completely positive.

The `N`-th Cesàro average is the nonnegative multiple `N⁻¹` of the finite sum
`∑_{n < N} T ^ n`, so it is completely positive.  These averages converge
pointwise, hence in the operator norm, to the mean-ergodic projection, and the
set of completely positive maps is closed in finite dimension.

Source: Wolf, Proposition 6.3(iii) and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--238. -/
theorem IsCPMap.meanErgodicProjection_isCPMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsCPMap T) (hbounded : T.HasBoundedOrbits) :
    IsCPMap (LinearMap.meanErgodicProjection T hbounded) := by
  classical
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact isCPMap_finZero _
  haveI : NeZero D := ⟨hD.ne'⟩
  set S : ℕ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    fun N ↦ (((N : ℝ)⁻¹ : ℝ) : ℂ) • ∑ n ∈ Finset.range N, T ^ n with hSdef
  have hScp : ∀ N, IsCPMap (S N) := fun N ↦
    (Finset.isCPMap_sum _ _ fun n _ ↦ hT.pow n).smul_nonneg (by positivity)
  have hSapply : ∀ (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ),
      S N X = birkhoffAverage ℂ T _root_.id N X := by
    intro N X
    simp only [hSdef, birkhoffAverage, birkhoffSum, LinearMap.smul_apply,
      LinearMap.coe_sum, Finset.sum_apply, Module.End.pow_apply, id_eq]
    push_cast
    rfl
  refine IsCPMap.of_tendsto_toCLM hScp
    (ContinuousLinearMap.tendsto_of_tendsto_apply_of_finiteDimensional fun X ↦ ?_)
  exact (hbounded.tendsto_birkhoffAverage_meanErgodicProjection X).congr fun N ↦
    (hSapply N X).symm

/-- The mean-ergodic projection `T_∞` of a quantum channel is again a quantum
channel: this is the assertion of Wolf's Cesàro-means proposition for `T_∞`
in the completely positive case.

Source: Wolf, Proposition 6.3 and Equation (6.14), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 226--238. -/
theorem IsChannel.meanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsChannel T) :
    IsChannel (LinearMap.meanErgodicProjection T
      (hT.cp.isPositiveMap.hasBoundedOrbits_of_tracePreserving hT.tp)) where
  cp := hT.cp.meanErgodicProjection_isCPMap _
  tp := hT.tp.meanErgodicProjection_isTracePreservingMap _

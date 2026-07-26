/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.StackedLayers
import TNLean.Channel.Peripheral.CyclicDecomposition.Decomposition
import TNLean.Channel.Peripheral.CyclicDecomposition.LetterShift
import TNLean.Channel.Peripheral.GroupStructure
import TNLean.MPS.Core.TPGauge
import TNLean.MPS.Core.CPPrimitive
import TNLean.MPS.Irreducible.FixedPointProjection
import TNLean.MPS.Irreducible.Adjoint
import TNLean.MPS.Irreducible.FormII
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.QPF.PosDef
import TNLean.MPS.MPDO.HorizontalBNT

/-!
# The cyclic projector of a nontrivial periodic vector

This file constructs, from a nontrivial $p$-periodic vector of the vertically
viewed tensor of a matrix product operator, the orthogonal projector demanded
by the periodic-sector step in the proof of Proposition 4.13 of
arXiv:1606.00608, lines 1888--1893.  A nontrivial $p$-periodic vector is an
eigenvector of the transfer map of an irreducible corner of the vertically
viewed tensor with peripheral eigenvalue $e^{2\pi iq/p}\ne 1$
(arXiv:1606.00608, lines 225--230).  The cyclic decomposition of the
peripheral spectrum (Wolf 2012, Theorem 6.6, formalized in
`TNLean/Channel/Peripheral/CyclicDecomposition`) attaches to it a cyclic
family of orthogonal projections permuted by one application of the transfer
map; the projector $Q$ is the complement of the orthogonal projection onto
the subspace carried by one cyclic sector.

Two of the three properties demanded of $Q$ by the cyclic-projector
hypothesis `PeriodicVectorYieldsCyclicProjector` are proved here
unconditionally:

* the **word invariance**: $Q$ is one-sided invariant for every full-period
  word of the vertically viewed tensor, because a full cyclic period returns
  each sector to itself; and
* the **single-letter displacement**: $Q\widetilde M\ne Q\widetilde MQ$,
  because one vertical layer moves each cyclic sector to the next one, and
  distinct sectors are orthogonal.

The source also states that $Q$ fails to commute with the density operator
$H^{(N)}$ at every length (arXiv:1606.00608, line 1889).  The proof needs only
one noncommuting length.  Normalized BNT-refined horizontal form supplies such
a length: otherwise the representative-grouped Lemma L would turn simultaneous
commutation into the forbidden letter-level invariance.  At that same length,
full-period word invariance gives commutation with $[H^{(N)}]^p$, and
positivity removes the power.  This proves the periodic-sector step under
normalized BNT-refined horizontal form, which is stronger than the literal
CPSV canonical-form hypothesis; see
`docs/paper-gaps/cpgsv17_periodic_sector_projector.tex`.

## Main results

* `MPSTensor.isIrreducibleTensor_smul_conj`: tensor irreducibility is
  preserved by rescaled conjugation with an invertible matrix.
* `MPSTensor.spectralUnitalGauge_schwarz_setup`: the rescaled unital gauge of
  an irreducible corner satisfies the hypotheses of Wolf Theorem 6.6.
* `MPOTensor.exists_displaced_invariant_projector_of_periodic_vector`: a
  nontrivial periodic vector of the vertically viewed tensor supplies an
  orthogonal projector, invariant for every full-period word and displaced by
  the single letters.
* `MPOTensor.NoninvariantProjectorNoncommuting`: the hypothesis that a
  displaced projector never commutes with the density operator.
* `MPOTensor.periodicVectorYieldsCyclicProjector_of_noncommutation`: the
  hypothesis implies `PeriodicVectorYieldsCyclicProjector`.
* `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_noncommutation`: granted
  the hypothesis, a matrix product density operator has no nontrivial
  periodic vectors in the vertical direction.
* `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_horizontalCF`: an MPDO in
  normalized BNT-refined horizontal form has no nontrivial periodic vectors in
  the vertical direction.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition 4.13, lines 1888--1893; lines 225--230 for periodic vectors
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Fin.NatCast

namespace MPSTensor

variable {d D : ℕ}

/-! ### Irreducibility under rescaled conjugation

The unital normalization of an irreducible corner conjugates the letters by
the square root of the positive transfer eigenvector.  Conjugation by an
invertible matrix does not preserve orthogonality, so an invariant orthogonal
projection of the conjugated tensor corresponds to an invariant *subspace* of
the original tensor; the support projection of the transported subspace
recovers an invariant orthogonal projection. -/

/-- **Rescaled conjugation preserves tensor irreducibility.** If `B` admits
no nontrivial invariant orthogonal projection, neither does
`c • (X⁻¹ * B v * X)` for an invertible `X` and a nonzero scalar `c`: an
invariant orthogonal projection `P` of the conjugated tensor transports to
the invariant subspace of `B` spanned by the columns of `X * P`, whose
support projection is a nontrivial invariant orthogonal projection of `B`.

This is the normalization step of arXiv:1606.00608, lines 224--225, for the
corner tensors: the rescaled unital gauge of an irreducible corner is again
irreducible. -/
theorem isIrreducibleTensor_smul_conj (B : MPSTensor d D)
    (hIrr : IsIrreducibleTensor B) {X : Matrix (Fin D) (Fin D) ℂ} (hX : IsUnit X)
    {c : ℂ} (hc : c ≠ 0) :
    IsIrreducibleTensor (fun v => c • (X⁻¹ * B v * X)) := by
  classical
  intro hHas
  apply hIrr
  obtain ⟨P, hPproj, hP0, hP1, hPinv⟩ := hHas
  have hXdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have hXHdet : IsUnit Xᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hXdet.star
  set Y : Matrix (Fin D) (Fin D) ℂ := X * P with hY
  set π : Matrix (Fin D) (Fin D) ℂ :=
    supportProj (D := D) (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y) with hπ
  refine ⟨π, isOrthogonalProjection_supportProj (D := D) (ρ := Y * Yᴴ)
    (hρ := Matrix.posSemidef_self_mul_conjTranspose Y), ?_, ?_, ?_⟩
  · -- `π ≠ 0` because `Y ≠ 0`.
    have hYne : Y ≠ 0 := by
      intro h0
      apply hP0
      calc P = X⁻¹ * (X * P) := (Matrix.nonsing_inv_mul_cancel_left X P hXdet).symm
        _ = 0 := by rw [← hY, h0, Matrix.mul_zero]
    have hSne : Y * Yᴴ ≠ 0 := fun h0 =>
      hYne (Matrix.self_mul_conjTranspose_eq_zero.mp h0)
    exact supportProj_ne_zero_of_ne_zero (Y * Yᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose Y) hSne
  · -- `π ≠ 1`: a nonzero vector in the kernel of `P` transports to the
    -- kernel of `Y * Yᴴ`, hence of `π`.
    have h1Pne : (1 : Matrix (Fin D) (Fin D) ℂ) - P ≠ 0 := by
      intro h0
      exact hP1 (by rw [sub_eq_zero] at h0; exact h0.symm)
    obtain ⟨i, j, hij⟩ : ∃ i j, ((1 : Matrix (Fin D) (Fin D) ℂ) - P) i j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact h1Pne (Matrix.ext fun i j => hall i j)
    set w : Fin D → ℂ := ((1 : Matrix (Fin D) (Fin D) ℂ) - P) *ᵥ Pi.single j 1 with hw
    have hwne : w ≠ 0 := by
      intro h0
      apply hij
      have := congrFun h0 i
      simpa [hw, Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hP1P : P * ((1 : Matrix (Fin D) (Fin D) ℂ) - P) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, hPproj.2, sub_self]
    have hPw : P *ᵥ w = 0 := by
      rw [hw, Matrix.mulVec_mulVec, hP1P, Matrix.zero_mulVec]
    set v : Fin D → ℂ := (Xᴴ)⁻¹ *ᵥ w with hv
    have hXHv : Xᴴ *ᵥ v = w := by
      rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Xᴴ hXHdet,
        Matrix.one_mulVec]
    have hvne : v ≠ 0 := by
      intro h0
      apply hwne
      rw [← hXHv, h0, Matrix.mulVec_zero]
    have hYY : Y * Yᴴ = X * (P * Xᴴ) := by
      rw [hY, Matrix.conjTranspose_mul, hPproj.1.eq]
      calc X * P * (P * Xᴴ) = X * (P * P * Xᴴ) := by simp only [Matrix.mul_assoc]
        _ = X * (P * Xᴴ) := by rw [hPproj.2]
    have hSv : (Y * Yᴴ) *ᵥ v = 0 := by
      rw [hYY, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXHv, hPw,
        Matrix.mulVec_zero]
    have hπv : π *ᵥ v = 0 :=
      supportProj_mulVec_eq_zero_of_mulVec_eq_zero (Y * Yᴴ)
        (Matrix.posSemidef_self_mul_conjTranspose Y) v hSv
    intro h1
    apply hvne
    rw [← Matrix.one_mulVec v, ← h1, hπv]
  · -- Invariance: `(1 - π) * B v * π = 0` for every letter.
    intro u
    have h' : ((1 : Matrix (Fin D) (Fin D) ℂ) - P) * (X⁻¹ * B u * X) * P = 0 := by
      have hs : c • (((1 : Matrix (Fin D) (Fin D) ℂ) - P) * (X⁻¹ * B u * X) * P) = 0 := by
        have := hPinv u
        calc c • (((1 : Matrix (Fin D) (Fin D) ℂ) - P) * (X⁻¹ * B u * X) * P)
            = (1 - P) * (c • (X⁻¹ * B u * X)) * P := by
              rw [Matrix.mul_smul, Matrix.smul_mul]
          _ = 0 := this
      exact (smul_eq_zero.mp hs).resolve_left hc
    have hinv' : X⁻¹ * B u * X * P = P * (X⁻¹ * B u * X * P) := by
      have h'' : X⁻¹ * B u * X * P - P * (X⁻¹ * B u * X * P) = 0 := by
        have := h'
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul] at this
        rw [← this]
        simp only [Matrix.mul_assoc]
      exact sub_eq_zero.mp h''
    have hGB : B u * Y = Y * (X⁻¹ * B u * X * P) := by
      calc B u * Y = B u * X * P := by rw [hY, Matrix.mul_assoc]
        _ = X * (X⁻¹ * (B u * X * P)) :=
            (Matrix.mul_nonsing_inv_cancel_left X _ hXdet).symm
        _ = X * (X⁻¹ * B u * X * P) := by simp only [Matrix.mul_assoc]
        _ = X * (P * (X⁻¹ * B u * X * P)) := by rw [← hinv']
        _ = Y * (X⁻¹ * B u * X * P) := by rw [hY]; simp only [Matrix.mul_assoc]
    exact one_sub_supportProj_mul_mul_supportProj_eq_zero Y hGB

/-! ### The unital gauge of a corner satisfies the Wolf Theorem 6.6 hypotheses -/

/-- **Unital Schwarz data for an irreducible corner.**  The rescaled unital
gauge $K^v=r^{-1/2}\rho^{-1/2}B^v\rho^{1/2}$ of an irreducible tensor $B$
with a positive definite transfer eigenvector $\rho$ of positive eigenvalue
$r$ (arXiv:1606.00608, lines 220--225: each corner map is rescaled to
spectral radius one) is a unital Kraus family, is again an irreducible
tensor with an irreducible transfer map, and its adjoint map has a positive
definite fixed point.  These are the hypotheses of the cyclic decomposition
of the peripheral spectrum, Wolf 2012, Theorem 6.6. -/
theorem spectralUnitalGauge_schwarz_setup [NeZero D]
    (B : MPSTensor d D) (hIrr : IsIrreducibleTensor B)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (rad : ℝ) (hρ : ρ.PosDef) (hrad : 0 < rad)
    (hfix : transferMap (d := d) (D := D) B ρ = (rad : ℂ) • ρ) :
    KadisonSchwarz.IsUnitalKraus (d := d) (D := D) (spectralUnitalGauge B rad ρ) ∧
    IsIrreducibleTensor (spectralUnitalGauge B rad ρ) ∧
    IsIrreducibleMap (transferMap (d := d) (D := D) (spectralUnitalGauge B rad ρ)) ∧
    ∃ σ : Matrix (Fin D) (Fin D) ℂ, σ.PosDef ∧
      Kraus.adjointMap (spectralUnitalGauge B rad ρ) σ = σ := by
  classical
  have hUnital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D)
      (spectralUnitalGauge B rad ρ) := by
    simpa [KadisonSchwarz.IsUnitalKraus] using
      spectralUnitalGauge_isUnital_of_transferMap_eigenvector B ρ rad hρ hrad hfix
  have hcne : ((↑((Real.sqrt rad)⁻¹) : ℂ)) ≠ 0 := by
    have hs : Real.sqrt rad ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrad)
    exact_mod_cast inv_ne_zero hs
  have hSunit : IsUnit (CFC.sqrt ρ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_cfc_sqrt_of_posDef ρ hρ)
  have hIrrK : IsIrreducibleTensor (spectralUnitalGauge B rad ρ) := by
    have h := isIrreducibleTensor_smul_conj B hIrr hSunit hcne
    exact h
  have hIrrMap : IsIrreducibleMap (transferMap (d := d) (D := D)
      (spectralUnitalGauge B rad ρ)) :=
    isIrreducibleCP_transferMap_of_isIrreducibleTensor _ hIrrK
  refine ⟨hUnital, hIrrK, hIrrMap, ?_⟩
  -- The adjoint of a unital family is trace-preserving; its transfer map is a
  -- channel and has a positive semidefinite fixed point, which irreducibility
  -- upgrades to a positive definite one.
  set K : MPSTensor d D := spectralUnitalGauge B rad ρ with hK
  have hTPadj : ∑ v : Fin d, ((K v)ᴴ)ᴴ * (K v)ᴴ = 1 := by
    simpa [Matrix.conjTranspose_conjTranspose] using hUnital
  have hCh : IsChannel (transferMap (d := d) (D := D) (fun v => (K v)ᴴ)) :=
    transferMap_isChannel (fun v => (K v)ᴴ) hTPadj
  obtain ⟨σ, hσ_psd, hσ_ne, hσ_fix⟩ :=
    hCh.exists_posSemidef_fixedPoint
      (E := transferMap (d := d) (D := D) (fun v => (K v)ᴴ)) (NeZero.pos D)
  have hIrrAdj : IsIrreducibleMap (transferMap (d := d) (D := D) (fun v => (K v)ᴴ)) :=
    isIrreducibleCP_transferMap_conjTranspose_of_isIrreducibleTensor K hIrrK
  have hσ_pd : σ.PosDef :=
    posSemidef_fixedPoint_isPosDef_of_irreducible (fun v => (K v)ᴴ) hIrrAdj σ
      hσ_psd hσ_ne hσ_fix
  refine ⟨σ, hσ_pd, ?_⟩
  simpa [Kraus.adjointMap, transferMap_apply, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using hσ_fix

/-- **Eigenvalue transport to the unital gauge.**  An eigenvalue $\mu$ of
the transfer map of $B$ becomes the eigenvalue $\mu/r$ of the transfer map
of the rescaled unital gauge $K^v=r^{-1/2}\rho^{-1/2}B^v\rho^{1/2}$: the
gauge conjugates the transfer map by a congruence and divides it by $r$.
In particular the peripheral eigenvalues $e^{2\pi iq/p}$ of
arXiv:1606.00608, lines 225--230, arise from the transfer eigenvalues of
modulus $r$. -/
theorem hasEigenvalue_transferMap_spectralUnitalGauge
    (B : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (rad : ℝ)
    (hρ : ρ.PosDef) (hrad : 0 < rad) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (transferMap (d := d) (D := D) B) μ) :
    Module.End.HasEigenvalue
      (transferMap (d := d) (D := D) (spectralUnitalGauge B rad ρ)) (μ / rad) := by
  classical
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have hXeq : transferMap (d := d) (D := D) B X = μ • X :=
    Module.End.mem_eigenspace_iff.mp (Module.End.hasEigenvector_iff.mp hX).1
  have hXne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt ρ with hS
  have hSdet : IsUnit S.det := isUnit_det_cfc_sqrt_of_posDef ρ hρ
  have hSH : Sᴴ = S := conjTranspose_cfc_sqrt ρ
  have hSinvH : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSH]
  set c : ℂ := (↑((Real.sqrt rad)⁻¹) : ℂ) with hc
  have hcstar : star c = c := by rw [hc, RCLike.star_def, Complex.conj_ofReal]
  have hcc : c * c = (↑rad : ℂ)⁻¹ := by
    rw [hc, ← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt hrad.le,
      Complex.ofReal_inv]
  set X' : Matrix (Fin D) (Fin D) ℂ := S⁻¹ * X * S⁻¹ with hX'
  have hX'ne : X' ≠ 0 := by
    intro h0
    apply hXne
    calc X = S * (S⁻¹ * X) := (Matrix.mul_nonsing_inv_cancel_left S X hSdet).symm
      _ = S * (S⁻¹ * (X * (S⁻¹ * S))) := by
          rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]
      _ = S * (X' * S) := by rw [hX']; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.zero_mul, Matrix.mul_zero]
  have hmap : transferMap (d := d) (D := D) (spectralUnitalGauge B rad ρ) X'
      = (μ / ↑rad) • X' := by
    have hterm : ∀ v : Fin d,
        spectralUnitalGauge B rad ρ v * X' * (spectralUnitalGauge B rad ρ v)ᴴ
          = (c * c) • (S⁻¹ * (B v * X * (B v)ᴴ) * S⁻¹) := by
      intro v
      have hKv : spectralUnitalGauge B rad ρ v = c • (S⁻¹ * B v * S) := rfl
      have hKvH : (spectralUnitalGauge B rad ρ v)ᴴ = c • (S * (B v)ᴴ * S⁻¹) := by
        rw [hKv, Matrix.conjTranspose_smul, hcstar, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul, hSH, hSinvH, Matrix.mul_assoc]
      rw [hKvH, hKv, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      rw [hX']
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hSdet,
        Matrix.nonsing_inv_mul_cancel_left _ _ hSdet]
    rw [transferMap_apply]
    calc ∑ v : Fin d,
          spectralUnitalGauge B rad ρ v * X' * (spectralUnitalGauge B rad ρ v)ᴴ
        = ∑ v : Fin d, (c * c) • (S⁻¹ * (B v * X * (B v)ᴴ) * S⁻¹) :=
          Finset.sum_congr rfl fun v _ => hterm v
      _ = (c * c) • (S⁻¹ * (∑ v : Fin d, B v * X * (B v)ᴴ) * S⁻¹) := by
          rw [← Finset.smul_sum, Finset.mul_sum, Finset.sum_mul]
      _ = (c * c) • (S⁻¹ * (μ • X) * S⁻¹) := by
          rw [show ∑ v : Fin d, B v * X * (B v)ᴴ
              = transferMap (d := d) (D := D) B X from
            (transferMap_apply (d := d) (D := D) B X).symm, hXeq]
      _ = (μ / ↑rad) • X' := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, hcc, hX',
            div_eq_mul_inv, mul_comm]
  exact hasEigenvalue_of_eigenvector_eq _ _ X' hmap hX'ne

end MPSTensor

namespace MPOTensor

open MPSTensor in
/-- **The displaced invariant projector of a nontrivial periodic vector**
(arXiv:1606.00608, lines 1888--1891, from Wolf 2012, Theorem 6.6).

A nontrivial periodic vector of the vertically viewed tensor — an irreducible
corner `B` reached through the isometry `V`, carrying a positive definite
transfer eigenvector of eigenvalue `r > 0` together with a transfer
eigenvalue `μ ≠ r` of modulus `r` — supplies a positive period `p` and an
orthogonal projector `Q` on the physical space such that

* `Q` is one-sided invariant for every length-`p` word of the vertically
  viewed tensor, and
* `Q` is displaced by a single vertical layer:
  $Q\widetilde M\ne Q\widetilde MQ$.

The projector is the complement of the orthogonal projection onto the
subspace carried by one cyclic sector of Wolf Theorem 6.6 for the rescaled
corner transfer map, transported through the isometry and the square root of
the transfer eigenvector.  A full cyclic period returns the sector to itself,
giving the word invariance; a single layer moves it to the neighboring
orthogonal sector, forbidding single-letter invariance. -/
theorem exists_displaced_invariant_projector_of_periodic_vector
    {d D : ℕ} (M : MPOTensor d D) {n : ℕ}
    (V : Matrix (Fin d) (Fin n) ℂ) (B : MPSTensor (D * D) n)
    (ρ : Matrix (Fin n) (Fin n) ℂ) (rad : ℝ)
    (hV : Vᴴ * V = 1)
    (hint : ∀ v : Fin (D * D), verticalTensor M v * V = V * B v)
    (hirr : MPSTensor.IsIrreducibleTensor B) (hρ : ρ.PosDef) (hrad : 0 < rad)
    (hfix : MPSTensor.transferMap (d := D * D) (D := n) B ρ = (rad : ℂ) • ρ)
    (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (MPSTensor.transferMap (d := D * D) (D := n) B) μ)
    (hnorm : ‖μ‖ = rad) (hne : μ ≠ (rad : ℂ)) :
    ∃ (p : ℕ) (Q : Matrix (Fin d) (Fin d) ℂ),
      p ≠ 0 ∧ Q.IsHermitian ∧ IsIdempotentElem Q ∧
      (∀ w : List (Fin (D * D)), w.length = p →
        Q * MPSTensor.evalWord (verticalTensor M) w =
          Q * MPSTensor.evalWord (verticalTensor M) w * Q) ∧
      M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q := by
  classical
  -- The corner space is nonzero: it carries an eigenvector.
  have hn : n ≠ 0 := by
    rintro rfl
    obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
    have hXne : X ≠ 0 := (Module.End.hasEigenvector_iff.mp hX).2
    exact hXne (Matrix.ext fun i _ => i.elim0)
  haveI : NeZero n := ⟨hn⟩
  -- The unital gauge of the corner and its Wolf Theorem 6.6 data.
  set K : MPSTensor (D * D) n := MPSTensor.spectralUnitalGauge B rad ρ with hK
  obtain ⟨hUnital, hIrrK, hIrrMap, σ, hσ, hσfix⟩ :=
    MPSTensor.spectralUnitalGauge_schwarz_setup B hirr ρ rad hρ hrad hfix
  obtain ⟨m, γ, hm_pos, hγprim, hset⟩ :=
    PeripheralSpectrum.peripheral_eigenvalues_cyclic_structure K hUnital σ hσ hσfix hIrrMap
  haveI : NeZero m := ⟨hm_pos.ne'⟩
  -- `μ / r` is a peripheral eigenvalue of the gauged transfer map, and it is
  -- not `1`, so the peripheral cyclic group has order at least two.
  have hradC : (rad : ℂ) ≠ 0 := by exact_mod_cast hrad.ne'
  have hμ'val : Module.End.HasEigenvalue
      (MPSTensor.transferMap (d := D * D) (D := n) K) (μ / rad) :=
    MPSTensor.hasEigenvalue_transferMap_spectralUnitalGauge B ρ rad hρ hrad hμ
  have hμ'norm : ‖μ / (rad : ℂ)‖ = 1 := by
    rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrad,
      div_self hrad.ne']
  have hμ'ne1 : μ / (rad : ℂ) ≠ 1 := fun h =>
    hne (by rwa [div_eq_one_iff_eq hradC] at h)
  have hm2 : 1 < m := by
    by_contra hm1'
    have hm1 : m = 1 := le_antisymm (not_lt.mp hm1') hm_pos
    have hμ'mem : μ / (rad : ℂ) ∈
        peripheralEigenvalues (MPSTensor.transferMap (d := D * D) (D := n) K) :=
      ⟨hμ'val, hμ'norm⟩
    rw [hset] at hμ'mem
    obtain ⟨k, hk⟩ := hμ'mem
    apply hμ'ne1
    rw [hk]
    subst hm1
    rw [Fin.eq_zero k]
    simp
  -- The cyclic family of Wolf Theorem 6.6 for the gauged corner map.
  have hperiph : peripheralEigenvalues (MPSTensor.transferMap (d := D * D) (D := n) K) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
    rw [hset]
    ext z
    simp [Set.mem_range, eq_comm]
  obtain ⟨U, P, _, _, _, hPproj, hPsum, _, hcyclic⟩ :=
    MPSTensor.exists_cyclic_decomposition_of_irreducible_schwarz
      (K := K) hUnital σ hσ hσfix hIrrMap hγprim hperiph
  -- Notation for the square root of the eigenvector and the scaling factor.
  set S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt ρ with hS
  have hSdet : IsUnit S.det := MPSTensor.isUnit_det_cfc_sqrt_of_posDef ρ hρ
  set c : ℂ := (↑((Real.sqrt rad)⁻¹) : ℂ) with hc
  have hcne : c ≠ 0 := by
    have hs : Real.sqrt rad ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hrad)
    rw [hc]
    exact_mod_cast inv_ne_zero hs
  -- Words of the vertically viewed tensor act on `V * S` through words of the
  -- gauged corner letters.
  have hword_int : ∀ w : List (Fin (D * D)),
      MPSTensor.evalWord (verticalTensor M) w * V = V * MPSTensor.evalWord B w := by
    intro w
    induction w with
    | nil => simp
    | cons v w ih =>
      rw [MPSTensor.evalWord_cons, MPSTensor.evalWord_cons, Matrix.mul_assoc, ih,
        ← Matrix.mul_assoc, hint v, Matrix.mul_assoc]
  have hletterB : ∀ v : Fin (D * D), B v * S = c⁻¹ • (S * K v) := by
    intro v
    have hKv : K v = c • (S⁻¹ * B v * S) := rfl
    rw [hKv, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hcne, one_smul,
      show S * (S⁻¹ * B v * S) = B v * S from by
        rw [Matrix.mul_assoc S⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hSdet]]
  have hkeyB : ∀ w : List (Fin (D * D)),
      MPSTensor.evalWord B w * S = (c⁻¹ ^ w.length) • (S * MPSTensor.evalWord K w) := by
    intro w
    induction w with
    | nil => simp
    | cons v w ih =>
      rw [MPSTensor.evalWord_cons, MPSTensor.evalWord_cons]
      calc B v * MPSTensor.evalWord B w * S
          = B v * (MPSTensor.evalWord B w * S) := by rw [Matrix.mul_assoc]
        _ = B v * ((c⁻¹ ^ w.length) • (S * MPSTensor.evalWord K w)) := by rw [ih]
        _ = (c⁻¹ ^ w.length) • (B v * S * MPSTensor.evalWord K w) := by
            rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = (c⁻¹ ^ w.length) • ((c⁻¹ • (S * K v)) * MPSTensor.evalWord K w) := by
            rw [hletterB v]
        _ = (c⁻¹ ^ (v :: w).length) • (S * (K v * MPSTensor.evalWord K w)) := by
            rw [Matrix.smul_mul, smul_smul, List.length_cons, pow_succ,
              mul_comm (c⁻¹ ^ w.length) c⁻¹, Matrix.mul_assoc]
  have hkey : ∀ w : List (Fin (D * D)),
      MPSTensor.evalWord (verticalTensor M) w * (V * S) =
        (c⁻¹ ^ w.length) • (V * S * MPSTensor.evalWord K w) := by
    intro w
    calc MPSTensor.evalWord (verticalTensor M) w * (V * S)
        = MPSTensor.evalWord (verticalTensor M) w * V * S := by
          rw [Matrix.mul_assoc]
      _ = V * MPSTensor.evalWord B w * S := by rw [hword_int w]
      _ = V * (MPSTensor.evalWord B w * S) := by rw [Matrix.mul_assoc]
      _ = V * ((c⁻¹ ^ w.length) • (S * MPSTensor.evalWord K w)) := by rw [hkeyB w]
      _ = (c⁻¹ ^ w.length) • (V * S * MPSTensor.evalWord K w) := by
          rw [Matrix.mul_smul, Matrix.mul_assoc]
  -- The projector: complement of the support projection of the transported
  -- cyclic sector `V S · ran (P 0)`.
  set Y : Matrix (Fin d) (Fin n) ℂ := V * S * P 0 with hY
  set π : Matrix (Fin d) (Fin d) ℂ :=
    MPSTensor.supportProj (Y * Yᴴ) (Matrix.posSemidef_self_mul_conjTranspose Y) with hπ
  have hπproj : IsOrthogonalProjection π :=
    MPSTensor.isOrthogonalProjection_supportProj (ρ := Y * Yᴴ)
      (hρ := Matrix.posSemidef_self_mul_conjTranspose Y)
  have hQproj : IsOrthogonalProjection (1 - π) := hπproj.one_sub
  -- Left cancellation of `V * S`.
  have hVScancel : ∀ {Z Z' : Matrix (Fin n) (Fin n) ℂ},
      V * S * Z = V * S * Z' → Z = Z' := by
    intro Z Z' hZZ
    have h1 : ∀ W : Matrix (Fin n) (Fin n) ℂ, S⁻¹ * (Vᴴ * (V * S * W)) = W := by
      intro W
      calc S⁻¹ * (Vᴴ * (V * S * W))
          = S⁻¹ * ((Vᴴ * V) * (S * W)) := by simp only [Matrix.mul_assoc]
        _ = S⁻¹ * (S * W) := by rw [hV, Matrix.one_mul]
        _ = W := Matrix.nonsing_inv_mul_cancel_left S W hSdet
    calc Z = S⁻¹ * (Vᴴ * (V * S * Z)) := (h1 Z).symm
      _ = S⁻¹ * (Vᴴ * (V * S * Z')) := by rw [hZZ]
      _ = Z' := h1 Z'
  -- The nonzero displaced sector index `0 - 1` in `Fin m`.
  have h01 : ((0 : Fin m) - 1) ≠ 0 := by
    intro h
    have h01' : (0 : Fin m) = 1 := sub_eq_zero.mp h
    have hv : (0 : ℕ) = 1 % m := by
      have := congrArg Fin.val h01'
      simpa [Fin.val_one'] using this
    rw [Nat.mod_eq_of_lt hm2] at hv
    exact absurd hv (by omega)
  refine ⟨m, 1 - π, hm_pos.ne', hQproj.1, hQproj.2, ?_, ?_⟩
  · -- Word invariance for full-period words: the sector returns to itself.
    intro w hw
    have hKw : MPSTensor.evalWord K w * P 0 = P 0 * MPSTensor.evalWord K w := by
      have := MPSTensor.evalWord_mul_cyclicProj K P hPproj hPsum hcyclic w 0
      rwa [hw, Fin.natCast_self, sub_zero] at this
    have hAY : MPSTensor.evalWord (verticalTensor M) w * Y =
        Y * ((c⁻¹ ^ w.length) • MPSTensor.evalWord K w) := by
      calc MPSTensor.evalWord (verticalTensor M) w * Y
          = MPSTensor.evalWord (verticalTensor M) w * (V * S) * P 0 := by
            rw [hY]; simp only [Matrix.mul_assoc]
        _ = ((c⁻¹ ^ w.length) • (V * S * MPSTensor.evalWord K w)) * P 0 := by
            rw [hkey w]
        _ = (c⁻¹ ^ w.length) • (V * S * (MPSTensor.evalWord K w * P 0)) := by
            rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]
        _ = (c⁻¹ ^ w.length) • (V * S * (P 0 * MPSTensor.evalWord K w)) := by
            rw [hKw]
        _ = (c⁻¹ ^ w.length) • (Y * MPSTensor.evalWord K w) := by
            rw [hY]; simp only [Matrix.mul_assoc]
        _ = Y * ((c⁻¹ ^ w.length) • MPSTensor.evalWord K w) := by
            rw [Matrix.mul_smul]
    have hinv0 : (1 - π) * MPSTensor.evalWord (verticalTensor M) w * π = 0 :=
      MPSTensor.one_sub_supportProj_mul_mul_supportProj_eq_zero Y hAY
    calc (1 - π) * MPSTensor.evalWord (verticalTensor M) w
        = (1 - π) * MPSTensor.evalWord (verticalTensor M) w * 1 := by
          rw [Matrix.mul_one]
      _ = (1 - π) * MPSTensor.evalWord (verticalTensor M) w * (π + (1 - π)) := by
          rw [add_sub_cancel]
      _ = (1 - π) * MPSTensor.evalWord (verticalTensor M) w * (1 - π) := by
          rw [Matrix.mul_add, hinv0, zero_add]
  · -- Single-letter displacement: one layer moves the sector to the
    -- neighboring orthogonal sector.
    intro hEq
    -- Letter-level invariance from the tensor equation.
    have hletter : ∀ v : Fin (D * D),
        (1 - π) * verticalTensor M v * π = 0 := by
      intro v
      have h1 : verticalTensor (M.ketLeftMul (1 - π)) v =
          verticalTensor ((M.ketLeftMul (1 - π)).braRightMul (1 - π)) v :=
        congrFun (congrArg verticalTensor hEq) v
      rw [verticalTensor_braRightMul, verticalTensor_ketLeftMul] at h1
      calc (1 - π) * verticalTensor M v * π
          = (1 - π) * verticalTensor M v * (1 - (1 - π)) := by
            rw [sub_sub_cancel]
        _ = (1 - π) * verticalTensor M v -
            (1 - π) * verticalTensor M v * (1 - π) := by
            rw [Matrix.mul_sub, Matrix.mul_one]
        _ = 0 := by rw [← h1, sub_self]
    -- The displaced sector kills every gauged letter.
    have hPK : ∀ v : Fin (D * D), P (0 - 1) * K v = 0 := by
      intro v
      -- Single-letter action on `Y`.
      have hKv0 : K v * P 0 = P (0 - 1) * K v := by
        have := MPSTensor.kraus_mul_cyclicProj K P hPproj hPsum hcyclic v (0 - 1)
        rwa [sub_add_cancel] at this
      have hsingle : verticalTensor M v * Y =
          c⁻¹ • (V * S * (P (0 - 1) * K v)) := by
        have hkey1 := hkey [v]
        simp only [List.length_cons, List.length_nil, zero_add, pow_one,
          MPSTensor.evalWord_cons, MPSTensor.evalWord_nil, Matrix.mul_one] at hkey1
        calc verticalTensor M v * Y
            = verticalTensor M v * (V * S) * P 0 := by
              rw [hY]; simp only [Matrix.mul_assoc]
          _ = (c⁻¹ • (V * S * K v)) * P 0 := by rw [hkey1]
          _ = c⁻¹ • (V * S * (K v * P 0)) := by
              rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]
          _ = c⁻¹ • (V * S * (P (0 - 1) * K v)) := by rw [hKv0]
      -- `π` fixes `Y` and absorbs the letter action.
      have hπY : π * Y = Y := MPSTensor.supportProj_mul_left_eq_self Y
      have hfix' : π * (verticalTensor M v * Y) = verticalTensor M v * Y := by
        have hAπ : verticalTensor M v * π = π * (verticalTensor M v * π) := by
          have h0 := hletter v
          have := sub_eq_zero.mp (by
            calc verticalTensor M v * π - π * (verticalTensor M v * π)
                = (1 - π) * verticalTensor M v * π := by
                  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
                    Matrix.mul_assoc]
              _ = 0 := h0)
          exact this
        calc π * (verticalTensor M v * Y)
            = π * (verticalTensor M v * (π * Y)) := by rw [hπY]
          _ = π * (verticalTensor M v * π) * Y := by simp only [Matrix.mul_assoc]
          _ = verticalTensor M v * π * Y := by rw [← hAπ]
          _ = verticalTensor M v * Y := by rw [Matrix.mul_assoc, hπY]
      -- Express the fixed equation through the support factorization.
      obtain ⟨W, hW⟩ := MPSTensor.exists_supportProj_eq_mul (Y * Yᴴ)
        (Matrix.posSemidef_self_mul_conjTranspose Y)
      have hππ : π = Y * (Yᴴ * W) := by rw [hπ, hW, Matrix.mul_assoc]
      have hZ : V * S * (P (0 - 1) * K v) =
          V * S * (P 0 * (Yᴴ * W * (V * S * (P (0 - 1) * K v)))) := by
        have hs : π * (V * S * (P (0 - 1) * K v)) = V * S * (P (0 - 1) * K v) := by
          have := hfix'
          rw [hsingle, Matrix.mul_smul] at this
          exact smul_right_injective _ (inv_ne_zero hcne) this
        calc V * S * (P (0 - 1) * K v)
            = π * (V * S * (P (0 - 1) * K v)) := hs.symm
          _ = Y * (Yᴴ * W * (V * S * (P (0 - 1) * K v))) := by
              rw [hππ]; simp only [Matrix.mul_assoc]
          _ = V * S * (P 0 * (Yᴴ * W * (V * S * (P (0 - 1) * K v)))) := by
              rw [hY]; simp only [Matrix.mul_assoc]
      have hcancel := hVScancel hZ
      have horth : P (0 - 1) * P 0 = 0 :=
        orthogonalProjection_mul_eq_zero_of_sum_eq_one P hPproj hPsum h01
      calc P (0 - 1) * K v
          = P (0 - 1) * (P (0 - 1) * K v) := by
            rw [← Matrix.mul_assoc, (hPproj (0 - 1)).2]
        _ = P (0 - 1) * (P 0 * (Yᴴ * W * (V * S * (P (0 - 1) * K v)))) := by
            conv_lhs => rw [hcancel]
        _ = 0 := by rw [← Matrix.mul_assoc, horth, Matrix.zero_mul]
    -- The cyclic action then annihilates the displaced sector, which is
    -- impossible: no cyclic projection vanishes.
    have hmap0 : MPSTensor.transferMap (d := D * D) (D := n) K (P 0) = 0 := by
      rw [MPSTensor.transferMap_apply]
      refine Finset.sum_eq_zero fun v _ => ?_
      have hKv0 : K v * P 0 = P (0 - 1) * K v := by
        have := MPSTensor.kraus_mul_cyclicProj K P hPproj hPsum hcyclic v (0 - 1)
        rwa [sub_add_cancel] at this
      rw [hKv0, hPK v, Matrix.zero_mul]
    have hP1 : P (0 - 1) = 0 := by
      have := hcyclic (0 - 1)
      rwa [sub_add_cancel, hmap0, eq_comm] at this
    exact MPSTensor.cyclicProj_ne_zero K P hPsum hcyclic (0 - 1) hP1

/-- **Hypothesis** (arXiv:1606.00608, lines 1888--1891, resting on the
canonical-form input of lines 1874--1887): an orthogonal projector on the
physical space that is displaced by the vertically viewed tensor —
$Q\widetilde M\ne Q\widetilde MQ$ — fails to commute with the density
operator $H^{(N)}$ at every length.

This is the horizontal-canonical-form step of the periodic-sector argument.
The source assumes literal canonical form in the horizontal direction.  Under
normalized BNT-refined horizontal form, Lemma L turns the full positive-length
family of first-site identities into the letter-level invariance
$Q\widetilde M=Q\widetilde MQ$.  The all-length assertion below is stronger
than needed: `hasNoPeriodicVectors_verticalTensor_of_horizontalCF` uses the
single noncommuting length supplied by the contrapositive of Lemma L. -/
def NoninvariantProjectorNoncommuting {d D : ℕ} (M : MPOTensor d D) : Prop :=
  ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.IsHermitian → IsIdempotentElem Q →
    M.ketLeftMul Q ≠ (M.ketLeftMul Q).braRightMul Q →
    ∀ N : ℕ, ¬ Commute (firstSiteMatrix Q N) (mpo M (N + 1))

/-- The non-commutation hypothesis discharges the cyclic-projector hypothesis
of the periodic-sector step: the cyclic decomposition of the peripheral
spectrum supplies the invariant, displaced projector unconditionally
(`exists_displaced_invariant_projector_of_periodic_vector`), and the
displacement upgrades to the all-length non-commutation family through the
hypothesis.  This reduces the periodic-sector step of the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1888--1893, to the explicit
all-length non-commutation interface.  This is a stronger conditional
formulation than the normalized BNT-refined theorem below. -/
theorem periodicVectorYieldsCyclicProjector_of_noncommutation
    {d D : ℕ} (M : MPOTensor d D)
    (hNC : NoninvariantProjectorNoncommuting M) :
    PeriodicVectorYieldsCyclicProjector M := by
  intro n V B ρ rad hV hint hirr hρ hrad hfix μ hμ hnorm hne
  obtain ⟨p, Q, hp, hherm, hidem, hword, hdisp⟩ :=
    exists_displaced_invariant_projector_of_periodic_vector M V B ρ rad hV hint
      hirr hρ hrad hfix μ hμ hnorm hne
  exact ⟨p, Q, hp, hherm, hidem, hword, hNC Q hherm hidem hdisp⟩

/-- The vertically viewed tensor of a matrix product density operator has no
nontrivial periodic vectors, granted that displaced projectors never commute
with the density operator.  This is the periodic-sector step in the proof of
Proposition 4.13 of arXiv:1606.00608, lines 1888--1893, with the projector
and its word invariance constructed from the cyclic decomposition of the
peripheral spectrum (Wolf 2012, Theorem 6.6) rather than assumed.

**Scope restriction (conditional on the non-commutation family):** the
hypothesis requires noncommutation at every length.  The theorem
`hasNoPeriodicVectors_verticalTensor_of_horizontalCF` instead uses one
noncommuting length supplied by normalized BNT-refined horizontal form; it is
not the literal source theorem. -/
theorem hasNoPeriodicVectors_verticalTensor_of_noncommutation
    {d D : ℕ} (M : MPOTensor d D) (hM : IsMPDO M)
    (hNC : NoninvariantProjectorNoncommuting M) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) :=
  hasNoPeriodicVectors_verticalTensor_of_cyclicProjector M hM
    (periodicVectorYieldsCyclicProjector_of_noncommutation M hNC)

/-- **The periodic-sector step for a single-letter injective matrix product
density operator, unconditionally.**

If `M`'s doubled-index tensor is (single-letter) injective, the vertically
viewed tensor has no nontrivial periodic vectors, with no further hypothesis.
This bypasses `NoninvariantProjectorNoncommuting` entirely: rather than
requiring the displaced-projector-noncommutation family at *every* chain
length, the contradiction only ever needs the commutation family at chain
length `2`, where `ketLeftMul_eq_braRightMul_of_commute_of_isInjective`
(`TNLean/MPS/MPDO/InvariantProjection.lean`) applies directly to `M`'s own
letters through injectivity's trace-pairing nondegeneracy — no horizontal
canonical-form decomposition or `SameMPV₂` transport is needed.

The word invariance of the constructed cyclic projector transfers to the
stacked tensor (`stackedTensor_ketLeftMul_invariant`), giving commutation with
$[H^{(2)}]^p$ unconditionally through the invariant-projection step applied to
the stack (`firstSiteMatrix_mul_mpo_comm`); positive semidefiniteness of the
density operators then removes the power (`mpo_commute_of_commute_pow`), and
injectivity turns the resulting commutation with $H^{(2)}$ into the
letter-level invariance that the displacement forbids.

**Scope restriction (single-letter injective tensors):** the source's
Proposition 4.13 allows `M` to be reducible, decomposed horizontally into
several gauge-inequivalent canonical-form blocks with weights; this theorem
covers the sub-case where `M`'s own tensor is already (single-letter)
injective.  The theorem `hasNoPeriodicVectors_verticalTensor_of_horizontalCF`
below treats normalized BNT-refined horizontal form. -/
theorem hasNoPeriodicVectors_verticalTensor_of_isInjective
    {d D : ℕ} (M : MPOTensor d D) (hM : IsMPDO M)
    (hInj : MPSTensor.IsInjective M.toMPSTensor) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  intro n V B ρ r hV hint hirr hρ hr hfix μ hμ hnorm
  by_contra hne
  obtain ⟨p, Q, hp, hQherm, hQidem, hword, hdisp⟩ :=
    exists_displaced_invariant_projector_of_periodic_vector M V B ρ r hV hint
      hirr hρ hr hfix μ hμ hnorm hne
  apply hdisp
  have hCommPow : Commute (firstSiteMatrix Q 1) (mpo M 2 ^ p) := by
    have h := firstSiteMatrix_mul_mpo_comm (stackedTensor M p) (hM.stackedTensor p) hQherm
      (stackedTensor_ketLeftMul_invariant M hword) 1
    rwa [mpo_stackedTensor] at h
  exact ketLeftMul_eq_braRightMul_of_commute_of_isInjective M hInj hQidem
    (mpo_commute_of_commute_pow M hM 2 (by omega) hp hCommPow)

/-- **The periodic-sector step for an MPDO in normalized BNT-refined
horizontal form.**

The vertically viewed tensor of an MPDO in normalized BNT-refined horizontal
form has no nontrivial periodic vector.  A periodic vector supplies an
orthogonal projector displaced by one vertical layer and invariant under every
word of one full period.  The BNT-refined horizontal form shows that this
displacement forces noncommutation with the density operator at some positive
length.
Full-period invariance gives commutation with the corresponding power of that
density operator, while positivity removes the power and gives a
contradiction.

This proves the periodic-sector paragraph of arXiv:1606.00608,
Proposition 4.13, lines 1888--1893, only under the stronger BNT-refined
horizontal hypothesis.  One noncommuting length is enough; the source states
the stronger all-length inequality, but the contradiction is pointwise in the
length.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; no literal canonical-form
conclusion is asserted.

**Local fix (noncommuting length):** the all-length inequality printed at
source line 1889 is replaced by the existential consequence of the BNT-refined
Lemma L, which is sufficient at lines 1890--1893. -/
theorem hasNoPeriodicVectors_verticalTensor_of_horizontalCF
    (M : MPOTensor d D) (hM : IsMPDO M) (hHorizontal : IsHorizontalCF M) :
    MPSTensor.HasNoPeriodicVectors (verticalTensor M) := by
  intro n V B ρ r hV hint hirr hρ hr hfix μ hμ hnorm
  by_contra hne
  obtain ⟨p, Q, hp, hQherm, hQidem, hword, hdisp⟩ :=
    exists_displaced_invariant_projector_of_periodic_vector M V B ρ r hV hint
      hirr hρ hr hfix μ hμ hnorm hne
  obtain ⟨N, hN⟩ := hHorizontal.exists_not_commute_of_displaced M hQidem hdisp
  apply hN
  have hCommPow : Commute (firstSiteMatrix Q N) (mpo M (N + 1) ^ p) := by
    have h := firstSiteMatrix_mul_mpo_comm (stackedTensor M p)
      (hM.stackedTensor p) hQherm (stackedTensor_ketLeftMul_invariant M hword) N
    rwa [mpo_stackedTensor] at h
  exact mpo_commute_of_commute_pow M hM (N + 1) (by omega) hp hCommPow

end MPOTensor

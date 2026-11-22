/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationCaseInvariance

/-!
# The determinants of conjugation-invariant gates along a gate path

For even ranks `ℓ, r`, the determinants `det u` and `det v` of standard-form gates in
the normal form of Proposition `corconj` (eqs. `ortuv`, `sympuv`) do not depend on
the remaining orthogonal or symplectic gauge, because `det(O_ℓ ⊗ O_r) = 1`
(arXiv:1703.09188, lines 1466--1480). Without fixing the gauge they are read off as
`J(u) = det(x)^{r/2} det(y)^{ℓ/2} det(u)` and `J'(v) = conj(det(x)^{r/2} det(y)^{ℓ/2}) det(v)`,
where `conj(u) u† = x ⊗ y` are the unitaries of Proposition `prop1conj`. These are
`±1`, do not depend on the choice of `x, y`, and are continuous along a continuous
path of gates, so they are constant along a path of gates each generating a
conjugation-invariant MPU. This is the step of the "only if" direction of Theorem
`prop:conjsym-strict-equiv` (lines 1500--1534) that follows the symmetry path
criterion; the source lifts `x(p), y(p)` continuously, while here the factors are
read off locally from `conj(u) u†`.

## Main definitions and results

* `MPOTensor.kronFactorDet`: `det(x)^{r/2} det(y)^{ℓ/2}`.
* `MPOTensor.kronFactorDet_eq_of_kronecker_eq`: it depends only on `x ⊗ y`.
* `MPOTensor.kronFactorDet_mul_det_eq_one_or_neg_one`: `J(u) = ±1`.
* `MPOTensor.det_eq_of_symmetric_gate_path`: the determinants are constant along a
  conjugation-invariant gate path.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d ℓ r : ℕ}

/-- `det(x)^{r/2} det(y)^{ℓ/2}` for `x` on `ℂ^ℓ` and `y` on `ℂ^r`. -/
noncomputable def kronFactorDet (x : Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : Matrix (Fin r) (Fin r) ℂ) :
    ℂ :=
  x.det ^ (r / 2) * y.det ^ (ℓ / 2)

theorem kronFactorDet_smul (hℓ : Even ℓ) (hr : Even r) (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)
    (y : Matrix (Fin r) (Fin r) ℂ) {c : ℂ} (hc : c ≠ 0) :
    kronFactorDet (c • x) (c⁻¹ • y) = kronFactorDet x y := by
  obtain ⟨a, rfl⟩ := hℓ
  obtain ⟨b, rfl⟩ := hr
  have h2 : ∀ n : ℕ, (n + n) / 2 = n := fun n ↦ by omega
  simp only [kronFactorDet, Matrix.det_smul, Fintype.card_fin, h2, mul_pow, ← pow_mul]
  rw [show (a + a) * b = (b + b) * a by ring, inv_pow]
  field_simp

/-- The left factor `K_{(·,s),(·,s')}` of a Kronecker product. -/
def kronLeftFactor (K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ) (s s' : Fin r) :
    Matrix (Fin ℓ) (Fin ℓ) ℂ :=
  fun i j ↦ K (i, s) (j, s')

/-- The right factor `K_{(a,·),(a',·)} / K_{(a,s),(a',s')}` of a Kronecker product. -/
noncomputable def kronRightFactor (K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ)
    (a a' : Fin ℓ) (s s' : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  fun t t' ↦ K (a, t) (a', t') / K (a, s) (a', s')

/-- `kronFactorDet` read off locally from the Kronecker product. -/
theorem kronFactorDet_eq_local (hℓ : Even ℓ) (hr : Even r) (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)
    (y : Matrix (Fin r) (Fin r) ℂ) {a a' : Fin ℓ} {s s' : Fin r}
    (h : (x ⊗ₖ y) (a, s) (a', s') ≠ 0) :
    kronFactorDet x y =
      kronFactorDet (kronLeftFactor (x ⊗ₖ y) s s') (kronRightFactor (x ⊗ₖ y) a a' s s') := by
  rw [Matrix.kroneckerMap_apply] at h
  have hx : x a a' ≠ 0 := left_ne_zero_of_mul h
  have hy : y s s' ≠ 0 := right_ne_zero_of_mul h
  have hL : kronLeftFactor (x ⊗ₖ y) s s' = y s s' • x := by
    ext i j
    simp [kronLeftFactor, Matrix.kroneckerMap_apply, mul_comm]
  have hR : kronRightFactor (x ⊗ₖ y) a a' s s' = (y s s')⁻¹ • y := by
    ext t t'
    simp only [kronRightFactor, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  rw [hL, hR, kronFactorDet_smul hℓ hr x y hy]

/-- **`kronFactorDet` depends only on the Kronecker product.** -/
theorem kronFactorDet_eq_of_kronecker_eq (hℓ : Even ℓ) (hr : Even r)
    {x x' : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y y' : Matrix (Fin r) (Fin r) ℂ}
    (h : x ⊗ₖ y = x' ⊗ₖ y') (hne : x ⊗ₖ y ≠ 0) : kronFactorDet x y = kronFactorDet x' y' := by
  obtain ⟨⟨a, s⟩, ⟨a', s'⟩, hK⟩ : ∃ i j, (x ⊗ₖ y) i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Matrix.ext hc)
  rw [kronFactorDet_eq_local hℓ hr x y hK, kronFactorDet_eq_local hℓ hr x' y' (h ▸ hK), h]

theorem continuousOn_kronFactorDet_local (a a' : Fin ℓ) (s s' : Fin r) :
    ContinuousOn (fun K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ ↦
        kronFactorDet (kronLeftFactor K s s') (kronRightFactor K a a' s s'))
      {K | K (a, s) (a', s') ≠ 0} := by
  have hL : Continuous fun K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ ↦
      kronLeftFactor K s s' :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      (continuous_apply (j, s')).comp (continuous_apply (i, s))
  have hR : ContinuousOn (fun K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ ↦
      kronRightFactor K a a' s s') {K | K (a, s) (a', s') ≠ 0} := by
    refine continuousOn_pi.mpr fun t ↦ continuousOn_pi.mpr fun t' ↦ ?_
    have h1 : Continuous fun K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ ↦ K (a, t) (a', t') :=
      (continuous_apply (a', t')).comp (continuous_apply (a, t))
    have h2 : Continuous fun K : Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ ↦ K (a, s) (a', s') :=
      (continuous_apply (a', s')).comp (continuous_apply (a, s))
    exact h1.continuousOn.div h2.continuousOn fun K hK ↦ hK
  exact ((hL.matrix_det.pow _).continuousOn).mul
    ((continuous_id.matrix_det.comp_continuousOn hR).pow _)

/-- **`J(u) = ±1`.** If `conj(u) = (x ⊗ y) u` with unitaries `x, y` that are both
symmetric or both skew-symmetric and the ranks are even, then
`det(x)^{r/2} det(y)^{ℓ/2} det(u) = ±1`: it is the determinant of the gate in the
normal form of Proposition `corconj`. Source: arXiv:1703.09188, lines 1466--1480. -/
theorem kronFactorDet_mul_det_eq_one_or_neg_one (hℓ : Even ℓ) (hr : Even r)
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ Matrix.unitaryGroup (Fin r) ℂ)
    (hT : (xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y))
    (hcu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) (hcv : v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ))
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (f : Fin d × Fin d ≃ Fin r × Fin ℓ) :
    (kronFactorDet x y * (u.submatrix id e).det = 1 ∨
        kronFactorDet x y * (u.submatrix id e).det = -1) ∧
      (starRingEnd ℂ (kronFactorDet x y) * (v.submatrix id f).det = 1 ∨
        starRingEnd ℂ (kronFactorDet x y) * (v.submatrix id f).det = -1) := by
  -- Normal forms `x = Uᵀ Λ U`, `y = Vᵀ Λ' V` with `det Λ = det Λ' = 1`.
  have hnf : ∀ {n : ℕ} (hn : Even n) {z : Matrix (Fin n) (Fin n) ℂ},
      z ∈ Matrix.unitaryGroup (Fin n) ℂ → (zᵀ = z ∨ zᵀ = -z) →
      ∃ (U Λ : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Λ.det = 1 ∧
        (Λᴴ).det = 1 ∧ z = Uᵀ * Λ * U := by
    intro n hn z hz hzT
    rcases hzT with h | h
    · obtain ⟨S, -, hS, hzS⟩ := Matrix.exists_symmetric_unitary_squareRoot z hz h
      exact ⟨S, 1, hS, by simp, by simp, by rw [Matrix.mul_one]; exact hzS⟩
    · obtain ⟨U, hU, hzU⟩ := Matrix.exists_unitary_congruence_sourceSkewForm hn z hz h
      refine ⟨U, _, hU, det_sourceSkewForm hn, ?_, hzU⟩
      rw [Matrix.det_conjTranspose, det_sourceSkewForm hn, star_one]
  obtain ⟨U, Λ, hU, hΛ, hΛ', hxU⟩ := hnf hℓ hx (hT.imp (fun h ↦ h.1) (fun h ↦ h.1))
  obtain ⟨V, Λ₂, hV, hΛ₂, hΛ₂', hyV⟩ := hnf hr hy (hT.imp (fun h ↦ h.2) (fun h ↦ h.2))
  have hdetx : x.det ^ (r / 2) = U.det ^ r := by
    rw [hxU, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hΛ, mul_one, ← sq, ← pow_mul,
      Nat.two_mul_div_two_of_even hr]
  have hdety : y.det ^ (ℓ / 2) = V.det ^ ℓ := by
    rw [hyV, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hΛ₂, mul_one, ← sq, ← pow_mul,
      Nat.two_mul_div_two_of_even hℓ]
  have hk : kronFactorDet x y = U.det ^ r * V.det ^ ℓ := by rw [kronFactorDet, hdetx, hdety]
  have hUV : (U ⊗ₖ V).det = U.det ^ r * V.det ^ ℓ := by
    rw [Matrix.det_kronecker, Fintype.card_fin, Fintype.card_fin]
  refine ⟨?_, ?_⟩
  · have hu' : ((U ⊗ₖ V) * u).IsUnitaryBetween :=
      ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
        (Matrix.kronecker_mem_unitary hU hV)).mul _ _ hu
    have h := det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul hu'
      (by rw [Matrix.det_kronecker, hΛ, hΛ₂, one_pow, one_pow, one_mul])
      (Matrix.map_star_gaugeLeft_eq_of_congruence hU hV hxU hyV hcu) e
    rwa [Matrix.det_mul_submatrix, hUV, ← hk] at h
  · have hv' : (v * (Vᴴ ⊗ₖ Uᴴ)).IsUnitaryBetween :=
      hv.mul _ _ ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mpr
        (Matrix.kronecker_mem_unitary (Unitary.star_mem hV) (Unitary.star_mem hU)))
    have h := det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul_right hv'
      (by rw [Matrix.det_kronecker, hΛ₂', hΛ', one_pow, one_pow, one_mul])
      (Matrix.map_star_gaugeRight_eq_of_congruence hU hV hxU hyV hcv) f
    have hVU : (Vᴴ ⊗ₖ Uᴴ).det = starRingEnd ℂ (kronFactorDet x y) := by
      rw [Matrix.det_kronecker, Matrix.det_conjTranspose, Matrix.det_conjTranspose, hk,
        Fintype.card_fin, Fintype.card_fin, map_mul, map_pow, map_pow, starRingEnd_apply,
        starRingEnd_apply, mul_comm]
    rwa [Matrix.det_submatrix_mul, hVU, mul_comm] at h

/-- A continuous `±1`-valued function on the unit interval is constant. -/
private theorem eq_of_continuous_of_eq_one_or_neg_one {f : unitInterval → ℂ} (hf : Continuous f)
    (h : ∀ p, f p = 1 ∨ f p = -1) : f 0 = f 1 := by
  have hg : Continuous fun p ↦ (f p).re := Complex.continuous_re.comp hf
  have hre : ∀ p, (f p).re ≠ 0 := fun p ↦ by rcases h p with h | h <;> simp [h]
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1
  · rw [h0, h1]
  · exfalso
    obtain ⟨p, hp⟩ := intermediate_value_univ 1 0 hg
      (show (0 : ℝ) ∈ Set.Icc (f 1).re (f 0).re by rw [h0, h1]; norm_num)
    exact hre p hp
  · exfalso
    obtain ⟨p, hp⟩ := intermediate_value_univ 0 1 hg
      (show (0 : ℝ) ∈ Set.Icc (f 0).re (f 1).re by rw [h0, h1]; norm_num)
    exact hre p hp
  · rw [h0, h1]

/-- **`J(u)` and `J'(v)` are constant along a continuous gate path.** Let `u(p), v(p)`
be continuous families of unitary gates and `x(p), y(p)` unitaries, both symmetric or
both skew-symmetric, with `conj(u) = (x ⊗ y) u` and `conj(v) = v (y† ⊗ x†)` at every
`p`. For even ranks, `det(x)^{r/2} det(y)^{ℓ/2} det(u)` and its conjugate-weighted
counterpart for `v` take the same values at both endpoints. No continuity of `x, y`
is assumed. Source: arXiv:1703.09188, proof of Theorem `prop:conjsym-strict-equiv`,
"only if", lines 1500--1534. -/
theorem kronFactorDet_mul_det_eq_of_path (hℓ : Even ℓ) (hr : Even r) [NeZero ℓ] [NeZero r]
    {u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : unitInterval → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hucont : Continuous u) (hvcont : Continuous v)
    (hu : ∀ p, (u p).IsUnitaryBetween) (hv : ∀ p, (v p).IsUnitaryBetween)
    (x : unitInterval → Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : unitInterval → Matrix (Fin r) (Fin r) ℂ)
    (hx : ∀ p, x p ∈ Matrix.unitaryGroup (Fin ℓ) ℂ) (hy : ∀ p, y p ∈ Matrix.unitaryGroup (Fin r) ℂ)
    (hT : ∀ p, ((x p)ᵀ = x p ∧ (y p)ᵀ = y p) ∨ ((x p)ᵀ = -x p ∧ (y p)ᵀ = -y p))
    (hcu : ∀ p, (u p).map (starRingEnd ℂ) = (x p ⊗ₖ y p) * u p)
    (hcv : ∀ p, (v p).map (starRingEnd ℂ) = v p * ((y p)ᴴ ⊗ₖ (x p)ᴴ))
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (f : Fin d × Fin d ≃ Fin r × Fin ℓ) :
    kronFactorDet (x 0) (y 0) * ((u 0).submatrix id e).det =
        kronFactorDet (x 1) (y 1) * ((u 1).submatrix id e).det ∧
      starRingEnd ℂ (kronFactorDet (x 0) (y 0)) * ((v 0).submatrix id f).det =
        starRingEnd ℂ (kronFactorDet (x 1) (y 1)) * ((v 1).submatrix id f).det := by
  -- Continuity of `p ↦ det(x p)^{r/2} det(y p)^{ℓ/2}`.
  have hK : Continuous fun p ↦ gateConjugationMatrix (u p) :=
    (hucont.matrix_map continuous_star).matrix_mul hucont.matrix_conjTranspose
  have hKeq : ∀ p, gateConjugationMatrix (u p) = x p ⊗ₖ y p := fun p ↦
    gateConjugationMatrix_eq (hu p).2 (hcu p)
  have hQ : Continuous fun p ↦ kronFactorDet (x p) (y p) := by
    refine continuous_iff_continuousAt.mpr fun p ↦ ?_
    obtain ⟨⟨a, s⟩, ⟨a', s'⟩, hne⟩ : ∃ i j, (x p ⊗ₖ y p) i j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact kronecker_ne_zero_of_mem_unitaryGroup (hx p) (hy p) (Matrix.ext hc)
    have hopen : IsOpen {q : unitInterval | gateConjugationMatrix (u q) (a, s) (a', s') ≠ 0} :=
      isOpen_ne_fun (hK.matrix_elem (a, s) (a', s')) continuous_const
    have hmem : p ∈ {q : unitInterval | gateConjugationMatrix (u q) (a, s) (a', s') ≠ 0} := by
      change gateConjugationMatrix (u p) (a, s) (a', s') ≠ 0
      rwa [hKeq p]
    have hev : (fun q ↦ kronFactorDet (x q) (y q)) =ᶠ[nhds p] fun q ↦
        kronFactorDet (kronLeftFactor (gateConjugationMatrix (u q)) s s')
          (kronRightFactor (gateConjugationMatrix (u q)) a a' s s') := by
      filter_upwards [hopen.mem_nhds hmem] with q hq
      change gateConjugationMatrix (u q) (a, s) (a', s') ≠ 0 at hq
      rw [hKeq q] at hq ⊢
      exact kronFactorDet_eq_local hℓ hr _ _ hq
    refine (ContinuousAt.congr ?_ hev.symm)
    exact ((continuousOn_kronFactorDet_local a a' s s').continuousAt
      ((isOpen_ne_fun (continuous_id.matrix_elem (a, s) (a', s')) continuous_const).mem_nhds
        (by change _ ≠ 0; rwa [hKeq p]))).comp hK.continuousAt
  have hdu : Continuous fun p ↦ ((u p).submatrix id e).det :=
    Continuous.matrix_det (continuous_pi fun i ↦ continuous_pi fun j ↦
      (continuous_apply (e j)).comp ((continuous_apply i).comp hucont))
  have hdv : Continuous fun p ↦ ((v p).submatrix id f).det :=
    Continuous.matrix_det (continuous_pi fun i ↦ continuous_pi fun j ↦
      (continuous_apply (f j)).comp ((continuous_apply i).comp hvcont))
  have hpm := fun p ↦ kronFactorDet_mul_det_eq_one_or_neg_one hℓ hr (hu p) (hv p) (hx p) (hy p)
    (hT p) (hcu p) (hcv p) e f
  exact ⟨eq_of_continuous_of_eq_one_or_neg_one (hQ.mul hdu) fun p ↦ (hpm p).1,
    eq_of_continuous_of_eq_one_or_neg_one ((Complex.continuous_conj.comp hQ).mul hdv)
      fun p ↦ (hpm p).2⟩

/-- At an endpoint in the normal form of `corconj`, `det(x)^{r/2} det(y)^{ℓ/2} = 1`. -/
private theorem kronFactorDet_eq_one_of_normalForm (hℓ : Even ℓ) (hr : Even r)
    [NeZero ℓ] [NeZero r]
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsUnitaryBetween)
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ Matrix.unitaryGroup (Fin r) ℂ)
    (hcu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u)
    (hnf : (u.map (starRingEnd ℂ) = u ∧ v.map (starRingEnd ℂ) = v) ∨
      (u.map (starRingEnd ℂ) = (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * u ∧
        v.map (starRingEnd ℂ) = v * (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ))) :
    kronFactorDet x y = 1 := by
  have hne := kronecker_ne_zero_of_mem_unitaryGroup hx hy
  rcases hnf with ⟨h, -⟩ | ⟨h, -⟩
  · have hK : x ⊗ₖ y = (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [← gateConjugationMatrix_eq hu.2 hcu, gateConjugationMatrix_eq hu.2 (u := u)
        (x := 1) (y := 1) (by rw [h, Matrix.one_kronecker_one, Matrix.one_mul])]
    rw [kronFactorDet_eq_of_kronecker_eq hℓ hr hK hne]
    simp [kronFactorDet]
  · rw [kronFactorDet_eq_of_kronecker_eq hℓ hr
      ((gateConjugationMatrix_eq hu.2 hcu).symm.trans (gateConjugationMatrix_eq hu.2 h)) hne]
    simp [kronFactorDet, det_sourceSkewForm]

/-- **The determinants along a conjugation-invariant gate path.** Let `ℓ, r` be even and
let `u(p), v(p)` be continuous families of unitary gates such that the MPU generated by
`u(p), v(p)` is invariant under complex conjugation at every `p`. If the gates at
both endpoints are real (eq. `ortuv`), or both in the symplectic form (eq. `sympuv`),
then `det u(0) = det u(1)` and `det v(0) = det v(1)`, read through fixed
identifications of the coordinate spaces.

This is the step of the "only if" direction of Theorem `prop:conjsym-strict-equiv`
that follows the symmetry path criterion: the source obtains a path `u(p), v(p)` of
standard-form gates preserving the symmetry (lines 1500--1503) and shows that the
determinants of the gauge-fixed gates cannot change along it (lines 1504--1534).
Here the invariant `det(x)^{r/2} det(y)^{ℓ/2} det u` is read directly from
`conj(u) u† = x ⊗ y`, so no continuous choice of `x(p), y(p)` is needed.

Source: arXiv:1703.09188, proof of Theorem `prop:conjsym-strict-equiv`,
lines 1500--1534. -/
theorem det_eq_of_symmetric_gate_path (hℓ : Even ℓ) (hr : Even r) [NeZero d] [NeZero ℓ]
    [NeZero r] {u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : unitInterval → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hucont : Continuous u) (hvcont : Continuous v)
    (hu : ∀ p, (u p).IsUnitaryBetween) (hv : ∀ p, (v p).IsUnitaryBetween)
    (hinv : ∀ p, ∀ N : ℕ, 0 < N → mpo (standardFormTensorOfGates (u p) (v p)) N =
      (mpo (standardFormTensorOfGates (u p) (v p)) N).map (starRingEnd ℂ))
    (hnf : ∀ p ∈ ({0, 1} : Set unitInterval),
      ((u p).map (starRingEnd ℂ) = u p ∧ (v p).map (starRingEnd ℂ) = v p) ∨
      ((u p).map (starRingEnd ℂ) = (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * u p ∧
        (v p).map (starRingEnd ℂ) =
          v p * (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ)))
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (f : Fin d × Fin d ≃ Fin r × Fin ℓ) :
    ((u 0).submatrix id e).det = ((u 1).submatrix id e).det ∧
      ((v 0).submatrix id f).det = ((v 1).submatrix id f).det := by
  have hcase : ∀ p, IsConjugationCaseI (u p) (v p) ∨ IsConjugationCaseII (u p) (v p) := fun p ↦
    (standardFormTensorOfGatesData (u p) (v p) (hu p) (hv p)).isConjugationCase_of_conjugation
      (hinv p)
  have hdata : ∀ p, ∃ (x : Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : Matrix (Fin r) (Fin r) ℂ),
      x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ ∧ y ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      ((xᵀ = x ∧ yᵀ = y) ∨ (xᵀ = -x ∧ yᵀ = -y)) ∧
      (u p).map (starRingEnd ℂ) = (x ⊗ₖ y) * u p ∧
      (v p).map (starRingEnd ℂ) = v p * (yᴴ ⊗ₖ xᴴ) := fun p ↦ by
    rcases hcase p with ⟨x, y, hx, hy, hxT, hyT, hcu, hcv⟩ | ⟨x, y, hx, hy, hxT, hyT, hcu, hcv⟩
    · exact ⟨x, y, hx, hy, Or.inl ⟨hxT, hyT⟩, hcu, hcv⟩
    · exact ⟨x, y, hx, hy, Or.inr ⟨hxT, hyT⟩, hcu, hcv⟩
  choose x y hx hy hT hcu hcv using hdata
  obtain ⟨hJu, hJv⟩ := kronFactorDet_mul_det_eq_of_path hℓ hr hucont hvcont hu hv x y hx hy hT
    hcu hcv e f
  have h0 := kronFactorDet_eq_one_of_normalForm hℓ hr (hu 0) (hx 0) (hy 0) (hcu 0)
    (hnf 0 (by simp))
  have h1 := kronFactorDet_eq_one_of_normalForm hℓ hr (hu 1) (hx 1) (hy 1) (hcu 1)
    (hnf 1 (by simp))
  rw [h0, h1] at hJu hJv
  rw [map_one, one_mul, one_mul] at hJv
  rw [one_mul, one_mul] at hJu
  exact ⟨hJu, hJv⟩

end MPOTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# The Bell-pair chain: adjacent regions obstruct the unrestricted CID forward implication

The printed CID definition of arXiv:1606.00608 (Definition 3.3, lines 437--448)
quantifies over all disjoint physical regions, and therefore admits *adjacent*
regions: with `n₂ = n₁' + 1` there is no free site between the two observables,
while every allowed shift `Δ ≥ 1` leaves at least one free site on each
complementary arc.  The forward implication "if `𝔼² = 𝔼`, then one will have
CID" (line 498) substitutes `𝔼ⁿ = 𝔼` into the two-observable trace formula
(lines 490--496).  Idempotence justifies that substitution only for `n ≥ 1`:
between adjacent observables one complementary transfer power is `𝔼⁰ = 1`,
which idempotence does not identify with `𝔼`.

This file formalizes the canonical concrete counterexample, the **Bell-pair
chain**: the canonical normal-tensor renormalization fixed point of Lemma
`lem:charact-NT-pure-RFP` (line 1300) with trivial gauge `X = 1`, trivial
isometry `U = 1`, and maximally mixed spectrum `Λ = (1/2, 1/2)`,

`A^{(α,β)}_{γ,δ} = δ_{γ,α} δ_{δ,β} √(1/2)`,   `(α, β) ∈ Fin 2 × Fin 2`.

Its generated states are the chains of `eq:III_MPSRFP`--`eq:III_varphi`
(lines 564--578): each node `n` carries two spins `aₙ, bₙ`, and the maximally
entangled pair `|φ⟩ = (|00⟩ + |11⟩)/√2` is shared between `bₙ` and `aₙ₊₁`.

## Main results

* `bellPairChainTensor_transferMap`: the transfer map is
  `𝔼(X) = tr(X) · diag(Λ)`, hence idempotent.
* `bellPairChainTensor_isNormalTensor`: the tensor is a single normal tensor
  (no copy weights).
* `bellPairChainTensor_adjacent_twoPointExpectation`: for `Z` on `b₁` and `Z`
  on `a₂` (adjacent regions, zero gap) the two-region expectation is `1`.
* `bellPairChainTensor_shifted_twoPointExpectation`: after an allowed shift
  (one free site on each complementary arc) the expectation is `⟨Z⟩² = 0`.
* `bellPairChainTensor_not_isPhysicalCID` and
  `bellPairChain_isTransferIdempotent_and_not_isPhysicalCID`: the unrestricted
  forward implication is refuted by a normal renormalization fixed point.

See `docs/paper-gaps/cpsv16_pure_zcl_adjacent_gap_cid_scope.tex`.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-! ### The tensor and its transfer map -/

/-- The letter coefficient `√(Λ_α) = √(1/2)` of the Bell-pair chain tensor. -/
private noncomputable def bellCoeff : ℂ := Real.sqrt (1 / 2)

private lemma bellCoeff_mul_star : bellCoeff * star bellCoeff = 1 / 2 := by
  have hstar : star (Real.sqrt (1 / 2 : ℝ) : ℂ) = (Real.sqrt (1 / 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [bellCoeff, hstar, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

private lemma bellCoeff_ne_zero : bellCoeff ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'

/-- The Bell-pair chain tensor: the canonical normal-tensor renormalization
fixed point of arXiv:1606.00608, `lem:charact-NT-pure-RFP` (line 1300), with
trivial gauge `X = 1`, trivial isometry `U = 1`, and `Λ = (1/2, 1/2)`.  The
physical index is the pair `(α, β) ∈ Fin 2 × Fin 2` of the two spins at one
node, and `A^{(α,β)} = √(1/2) · |α⟩⟨β|`.

The matrix-product coefficient of a basis word forces the second spin of node
`n` to coincide with the first spin of node `n + 1`, so the generated state is
the Bell-pair chain of `eq:III_MPSRFP`--`eq:III_varphi` (lines 564--578): the
pair `|φ⟩ = (|00⟩ + |11⟩)/√2` is shared between `bₙ` and `aₙ₊₁`. -/
noncomputable def bellPairChainTensor : MPSTensor (2 * 2) 2 := fun i =>
  bellCoeff • Matrix.single (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 1

/-- The conjugated letter product collapses to a diagonal matrix unit. -/
private lemma bellPairChainTensor_letter_conj (a b : Fin 2)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    bellPairChainTensor (finProdFinEquiv (a, b)) * X *
        (bellPairChainTensor (finProdFinEquiv (a, b)))ᴴ =
      Matrix.single a a ((1 / 2 : ℂ) * X b b) := by
  have hletter : (bellPairChainTensor (finProdFinEquiv (a, b)))ᴴ =
      star bellCoeff • Matrix.single b a 1 := by
    rw [bellPairChainTensor, Equiv.symm_apply_apply, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_single, star_one]
  rw [hletter, bellPairChainTensor, Equiv.symm_apply_apply, smul_mul_assoc,
    Matrix.mul_smul, smul_mul_assoc, smul_smul, Matrix.single_mul_mul_single,
    one_mul, mul_one, Matrix.smul_single, smul_eq_mul,
    show star bellCoeff * bellCoeff = 1 / 2 by
      rw [mul_comm]; exact bellCoeff_mul_star]

/-- Summing the diagonal matrix units over the first spin gives the identity
contribution of the transfer map. -/
private lemma single_sum_one (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, Matrix.single a a ((1 / 2 : ℂ) * X b b)) =
      (1 / 2 * Matrix.trace X) • 1 := by
  have hinner : ∀ a : Fin 2,
      (∑ b : Fin 2, Matrix.single a a ((1 / 2 : ℂ) * X b b)) =
        Matrix.single a a ((1 / 2 : ℂ) * Matrix.trace X) := by
    intro a
    have h1 : (∑ b : Fin 2, Matrix.single a a ((1 / 2 : ℂ) * X b b)) =
        Matrix.single a a (∑ b : Fin 2, (1 / 2 : ℂ) * X b b) := by
      change (∑ b : Fin 2, Matrix.singleAddMonoidHom a a ((1 / 2 : ℂ) * X b b)) =
        Matrix.singleAddMonoidHom a a (∑ b : Fin 2, (1 / 2 : ℂ) * X b b)
      rw [map_sum]
    rw [h1, Fin.sum_univ_two, Matrix.trace_fin_two]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [show (∑ a : Fin 2, Matrix.single a a ((1 / 2 : ℂ) * Matrix.trace X)) =
      ((1 / 2 : ℂ) * Matrix.trace X) • ∑ a : Fin 2, Matrix.single a a 1 from by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  rw [Matrix.sum_single_one]

/-- Summing the diagonal matrix units against a sign on the first spin gives a
diagonal matrix. -/
private lemma single_sum_fst (s : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, Matrix.single a a (s a * ((1 / 2 : ℂ) * X b b))) =
      (1 / 2 * Matrix.trace X) • Matrix.diagonal s := by
  have hinner : ∀ a : Fin 2,
      (∑ b : Fin 2, Matrix.single a a (s a * ((1 / 2 : ℂ) * X b b))) =
        Matrix.single a a (s a * ((1 / 2 : ℂ) * Matrix.trace X)) := by
    intro a
    have h1 : (∑ b : Fin 2, Matrix.single a a (s a * ((1 / 2 : ℂ) * X b b))) =
        Matrix.single a a (∑ b : Fin 2, s a * ((1 / 2 : ℂ) * X b b)) := by
      change (∑ b : Fin 2, Matrix.singleAddMonoidHom a a (s a * ((1 / 2 : ℂ) * X b b))) =
        Matrix.singleAddMonoidHom a a (∑ b : Fin 2, s a * ((1 / 2 : ℂ) * X b b))
      rw [map_sum]
    rw [h1, Fin.sum_univ_two, Matrix.trace_fin_two]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [show (∑ a : Fin 2, Matrix.single a a (s a * ((1 / 2 : ℂ) * Matrix.trace X))) =
      ∑ a : Fin 2, Matrix.single a a (((1 / 2 : ℂ) * Matrix.trace X) * s a) from
    Finset.sum_congr rfl fun a _ => by rw [mul_comm (s a)]]
  rw [show (∑ a : Fin 2, Matrix.single a a (((1 / 2 : ℂ) * Matrix.trace X) * s a)) =
      ((1 / 2 : ℂ) * Matrix.trace X) • ∑ a : Fin 2, Matrix.single a a (s a) from by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_single, smul_eq_mul]]
  rw [Matrix.sum_single_eq_diagonal]

/-- Summing the diagonal matrix units against a sign on the second spin gives a
scalar multiple of the identity. -/
private lemma single_sum_snd (s : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ a : Fin 2, ∑ b : Fin 2, Matrix.single a a (s b * ((1 / 2 : ℂ) * X b b))) =
      (1 / 2 * (∑ b : Fin 2, s b * X b b)) • 1 := by
  have hinner : ∀ a : Fin 2,
      (∑ b : Fin 2, Matrix.single a a (s b * ((1 / 2 : ℂ) * X b b))) =
        Matrix.single a a ((1 / 2 : ℂ) * (∑ b : Fin 2, s b * X b b)) := by
    intro a
    have h1 : (∑ b : Fin 2, Matrix.single a a (s b * ((1 / 2 : ℂ) * X b b))) =
        Matrix.single a a (∑ b : Fin 2, s b * ((1 / 2 : ℂ) * X b b)) := by
      change (∑ b : Fin 2, Matrix.singleAddMonoidHom a a (s b * ((1 / 2 : ℂ) * X b b))) =
        Matrix.singleAddMonoidHom a a (∑ b : Fin 2, s b * ((1 / 2 : ℂ) * X b b))
      rw [map_sum]
    rw [h1]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [show (∑ a : Fin 2, Matrix.single a a ((1 / 2 : ℂ) * (∑ b : Fin 2, s b * X b b))) =
      ((1 / 2 : ℂ) * (∑ b : Fin 2, s b * X b b)) • ∑ a : Fin 2, Matrix.single a a 1 from by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  rw [Matrix.sum_single_one]

/-- The transfer map of the Bell-pair chain tensor is
`𝔼(X) = tr(X) · diag(Λ)`, evaluated entrywise. -/
theorem bellPairChainTensor_transferMap_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    transferMap bellPairChainTensor X = (1 / 2 * Matrix.trace X) • 1 := by
  rw [transferMap_apply, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp_rw [bellPairChainTensor_letter_conj]
  exact single_sum_one X

/-- The transfer map of the Bell-pair chain tensor in rank-one form:
`𝔼(X) = tr(X) · diag(Λ)`. -/
theorem bellPairChainTensor_transferMap :
    transferMap bellPairChainTensor =
      (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • 1) := by
  ext X
  rw [bellPairChainTensor_transferMap_apply, LinearMap.smulRight_apply,
    Matrix.traceLinearMap_apply, smul_smul, mul_comm (Matrix.trace X) (1 / 2 : ℂ)]

private lemma bell_trace_half_one :
    Matrix.traceLinearMap (Fin 2) ℂ ℂ ((1 / 2 : ℂ) • 1) = 1 := by
  rw [Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- Composition of rank-one linear maps of the form `X ↦ f(X) • x`. -/
private lemma smulRight_comp_smulRight {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f g : M →ₗ[ℂ] ℂ) (x y : M) :
    (f.smulRight x) ∘ₗ (g.smulRight y) = (f y) • (g.smulRight x) := by
  ext z
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul,
    LinearMap.smul_apply, smul_smul]
  rw [mul_comm (g z) (f y)]

/-- The transfer map `𝔼(X) = tr(X) · diag(Λ)` is idempotent since
`tr(diag Λ) = 1`: the Bell-pair chain tensor is a renormalization fixed point
(arXiv:1606.00608, Definition `defRFP`, lines 398--424). -/
theorem bellPairChainTensor_isTransferIdempotent :
    IsTransferIdempotent bellPairChainTensor := by
  unfold IsTransferIdempotent
  rw [bellPairChainTensor_transferMap, smulRight_comp_smulRight, bell_trace_half_one,
    one_smul]

/-! ### The two single-spin `Z` observables -/

/-- The Pauli `Z` eigenvalue sign on a basis spin state. -/
private def zSign : Fin 2 → ℂ := fun a => if a = 0 then 1 else -1

/-- The Pauli `Z` matrix on one spin. -/
private def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private lemma pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma trace_pauliZ : Matrix.trace pauliZ = 0 := by
  simp [pauliZ, Matrix.trace_fin_two_of]

private lemma diagonal_zSign : Matrix.diagonal zSign = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, zSign]

/-- `Z` on the first spin `aₙ` of a node: the single-node block observable
`Z ⊗ I` on the two-spin physical space, presented as a matrix on one-letter
words.  Under `finProdFinEquiv` the physical index `Fin (2 * 2)` is the spin
pair `(α, β) ∈ Fin 2 × Fin 2`, and this observable is diagonal with sign
`z α`. -/
noncomputable def bellPairChainZFirst :
    Matrix (Fin 1 → Fin (2 * 2)) (Fin 1 → Fin (2 * 2)) ℂ :=
  (Matrix.diagonal fun i => zSign (finProdFinEquiv.symm i).1).submatrix
    (fun f => f 0) (fun f => f 0)

/-- `Z` on the second spin `bₙ` of a node: the single-node block observable
`I ⊗ Z`, presented as a matrix on one-letter words. -/
noncomputable def bellPairChainZSecond :
    Matrix (Fin 1 → Fin (2 * 2)) (Fin 1 → Fin (2 * 2)) ℂ :=
  (Matrix.diagonal fun i => zSign (finProdFinEquiv.symm i).2).submatrix
    (fun f => f 0) (fun f => f 0)

private lemma bell_trace_pauliZ_mul (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (pauliZ * X) = ∑ b : Fin 2, zSign b * X b b := by
  rw [Matrix.trace_fin_two]
  simp [pauliZ, zSign, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### One-letter observable transfer maps -/

private lemma evalWord_ofFn_const_one (A : MPSTensor d D) (i : Fin d) :
    evalWord A (List.ofFn fun _ : Fin 1 => i) = A i := by
  rw [List.ofFn_const, List.replicate_one, evalWord_cons, evalWord_nil, mul_one]

private lemma sum_fin_one_arrow (F : (Fin 1 → Fin d) → Matrix (Fin D) (Fin D) ℂ) :
    (∑ σ : Fin 1 → Fin d, F σ) = ∑ i : Fin d, F fun _ => i := by
  refine Finset.sum_bij (fun σ _ => σ 0) (fun σ _ => Finset.mem_univ _) ?_ ?_
    (fun σ _ => ?_)
  · intro σ _ τ _ h
    funext x
    rw [Fin.eq_zero x]
    exact h
  · intro i _
    exact ⟨fun _ => i, Finset.mem_univ _, rfl⟩
  · congr 1
    funext x
    rw [Fin.eq_zero x]

/-- The one-letter observable transfer map as a plain double sum over physical
indices. -/
private lemma physicalObservableTransfer_one_apply (A : MPSTensor d D)
    (O : Matrix (Fin 1 → Fin d) (Fin 1 → Fin d) ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A 1 O X =
      ∑ i : Fin d, ∑ j : Fin d, O (fun _ => j) (fun _ => i) • (A i * X * (A j)ᴴ) := by
  classical
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [sum_fin_one_arrow]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_fin_one_arrow]
  apply Finset.sum_congr rfl
  intro j _
  rw [evalWord_ofFn_const_one, evalWord_ofFn_const_one, Matrix.mul_assoc]

/-- The observable transfer map of `Z` on the first spin:
`𝔼_{Z ⊗ I}(X) = tr(X) · (Z · diag Λ)`. -/
private lemma bell_observableTransfer_fst_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physicalObservableTransfer bellPairChainTensor 1 bellPairChainZFirst X =
      (1 / 2 * Matrix.trace X) • pauliZ := by
  rw [physicalObservableTransfer_one_apply]
  have hO : ∀ i j : Fin (2 * 2),
      bellPairChainZFirst (fun _ => j) (fun _ => i) •
          (bellPairChainTensor i * X * (bellPairChainTensor j)ᴴ) =
        if j = i then
          zSign (finProdFinEquiv.symm j).1 •
            (bellPairChainTensor i * X * (bellPairChainTensor j)ᴴ)
        else 0 := by
    intro i j
    by_cases h : j = i <;>
      simp [h, bellPairChainZFirst, Matrix.submatrix_apply]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hO i j]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq' Finset.univ i _]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp_rw [Equiv.symm_apply_apply, bellPairChainTensor_letter_conj, Matrix.smul_single,
    smul_eq_mul]
  rw [← diagonal_zSign]
  exact single_sum_fst zSign X

/-- The observable transfer map of `Z` on the first spin, as a rank-one linear
map. -/
private lemma bell_observableTransfer_fst :
    physicalObservableTransfer bellPairChainTensor 1 bellPairChainZFirst =
      (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • pauliZ) := by
  ext X
  rw [bell_observableTransfer_fst_apply, LinearMap.smulRight_apply,
    Matrix.traceLinearMap_apply, smul_smul, mul_comm (Matrix.trace X) (1 / 2 : ℂ)]

/-- The observable transfer map of `Z` on the second spin:
`𝔼_{I ⊗ Z}(X) = tr(Z X) · diag Λ`. -/
private lemma bell_observableTransfer_snd_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physicalObservableTransfer bellPairChainTensor 1 bellPairChainZSecond X =
      (1 / 2 * (∑ b : Fin 2, zSign b * X b b)) • 1 := by
  rw [physicalObservableTransfer_one_apply]
  have hO : ∀ i j : Fin (2 * 2),
      bellPairChainZSecond (fun _ => j) (fun _ => i) •
          (bellPairChainTensor i * X * (bellPairChainTensor j)ᴴ) =
        if j = i then
          zSign (finProdFinEquiv.symm j).2 •
            (bellPairChainTensor i * X * (bellPairChainTensor j)ᴴ)
        else 0 := by
    intro i j
    by_cases h : j = i <;>
      simp [h, bellPairChainZSecond, Matrix.submatrix_apply]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hO i j]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_ite_eq' Finset.univ i _]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp_rw [Equiv.symm_apply_apply, bellPairChainTensor_letter_conj, Matrix.smul_single,
    smul_eq_mul]
  exact single_sum_snd zSign X

/-- The observable transfer map of `Z` on the second spin, as a rank-one linear
map. -/
private lemma bell_observableTransfer_snd :
    physicalObservableTransfer bellPairChainTensor 1 bellPairChainZSecond =
      ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).comp (LinearMap.mulLeft ℂ pauliZ)).smulRight
        ((1 / 2 : ℂ) • 1) := by
  ext X
  rw [bell_observableTransfer_snd_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, Matrix.traceLinearMap_apply,
    bell_trace_pauliZ_mul, smul_smul,
    mul_comm (∑ b : Fin 2, zSign b * X b b) (1 / 2 : ℂ)]

/-! ### The adjacent and shifted two-region expectations -/

/-- The adjacent two-region expectation: with `Z` on `b₁` and `Z` on `a₂`
(zero free sites between the observables, two on the complementary arc), the
expectation is the Bell-pair value `⟨φ|Z ⊗ Z|φ⟩ = 1`.  This is the
`𝔼⁰ = 1` case of the two-observable formula at arXiv:1606.00608, lines
490--496, which idempotence does not govern. -/
theorem bellPairChainTensor_adjacent_twoPointExpectation :
    physicalTwoPointExpectation bellPairChainTensor 1 1
      bellPairChainZFirst bellPairChainZSecond 2 0 = 1 := by
  have hcomp : physicalObservableTransfer bellPairChainTensor 1 bellPairChainZSecond ∘ₗ
        ((transferMap bellPairChainTensor) ^ 0) ∘ₗ
        physicalObservableTransfer bellPairChainTensor 1 bellPairChainZFirst ∘ₗ
          ((transferMap bellPairChainTensor) ^ 2) =
      (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight ((1 / 2 : ℂ) • 1) := by
    ext X
    simp only [LinearMap.comp_apply, pow_zero, Module.End.one_apply, pow_two,
      Module.End.mul_apply]
    rw [bell_observableTransfer_snd, bell_observableTransfer_fst,
      bellPairChainTensor_transferMap]
    simp only [one_div, LinearMap.coe_smulRight, Matrix.traceLinearMap_apply, map_smul,
      Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, smul_inv_smul₀, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, Matrix.smul_apply, smul_eq_mul, mul_eq_mul_left_iff,
      inv_eq_zero, or_false]
    left
    rw [pauliZ_sq, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
    exact mul_inv_cancel_left₀ (show (2 : ℂ) ≠ 0 by norm_num) _
  unfold physicalTwoPointExpectation
  rw [hcomp, LinearMap.trace_smulRight, bell_trace_half_one]

/-- The shifted two-region expectation: after an allowed shift `Δ ≥ 1` (here
one free site on each complementary arc), the expectation factorizes as
`⟨Z⟩ · ⟨Z⟩ = 0`. -/
theorem bellPairChainTensor_shifted_twoPointExpectation :
    physicalTwoPointExpectation bellPairChainTensor 1 1
      bellPairChainZFirst bellPairChainZSecond 1 1 = 0 := by
  have hcomp : physicalObservableTransfer bellPairChainTensor 1 bellPairChainZSecond ∘ₗ
        ((transferMap bellPairChainTensor) ^ 1) ∘ₗ
        physicalObservableTransfer bellPairChainTensor 1 bellPairChainZFirst ∘ₗ
          ((transferMap bellPairChainTensor) ^ 1) = 0 := by
    ext X
    simp only [LinearMap.comp_apply, pow_one]
    rw [bell_observableTransfer_snd, bell_observableTransfer_fst,
      bellPairChainTensor_transferMap]
    simp only [one_div, LinearMap.coe_smulRight, Matrix.traceLinearMap_apply, map_smul,
      Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, smul_inv_smul₀, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, mul_one, Matrix.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, Matrix.zero_apply, mul_eq_zero, inv_eq_zero, false_or,
      or_self_left]
    exact Or.inr (Or.inl trace_pauliZ)
  unfold physicalTwoPointExpectation
  rw [hcomp, map_zero]

/-- The Bell-pair chain does not have correlations independent of the distance
in the unrestricted sense of arXiv:1606.00608, Definition 3.3 (lines 437--448):
the adjacent configuration has expectation `1`, while the shifted configuration
has expectation `0`. -/
theorem bellPairChainTensor_not_isPhysicalCID :
    ¬ IsPhysicalCID bellPairChainTensor := by
  intro hCID
  have h := hCID 1 1 bellPairChainZFirst bellPairChainZSecond 2 0 1 1
    le_rfl le_rfl (by norm_num)
  rw [bellPairChainTensor_adjacent_twoPointExpectation,
    bellPairChainTensor_shifted_twoPointExpectation] at h
  exact one_ne_zero h

/-! ### Normality -/

/-- The four letters of the Bell-pair chain tensor are the (rescaled) matrix
units, so they span the full matrix algebra. -/
theorem bellPairChainTensor_isInjective : IsInjective bellPairChainTensor := by
  rw [IsInjective, eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  have hletter : Matrix.single a b (M a b) =
      (M a b * bellCoeff⁻¹) • bellPairChainTensor (finProdFinEquiv (a, b)) := by
    rw [bellPairChainTensor, Equiv.symm_apply_apply, smul_smul, Matrix.smul_single,
      smul_eq_mul, mul_one, mul_assoc, inv_mul_cancel₀ bellCoeff_ne_zero, mul_one]
  rw [hletter]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨finProdFinEquiv (a, b), rfl⟩)

/-- The Bell-pair chain tensor is algebraically normal: it is already
`1`-block injective. -/
theorem bellPairChainTensor_isNormal : IsNormal bellPairChainTensor :=
  bellPairChainTensor_isInjective.isNormal

/-- The Bell-pair chain tensor is left-canonical:
`∑ (α,β), (A^{(α,β)})† A^{(α,β)} = 1`. -/
theorem bellPairChainTensor_isLeftCanonical : IsLeftCanonical bellPairChainTensor := by
  unfold IsLeftCanonical
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  have hletter : ∀ a b : Fin 2,
      (bellPairChainTensor (finProdFinEquiv (a, b)))ᴴ *
        bellPairChainTensor (finProdFinEquiv (a, b)) =
      Matrix.single b b (1 / 2 : ℂ) := by
    intro a b
    rw [bellPairChainTensor, Equiv.symm_apply_apply, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_single, star_one, smul_mul_assoc, Matrix.mul_smul, smul_smul,
      Matrix.single_mul_single_same, one_mul, Matrix.smul_single, smul_eq_mul, mul_one,
      show star bellCoeff * bellCoeff = 1 / 2 by
        rw [mul_comm]; exact bellCoeff_mul_star]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hletter a b]
  rw [Finset.sum_congr rfl fun a _ =>
    show (∑ b : Fin 2, Matrix.single b b (1 / 2 : ℂ)) = (1 / 2 : ℂ) • 1 from by
      rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = ∑ b : Fin 2, Matrix.single b b 1 from
        Matrix.sum_single_one.symm]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, two_nsmul, ← add_smul,
    show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, one_smul]

/-- The Bell-pair chain tensor is a single normal tensor in the sense of the
canonical-form normalization of arXiv:1606.00608 (lines 224--235): no copy
weights are involved. -/
theorem bellPairChainTensor_isNormalTensor : IsNormalTensor bellPairChainTensor :=
  isNormalTensor_of_isNormal_leftCanonical _ bellPairChainTensor_isNormal
    bellPairChainTensor_isLeftCanonical

/-! ### The obstruction -/

/-- The canonical normal renormalization fixed point of
`lem:charact-NT-pure-RFP` with `Λ = (1/2, 1/2)` is transfer idempotent but
does not have physical CID: the unrestricted forward implication of
arXiv:1606.00608 (line 498) is false for adjacent regions, because the
`𝔼⁰ = 1` block between adjacent observables is not governed by idempotence. -/
theorem bellPairChain_isTransferIdempotent_and_not_isPhysicalCID :
    IsTransferIdempotent bellPairChainTensor ∧ ¬ IsPhysicalCID bellPairChainTensor :=
  ⟨bellPairChainTensor_isTransferIdempotent, bellPairChainTensor_not_isPhysicalCID⟩

/-- The full counterexample: a single normal tensor, with no copy
weights, that is a renormalization fixed point but fails the source CID
condition for adjacent regions. -/
theorem bellPairChain_isNormalTensor_isTransferIdempotent_and_not_isPhysicalCID :
    IsNormalTensor bellPairChainTensor ∧ IsTransferIdempotent bellPairChainTensor ∧
      ¬ IsPhysicalCID bellPairChainTensor :=
  ⟨bellPairChainTensor_isNormalTensor, bellPairChainTensor_isTransferIdempotent,
    bellPairChainTensor_not_isPhysicalCID⟩

end MPSTensor

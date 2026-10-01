/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalSupportTransport
import TNLean.MPS.ParentHamiltonian.Martingale.OverlapReduction
import TNLean.Algebra.FinSumPermutation
import TNLean.Algebra.FinVecEta

/-!
# The frame operator of the local ground space

For an MPS tensor `A` the local ground space `G_n(A)` on `n` sites is the range of the
boundary parametrization `Γ_n(X)(σ) = tr[A^σ X]`. Its adjoint for the Hilbert--Schmidt inner
product is `Γ_n† ψ = ∑_τ ψ(τ) (A^τ)†`, and the operator `Γ_n Γ_n†` on the `n`-site space has the
matrix `tr[A^σ (A^τ)†]`. This operator is Hermitian for every tensor. When
`Γ_n Γ_n† Γ_n = c Γ_n` for a positive `c`, it is `c` times the orthogonal projector onto
`G_n(A)`, so the parent interaction is `1 - c⁻¹ Γ_n Γ_n†`.

On three sites, if the two lifts of `Γ_2 Γ_2†` to the overlapping pairs of sites multiply in
either order to the same multiple of `Γ_3 Γ_3†`, then the translated two-site parent terms
commute on every ring of at least three sites.

These are the steps of the proofs of Lemma 6.11 and Theorem 6.12 of Schuch, Cirac, and
Pérez-García (arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 2098–2156) that do not use
`G`-isometry; the `G`-isometric input is supplied in `TNLean.PEPS.GIsometricParentHamiltonian`.

## Main definitions

* `MPSTensor.groundSpaceMapAdjoint A n`: the map `ψ ↦ ∑_τ ψ(τ) (A^τ)†`.
* `MPSTensor.groundSpaceFrame A n`: the operator `Γ_n Γ_n†`.

## Main results

* `MPSTensor.groundSpaceFrame_isHermitian`: the matrix of `Γ_n Γ_n†` is Hermitian.
* `MPSTensor.parentInteraction_eq_one_sub_smul_groundSpaceFrame`: if `Γ_n Γ_n† Γ_n = c Γ_n`
  with `c > 0`, then the parent interaction is `1 - c⁻¹ Γ_n Γ_n†`.
* `MPSTensor.isNNCPH_of_pairLift_groundSpaceFrame`: commutation of the two-site parent terms
  on every ring of at least three sites from the three-site identities.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

section Sums

variable {M : Type*} [AddCommMonoid M]

/-- A sum over two-site configurations is a double sum over the two letters. -/
theorem sum_cfg_two (f : Cfg d 2 → M) : ∑ σ, f σ = ∑ a, ∑ b, f ![a, b] := by
  rw [← (finTwoArrowEquiv (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A sum over three-site configurations is a triple sum over the three letters. -/
theorem sum_cfg_three (f : Cfg d 3 → M) : ∑ σ, f σ = ∑ a, ∑ b, ∑ c, f ![a, b, c] := by
  rw [← (Fin.consEquiv fun _ : Fin 3 => Fin d).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cfg_two]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1

end Sums

/-- The adjoint of the boundary parametrization `Γ_n` for the Hilbert--Schmidt inner product:
`ψ ↦ ∑_τ ψ(τ) (A^τ)†`. -/
noncomputable def groundSpaceMapAdjoint (A : MPSTensor d D) (n : ℕ) :
    NSiteSpace d n →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ τ : Cfg d n, (LinearMap.proj τ).smulRight (Kraus.evalWord A (List.ofFn τ))ᴴ

theorem groundSpaceMapAdjoint_apply (A : MPSTensor d D) (n : ℕ) (ψ : NSiteSpace d n) :
    groundSpaceMapAdjoint A n ψ = ∑ τ, ψ τ • (Kraus.evalWord A (List.ofFn τ))ᴴ := by
  simp [groundSpaceMapAdjoint]

/-- The operator `Γ_n Γ_n†` on the `n`-site space, with matrix `tr[A^σ (A^τ)†]`. For `n = 2` it
is the operator of arXiv:1001.3807, equation `eq:iso:ham-proj-from-A`
(`Papers/1001.3807/paper_v3.tex` lines 2103–2107, figure `figs4/ham-proj-from-A.pdf`), in
which the tensors `A†` are the adjoint matrices. -/
noncomputable def groundSpaceFrame (A : MPSTensor d D) (n : ℕ) :
    Module.End ℂ (NSiteSpace d n) :=
  groundSpaceMap A n ∘ₗ groundSpaceMapAdjoint A n

theorem groundSpaceFrame_apply (A : MPSTensor d D) (n : ℕ) (ψ : NSiteSpace d n)
    (σ : Cfg d n) :
    groundSpaceFrame A n ψ σ = ∑ τ, ψ τ *
      Matrix.trace (Kraus.evalWord A (List.ofFn σ) * (Kraus.evalWord A (List.ofFn τ))ᴴ) := by
  simp [groundSpaceFrame, groundSpaceMapAdjoint_apply, Matrix.mul_sum, Matrix.trace_sum]

/-- The matrix of `Γ_n Γ_n†` is Hermitian. -/
theorem groundSpaceFrame_isHermitian (A : MPSTensor d D) (n : ℕ) :
    (LinearMap.toMatrix' (groundSpaceFrame A n)).IsHermitian := by
  classical
  ext σ τ
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, groundSpaceFrame_apply,
    Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- If `Γ_n Γ_n† Γ_n = c Γ_n` with `c > 0`, then `c⁻¹ Γ_n Γ_n†` is idempotent. -/
theorem isIdempotentElem_smul_groundSpaceFrame {A : MPSTensor d D} {n : ℕ} {c : ℂ}
    (hc : c ≠ 0)
    (h : groundSpaceMap A n ∘ₗ groundSpaceMapAdjoint A n ∘ₗ groundSpaceMap A n =
      c • groundSpaceMap A n) :
    IsIdempotentElem (c⁻¹ • groundSpaceFrame A n) := by
  have h' : groundSpaceFrame A n * groundSpaceFrame A n = c • groundSpaceFrame A n := by
    simp only [groundSpaceFrame, Module.End.mul_eq_comp]
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (groundSpaceMapAdjoint A n), ←
      LinearMap.comp_assoc, h, LinearMap.smul_comp]
  rw [IsIdempotentElem, smul_mul_smul_comm, h', smul_smul, mul_assoc, inv_mul_cancel₀ hc,
    mul_one]

/-- If `Γ_n Γ_n† Γ_n = c Γ_n` with `c ≠ 0`, then the range of `Γ_n Γ_n†` is the local ground
space `G_n(A)`. -/
theorem range_groundSpaceFrame {A : MPSTensor d D} {n : ℕ} {c : ℂ} (hc : c ≠ 0)
    (h : groundSpaceMap A n ∘ₗ groundSpaceMapAdjoint A n ∘ₗ groundSpaceMap A n =
      c • groundSpaceMap A n) :
    LinearMap.range (groundSpaceFrame A n) = groundSpace A n := by
  refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
  rintro _ ⟨X, rfl⟩
  refine ⟨c⁻¹ • groundSpaceMap A n X, ?_⟩
  have hX := LinearMap.congr_fun h X
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hX
  rw [map_smul, groundSpaceFrame, LinearMap.comp_apply, hX, smul_smul, inv_mul_cancel₀ hc,
    one_smul]

/-- If `Γ_n Γ_n† Γ_n = c Γ_n` with `c > 0`, then `c⁻¹ Γ_n Γ_n†` is the orthogonal projector onto
the local ground space, so the parent interaction `1 - Π_{G_n(A)}` is `1 - c⁻¹ Γ_n Γ_n†`. -/
theorem parentInteraction_eq_one_sub_smul_groundSpaceFrame {A : MPSTensor d D} {n : ℕ}
    {c : ℝ} (hc : 0 < c)
    (h : groundSpaceMap A n ∘ₗ groundSpaceMapAdjoint A n ∘ₗ groundSpaceMap A n =
      (c : ℂ) • groundSpaceMap A n) :
    parentInteraction A n = 1 - ((c : ℂ)⁻¹ • groundSpaceFrame A n) := by
  classical
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  set P := (c : ℂ)⁻¹ • groundSpaceFrame A n with hP
  let e := WithLp.linearEquiv 2 ℂ (NSiteSpace d n)
  -- The Euclidean form of `P` is a symmetric projection with range `G_n(A)`.
  let PES : EuclideanSpace ℂ (Cfg d n) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d n) :=
    e.symm.toLinearMap ∘ₗ P ∘ₗ e.toLinearMap
  have hPES : PES = Matrix.toEuclideanLin (LinearMap.toMatrix' P) := by
    refine LinearMap.ext fun v => ?_
    simp [PES, e, Matrix.toLpLin_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hsym : PES.IsSymmetric := by
    rw [hPES, Matrix.isSymmetric_toEuclideanLin_iff, hP, map_smul]
    refine (groundSpaceFrame_isHermitian A n).smul ?_
    rw [IsSelfAdjoint, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hidem : IsIdempotentElem PES := by
    have hP2 := isIdempotentElem_smul_groundSpaceFrame hc' h
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hP2 (e v)
    simp only [Module.End.mul_apply] at this
    have := congrArg e.symm this
    simpa [PES, hP] using this
  have hrange : LinearMap.range PES = groundSpaceES A n := by
    rw [groundSpaceES, ← range_groundSpaceFrame hc' h]
    simp only [PES, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    rw [hP, LinearMap.range_smul _ _ (inv_ne_zero hc')]
  obtain ⟨_, hPES'⟩ :=
    (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).1 ⟨hidem, hsym⟩
  refine LinearMap.ext fun ψ => ?_
  have hψ := LinearMap.congr_fun hPES' (e.symm ψ)
  simp only [hrange] at hψ
  have hψ' : P ψ = e ((groundSpaceES A n).starProjection (e.symm ψ)) := by
    have := congrArg e hψ
    simpa [PES] using this
  rw [LinearMap.sub_apply, Module.End.one_apply, hψ']
  simp only [parentInteraction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.starProjection_orthogonal']
  simp [e]

/-! ### Three sites -/

theorem leftPairLift_smul (k : ℂ) (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    leftPairLift (k • Q) = k • leftPairLift Q := by
  ext ψ σ
  simp

theorem rightPairLift_smul (k : ℂ) (Q : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    rightPairLift (k • Q) = k • rightPairLift Q := by
  ext ψ σ
  simp

@[simp] theorem replaceAXCfg_vecCons (s₀ s₁ s₂ a b : Fin d) :
    replaceAXCfg ![s₀, s₁, s₂] ![a, b] = ![a, b, s₂] := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem replaceXBCfg_vecCons (s₀ s₁ s₂ a b : Fin d) :
    replaceXBCfg ![s₀, s₁, s₂] ![a, b] = ![s₀, a, b] := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem axPairCfg_vecCons (s₀ s₁ s₂ : Fin d) :
    axPairCfg ![s₀, s₁, s₂] = ![s₀, s₁] := by
  funext k
  fin_cases k <;> rfl

@[simp] theorem xbPairCfg_vecCons (s₀ s₁ s₂ : Fin d) :
    xbPairCfg ![s₀, s₁, s₂] = ![s₁, s₂] := by
  funext k
  fin_cases k <;> rfl

/-- The word of a two-letter configuration. -/
theorem evalWord_ofFn_two (A : MPSTensor d D) (a b : Fin d) :
    Kraus.evalWord A (List.ofFn ![a, b]) = A a * A b := by
  simp [List.ofFn_succ]

/-- The word of a three-letter configuration. -/
theorem evalWord_ofFn_three (A : MPSTensor d D) (a b c : Fin d) :
    Kraus.evalWord A (List.ofFn ![a, b, c]) = A a * A b * A c := by
  simp [List.ofFn_succ, Matrix.mul_assoc]

/-- The product of the lift of `Γ_2 Γ_2†` to the first pair of sites with its lift to the second
pair has the matrix `∑_b tr[A^{s₀} A^{s₁} (A^{w₀} A^b)†] tr[A^b A^{s₂} (A^{w₁} A^{w₂})†]`; if this
sum is `c tr[A^{s₀s₁s₂} (A^{w₀w₁w₂})†]`, the product is `c Γ_3 Γ_3†`. -/
theorem leftPairLift_mul_rightPairLift_groundSpaceFrame (A : MPSTensor d D) (c : ℂ)
    (h : ∀ s₀ s₁ s₂ w₀ w₁ w₂ : Fin d,
      ∑ b, Matrix.trace (A s₀ * A s₁ * (A w₀ * A b)ᴴ) *
          Matrix.trace (A b * A s₂ * (A w₁ * A w₂)ᴴ) =
        c * Matrix.trace (A s₀ * A s₁ * A s₂ * (A w₀ * A w₁ * A w₂)ᴴ)) :
    leftPairLift (groundSpaceFrame A 2) * rightPairLift (groundSpaceFrame A 2) =
      c • groundSpaceFrame A 3 := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  rw [Matrix.eq_vecCons_fin_three σ]
  simp only [Module.End.mul_apply, leftPairLift_apply, rightPairLift_apply, groundSpaceFrame_apply,
    LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_cfg_two, sum_cfg_three, Finset.mul_sum]
  simp only [replaceAXCfg_vecCons, replaceXBCfg_vecCons, axPairCfg_vecCons, xbPairCfg_vecCons,
    evalWord_ofFn_two, evalWord_ofFn_three, sum_cfg_two (d := d), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm, ← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The product of the lift of `Γ_2 Γ_2†` to the second pair of sites with its lift to the first
pair has the matrix `∑_b tr[A^{s₀} A^b (A^{w₀} A^{w₁})†] tr[A^{s₁} A^{s₂} (A^b A^{w₂})†]`; if this
sum is `c tr[A^{s₀s₁s₂} (A^{w₀w₁w₂})†]`, the product is `c Γ_3 Γ_3†`. -/
theorem rightPairLift_mul_leftPairLift_groundSpaceFrame (A : MPSTensor d D) (c : ℂ)
    (h : ∀ s₀ s₁ s₂ w₀ w₁ w₂ : Fin d,
      ∑ b, Matrix.trace (A s₀ * A b * (A w₀ * A w₁)ᴴ) *
          Matrix.trace (A s₁ * A s₂ * (A b * A w₂)ᴴ) =
        c * Matrix.trace (A s₀ * A s₁ * A s₂ * (A w₀ * A w₁ * A w₂)ᴴ)) :
    rightPairLift (groundSpaceFrame A 2) * leftPairLift (groundSpaceFrame A 2) =
      c • groundSpaceFrame A 3 := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  rw [Matrix.eq_vecCons_fin_three σ]
  simp only [Module.End.mul_apply, leftPairLift_apply, rightPairLift_apply, groundSpaceFrame_apply,
    LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_cfg_two, sum_cfg_three, Finset.mul_sum]
  simp only [replaceAXCfg_vecCons, replaceXBCfg_vecCons, axPairCfg_vecCons, xbPairCfg_vecCons,
    evalWord_ofFn_two, evalWord_ofFn_three, sum_cfg_two (d := d), Finset.sum_mul, Finset.mul_sum]
  rw [Fintype.sum_last_two_first_four]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm, ← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- If `Γ_2 Γ_2† Γ_2 = c Γ_2` with `c > 0` and the lifts of `Γ_2 Γ_2†` to the two overlapping
pairs of three sites commute, then the translated two-site parent terms commute on every ring of
at least three sites. -/
theorem isNNCPH_of_pairLift_groundSpaceFrame {A : MPSTensor d D} {c : ℝ} (hc : 0 < c)
    (h : groundSpaceMap A 2 ∘ₗ groundSpaceMapAdjoint A 2 ∘ₗ groundSpaceMap A 2 =
      (c : ℂ) • groundSpaceMap A 2)
    (hcomm : leftPairLift (groundSpaceFrame A 2) * rightPairLift (groundSpaceFrame A 2) =
      rightPairLift (groundSpaceFrame A 2) * leftPairLift (groundSpaceFrame A 2))
    {N : ℕ} (hN : 3 ≤ N) : IsNNCPH A N := by
  have hC : Commute (leftPairLift (groundSpaceFrame A 2))
      (rightPairLift (groundSpaceFrame A 2)) := hcomm
  have h₃ : localTerm A 2 3 (0 : Fin 3) * localTerm A 2 3 (1 : Fin 3) =
      localTerm A 2 3 (1 : Fin 3) * localTerm A 2 3 (0 : Fin 3) := by
    rw [localTerm_two_three_zero_eq_leftPairLift_parentInteraction,
      localTerm_two_three_one_eq_rightPairLift_parentInteraction,
      parentInteraction_eq_one_sub_smul_groundSpaceFrame hc h, leftPairLift_one_sub,
      rightPairLift_one_sub, leftPairLift_smul, rightPairLift_smul]
    set k := ((c : ℂ)⁻¹)
    exact ((Commute.one_left _).sub_left (((Commute.one_right _)).sub_right
      ((hC.smul_left k).smul_right k))).eq
  exact isNNCPH_of_adjacent_twoSite_commute (by omega) fun i =>
    localTerm_adjacent_twoSite_commute_of_threeSite_zero_one_commute h₃ hN i

end MPSTensor

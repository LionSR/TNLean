/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.LocalObservableInsertion
import TNLean.MPS.ParentHamiltonian.GroundSpaceCompressionNorm
import TNLean.MPS.ParentHamiltonian.GramInverseConvergence

/-!
# Scalar compression of an interior observable to a primitive MPS ground space

For a single normalized primitive tensor with a positive-definite invariant
matrix, a fixed observable supported far from both ends acts asymptotically
as its scalar expectation on the entire finite-chain boundary space.
Centering this expectation makes the ground-space component of the observable
vanish uniformly over all unit boundary vectors.

This is the tensor-specific subtraction step in Nachtergaele,
arXiv:cond-mat/9410110, lines 933--947 and 2649--2675. No uniqueness of the
finite open-chain ground space is assumed.

**Scope restriction (one primitive sector):** The results concern one primitive
sector. Mixed-sector decay and identification with an infinite-volume state
remain separate, as documented in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open Filter
open scoped Matrix Topology ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- The compression of a fixed interior observable approaches its scalar
expectation, in operator norm on the complete finite-chain ground space.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundSpace_compression_tendsto_scalar
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n =>
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection.comp
          (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
            (bulkObservable X (ℓ n) (r n))).comp
              (groundSpaceES A ((ℓ n + k) + r n)).starProjection) -
        observableInsertionExpectation A ρ X •
          (groundSpaceES A ((ℓ n + k) + r n)).starProjection‖) f (nhds 0) := by
  let N (n : ι) := (ℓ n + k) + r n
  let η := observableInsertionExpectation A ρ X
  let Iinf := Ring.inverse (Matrix.gramReshuffle (fixedPointProj ρ (ne_of_gt hρ.trace_pos)))
  let C (n : ι) := (groundSpaceMapES A (N n)).adjoint.comp
    (((Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
      (bulkObservable X (ℓ n) (r n))).comp (groundSpaceMapES A (N n))) -
        η • groundSpaceGram A (N n)
  have hN : Tendsto N f atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hℓ.eventually (eventually_ge_atTop b)] with n hn
    dsimp [N]
    omega
  have hC : Tendsto C f (nhds 0) := by
    have hlim := (hP.groundSpaceMapES_bulkObservable_compression_tendsto X hℓ hr).sub
      ((tendsto_const_nhds (x := η)).smul
        (hP.groundSpaceGram_tendsto_gramReshuffle_fixedPointProj.comp hN))
    simpa only [C, N, η, Function.comp_def, sub_self] using hlim
  have hInv : ∀ᶠ n in f, ∃ hInj : Function.Injective (groundSpaceMapES A (N n)),
      ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A (N n)) hInj‖ ≤ 2 * ‖Iinf‖ := by
    filter_upwards [hN.eventually
      (hP.eventually_groundSpaceMapES_injective_and_inverseGram_bound hρ
        (a := 1 / 2) (by norm_num) (by norm_num))] with n hn
    obtain ⟨hInj, _, hdispl⟩ := hn
    norm_num at hdispl
    have hdispl' : ‖ContinuousLinearMap.inverseGram (groundSpaceMapES A (N n)) hInj -
        Iinf‖ ≤ ‖Iinf‖ := by
      simpa only [Iinf] using hdispl
    have htriangle := norm_le_norm_sub_add
      (ContinuousLinearMap.inverseGram (groundSpaceMapES A (N n)) hInj) Iinf
    refine ⟨hInj, ?_⟩
    linarith
  have hnorm : Tendsto (fun n => ‖C n‖) f (nhds 0) := by
    simpa only [norm_zero] using hC.norm
  have h := ContinuousLinearMap.tendsto_starProjection_comp_sub_smul_zero_of_inverseGram_bound
    (E := fun _ : ι => EuclideanSpace ℂ (Fin D × Fin D))
    (F := fun n => EuclideanSpace ℂ (Cfg d (N n)))
    (fun n => groundSpaceMapES A (N n))
    (fun n => (Matrix.toEuclideanCLM (n := Cfg d (N n)) (𝕜 := ℂ))
      (bulkObservable X (ℓ n) (r n))) (fun _ => η) hInv
    (by simpa only [C, groundSpaceGram] using hnorm)
  simpa only [range_groundSpaceMapES] using h

/-- Centering the primitive-sector expectation makes the compressed observable
vanish in operator norm. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 933--947 and 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundSpace_compression_tendsto_zero
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop) :
    Tendsto (fun n =>
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection.comp
          (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
            (bulkObservable X (ℓ n) (r n))).comp
              (groundSpaceES A ((ℓ n + k) + r n)).starProjection)‖) f (nhds 0) := by
  simpa only [hcenter, zero_smul, sub_zero] using
    hP.bulkObservable_groundSpace_compression_tendsto_scalar hρ X hℓ hr


/-- Scalar compression controls the action on every bounded ground vector,
uniformly in the boundary condition. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundSpace_projection_eventually_near_expectation
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in f, ∀ ψ ∈ groundSpaceES A ((ℓ n + k) + r n), ‖ψ‖ ≤ 1 →
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection
          (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
            (bulkObservable X (ℓ n) (r n))) ψ) -
        observableInsertionExpectation A ρ X • ψ‖ < ε := by
  have hlim := hP.bulkObservable_groundSpace_compression_tendsto_scalar hρ X hℓ hr
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with n hn
  intro ψ hψ hnorm
  have hfix := Submodule.starProjection_eq_self_iff.mpr hψ
  calc
    _ = ‖((groundSpaceES A ((ℓ n + k) + r n)).starProjection.comp
        (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
          (bulkObservable X (ℓ n) (r n))).comp
            (groundSpaceES A ((ℓ n + k) + r n)).starProjection) -
        observableInsertionExpectation A ρ X •
          (groundSpaceES A ((ℓ n + k) + r n)).starProjection) ψ‖ := by
      simp only [sub_apply, ContinuousLinearMap.comp_apply,
        smul_apply, hfix]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ ψ
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hnorm
    _ < ε := hn

/-- For centered observables, the full ground-space projection norm squared
vanishes along every eventually bounded family of boundary vectors. This is
precisely the finite-volume subtraction term in Nachtergaele,
arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundSpace_projection_norm_sq_tendsto_zero
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    (hcenter : observableInsertionExpectation A ρ X = 0)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop)
    (ψ : (n : ι) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (hψ : ∀ᶠ n in f, ψ n ∈ groundSpaceES A ((ℓ n + k) + r n))
    (hbound : ∀ᶠ n in f, ‖ψ n‖ ≤ 1) :
    Tendsto (fun n =>
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection
        (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
          (bulkObservable X (ℓ n) (r n))) (ψ n))‖ ^ 2) f (nhds 0) := by
  have hnorm : Tendsto (fun n =>
      ‖(groundSpaceES A ((ℓ n + k) + r n)).starProjection
        (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
          (bulkObservable X (ℓ n) (r n))) (ψ n))‖) f (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hP.bulkObservable_groundSpace_compression_tendsto_zero hρ X hcenter hℓ hr)
    filter_upwards [hψ, hbound] with n hn hb
    have hfix := Submodule.starProjection_eq_self_iff.mpr hn
    calc
      _ = ‖((groundSpaceES A ((ℓ n + k) + r n)).starProjection.comp
          (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
            (bulkObservable X (ℓ n) (r n))).comp
              (groundSpaceES A ((ℓ n + k) + r n)).starProjection)) (ψ n)‖ := by
        simp only [ContinuousLinearMap.comp_apply, hfix]
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ (ψ n)
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hb
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hnorm.pow 2

/-- Every unit open-chain ground vector has the same limiting interior
expectation. The boundary condition may vary with the chain length.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 2649--2675. -/
theorem IsPrimitiveMPS.bulkObservable_groundState_expectation_tendsto
    [NeZero D] {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : IsPrimitiveMPS A ρ) (hρ : ρ.PosDef) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ)
    {ι : Type*} {f : Filter ι} {ℓ r : ι → ℕ}
    (hℓ : Tendsto ℓ f atTop) (hr : Tendsto r f atTop)
    (ψ : (n : ι) → EuclideanSpace ℂ (Cfg d ((ℓ n + k) + r n)))
    (hψ : ∀ᶠ n in f, ψ n ∈ groundSpaceES A ((ℓ n + k) + r n))
    (hunit : ∀ᶠ n in f, ‖ψ n‖ = 1) :
    Tendsto (fun n => inner ℂ (ψ n)
      (((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
        (bulkObservable X (ℓ n) (r n))) (ψ n))) f
      (nhds (observableInsertionExpectation A ρ X)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (hP.bulkObservable_groundSpace_compression_tendsto_scalar hρ X hℓ hr)
  filter_upwards [hψ, hunit] with n hg hu
  exact ContinuousLinearMap.norm_inner_sub_scalar_le_compression
    (groundSpaceES A ((ℓ n + k) + r n))
    ((Matrix.toEuclideanCLM (n := Cfg d ((ℓ n + k) + r n)) (𝕜 := ℂ))
      (bulkObservable X (ℓ n) (r n))) (observableInsertionExpectation A ρ X)
        (ψ n) hg hu

end MPSTensor

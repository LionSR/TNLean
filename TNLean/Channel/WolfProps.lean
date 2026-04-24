/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Wolf Chapter 2 representation corollaries (Props 2.2–2.4)

This file formalises the remaining Chapter 2 representation corollaries from
Wolf's *Quantum Channels & Operations: Guided Tour*:

* **Prop 2.2** — every sesquilinear sandwich `A * X * Bᴴ` decomposes as a
  signed complex combination of four CP-sandwich terms (polarization
  identity). Any linear map expressible as `∑ᵢ Aᵢ * X * Bᵢᴴ` is therefore
  a complex linear combination of CP maps.
* **Prop 2.3** — no information without disturbance: any linear map fixing
  every rank-one self-outer-product is the identity. In particular, a
  quantum channel that leaves every pure state invariant is the identity.
* **Prop 2.4** (sufficient direction) — equivalence of ensembles: two
  pure-state ensembles related by an isometric mixing matrix yield the same
  density operator, matching the Hughston–Jozsa–Wootters characterization.
  The converse (necessity) requires Schmidt/purification machinery not yet
  available in the repository.

## Main results

* `WolfProps.polarization_sandwich` — Prop 2.2 as a polarization identity.
* `WolfProps.cp_decomposition_of_sandwich_sum` — Prop 2.2 corollary: every
  `∑ᵢ Aᵢ * X * Bᵢᴴ` is a signed ℂ-linear combination of CP maps.
* `WolfProps.vecMulVec_star_eq_polarization` — polarization of rank-one
  outer products into rank-one self-outer-products.
* `WolfProps.linearMap_eq_id_of_fixes_rankOne` — Prop 2.3 (linear-algebra
  form): a linear map fixing every `vecMulVec v (star v)` is the identity.
* `WolfProps.channel_eq_id_of_fixes_pureStates` — Prop 2.3 (channel form):
  a quantum channel fixing every pure-state projector is the identity.
* `WolfProps.pureEnsembleDensity_eq_of_isometric_mixing` — Prop 2.4
  (sufficient direction): isometric mixing preserves the density operator.

## Design notes

The Prop 2.2 polarization is proved at the entry level by reducing to a
scalar polarization identity in `ℂ` (which is closed by
`linear_combination`). The Prop 2.3 reduction chain exploits the fact that
rank-one outer products span `M_D(ℂ)` over `ℂ`, obtained by specializing
the rank-one polarization to standard-basis vectors. The Prop 2.4 proof
is a direct algebraic computation matching the abstract Kraus-freedom
sufficient-direction lemma `kraus_same_map_of_isometry_combination`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Props 2.2–2.4][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {D : ℕ}

namespace WolfProps

/-! ### Scalar polarization -/

/-- Scalar polarization identity used entry-wise to prove the sandwich
polarization (Prop 2.2). For any four complex numbers `α β γ δ`,

  `4 · α · (star δ) = (α+β)(star γ + star δ) - (α-β)(star γ - star δ)
     + I · (α + I·β)(star γ - I·star δ) - I · (α - I·β)(star γ + I·star δ).`

This is the sesquilinear polarization of `(α, γ) ↦ α · star δ` along
`(β, δ)`, after substituting `I * I = -1`. -/
private theorem scalar_polarization (α β γ δ : ℂ) :
    (4 : ℂ) * (α * star δ) =
      (α + β) * (star γ + star δ) - (α - β) * (star γ - star δ) +
        Complex.I * ((α + Complex.I * β) *
          (star γ + (-Complex.I) * star δ)) -
        Complex.I * ((α - Complex.I * β) *
          (star γ + Complex.I * star δ)) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (2 * α * star δ - 2 * β * star γ) * hI

/-- Scalar lemma: `star Complex.I = -Complex.I`. -/
private theorem star_I_eq_neg_I : (star Complex.I : ℂ) = -Complex.I := by
  change (starRingEnd ℂ) Complex.I = -Complex.I
  exact Complex.conj_I

/-! ### Sandwich polarization (Prop 2.2 core identity) -/

/-- **Prop 2.2 (Wolf), polarization form**. The sesquilinear sandwich
`A * X * Bᴴ` decomposes as a signed ℂ-linear combination of four
CP-sandwich terms `K X Kᴴ`:

  `4 • (A X Bᴴ) = (A+B) X (A+B)ᴴ - (A-B) X (A-B)ᴴ
      + I • (A + I•B) X (A + I•B)ᴴ - I • (A - I•B) X (A - I•B)ᴴ`.

Each summand `K X Kᴴ` on the right is manifestly completely positive (it has
`K` as a one-element Kraus family), so this identity expresses every
sesquilinear sandwich as a complex linear combination of CP-sandwich maps. -/
theorem polarization_sandwich (A B X : Matrix (Fin D) (Fin D) ℂ) :
    (4 : ℂ) • (A * X * Bᴴ) =
      ((A + B) * X * (A + B)ᴴ) - ((A - B) * X * (A - B)ᴴ) +
        Complex.I • ((A + Complex.I • B) * X * (A + Complex.I • B)ᴴ) -
        Complex.I • ((A - Complex.I • B) * X * (A - Complex.I • B)ᴴ) := by
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.conjTranspose_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have pw : ∀ x i : Fin D,
      4 * (A a i * X i x * star (B b x)) =
        ((A a i + B a i) * X i x * star (A b x + B b x)) -
          ((A a i - B a i) * X i x * star (A b x - B b x)) +
          Complex.I * ((A a i + Complex.I * B a i) * X i x *
              star (A b x + Complex.I * B b x)) -
          Complex.I * ((A a i - Complex.I * B a i) * X i x *
              star (A b x - Complex.I * B b x)) := by
    intro x i
    have h := scalar_polarization (A a i) (B a i) (A b x) (B b x)
    simp only [star_add, star_sub, StarMul.star_mul, star_I_eq_neg_I]
    linear_combination (X i x) * h
  calc ∑ x : Fin D, ∑ i : Fin D, 4 * (A a i * X i x * star (B b x))
      = ∑ x : Fin D, ∑ i : Fin D,
          (((A a i + B a i) * X i x * star (A b x + B b x)) -
            ((A a i - B a i) * X i x * star (A b x - B b x)) +
            Complex.I * ((A a i + Complex.I * B a i) * X i x *
                star (A b x + Complex.I * B b x)) -
            Complex.I * ((A a i - Complex.I * B a i) * X i x *
                star (A b x - Complex.I * B b x))) :=
        Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => pw _ _
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **Prop 2.2 (Wolf), CP-decomposition form**. Every map expressible as
`T(X) = ∑ᵢ Aᵢ * X * Bᵢᴴ` has the explicit ℂ-linear CP-decomposition

  `4 • T(X) = ∑ᵢ (Aᵢ+Bᵢ) X (Aᵢ+Bᵢ)ᴴ - ∑ᵢ (Aᵢ-Bᵢ) X (Aᵢ-Bᵢ)ᴴ
      + I • ∑ᵢ (Aᵢ + I•Bᵢ) X (Aᵢ + I•Bᵢ)ᴴ
      - I • ∑ᵢ (Aᵢ - I•Bᵢ) X (Aᵢ - I•Bᵢ)ᴴ`,

where each of the four sums is a completely positive map. -/
theorem cp_decomposition_of_sandwich_sum
    {ι : Type*} [Fintype ι] (A B : ι → Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (4 : ℂ) • (∑ i, A i * X * (B i)ᴴ) =
      (∑ i, (A i + B i) * X * (A i + B i)ᴴ)
        - (∑ i, (A i - B i) * X * (A i - B i)ᴴ)
        + Complex.I •
            (∑ i, (A i + Complex.I • B i) * X * (A i + Complex.I • B i)ᴴ)
        - Complex.I •
            (∑ i, (A i - Complex.I • B i) * X * (A i - Complex.I • B i)ᴴ) := by
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => polarization_sandwich (A i) (B i) X

/-! ### Prop 2.3: no information without disturbance -/

/-- **Rank-one polarization identity**: every outer product `u · star v`
is a signed ℂ-linear combination of four rank-one self-outer-products. -/
theorem vecMulVec_star_eq_polarization (u v : Fin D → ℂ) :
    (4 : ℂ) • (Matrix.vecMulVec u (star v)) =
      Matrix.vecMulVec (u + v) (star (u + v))
        - Matrix.vecMulVec (u - v) (star (u - v))
        + Complex.I •
            Matrix.vecMulVec (u + Complex.I • v) (star (u + Complex.I • v))
        - Complex.I •
            Matrix.vecMulVec (u - Complex.I • v) (star (u - Complex.I • v)) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.sub_apply,
    Matrix.add_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.star_apply, smul_eq_mul]
  have h := scalar_polarization (u a) (v a) (u b) (v b)
  simp only [star_add, star_sub, StarMul.star_mul, star_I_eq_neg_I]
  linear_combination h

/-- Linear maps fixing rank-one self-outer-products also fix generic rank-one
outer products (after polarizing via `vecMulVec_star_eq_polarization`). -/
private theorem T_fixes_vecMulVec_star_of_fixes_self
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : ∀ v : Fin D → ℂ, T (Matrix.vecMulVec v (star v)) =
                                    Matrix.vecMulVec v (star v))
    (u v : Fin D → ℂ) :
    T (Matrix.vecMulVec u (star v)) = Matrix.vecMulVec u (star v) := by
  -- Apply T to both sides of `vecMulVec_star_eq_polarization` and
  -- use linearity plus the hypothesis on self-outer-products.
  have hmul : (4 : ℂ) • T (Matrix.vecMulVec u (star v)) =
      (4 : ℂ) • Matrix.vecMulVec u (star v) := by
    have h := congrArg T (vecMulVec_star_eq_polarization u v)
    simp only [map_smul, map_sub, map_add, hT] at h
    rw [h, ← vecMulVec_star_eq_polarization]
  -- Cancel the scalar `4`.
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact smul_right_injective _ h4 hmul

section Prop23

variable [NeZero D]
variable (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- **Prop 2.3 (Wolf), linear-algebra form**: a linear map fixing every
rank-one self-outer-product `vecMulVec v (star v)` is the identity map.

This captures "no information without disturbance" at the algebra level:
the rank-one self-outer-products span `M_D(ℂ)` over `ℂ`, so a linear map
agreeing with the identity on this spanning set equals the identity. -/
theorem linearMap_eq_id_of_fixes_rankOne
    (hT : ∀ v : Fin D → ℂ, T (Matrix.vecMulVec v (star v)) =
                                    Matrix.vecMulVec v (star v)) :
    T = LinearMap.id := by
  -- It suffices to agree on every matrix; use `Matrix.induction_on`.
  refine LinearMap.ext fun M => ?_
  change T M = M
  refine Matrix.induction_on M ?_ ?_
  · intro p q hp hq
    rw [map_add, hp, hq]
  · intro i j c
    -- `Matrix.single i j c = c • vecMulVec (Pi.single i 1) (star (Pi.single j 1))`.
    have hsingle : (Matrix.single i j c : Matrix (Fin D) (Fin D) ℂ) =
        c • Matrix.vecMulVec (Pi.single i (1 : ℂ))
              (star (Pi.single j (1 : ℂ)) : Fin D → ℂ) := by
      have hstar : (star (Pi.single j (1 : ℂ)) : Fin D → ℂ) =
          Pi.single j (1 : ℂ) := by
        ext k; simp [Pi.single_apply, Pi.star_apply]
      rw [hstar]
      rw [← Matrix.single_eq_single_vecMulVec_single (i := i) (j := j)]
      ext a b
      simp [Matrix.single_apply]
    rw [hsingle, map_smul,
        T_fixes_vecMulVec_star_of_fixes_self (D := D) T hT (Pi.single i (1 : ℂ))
          (Pi.single j (1 : ℂ))]

/-- **Prop 2.3 (Wolf), pure-state form**: any linear map (in particular any
quantum channel) leaving every pure-state projector `vecMulVec v (star v)`
invariant is the identity. This is the standard "no information without
disturbance" statement in quantum information theory, phrased directly in
terms of pure-state projectors. -/
theorem channel_eq_id_of_fixes_pureStates
    (hT : ∀ v : Fin D → ℂ, T (Matrix.vecMulVec v (star v)) =
                                    Matrix.vecMulVec v (star v)) :
    T = LinearMap.id :=
  linearMap_eq_id_of_fixes_rankOne T hT

end Prop23

/-! ### Prop 2.4: equivalence of ensembles (sufficient direction) -/

/-- The density operator associated to a pure-state (unnormalized) ensemble
`{ψᵢ}`: the sum of rank-one projectors `∑ᵢ |ψᵢ⟩⟨ψᵢ|`. The weights `pᵢ`
can be absorbed into `ψᵢ` by replacing `ψᵢ` with `√pᵢ · ψᵢ`, so this
definition captures the general weighted pure-state ensemble. -/
noncomputable def pureEnsembleDensity
    {ι : Type*} [Fintype ι] (ψ : ι → (Fin D → ℂ)) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, Matrix.vecMulVec (ψ i) (star (ψ i))

/-- **Prop 2.4 (Wolf), sufficient direction** (Hughston–Jozsa–Wootters).
If two pure-state ensembles `{ψᵢ}_{i ∈ ι₁}` and `{φⱼ}_{j ∈ ι₂}` are related
by an isometric mixing matrix `V : Matrix ι₁ ι₂ ℂ` (that is, `Vᴴ V = 1` and
`ψᵢ = ∑ⱼ Vᵢⱼ • φⱼ`), then they induce the same density operator.

The converse (necessity) — extracting such an isometry from equal density
operators — requires Schmidt-decomposition machinery currently absent from
the repository; see `TNLean/Channel/WolfChapter2Index.lean`. -/
theorem pureEnsembleDensity_eq_of_isometric_mixing
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : ι₁ → (Fin D → ℂ)) (φ : ι₂ → (Fin D → ℂ))
    (V : Matrix ι₁ ι₂ ℂ) (hV : Vᴴ * V = 1)
    (hψ : ∀ i, ψ i = fun a => ∑ j, V i j * φ j a) :
    pureEnsembleDensity ψ = pureEnsembleDensity φ := by
  unfold pureEnsembleDensity
  -- Expand each `vecMulVec (ψ i) (star (ψ i))` using `hψ`, then use the
  -- orthogonality relation `∑ᵢ conj(Vᵢₗ') * Vᵢₗ = δₗₗ'` from `Vᴴ V = 1`.
  ext a b
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, hψ]
  -- LHS entry: ∑ i, (∑ j, V i j * φ j a) * star (∑ j', V i j' * φ j' b)
  -- RHS entry: ∑ j, φ j a * star (φ j b)
  have hV_entry : ∀ l l' : ι₂,
      ∑ i : ι₁, (starRingEnd ℂ) (V i l) * V i l' = if l = l' then 1 else 0 := by
    intro l l'
    have h := congrArg (fun M : Matrix ι₂ ι₂ ℂ => M l l') hV
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    ∑ i : ι₁, (∑ j, V i j * φ j a) * star (∑ j', V i j' * φ j' b)
        = ∑ i : ι₁, ∑ j : ι₂, ∑ j' : ι₂,
            (V i j * φ j a) * star (V i j' * φ j' b) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul, star_sum]
          simp_rw [Finset.mul_sum]
    _ = ∑ j : ι₂, ∑ j' : ι₂,
          (∑ i : ι₁, V i j * star (V i j')) * (φ j a * star (φ j' b)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j' _ => ?_
          simp_rw [Finset.sum_mul, StarMul.star_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ j : ι₂, ∑ j' : ι₂,
          (if j' = j then 1 else 0) * (φ j a * star (φ j' b)) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          congr 1
          have h := hV_entry j' j
          -- `h : ∑ i, conj(V i j') * V i j = if j' = j then 1 else 0`
          -- Rewrite `star (V i j') = conj (V i j')` and commute the product.
          simpa [mul_comm] using h
    _ = ∑ j : ι₂, (φ j a * star (φ j b)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hj; simp [show j' ≠ j from hj]
          · simp

end WolfProps

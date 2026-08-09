/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.Channel.KrausFreedom
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Wolf Chapter 2 representation corollaries (Propositions 2.2–2.4)

This file formalises the remaining Chapter 2 representation corollaries from
Wolf's *Quantum Channels & Operations: Guided Tour*:

* **Proposition 2.2** — every sesquilinear sandwich `A * X * Bᴴ` decomposes as a
  signed complex combination of four single-Kraus terms (polarization
  identity). Any linear map expressible as `∑ᵢ Aᵢ * X * Bᵢᴴ` is therefore
  a complex linear combination of CP maps.
* **Proposition 2.3** — no information without disturbance: any linear map fixing
  every rank-one self-outer-product is the identity. In particular, a
  quantum channel that leaves every pure state invariant is the identity.
* **Proposition 2.4** — equivalence of ensembles (Hughston–Jozsa–Wootters, Wolf Eq. (2.10)): two
  pure-state ensembles are related by an isometric mixing matrix iff they
  induce the same density operator. Both directions are formalised.

## Main results

* `WolfProps.polarization_sandwich` — Proposition 2.2 as a polarization identity.
* `WolfProps.cp_decomposition_of_sandwich_sum` — Proposition 2.2 corollary: every
  `∑ᵢ Aᵢ * X * Bᵢᴴ` is a signed ℂ-linear combination of CP maps.
* `WolfProps.vecMulVec_star_eq_polarization` — polarization of rank-one
  outer products into rank-one self-outer-products.
* `WolfProps.exists_eq_smul_id_of_maps_rankOne_to_span` — a linear map preserving
  every rank-one self-outer-product ray is a scalar multiple of the identity.
* `WolfProps.linearMap_eq_id_of_fixes_rankOne` — Proposition 2.3 (linear-algebra
  form): a linear map fixing every `vecMulVec v (star v)` is the identity.
* `WolfProps.linearMap_eq_of_eq_on_rankOne` — two linear maps that agree on every
  `vecMulVec v (star v)` are equal.
* `WolfProps.channel_eq_id_of_fixes_pureStates` — Proposition 2.3 (channel form):
  a quantum channel fixing every pure-state projector is the identity.
* `WolfProps.pureEnsembleDensity_eq_of_isometric_mixing` — Proposition 2.4
  (sufficient direction): isometric mixing preserves the density operator.
* `WolfProps.exists_isometric_mixing_of_pureEnsembleDensity_eq` — Proposition 2.4
  (necessary direction, HJW converse): equal densities force an isometric
  mixing matrix between the two ensembles.
* `WolfProps.pureEnsembleDensity_eq_iff_exists_isometric_mixing` — Proposition 2.4
  stated as an iff.

## Design notes

The Proposition 2.2 polarization is proved at the entry level by reducing to a
scalar polarization identity in `ℂ` (which is closed by
`linear_combination`). The Proposition 2.3 reduction chain exploits the fact that
rank-one outer products span `M_D(ℂ)` over `ℂ`, obtained by specializing
the rank-one polarization to standard-basis vectors. The Proposition 2.4
sufficient direction is a direct algebraic computation matching the
abstract Kraus-freedom sufficient-direction lemma
`kraus_same_map_of_isometry_combination`; the HJW converse reduces to
`kraus_rectangular_freedom'` by embedding each state vector as the `0`-th
column of a `D × D` matrix (with zeros elsewhere). The density equality
`ρ_ψ = ρ_φ` then forces the embedded Kraus families to define the same
completely positive map `X ↦ X_{0 0} · ρ`, and reading column `0` of the resulting
rectangular isometry recovers the vector relation `ψᵢ = ∑ⱼ Vᵢⱼ · φⱼ`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Propositions 2.2–2.4][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {D : ℕ}

namespace WolfProps

/-! ### Scalar polarization -/

/-- Scalar polarization identity used entry-wise to prove the sandwich
polarization (Proposition 2.2). For any four complex numbers `α β γ δ`,

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

/-! ### Sandwich polarization (Proposition 2.2 core identity) -/

/-- **Proposition 2.2 (Wolf), polarization form**. The sesquilinear sandwich
`A * X * Bᴴ` decomposes as a signed ℂ-linear combination of four
single-Kraus terms `K X Kᴴ`:

  `4 • (A X Bᴴ) = (A+B) X (A+B)ᴴ - (A-B) X (A-B)ᴴ
      + I • (A + I•B) X (A + I•B)ᴴ - I • (A - I•B) X (A - I•B)ᴴ`.

Each summand `K X Kᴴ` on the right is manifestly completely positive (it has
`K` as a one-element Kraus family), so this identity expresses every
sesquilinear sandwich as a complex linear combination of single-Kraus maps. -/
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
    simp only [star_add, star_sub, StarMul.star_mul,
      (show (star Complex.I : ℂ) = -Complex.I from Complex.conj_I)]
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

/-- **Proposition 2.2 (Wolf), CP-decomposition form**. Every map expressible as
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

/-! ### Proposition 2.3: no information without disturbance -/

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
  simp only [star_add, star_sub, StarMul.star_mul,
    (show (star Complex.I : ℂ) = -Complex.I from Complex.conj_I)]
  linear_combination h

/-- A complex-linear endomorphism of matrices which preserves every ray spanned
by a rank-one self-outer-product is a scalar multiple of the identity.

If $P_v=vv^*$ and $T(P_v)=c_vP_v$, then the parallelogram identity
$P_{e_i+e_j}+P_{e_i-e_j}=2P_{e_i}+2P_{e_j}$ forces
$c_{e_i}=c_{e_j}$ for all $i\ne j$.  The analogous identity for
$e_i\pm\mathrm{i}e_j$ controls the imaginary off-diagonal entries.  Rank-one
polarization then extends the common scalar coefficient to all matrix units. -/
theorem exists_eq_smul_id_of_maps_rankOne_to_span
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : ∀ v : Fin D → ℂ, ∃ c : ℂ,
      T (Matrix.vecMulVec v (star v)) = c • Matrix.vecMulVec v (star v)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  classical
  by_cases hD : D = 0
  · subst D
    exact ⟨0, Subsingleton.elim _ _⟩
  choose c hc using hT
  let e : Fin D → Fin D → ℂ := fun i ↦ Pi.single i 1
  let P : (Fin D → ℂ) → Matrix (Fin D) (Fin D) ℂ :=
    fun v ↦ Matrix.vecMulVec v (star v)
  have hreal (i j : Fin D) (hij : i ≠ j) :
      c (e i + e j) = c (e i) ∧ c (e i - e j) = c (e i) ∧
        c (e j) = c (e i) := by
    have hpar : P (e i + e j) + P (e i - e j) =
        (2 : ℂ) • P (e i) + (2 : ℂ) • P (e j) := by
      ext a b
      simp [P, Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_sub]
      ring
    have hmap := congrArg T hpar
    simp only [map_add, map_smul, P, hc] at hmap
    have hii := congrFun (congrFun hmap i) i
    have hjj := congrFun (congrFun hmap j) j
    have hij' := congrFun (congrFun hmap i) j
    simp only [star_add, Pi.star_single, star_one, star_sub, Matrix.add_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.single_eq_same,
      ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne, add_zero, mul_one,
      smul_eq_mul, Pi.sub_apply, sub_zero, mul_zero, Pi.single_eq_of_ne', zero_add,
      zero_sub, mul_neg, neg_neg, e] at hii hjj hij'
    dsimp [e] at hii hjj hij' ⊢
    constructor
    · linear_combination (1 / (2 : ℂ)) * hii + (1 / (2 : ℂ)) * hij'
    constructor
    · linear_combination (1 / (2 : ℂ)) * hii - (1 / (2 : ℂ)) * hij'
    · linear_combination (1 / (2 : ℂ)) * hii - (1 / (2 : ℂ)) * hjj
  have himag (i j : Fin D) (hij : i ≠ j) :
      c (e i + Complex.I • e j) = c (e i) ∧
        c (e i - Complex.I • e j) = c (e i) := by
    have hpar : P (e i + Complex.I • e j) + P (e i - Complex.I • e j) =
        (2 : ℂ) • P (e i) + (2 : ℂ) • P (e j) := by
      ext a b
      simp [P, Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_sub]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hmap := congrArg T hpar
    simp only [map_add, map_smul, P, hc] at hmap
    have hii := congrFun (congrFun hmap i) i
    have hij' := congrFun (congrFun hmap i) j
    simp only [star_add, Pi.star_single, star_one, star_smul, RCLike.star_def,
      Complex.conj_I, neg_smul, star_sub, sub_neg_eq_add, Matrix.add_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.single_eq_same,
      Pi.smul_apply, ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul,
      mul_zero, add_zero, Pi.neg_apply, neg_zero, mul_one, Pi.sub_apply, sub_zero,
      Pi.single_eq_of_ne', zero_add, mul_neg, one_mul, e] at hii hij'
    dsimp [e] at hii hij' ⊢
    have heq : c (e i + Complex.I • e j) =
        c (e i - Complex.I • e j) := by
      dsimp [e]
      have hI := Complex.I_mul_I
      linear_combination Complex.I * hij' -
        (c (Pi.single i 1 - Complex.I • Pi.single j 1) -
          c (Pi.single i 1 + Complex.I • Pi.single j 1)) * hI
    constructor
    · linear_combination (1 / (2 : ℂ)) * hii + (1 / (2 : ℂ)) * heq
    · linear_combination (1 / (2 : ℂ)) * hii - (1 / (2 : ℂ)) * heq
  let i₀ : Fin D := ⟨0, Nat.pos_of_ne_zero hD⟩
  have hbasis (i : Fin D) : c (e i) = c (e i₀) := by
    by_cases hi : i = i₀
    · subst i
      rfl
    · exact (hreal i i₀ hi).2.2.symm
  have hunit (i j : Fin D) :
      T (Matrix.vecMulVec (e i) (star (e j))) =
        c (e i₀) • Matrix.vecMulVec (e i) (star (e j)) := by
    by_cases hij : i = j
    · subst j
      rw [hc, hbasis]
    · have hpol := congrArg T (vecMulVec_star_eq_polarization (e i) (e j))
      simp only [map_smul, map_sub, map_add, hc] at hpol
      rw [(hreal i j hij).1, (hreal i j hij).2.1,
        (himag i j hij).1, (himag i j hij).2] at hpol
      have hmul : (4 : ℂ) • T (Matrix.vecMulVec (e i) (star (e j))) =
          (4 : ℂ) • (c (e i) • Matrix.vecMulVec (e i) (star (e j))) := by
        rw [hpol]
        ext a b
        simp [Matrix.vecMulVec_apply, Pi.star_apply, star_add, star_sub]
        ring_nf
        rw [Complex.I_sq]
        ring
      have h4 : (4 : ℂ) ≠ 0 := by norm_num
      rw [← hbasis i]
      exact smul_right_injective _ h4 hmul
  refine ⟨c (e i₀), ?_⟩
  refine LinearMap.ext fun M ↦ ?_
  change T M = c (e i₀) • M
  refine Matrix.induction_on' M ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [map_add, hp, hq, smul_add]
  · intro i j a
    have hsingle : (Matrix.single i j a : Matrix (Fin D) (Fin D) ℂ) =
        a • Matrix.vecMulVec (e i) (star (e j)) := by
      have hstar : (star (e j) : Fin D → ℂ) = e j := by
        ext k
        simp [e, Pi.single_apply, Pi.star_apply]
      rw [hstar]
      change Matrix.single i j a =
        a • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)
      rw [← Matrix.single_eq_single_vecMulVec_single (i := i) (j := j)]
      ext p q
      simp [Matrix.single_apply]
    rw [hsingle, map_smul, hunit]
    simp only [smul_smul]
    rw [mul_comm a]

section Prop23

variable (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- **Proposition 2.3 (Wolf), linear-algebra form**: a linear map fixing every
rank-one self-outer-product `vecMulVec v (star v)` is the identity map.

This captures "no information without disturbance" at the algebra level:
the rank-one self-outer-products span `M_D(ℂ)` over `ℂ`, so a linear map
agreeing with the identity on this spanning set equals the identity. -/
theorem linearMap_eq_id_of_fixes_rankOne
    (hT : ∀ v : Fin D → ℂ, T (Matrix.vecMulVec v (star v)) =
                                    Matrix.vecMulVec v (star v)) :
    T = LinearMap.id := by
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_maps_rankOne_to_span (D := D) T fun v ↦
    ⟨1, by simpa using hT v⟩
  by_cases hD : D = 0
  · subst D
    exact Subsingleton.elim _ _
  let i₀ : Fin D := ⟨0, Nat.pos_of_ne_zero hD⟩
  have hfix := hT (Pi.single i₀ (1 : ℂ))
  rw [hc] at hfix
  have hii := congrFun (congrFun hfix i₀) i₀
  have hc_one : c = 1 := by
    simpa [Matrix.vecMulVec_apply, Pi.star_apply, i₀] using hii
  simpa [hc_one] using hc

/-- Two complex-linear matrix maps are equal if they agree on every rank-one
self-outer-product `vecMulVec v (star v)`. -/
theorem linearMap_eq_of_eq_on_rankOne
    (T S : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ v : Fin D → ℂ,
      T (Matrix.vecMulVec v (star v)) = S (Matrix.vecMulVec v (star v))) :
    T = S := by
  have hfix : T - S + LinearMap.id = LinearMap.id :=
    linearMap_eq_id_of_fixes_rankOne (T - S + LinearMap.id) fun v ↦ by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, h v,
        sub_self, zero_add]
  apply LinearMap.ext
  intro X
  have hX := LinearMap.congr_fun hfix X
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    add_eq_right, sub_eq_zero] using hX

/-- **Proposition 2.3 (Wolf), pure-state form**: any linear map (in particular any
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

/-! ### Proposition 2.4: equivalence of ensembles (sufficient direction) -/

/-- The density operator associated to a pure-state (unnormalized) ensemble
`{ψᵢ}`: the sum of rank-one projectors `∑ᵢ |ψᵢ⟩⟨ψᵢ|`. The weights `pᵢ`
can be absorbed into `ψᵢ` by replacing `ψᵢ` with `√pᵢ · ψᵢ`, so this
definition captures the general weighted pure-state ensemble.

The `noncomputable` marker is forced by `star` on `ℂ`, which reduces
through `instCommCStarAlgebraComplex` — itself noncomputable. -/
noncomputable def pureEnsembleDensity
    {ι : Type*} [Fintype ι] (ψ : ι → (Fin D → ℂ)) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, Matrix.vecMulVec (ψ i) (star (ψ i))

/-- **Proposition 2.4 (Wolf), sufficient direction** (Hughston–Jozsa–Wootters).
If two pure-state ensembles `{ψᵢ}_{i ∈ ι₁}` and `{φⱼ}_{j ∈ ι₂}` are related
by an isometric mixing matrix `V : Matrix ι₁ ι₂ ℂ` (that is, `Vᴴ V = 1` and
`ψᵢ = ∑ⱼ Vᵢⱼ • φⱼ`), then they induce the same density operator.

The converse (necessity) is
`exists_isometric_mixing_of_pureEnsembleDensity_eq`, and both directions
are stated as `pureEnsembleDensity_eq_iff_exists_isometric_mixing`. -/
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

/-- **Proposition 2.4 (Wolf), necessary direction** (Hughston–Jozsa–Wootters
converse). If two pure-state ensembles `{ψᵢ}_{i ∈ ι₁}` and
`{φⱼ}_{j ∈ ι₂}` induce the same pure-ensemble density operator and
`card ι₂ ≤ card ι₁`, then there exists a tall isometric mixing matrix
`V : Matrix ι₁ ι₂ ℂ` with `Vᴴ V = 1` satisfying
`ψᵢ = ∑ⱼ Vᵢⱼ • φⱼ`.

The cardinality hypothesis is what makes `V` a tall isometry
(`Vᴴ V = 1`, i.e. orthonormal columns). The symmetric case
`card ι₁ ≤ card ι₂` is obtained by swapping the roles of `ψ` and `φ`.

The proof reduces to rectangular Kraus freedom
`kraus_rectangular_freedom'`. Embed each vector `ψᵢ`, `φⱼ` as the
`0`-th column of a `D × D` matrix (zeros elsewhere). For any square
input `X`, the embedded Kraus sandwiches evaluate entry-wise to
`X_{0 0} • ρ`; the density equality therefore forces the two Kraus
families to define the same CP map. Rectangular Kraus freedom supplies
an isometry `V` relating them, and reading off column `0` of
`Kᵢ = ∑ⱼ Vᵢⱼ • Lⱼ` recovers the vector relation. -/
theorem exists_isometric_mixing_of_pureEnsembleDensity_eq
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : ι₁ → (Fin D → ℂ)) (φ : ι₂ → (Fin D → ℂ))
    (hρ : pureEnsembleDensity ψ = pureEnsembleDensity φ)
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    ∃ V : Matrix ι₁ ι₂ ℂ, Vᴴ * V = 1 ∧
      ∀ i, ψ i = fun a => ∑ j, V i j * φ j a := by
  -- Any inhabitant of `Fin D` yields the canonical column-`0` index. Factored
  -- out once since the same `⟨0, _⟩` witness is needed both when forming the
  -- Kraus-map equality and when reading off column `0` of the resulting
  -- rectangular isometry; bundling the `0 < D` derivation into a single `Fin D`
  -- auxiliary lemma avoids rebuilding `Nat.pos_of_ne_zero` at each call site.
  let c₀_of : Fin D → Fin D :=
    fun a => ⟨0, Nat.pos_of_ne_zero (fun hDeq => (hDeq ▸ a).elim0)⟩
  -- Embed each vector as the `0`-th column of a `D × D` matrix. Pattern-match
  -- on the underlying `Nat` of `Fin D` so no `0 < D` hypothesis is needed to
  -- form the column index, and the match reduces definitionally at `⟨0, _⟩`.
  let K : ι₁ → Matrix (Fin D) (Fin D) ℂ :=
    fun i => Matrix.of
      (fun a c => match c with | ⟨0, _⟩ => ψ i a | ⟨_ + 1, _⟩ => 0)
  let L : ι₂ → Matrix (Fin D) (Fin D) ℂ :=
    fun j => Matrix.of
      (fun a c => match c with | ⟨0, _⟩ => φ j a | ⟨_ + 1, _⟩ => 0)
  have hK_apply : ∀ i a c,
      K i a c = match c with | ⟨0, _⟩ => ψ i a | ⟨_ + 1, _⟩ => 0 :=
    fun _ _ _ => rfl
  have hL_apply : ∀ j a c,
      L j a c = match c with | ⟨0, _⟩ => φ j a | ⟨_ + 1, _⟩ => 0 :=
    fun _ _ _ => rfl
  -- Auxiliary lemma: collapse a single-column Kraus sandwich `(M * X * Mᴴ)` at
  -- entry `(a, b)` for any single vector `v` with column-`0` encoding.
  -- Applied to each summand below for both the `ψ` and `φ` families.
  have sandwich_entry : ∀ (v : Fin D → ℂ) (M : Matrix (Fin D) (Fin D) ℂ)
      (hM : ∀ a c, M a c = match c with | ⟨0, _⟩ => v a | ⟨_ + 1, _⟩ => 0)
      (X : Matrix (Fin D) (Fin D) ℂ) (a b : Fin D) (hD : 0 < D),
      (M * X * Mᴴ) a b = v a * X ⟨0, hD⟩ ⟨0, hD⟩ * star (v b) := by
    intro v M hM X a b hD
    set c₀ : Fin D := ⟨0, hD⟩
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hM]
    have inner_c : ∀ d,
        (∑ c, (match c with | ⟨0, _⟩ => v a | ⟨_ + 1, _⟩ => (0 : ℂ)) * X c d) =
          v a * X c₀ d := by
      intro d
      -- `rw` closes the main equality via its `rfl` finisher: at `c₀ = ⟨0, _⟩`
      -- the `match` reduces definitionally. Only the two side conditions of
      -- `Finset.sum_eq_single` remain.
      rw [Finset.sum_eq_single c₀]
      · intro c _ hcne
        obtain ⟨c, hc⟩ := c
        cases c with
        | zero => exact absurd rfl hcne
        | succ _ => simp
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [inner_c]
    rw [Finset.sum_eq_single c₀]
    · intro d _ hdne
      obtain ⟨d, hd⟩ := d
      cases d with
      | zero => exact absurd rfl hdne
      | succ _ => simp
    · intro h; exact absurd (Finset.mem_univ _) h
  -- The two embedded Kraus families define the same completely positive map.
  have hKraus : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∑ i, K i * X * (K i)ᴴ = ∑ j, L j * X * (L j)ᴴ := by
    intro X
    ext a b
    -- `a : Fin D` produces the column-`0` witness via `c₀_of`.
    let c₀ : Fin D := c₀_of a
    -- Compute each side as `X c₀ c₀ * ρ_v a b`, then use `hρ`.
    have lhs_eq : (∑ i, K i * X * (K i)ᴴ) a b =
        X c₀ c₀ * (pureEnsembleDensity ψ) a b := by
      rw [Matrix.sum_apply]
      have each_i : ∀ i, (K i * X * (K i)ᴴ) a b =
          ψ i a * X c₀ c₀ * star (ψ i b) :=
        fun i => sandwich_entry (ψ i) (K i) (hK_apply i) X a b c₀.isLt
      simp_rw [each_i]
      simp only [pureEnsembleDensity, Matrix.sum_apply, Matrix.vecMulVec_apply,
        Pi.star_apply]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        Fintype.sum_mul_mul_eq_mul_sum_mul (X c₀ c₀)
          (fun i => ψ i a) (fun i => star (ψ i b))
    have rhs_eq : (∑ j, L j * X * (L j)ᴴ) a b =
        X c₀ c₀ * (pureEnsembleDensity φ) a b := by
      rw [Matrix.sum_apply]
      have each_j : ∀ j, (L j * X * (L j)ᴴ) a b =
          φ j a * X c₀ c₀ * star (φ j b) :=
        fun j => sandwich_entry (φ j) (L j) (hL_apply j) X a b c₀.isLt
      simp_rw [each_j]
      simp only [pureEnsembleDensity, Matrix.sum_apply, Matrix.vecMulVec_apply,
        Pi.star_apply]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        Fintype.sum_mul_mul_eq_mul_sum_mul (X c₀ c₀)
          (fun j => φ j a) (fun j => star (φ j b))
    rw [lhs_eq, rhs_eq, hρ]
  -- Apply rectangular Kraus freedom to extract the isometry `V`.
  obtain ⟨V, hV_iso, hV_decomp⟩ := kraus_rectangular_freedom' K L hKraus hCard
  refine ⟨V, hV_iso, ?_⟩
  intro i
  funext a
  let c₀ : Fin D := c₀_of a
  -- At `c₀ = ⟨0, _⟩` both match branches reduce definitionally, so
  -- `K i a c₀ = ψ i a` and `L j a c₀ = φ j a` hold by `rfl`.
  have hKic₀ : K i a c₀ = ψ i a := rfl
  have hLjc₀ : ∀ j, L j a c₀ = φ j a := fun _ => rfl
  -- Read off the `(a, c₀)` entry of `K i = ∑ j, V i j • L j`.
  have h_entry := congr_fun (congr_fun (hV_decomp i) a) c₀
  rw [hKic₀] at h_entry
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hLjc₀] at h_entry
  exact h_entry

/-- **Proposition 2.4 (Wolf), Hughston–Jozsa–Wootters equivalence**. Two
pure-state ensembles `{ψᵢ}_{i ∈ ι₁}` and `{φⱼ}_{j ∈ ι₂}` with
`card ι₂ ≤ card ι₁` induce the same pure-ensemble density operator iff
they are related by a tall isometric mixing matrix
`V : Matrix ι₁ ι₂ ℂ` with `Vᴴ V = 1` and `ψᵢ = ∑ⱼ Vᵢⱼ • φⱼ`. -/
theorem pureEnsembleDensity_eq_iff_exists_isometric_mixing
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ψ : ι₁ → (Fin D → ℂ)) (φ : ι₂ → (Fin D → ℂ))
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    pureEnsembleDensity ψ = pureEnsembleDensity φ ↔
      ∃ V : Matrix ι₁ ι₂ ℂ, Vᴴ * V = 1 ∧
        ∀ i, ψ i = fun a => ∑ j, V i j * φ j a :=
  ⟨fun hρ =>
    exists_isometric_mixing_of_pureEnsembleDensity_eq ψ φ hρ hCard,
   fun ⟨V, hV, hψ⟩ =>
    pureEnsembleDensity_eq_of_isometric_mixing ψ φ V hV hψ⟩

end WolfProps

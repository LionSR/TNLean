/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FrustrationFree.Model
import TNLean.PEPS.AreaLaw.FrustrationFree.PlanarSweep
import TNLean.PEPS.AreaLaw.FrustrationFree.SweepContraction

/-!
# The sweep of a frustration-free Hamiltonian

For an instance of the frustration-free model `eq:model` and a colouring `c` of the overlap
graph of the supports with `χ = d_R + 1` colours, the sweep is

`D = ∏_X (1 - Π_X)`,

the product of the complements of the range projections `Π_X` of the terms, the supports taken
colour by colour. This module proves the two properties of `D` the amplification step uses.

* **Contraction** (`eq:sweep`): `D Ω = Ω` and `‖D^t v‖ ≤ θ^t ‖v‖` for `v ⟂ Ω`, with
  `θ = (1 + (Δ/J)/(d_R + 1)²)^{-1/2}`.
* **Exact light cone** (`eq:cone`): if every block of an operator `B` on the sites and a
  register acts on `U`, then `(D^t ⊗ 1) B (Ω ⊗ ξ) = (L ⊗ 1) B (Ω ⊗ ξ)` for an operator `L`
  acting on `N_{R χ t}(U)` with `L Ω = Ω` and `Lᴴ Ω = Ω`.

The note writes the factors as `(1 - h_X/J)^{1/2}`; the range projections are used here, see
`docs/paper-gaps/ffarealaw_sweep_range_projections.tex`.

## Main definitions

* `IsFrustrationFreeGapped.sweepOp`: the sweep `D`.
* `sweepContraction`: the factor `θ`.

## Main statements

* `IsFrustrationFreeGapped.sweepOp_mulVec_self`, `norm_sweepOp_pow_apply_le`: contraction.
* `IsFrustrationFreeGapped.exists_sweepOp_pow_lightCone`: the light cone.

## References

* Reading note *Entanglement across a cut in two-dimensional frustration-free ground states*,
  November 18, 2026, `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`,
  "Contraction in one sweep" and "Exact localization on the perturbed vector".
-/

open Matrix ManyBody TNLean.Lattice
open scoped InnerProductSpace ComplexOrder MatrixOrder Kronecker

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem complementProd_congr {h h' : ℕ → E →L[𝕜] E} {n : ℕ} (hh : ∀ i < n, h i = h' i) :
    complementProd h n = complementProd h' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [complementProd_succ, complementProd_succ, hh n n.lt_succ_self,
      ih fun i hi ↦ hh i (hi.trans n.lt_succ_self)]

end ContinuousLinearMap

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*}

local notation "clmX" => toEuclideanCLM (n := Config X) (𝕜 := ℂ)

/-- The projections of a word, as a sequence indexed by positions, zero past its end. -/
noncomputable def wordProjections (P : κ → Matrix (Config X) (Config X) ℂ) (l : List κ) :
    ℕ → EuclideanSpace ℂ (Config X) →L[ℂ] EuclideanSpace ℂ (Config X) :=
  fun i ↦ (l[i]?).elim 0 fun k ↦ clmX (P k)

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- A sum over the positions of a word without repetition that contains every letter is the sum
over the letters. -/
theorem sum_range_getElem?_elim {M : Type*} [Fintype κ] [AddCommMonoid M]
    (g : κ → M) {w : List κ} (hw : w.Nodup) (hall : ∀ x, x ∈ w) :
    ∑ i ∈ Finset.range w.length, (w[i]?).elim 0 g = ∑ x, g x := by
  classical
  rw [Finset.sum_range]
  have : ∀ i : Fin w.length, (w[i.1]?).elim 0 g = g w[i] := fun i ↦ by simp
  simp_rw [this]
  have hm : List.ofFn (fun i : Fin w.length ↦ g w[i]) = w.map g :=
    List.ext_getElem (by simp) fun i _ _ ↦ by simp
  rw [← List.sum_ofFn, hm, ← List.sum_toFinset _ hw]
  congr 1
  ext x
  simp [hall]

/-- The sweep of the complements of projections, as a product of complements in QICLean's
form. -/
theorem toEuclideanCLM_sweepProd (P : κ → Matrix (Config X) (Config X) ℂ) (l : List κ) :
    clmX (sweepProd (fun k ↦ 1 - P k) l) =
      ContinuousLinearMap.complementProd (wordProjections P l) l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [sweepProd]
  | append_singleton l k ih =>
    rw [sweepProd_append, List.length_append, List.length_singleton,
      ContinuousLinearMap.complementProd_succ, ContinuousLinearMap.complementProd_congr
        (h' := wordProjections P l) fun i hi ↦ by
          simp [wordProjections, List.getElem?_append_left hi], ← ih]
    simp [sweepProd, wordProjections, map_mul, map_sub]

end TNLean.PEPS.AreaLaw.FrustrationFree

namespace TNLean.PEPS.AreaLaw.FrustrationFree

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {h : PlaneInteraction Λ q R} {J Δ : ℝ}
  {Ω : StateSpace Λ q}

/-- The contraction factor `θ = (1 + (Δ/J)/(d_R + 1)²)^{-1/2}` of one sweep (`eq:sweep`). -/
noncomputable def sweepContraction (R : ℕ) (J Δ : ℝ) : ℝ :=
  (√(1 + Δ / J / ((overlapDegreeBound R : ℝ) + 1) ^ 2))⁻¹

theorem sweepContraction_nonneg (R : ℕ) (J Δ : ℝ) : 0 ≤ sweepContraction R J Δ :=
  inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem sweepContraction_lt_one {R : ℕ} {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    sweepContraction R J Δ < 1 := by
  rw [sweepContraction]
  refine inv_lt_one_of_one_lt₀ ?_
  rw [Real.lt_sqrt zero_le_one, one_pow]
  have : 0 < Δ / J / ((overlapDegreeBound R : ℝ) + 1) ^ 2 := by positivity
  linarith

theorem sweepContraction_pos {R : ℕ} {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    0 < sweepContraction R J Δ := by
  rw [sweepContraction]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

local notation "clm" => toEuclideanCLM (n := Configuration Λ q) (𝕜 := ℂ)

namespace IsFrustrationFreeGapped

variable (hff : IsFrustrationFreeGapped h J Δ Ω)

/-- The range projection `Π_X` of the term `h_X`. -/
noncomputable def termProj (X : AdmissibleSupport Λ R) :
    Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  (hff.isHermitian X).supportProj

/-- The sweep `D = ∏_X (1 - Π_X)`, the supports taken colour by colour. -/
noncomputable def sweepOp
    (c : (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))) :
    Matrix (Configuration Λ q) (Configuration Λ q) ℂ :=
  sweepProd (fun X ↦ 1 - hff.termProj X) (sweepWord c)

theorem termProj_mem (X : AdmissibleSupport Λ R) :
    hff.termProj X ∈ supportedOperators (fun _ : Site Λ ↦ Fin q) X.1 :=
  supportProj_mem_supportedOperators (hff.isHermitian X) (h.mem X)

theorem termProj_mulVec (X : AdmissibleSupport Λ R) :
    hff.termProj X *ᵥ WithLp.ofLp Ω = 0 :=
  (hff.isHermitian X).supportProj_mulVec_eq_zero_of_mulVec_eq_zero _ (hff.mulVec_eq_zero X)

theorem factor_mem (X : AdmissibleSupport Λ R) :
    1 - hff.termProj X ∈ supportedOperators (fun _ : Site Λ ↦ Fin q) X.1 :=
  sub_mem (one_mem _) (hff.termProj_mem X)

theorem factor_mulVec (X : AdmissibleSupport Λ R) :
    (1 - hff.termProj X) *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  have h0 := hff.termProj_mulVec X
  unfold termProj at h0 ⊢
  rw [sub_mulVec, one_mulVec, h0, sub_zero]

theorem conjTranspose_factor_mulVec (X : AdmissibleSupport Λ R) :
    (1 - hff.termProj X)ᴴ *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  have h0 := hff.factor_mulVec X
  unfold termProj at h0 ⊢
  rw [conjTranspose_sub, conjTranspose_one, (hff.isHermitian X).supportProj_isHermitian.eq, h0]

/-- The sweep fixes `Ω`. -/
theorem sweepOp_mulVec_self
    (c : (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))) :
    hff.sweepOp c *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  have := retainedProd_mulVec_eq_self (T := fun X : AdmissibleSupport Λ R ↦ X.1)
    hff.factor_mulVec ∅ (sweepWord c)
  -- every factor of the word meets no site of the empty region, so the sweep is the full product
  suffices hs : ∀ l : List (AdmissibleSupport Λ R),
      sweepProd (fun X ↦ 1 - hff.termProj X) l *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω from hs _
  intro l
  induction l with
  | nil => exact one_mulVec _
  | cons k l ih => rw [sweepProd, ← mulVec_mulVec, hff.factor_mulVec, ih]

theorem sweepOp_pow_mulVec_self
    (c : (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))) (t : ℕ) :
    (hff.sweepOp c ^ t) *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← mulVec_mulVec, hff.sweepOp_mulVec_self, ih]

/-- The quadratic form of the range projections dominates `(Δ / J) ‖v‖²` on `Ω^⊥`. -/
theorem mul_norm_sq_le_re_inner_sum_termProj (hJ : 0 < J) {v : StateSpace Λ q}
    (hv : ⟪Ω, v⟫_ℂ = 0) :
    Δ / J * ‖v‖ ^ 2 ≤
      RCLike.re ⟪v, clm (∑ X, hff.termProj X) v⟫_ℂ := by
  have hle := Matrix.le_iff.mp (hff.smul_sub_le_sum_supportProj hJ)
  have h0 := (isPositive_toEuclideanLin_iff.mpr hle).re_inner_nonneg_right v
  have hP : toEuclideanLin (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) v = 0 := by
    have : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp v = 0 := by
      rw [← hv, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    ext c
    simp [toEuclideanLin, vecMulVec_mulVec, this]
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, map_sub,
    LinearMap.sub_apply, hP, sub_zero, inner_sub_right, inner_smul_right] at h0
  have h1 : toEuclideanLin (1 : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) v = v := by
    simp
  rw [h1, inner_self_eq_norm_sq_to_K, map_sub, sub_nonneg] at h0
  refine le_of_eq_of_le ?_ h0
  simp only [RCLike.re_to_complex]
  norm_cast
  rw [Complex.re_ofReal_mul]
  rfl

open scoped Classical in
/-- **One sweep contracts `Ω^⊥`** (`eq:sweep` of the frustration-free area-law note): for every
`v ⟂ Ω`, `‖D^t v‖ ≤ θ^t ‖v‖`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one sweep".
-/
theorem norm_sweepOp_pow_apply_le (hJ : 0 < J) (hΔ : 0 < Δ)
    (c : (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))) (t : ℕ)
    {v : StateSpace Λ q} (hv : ⟪Ω, v⟫_ℂ = 0) :
    ‖clm (hff.sweepOp c ^ t) v‖ ≤ sweepContraction R J Δ ^ t * ‖v‖ := by
  set w := sweepWord c
  set P := wordProjections (fun X : AdmissibleSupport Λ R ↦ hff.termProj X) w
  have hD : clm (hff.sweepOp c) = ContinuousLinearMap.complementProd P w.length :=
    toEuclideanCLM_sweepProd _ w
  have hP : ∀ k, IsStarProjection (P k) := fun k ↦ by
    simp only [P, wordProjections]
    cases w[k]? with
    | none => exact IsStarProjection.zero _
    | some X => exact ((hff.isHermitian X).isStarProjection_supportProj).map clm
  have hPΩ : ∀ k, P k Ω = 0 := fun k ↦ by
    simp only [P, wordProjections]
    cases w[k]? with
    | none => rfl
    | some X =>
      change WithLp.toLp 2 (hff.termProj X *ᵥ WithLp.ofLp Ω) = 0
      rw [hff.termProj_mulVec]
      rfl
  have hPget : ∀ i (hi : i < w.length), P i = clm (hff.termProj w[i]) := fun i hi ↦ by
    simp [P, wordProjections, List.getElem?_eq_getElem hi]
  have hdeg : ∀ i < w.length, ((Finset.range w.length).filter
      fun j ↦ j ≠ i ∧ ¬Commute (P i) (P j)).card ≤ overlapDegreeBound R := by
    intro i hi
    refine (Finset.card_le_card_of_injOn (fun j ↦ w.getD j w[i])
      (t := (supportOverlapGraph Λ R).neighborFinset w[i]) ?_ ?_).trans
      (degree_overlapGraph_le w[i])
    · intro j hj
      obtain ⟨hjr, hji, hc⟩ := Finset.mem_filter.mp hj
      have hj' := Finset.mem_range.mp hjr
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, SimpleGraph.overlapGraph_adj]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
      refine ⟨fun heq ↦ hji ((nodup_sweepWord c).getElem_inj_iff.mp heq.symm), ?_⟩
      by_contra hd
      rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hd
      apply hc
      rw [hPget i hi, hPget j hj']
      exact ((commute_of_mem_supportedOperators_of_disjoint (hff.termProj_mem _)
        (hff.termProj_mem _) hd).map clm)
    · intro j hj k hk hjk
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
        List.getElem?_eq_getElem hk', Option.getD_some] at hjk
      exact (nodup_sweepWord c).getElem_inj_iff.mp hjk
  have hsum : ∑ i ∈ Finset.range w.length, P i = clm (∑ X, hff.termProj X) := by
    rw [map_sum]
    exact sum_range_getElem?_elim _ (nodup_sweepWord c) (mem_sweepWord c)
  have hgap : ∀ u : StateSpace Λ q, ⟪Ω, u⟫_ℂ = 0 →
      Δ / J * ‖u‖ ^ 2 ≤ RCLike.re ⟪u, (∑ i ∈ Finset.range w.length, P i) u⟫_ℂ := by
    intro u hu
    rw [hsum]
    exact hff.mul_norm_sq_le_re_inner_sum_termProj hJ hu
  have key := ContinuousLinearMap.norm_pow_complementProd_le_of_gap hP hPΩ hdeg
    (div_nonneg hΔ.le hJ.le) hgap t hv
  rw [map_pow, hD]
  exact key

/-- **The exact light cone of `t` sweeps** (`eq:cone` of the frustration-free area-law note). If
every block of an operator `B` on the sites and a register acts on `U`, there is an operator `L`
acting on `N_{R χ t}(U)`, `χ = d_R + 1`, with `L Ω = Ω`, `Lᴴ Ω = Ω` and
`(D^t ⊗ 1) B (Ω ⊗ ξ) = (L ⊗ 1) B (Ω ⊗ ξ)`. Source:
`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Exact localization on the
perturbed vector". -/
theorem exists_sweepOp_pow_lightCone
    (c : (supportOverlapGraph Λ R).Coloring (Fin (overlapDegreeBound R + 1))) (t : ℕ)
    {α : Type*} [Fintype α] [DecidableEq α] {U : Finset (Site Λ)}
    {B : Matrix (Configuration Λ q × α) (Configuration Λ q × α) ℂ}
    (hB : ∀ a b, B.submatrix (fun σ ↦ (σ, a)) (fun τ ↦ (τ, b)) ∈
      supportedOperators (fun _ : Site Λ ↦ Fin q) U) (ξ : α → ℂ) :
    ∃ L : Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
      L ∈ supportedOperators (fun _ : Site Λ ↦ Fin q)
          (graphNeighborhood Λ (R * (overlapDegreeBound R + 1) * t) U) ∧
        L *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω ∧ Lᴴ *ᵥ WithLp.ofLp Ω = WithLp.ofLp Ω ∧
        ((hff.sweepOp c ^ t) ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ
            (B *ᵥ (fun p : Configuration Λ q × α ↦ WithLp.ofLp Ω p.1 * ξ p.2)) =
          (L ⊗ₖ (1 : Matrix α α ℂ)) *ᵥ
            (B *ᵥ (fun p : Configuration Λ q × α ↦ WithLp.ofLp Ω p.1 * ξ p.2)) := by
  set l := (List.replicate t (sweepWord c)).flatten
  refine ⟨retainedProd (fun X ↦ 1 - hff.termProj X) (fun X : AdmissibleSupport Λ R ↦ X.1) U l,
    supportedOperators_mono (retainedSet_sweepWord_pow_subset c U t)
      (retainedProd_mem_supportedOperators hff.factor_mem U l),
    retainedProd_mulVec_eq_self hff.factor_mulVec U l,
    conjTranspose_retainedProd_mulVec_eq_self hff.conjTranspose_factor_mulVec U l, ?_⟩
  rw [sweepOp, ← sweepProd_flatten_replicate]
  exact kronecker_one_mulVec_sweep_eq_retained hff.factor_mem hff.factor_mulVec ξ l U B hB

end IsFrustrationFreeGapped

end TNLean.PEPS.AreaLaw.FrustrationFree

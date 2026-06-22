/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.TransferMatrix
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.NormalForm
import TNLean.Algebra.HermitianHelpers
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Lorentz normal form for quantum channels (Wolf Section 2.3, Propositions 2.8–2.11)

This file formalises the existence results for normal forms of quantum channels
under filtering operations, as described in Wolf Section 2.3 (Eqs. (2.35)-(2.43)).
The central idea is that every CP map with full Kraus rank can be brought to a
doubly-stochastic normal form by pre- and post-composition with invertible
Kraus-rank-1 CP maps (filtering operations).  For qubit channels (D = 2) the
equivalence class under
SL(2, ℂ)-filterings admits a particularly explicit classification — the *Lorentz
normal form* — with three canonical representatives.

## Structure

1. **Filtering operations.**  An `SLFiltering` is a CP map Φ(X) = S X S† where
   `det S = 1`.  Such maps are invertible and have Kraus rank 1.

2. **Doubly-stochastic maps.**  A linear map T is *doubly-stochastic* if both
   `T(1)` and the partial trace of its Choi matrix over the first subsystem
   are proportional to the identity matrix.  This is the normal form target
   for the generic construction (Wolf Proposition 2.8).

3. **Generic normal form (Wolf Proposition 2.8).**  For a CP map with full Kraus rank
   (equivalently, a positive-definite Choi matrix), there exist SL-filterings
   Φ₁, Φ₂ such that Φ₂ ∘ T ∘ Φ₁ is doubly-stochastic.

4. **Lorentz normal form for qubit channels (Wolf Proposition 2.9 / Proposition 2.11).**
   For every qubit channel (D = 2), after suitable SL(2, ℂ)-filterings, the
   Pauli-basis transfer matrix takes one of three canonical forms: diagonal,
   non-diagonal, or singular.

## Dependencies on missing Mathlib infrastructure

The compactness / minimisation core (the infimum over SL(n, ℂ) filterings is
attained) is now formalised as `infimum_is_attained`.  The remaining gap is the
AM–GM optimality iteration (Step 5 below) that turns a minimiser into a
doubly-stochastic normal form; it is still `sorry` inside
`exists_normal_form_generic`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.3][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder Kronecker Matrix.Norms.Frobenius
open Matrix Finset
open ChoiJamiolkowski

namespace Wolf

section FilteringOperations

/-- An `SLFiltering` for `D × D` matrices bundles a matrix `S` with
`det S = 1` (and `S` invertible) together with its associated CP map
`Φ(X) = S X S†`.  Such maps are called *filtering operations* in Wolf Section 2.3. -/
structure SLFiltering (D : ℕ) where
  /-- The filtering matrix, with determinant 1. -/
  S : Matrix (Fin D) (Fin D) ℂ
  /-- `det S = 1`. -/
  det_eq_one : S.det = 1
  /-- The CP map: Φ(X) = S X S†. -/
  map : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- `map` is exactly the unitary conjugation by `S`. -/
  map_eq : map = unitaryConjLM (D := D) S
  /-- SL-filterings are CP. -/
  cp : IsCPMap map

/-- The matrix `S` of an SL-filtering is invertible (follows from `det_eq_one`). -/
lemma SLFiltering.S_isUnit {D : ℕ} (Φ : SLFiltering D) : IsUnit Φ.S := by
  have h : Φ.S.det = 1 := Φ.det_eq_one
  have hdet : IsUnit (Φ.S.det) := by rw [h]; exact isUnit_one
  -- In a CommRing, a matrix is invertible iff its determinant is a unit.
  refine (Matrix.isUnit_iff_isUnit_det Φ.S).mpr hdet

/-- The identity map is an SL-filtering (S = 1). -/
noncomputable def SLFiltering.id (D : ℕ) : SLFiltering D where
  S := 1
  det_eq_one := by simp
  map := unitaryConjLM (D := D) 1
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) 1

/-- Composition of two SL-filterings is an SL-filtering. -/
noncomputable def SLFiltering.comp {D : ℕ} (Φ Ψ : SLFiltering D) : SLFiltering D where
  S := Φ.S * Ψ.S
  det_eq_one := by
    rw [Matrix.det_mul, Φ.det_eq_one, Ψ.det_eq_one, one_mul]
  map := unitaryConjLM (D := D) (Φ.S * Ψ.S)
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) (Φ.S * Ψ.S)

/-- `unitaryConjLM A ∘ₗ unitaryConjLM B = unitaryConjLM (A * B)`. -/
lemma unitaryConjLM_comp {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ) :
    unitaryConjLM (D := D) A ∘ₗ unitaryConjLM (D := D) B =
    unitaryConjLM (D := D) (A * B) := by
  ext X; simp [unitaryConjLM_apply, Matrix.mul_assoc, Matrix.conjTranspose_mul]

end FilteringOperations

/-! ### Doubly-stochastic maps -/

section DoublyStochastic

variable {D : ℕ} (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- A CP map `T` is **doubly-stochastic** if `T(1) ∝ 1` and the reduced density
matrix `tr₁[τ]` of its Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` is proportional to
the identity.  By Choi–Jamiołkowski, this is equivalent to both `T(1)` and
`T*(1)` being proportional to identity, which is the target normal form in
Wolf Proposition 2.8.

We use the partial-trace formulation to avoid depending on the adjoint of `T`
as a Hilbert–Schmidt operator. -/
def DoublyStochastic : Prop :=
  (∃ c₁ : ℂ, T 1 = c₁ • (1 : Matrix (Fin D) (Fin D) ℂ)) ∧
  (∃ c₂ : ℂ, Matrix.traceLeft (choiMatrix T) = c₂ • (1 : Matrix (Fin D) (Fin D) ℂ))

/-- Doubly-stochastic implies T(1) ∝ 1. -/
lemma DoublyStochastic.unital (hT : DoublyStochastic T) :
    ∃ c : ℂ, T 1 = c • (1 : Matrix (Fin D) (Fin D) ℂ) := hT.1

/-- Doubly-stochastic implies the partial trace of the Choi matrix is ∝ 1
(equivalently, T*(1) ∝ 1). -/
lemma DoublyStochastic.tracePreserving (hT : DoublyStochastic T) :
    ∃ c : ℂ, Matrix.traceLeft (choiMatrix T) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ) := hT.2

end DoublyStochastic

/-! ### Generic normal form (Wolf Proposition 2.8)

The proof idea (see Wolf Section 2.3):
1. Work at the level of the Choi matrix τ = (T ⊗ id)(|Ω⟩⟨Ω|).
2. Under SL-filterings Φ(X) = S X S†, τ transforms as τ → (S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†.
3. Minimize tr[τ'] over S₁, S₂ with det = 1.
4. The infimum is attained (compactness of the bounded subset of SL(n, ℂ)).
5. At the optimum, both partial traces of τ' are proportional to identity,
   giving doubly-stochastic T'.

Step 4 is the compactness/minimisation argument, now formalised as
`infimum_is_attained` below.  Step 5 follows from the optimality condition
(AM–GM iteration) and is the remaining `sorry` in `exists_normal_form_generic`. -/

section GenericNormalForm

variable {D : ℕ}

/-- **Key lemma (Wolf Section 2.3, compactness/minimisation core).**  For a
positive-definite Choi matrix τ, the infimum of `tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]`
over `S₁, S₂` with `det = 1` is attained.  That is, the continuous function
`(S₁, S₂) ↦ tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]`
achieves its minimum on `SL(D, ℂ) × SL(D, ℂ)`.

**Proof** (Wolf Section 2.3).  Throughout, `‖·‖` denotes the Frobenius
(Hilbert–Schmidt) norm `‖M‖² = tr[M M†]`; the coercivity bound below is false
for the operator norm (e.g. `‖I‖_op² = 1 < D`).  With `X = S₂ ⊗ₖ S₁`:

* positive-semidefiniteness of `τ - λ_min(τ)·I` gives the smallest-eigenvalue
  bound `λ_min(τ) · tr[X† X] ≤ tr[X τ X†]`;
* the Kronecker factorisation of the Hilbert–Schmidt norm gives
  `tr[X† X] = ‖S₂‖² · ‖S₁‖²`;
* the singular-value AM–GM inequality gives `‖S_i‖² ≥ D` whenever `det S_i = 1`.

Together these yield `tr[X τ X†] ≥ λ_min(τ) · D · ‖S_i‖²`, so any pair whose
value is at most the value at the identity lies in a fixed Frobenius ball
`{‖S‖² ≤ R}`.  Intersecting that ball with `{det S = 1}` gives a closed and
bounded — hence compact, by finite-dimensional Heine–Borel — set on which the
continuous trace functional attains its minimum; any pair outside the ball has
value exceeding the value at the identity, so this minimiser is global.  The
degenerate case `D = 0` is handled separately (all traces vanish). -/
lemma infimum_is_attained
    {τ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hτ_posDef : τ.PosDef) :
    ∃ (S₁ S₂ : Matrix (Fin D) (Fin D) ℂ),
      S₁.det = 1 ∧ S₂.det = 1 ∧
      ∀ (T₁ T₂ : Matrix (Fin D) (Fin D) ℂ),
        T₁.det = 1 → T₂.det = 1 →
        (Matrix.trace (((T₂ ⊗ₖ T₁) * τ * ((T₂ ⊗ₖ T₁)ᴴ)))).re ≥
          (Matrix.trace (((S₂ ⊗ₖ S₁) * τ * ((S₂ ⊗ₖ S₁)ᴴ)))).re := by
  classical
  -- Degenerate dimension: over `Fin 0` every matrix is empty and all traces vanish.
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    refine ⟨1, 1, by simp, by simp, ?_⟩
    intro T₁ T₂ _ _
    simp [Matrix.trace]
  haveI : Nonempty (Fin D) := ⟨⟨0, hDpos⟩⟩
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  -- Smallest eigenvalue of `τ`, positive by positive-definiteness.
  set lam : ℝ := minEigenvalue hτ_posDef.isHermitian with hlam
  have hlam_pos : 0 < lam := minEigenvalue_pos_of_posDef hτ_posDef.isHermitian hτ_posDef
  -- The trace functional on pairs `(S₁, S₂)`.
  set f : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ → ℝ :=
    fun p => (Matrix.trace ((p.2 ⊗ₖ p.1) * τ * ((p.2 ⊗ₖ p.1)ᴴ))).re with hf
  -- Coercivity: `tr[(B ⊗ₖ A) τ (B ⊗ₖ A)†] ≥ λ_min(τ) · ‖B‖² · ‖A‖²`.
  have hcoer : ∀ A B : Matrix (Fin D) (Fin D) ℂ,
      lam * (‖B‖ ^ 2 * ‖A‖ ^ 2) ≤
        (Matrix.trace ((B ⊗ₖ A) * τ * ((B ⊗ₖ A)ᴴ))).re := by
    intro A B
    have h1 := posDef_minEigenvalue_mul_trace_conjTranspose_mul_self_le hτ_posDef (B ⊗ₖ A)
    have h2 := (Complex.le_def.mp h1).1
    rw [Complex.re_ofReal_mul, Matrix.trace_conjTranspose_mul_self_re_kronecker,
      Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
      Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq] at h2
    exact h2
  -- Unit determinant forces the Frobenius norm squared to be at least the dimension.
  have hamgm : ∀ S : Matrix (Fin D) (Fin D) ℂ, S.det = 1 → (D : ℝ) ≤ ‖S‖ ^ 2 := by
    intro S hS
    have hnorm : ‖S.det‖ = 1 := by rw [hS]; exact norm_one
    have h := Matrix.card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one S hnorm
    rwa [Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, Fintype.card_fin] at h
  -- The trace of `τ` is the value of `f` at the identity pair.
  set v₀ : ℝ := (Matrix.trace τ).re with hv₀
  have hf11 : f (1, 1) = v₀ := by
    change (Matrix.trace (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
      τ * (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ))).re = v₀
    rw [Matrix.one_kronecker_one, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  have hone_norm : ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ^ 2 = (D : ℝ) := by
    rw [← Matrix.trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin]
    simp
  -- Hence `λ_min(τ) · D² ≤ v₀`.
  have hlamDD : lam * ((D : ℝ) * (D : ℝ)) ≤ v₀ := by
    have h := hcoer 1 1
    rw [hone_norm] at h
    calc lam * ((D : ℝ) * (D : ℝ)) ≤ _ := h
      _ = v₀ := hf11
  -- Search radius `R = v₀ / (λ_min(τ) · D)`.
  have hlamD_pos : 0 < lam * (D : ℝ) := mul_pos hlam_pos hDR
  have hlamD_ne : lam * (D : ℝ) ≠ 0 := ne_of_gt hlamD_pos
  have hv₀_pos : 0 < v₀ := lt_of_lt_of_le (mul_pos hlam_pos (mul_pos hDR hDR)) hlamDD
  set R : ℝ := v₀ / (lam * (D : ℝ)) with hR
  have hR_pos : 0 < R := div_pos hv₀_pos hlamD_pos
  have hkey : lam * (D : ℝ) * R = v₀ := by
    rw [hR, ← mul_div_assoc, mul_div_cancel_left₀ v₀ hlamD_ne]
  have hD_le_R : (D : ℝ) ≤ R := by
    rw [hR, le_div_iff₀ hlamD_pos]
    have h : (D : ℝ) * (lam * (D : ℝ)) = lam * ((D : ℝ) * (D : ℝ)) := by ring
    rw [h]; exact hlamDD
  -- The compact search set: unit determinants inside a Frobenius ball.
  set K : Set (Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ) :=
    {p | p.1.det = 1 ∧ p.2.det = 1 ∧ ‖p.1‖ ^ 2 ≤ R ∧ ‖p.2‖ ^ 2 ≤ R} with hKdef
  have h11K : ((1 : Matrix (Fin D) (Fin D) ℂ), (1 : Matrix (Fin D) (Fin D) ℂ)) ∈ K := by
    rw [hKdef, Set.mem_setOf_eq]
    refine ⟨Matrix.det_one, Matrix.det_one, ?_, ?_⟩
    · change ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ^ 2 ≤ R
      rw [hone_norm]; exact hD_le_R
    · change ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ^ 2 ≤ R
      rw [hone_norm]; exact hD_le_R
  -- Continuity of `f`.
  have hf_cont : Continuous f := by
    have hk : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        (p.2 ⊗ₖ p.1) := continuous_snd.matrix_kronecker continuous_fst
    exact Complex.continuous_re.comp
      ((hk.matrix_mul continuous_const).matrix_mul hk.matrix_conjTranspose).matrix_trace
  -- `K` is closed and bounded, hence compact.
  have hK_closed : IsClosed K := by
    have c1 : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        p.1.det := continuous_fst.matrix_det
    have c2 : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        p.2.det := continuous_snd.matrix_det
    have c3 : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        ‖p.1‖ ^ 2 := continuous_fst.norm.pow 2
    have c4 : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        ‖p.2‖ ^ 2 := continuous_snd.norm.pow 2
    rw [hKdef]
    simp only [Set.setOf_and]
    exact (isClosed_eq c1 continuous_const).inter ((isClosed_eq c2 continuous_const).inter
      ((isClosed_le c3 continuous_const).inter (isClosed_le c4 continuous_const)))
  have hsub : K ⊆ Metric.closedBall (0 : Matrix (Fin D) (Fin D) ℂ ×
      Matrix (Fin D) (Fin D) ℂ) (Real.sqrt R) := by
    intro p hp
    rw [hKdef, Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le ((Real.le_sqrt (norm_nonneg _) hR_pos.le).mpr hp.2.2.1)
      ((Real.le_sqrt (norm_nonneg _) hR_pos.le).mpr hp.2.2.2)
  have hK_compact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hK_closed (Metric.isBounded_closedBall.subset hsub)
  -- Extreme value theorem on `K`.
  obtain ⟨q, hqK, hq_min⟩ := hK_compact.exists_isMinOn ⟨_, h11K⟩ hf_cont.continuousOn
  rw [hKdef, Set.mem_setOf_eq] at hqK
  have hmin := isMinOn_iff.mp hq_min
  refine ⟨q.1, q.2, hqK.1, hqK.2.1, ?_⟩
  intro T₁ T₂ hT₁ hT₂
  change f q ≤ f (T₁, T₂)
  by_cases hmem : ‖T₁‖ ^ 2 ≤ R ∧ ‖T₂‖ ^ 2 ≤ R
  · apply hmin
    rw [hKdef, Set.mem_setOf_eq]
    exact ⟨hT₁, hT₂, hmem.1, hmem.2⟩
  · -- One factor escapes the ball, so the value exceeds `v₀ ≥ f q`.
    have hqv : f q ≤ v₀ := by
      have hh := hmin (1, 1) h11K
      rwa [hf11] at hh
    have hT₁D : (D : ℝ) ≤ ‖T₁‖ ^ 2 := hamgm T₁ hT₁
    have hT₂D : (D : ℝ) ≤ ‖T₂‖ ^ 2 := hamgm T₂ hT₂
    rw [not_and_or] at hmem
    have hprod : (D : ℝ) * R < ‖T₂‖ ^ 2 * ‖T₁‖ ^ 2 := by
      rcases hmem with h | h
      · rw [not_le] at h
        calc (D : ℝ) * R < (D : ℝ) * ‖T₁‖ ^ 2 := mul_lt_mul_of_pos_left h hDR
          _ ≤ ‖T₂‖ ^ 2 * ‖T₁‖ ^ 2 := mul_le_mul_of_nonneg_right hT₂D (by positivity)
      · rw [not_le] at h
        calc (D : ℝ) * R = R * (D : ℝ) := by ring
          _ < ‖T₂‖ ^ 2 * (D : ℝ) := mul_lt_mul_of_pos_right h hDR
          _ ≤ ‖T₂‖ ^ 2 * ‖T₁‖ ^ 2 := mul_le_mul_of_nonneg_left hT₁D (by positivity)
    have hbig : v₀ < f (T₁, T₂) := by
      have hlt : v₀ < lam * (‖T₂‖ ^ 2 * ‖T₁‖ ^ 2) := by
        rw [← hkey, mul_assoc]
        exact mul_lt_mul_of_pos_left hprod hlam_pos
      exact lt_of_lt_of_le hlt (hcoer T₁ T₂)
    exact le_of_lt (lt_of_le_of_lt hqv hbig)

/-- **Wolf Proposition 2.9: generic normal form for CP maps with full Kraus rank.**

Let `T : M_D(ℂ) → M_D(ℂ)` be a completely positive map with full Kraus rank
(equivalently, its Choi matrix is positive-definite).  Then there exist
SL(D, ℂ)-filterings Φ₁, Φ₂ such that `Φ₂ ∘ T ∘ Φ₁` is doubly-stochastic.

This is the CP-map version of Wolf Proposition 2.8 (which is stated at the τ-level).
The Lorentz normal form for qubit channels (Proposition 2.9) is the D = 2
specialisation with the complete classification of the possible
doubly-stochastic normal forms. -/
theorem exists_normal_form_generic
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (_hCP : IsCPMap T)
    (_hFullRank : (choiMatrix T).PosDef) :
    ∃ (Φ₁ Φ₂ : SLFiltering D),
      DoublyStochastic (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  let τ := choiMatrix T
  obtain ⟨_S₁, _S₂, _, _, _⟩ := infimum_is_attained (τ := τ) _hFullRank
  sorry

end GenericNormalForm

/-! ### Lorentz normal form for qubit channels (Wolf Proposition 2.9 / Proposition 2.11)

For `D = 2` (qubit channels), the doubly-stochastic normal form from
Proposition 2.8 is further simplified using the Lorentz group action on the
transfer matrix.  The result is a complete classification into three
canonical forms.

We work in the Pauli basis representation: let σ₀, …, σ₃ be the Pauli
matrices (σ₀ = 1, σ₁ = σₓ, σ₂ = σ_y, σ₃ = σ_z).  For a
Hermiticity-preserving TP qubit channel `T`, the Pauli-basis transfer
matrix
  `T̂_{ij} = (1/2) tr[σ_i T(σ_j)]`   (i, j ∈ {0,1,2,3})
has real entries and the block structure
  `T̂ = [1 0; v Δ]`
where `v ∈ ℝ³` and `Δ` is a 3×3 real matrix (the Bloch-ball affine map:
`x ↦ v + Δ x`).

After SL(2, ℂ) filtering (which acts on `T̂` as a Lorentz transformation
`L₂ T̂ L₁` with `L_i ∈ SO⁺(1,3)`), the transfer matrix can be brought to
one of three canonical forms (Wolf Proposition 2.9):

1. **Diagonal** (generic, full Kraus rank): `T̂` is diagonal —
   `v = 0` and `Δ = diag(λ₁, λ₂, λ₃)` with the CP condition
   `λ₁ + λ₂ ≤ 1 + λ₃`.  This is the doubly-stochastic case.

2. **Non-diagonal** (Kraus rank 3): `T̂` has
   `Δ = diag(x/√3, x/√3, 1/3)`, `v = (0, 0, 2/3)`, with
   `0 ≤ x ≤ 1`.

3. **Singular** (Kraus rank 2): `T̂` has `Δ = 0` and `v = (0, 0, 1)`;
   the channel maps every input to a single pure state. -/

section LorentzNormalFormQubit

/-- The four Pauli matrices as 2×2 complex matrices, indexed by `Fin 4`:
`σ₀ = [[1,0],[0,1]]`, `σ₁ = [[0,1],[1,0]]`, `σ₂ = [[0,-I],[I,0]]`,
`σ₃ = [[1,0],[0,-1]]`. -/
def pauliMatrices : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- The entry `(i,j)` of the **Pauli-basis transfer matrix** of a linear map
`T : M₂(ℂ) → M₂(ℂ)`:
  `T̂_{ij} = (1/2) tr[σ_i T(σ_j)]`.

This is the `4×4` matrix representing `T` in the Pauli basis
`{σ₀/√2, σ₁/√2, σ₂/√2, σ₃/√2}`, so that `T̂` has real entries for
Hermiticity-preserving `T`. -/
noncomputable def pauliTransferEntry
    (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 4) : ℂ :=
  ((1 : ℂ) / 2) * Matrix.trace (pauliMatrices i * T (pauliMatrices j))

/-- A Hermiticity-preserving TP qubit channel `T'` is in **diagonal Lorentz normal
form** (Wolf Proposition 2.9, case 1) if its Pauli-basis transfer matrix is diagonal:
`T'(1) = 1` (unital) and all off-diagonal entries of `T̂` vanish
(i.e., `v = 0` and `Δ = diag(λ₁, λ₂, λ₃)`).

Furthermore, the singular values satisfy the complete-positivity condition
`λ₁ + λ₂ ≤ 1 + λ₃` (not checked here; future refinement). -/
def IsLorentzDiagonal
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧ T' 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    ∀ (i j : Fin 4), i ≠ j → pauliTransferEntry T' i j = 0

/-- A Hermiticity-preserving TP qubit channel `T'` is in **non-diagonal Lorentz
normal form** (Wolf Proposition 2.9, case 2) if its Pauli-basis transfer matrix has
`Δ = diag(x/√3, x/√3, 1/3)` and `v = (0, 0, 2/3)` for some `x ∈ [0, 1]`.

The channel condition supplies the trace-preserving first row. The predicate
records the non-trivial translation entry, the three diagonal entries, and the
vanishing of all off-diagonal entries except the allowed translation. -/
def IsLorentzNonDiagonal
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ 1 ∧
      pauliTransferEntry T' 3 0 = (2/3 : ℂ) ∧
      pauliTransferEntry T' 1 1 = ((x / Real.sqrt 3 : ℝ) : ℂ) ∧
      pauliTransferEntry T' 2 2 = ((x / Real.sqrt 3 : ℝ) : ℂ) ∧
      pauliTransferEntry T' 3 3 = (1/3 : ℂ) ∧
      ∀ (i j : Fin 4), i ≠ j → (i, j) ≠ ((3 : Fin 4), (0 : Fin 4)) →
        pauliTransferEntry T' i j = 0

/-- A Hermiticity-preserving TP qubit channel `T'` is in **singular Lorentz normal
form** (Wolf Proposition 2.9, case 3) if its Pauli-basis transfer matrix has
`Δ = 0` and `v = (0, 0, 1)`.  That is, only `T̂_{00} = 1` and
`T̂_{30} = 1` are nonzero; the channel maps every input to the pure state
`(1 + σ_z)/2`. -/
def IsLorentzSingular
    (T' : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsChannel T' ∧
    pauliTransferEntry T' 3 0 = 1 ∧
    ∀ (i j : Fin 4), (i, j) ≠ (0, 0) ∧ (i, j) ≠ (3, 0) → pauliTransferEntry T' i j = 0

/-- **Lorentz normal form for qubit channels (Wolf Proposition 2.9 / Proposition 2.11).**

For every qubit channel `T : M₂(ℂ) → M₂(ℂ)`, there exist SL(2, ℂ)-filterings
Φ₁, Φ₂ such that the filtered channel `T' = Φ₂ ∘ T ∘ Φ₁` is in one of the
three Lorentz normal forms: diagonal, non-diagonal, or singular.

The proof is not yet formalised; it depends on:
- The compactness lemma `infimum_is_attained` (above);
- The Lorentz group classification of SL(2, ℂ) orbits (spinor map
  SL(2, ℂ) → SO⁺(1, 3));
- The complete-positivity condition `λ₁ + λ₂ ≤ 1 + λ₃`.

See Wolf Section 2.3 for the complete proof. -/
theorem exists_lorentz_normal_form_qubit
    (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (_hCh : IsChannel T) :
    ∃ (Φ₁ Φ₂ : SLFiltering 2),
      IsLorentzDiagonal (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) ∨
      IsLorentzNonDiagonal (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) ∨
      IsLorentzSingular (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  sorry

end LorentzNormalFormQubit

/-
## Connection to transfer-matrix normal forms (Wolf Section 2.3)

The results above are stated at the level of CP maps.  The corresponding
transfer-matrix formulation (Propositions 2.7-2.8 in the blueprint / TransferMatrix.lean)
is obtained by applying `transferMatrix` to both sides.  The SVD normal form
(`Matrix.svd_of_isUnit`, `transferMatrix_svd_of_isUnit`) provides the
algebraic engine: after SL-filterings, the transfer matrix of the doubly-stochastic
map admits an SVD, which for D = 2 yields the Lorentz normal form decomposition.
-/

end Wolf

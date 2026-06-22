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
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

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

## Compactness / minimisation argument

The compactness / minimisation argument used in the proof of Proposition 2.8 and 2.9
(over SL(n, ℂ) filterings) is formalised in `infimum_is_attained`: the trace
functional is coercive on `{det = 1}`, so a global minimiser exists by the
extreme value theorem on a compact Frobenius ball.  See the documentation of
`infimum_is_attained` for the proof outline.

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

Step 4 is the compactness/minimisation argument, formalised in
`infimum_is_attained` below.  Step 5 follows from the optimality condition (AGM
iteration), and is not yet formalised. -/

section GenericNormalForm

variable {D : ℕ}

/-- **Key lemma.**  For a positive-definite Choi matrix τ, the infimum of
`tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` over `S₁, S₂` with `det = 1` is attained.  That
is, the continuous function `(S₁, S₂) ↦ tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` achieves
its minimum on the domain of SL(n, ℂ) × SL(n, ℂ).

**Proof** (Wolf Section 2.3).  Throughout, `‖·‖` denotes the Frobenius
(Hilbert–Schmidt) norm `‖M‖² = tr[M M†]`; the coercivity bounds below are false
for the operator norm (e.g. `‖I‖_op² = 1 < n`).  Writing `X = S₂ ⊗ₖ S₁`, the
smallest-eigenvalue bound for a positive-definite matrix gives
`λ_min(τ) · tr[Xᴴ X] ≤ tr[X τ Xᴴ]`, Hilbert–Schmidt multiplicativity of the
Kronecker product gives `tr[Xᴴ X] = tr[S₂ᴴ S₂] · tr[S₁ᴴ S₁]`, and the determinant
AM–GM estimate gives `tr[Sᵢᴴ Sᵢ] = ‖Sᵢ‖² ≥ n` whenever `det Sᵢ = 1`.  Combining
these, `tr[X τ Xᴴ] ≥ λ_min(τ) · n · ‖Sᵢ‖²` for each factor, so any minimiser is
confined to the bounded set `{S | ‖S‖ ≤ C}`.  Intersecting with the closed set
`det S = 1` gives a compact set on which the continuous trace functional attains
its minimum by the extreme value theorem; a value outside the sublevel set is
automatically larger than the value at the identity, so this minimiser is
global. -/
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
  -- The degenerate case `D = 0`: all matrices are `0 × 0`, every trace vanishes.
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    refine ⟨1, 1, Matrix.det_one, Matrix.det_one, ?_⟩
    intro T₁ T₂ _ _
    simp [Matrix.trace, Matrix.diag]
  haveI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  haveI : Nonempty (Fin D × Fin D) := ⟨(⟨0, hD⟩, ⟨0, hD⟩)⟩
  haveI : ProperSpace
      (Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ) :=
    FiniteDimensional.proper_rclike ℂ _
  -- The functional to minimise, as a function of the pair `(S₁, S₂)`.
  let g : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ → ℝ :=
    fun p => (Matrix.trace ((p.2 ⊗ₖ p.1) * τ * ((p.2 ⊗ₖ p.1)ᴴ))).re
  set lam : ℝ := minEigenvalue hτ_posDef.isHermitian with hlam_def
  have hlam : 0 < lam := minEigenvalue_pos_of_posDef hτ_posDef.isHermitian hτ_posDef
  set cardR : ℝ := (Fintype.card (Fin D) : ℝ) with hcardR
  have hcardR_pos : 0 < cardR := by
    rw [hcardR]; exact_mod_cast Fintype.card_pos
  -- Coercivity: the value dominates `λ · ‖S₂‖² · ‖S₁‖²`.
  have key : ∀ S₁ S₂ : Matrix (Fin D) (Fin D) ℂ,
      lam * ((Matrix.trace (S₂ᴴ * S₂)).re * (Matrix.trace (S₁ᴴ * S₁)).re) ≤
        g (S₁, S₂) := by
    intro S₁ S₂
    have hle := (Complex.le_def.mp
      (posDef_minEigenvalue_mul_trace_conjTranspose_mul_self_le hτ_posDef (S₂ ⊗ₖ S₁))).1
    rw [Complex.re_ofReal_mul, trace_conjTranspose_mul_self_re_kronecker] at hle
    exact hle
  -- The bound at the identity confines minimisers to a Frobenius ball.
  set B : ℝ := g (1, 1) with hB
  set C : ℝ := Real.sqrt (B / (lam * cardR)) with hC
  have hbound : ∀ S₁ S₂ : Matrix (Fin D) (Fin D) ℂ, S₁.det = 1 → S₂.det = 1 →
      g (S₁, S₂) ≤ B → ‖S₁‖ ≤ C ∧ ‖S₂‖ ≤ C := by
    intro S₁ S₂ h1 h2 hgB
    have hd1 : ‖S₁.det‖ = 1 := by rw [h1]; simp
    have hd2 : ‖S₂.det‖ = 1 := by rw [h2]; simp
    have hn1 : cardR ≤ (Matrix.trace (S₁ᴴ * S₁)).re :=
      card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one S₁ hd1
    have hn2 : cardR ≤ (Matrix.trace (S₂ᴴ * S₂)).re :=
      card_le_trace_conjTranspose_mul_self_re_of_det_norm_eq_one S₂ hd2
    have ht1 : 0 ≤ (Matrix.trace (S₁ᴴ * S₁)).re := hcardR_pos.le.trans hn1
    have ht2 : 0 ≤ (Matrix.trace (S₂ᴴ * S₂)).re := hcardR_pos.le.trans hn2
    have hδ : 0 < lam * cardR := mul_pos hlam hcardR_pos
    -- Bound on `‖S₁‖`.
    have hsq1 : ‖S₁‖ ^ 2 ≤ B / (lam * cardR) := by
      have hchain : (lam * cardR) * (Matrix.trace (S₁ᴴ * S₁)).re ≤ B := by
        calc (lam * cardR) * (Matrix.trace (S₁ᴴ * S₁)).re
            = lam * (cardR * (Matrix.trace (S₁ᴴ * S₁)).re) := by ring
          _ ≤ lam * ((Matrix.trace (S₂ᴴ * S₂)).re * (Matrix.trace (S₁ᴴ * S₁)).re) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hn2 ht1) hlam.le
          _ ≤ g (S₁, S₂) := key S₁ S₂
          _ ≤ B := hgB
      rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, le_div_iff₀ hδ, mul_comm]
      exact hchain
    have hsq2 : ‖S₂‖ ^ 2 ≤ B / (lam * cardR) := by
      have hchain : (lam * cardR) * (Matrix.trace (S₂ᴴ * S₂)).re ≤ B := by
        calc (lam * cardR) * (Matrix.trace (S₂ᴴ * S₂)).re
            = lam * ((Matrix.trace (S₂ᴴ * S₂)).re * cardR) := by ring
          _ ≤ lam * ((Matrix.trace (S₂ᴴ * S₂)).re * (Matrix.trace (S₁ᴴ * S₁)).re) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hn1 ht2) hlam.le
          _ ≤ g (S₁, S₂) := key S₁ S₂
          _ ≤ B := hgB
      rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, le_div_iff₀ hδ, mul_comm]
      exact hchain
    refine ⟨?_, ?_⟩
    · rw [hC, ← Real.sqrt_sq (norm_nonneg S₁)]; exact Real.sqrt_le_sqrt hsq1
    · rw [hC, ← Real.sqrt_sq (norm_nonneg S₂)]; exact Real.sqrt_le_sqrt hsq2
  -- The compact constraint set.
  set Kc : Set (Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ) :=
    {p | p.1.det = 1 ∧ p.2.det = 1 ∧ ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C} with hKc
  have hgcont : Continuous g := by
    have hk : Continuous fun p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ =>
        p.2 ⊗ₖ p.1 := Continuous.matrix_kronecker continuous_snd continuous_fst
    exact Complex.continuous_re.comp
      ((hk.matrix_mul continuous_const).matrix_mul hk.matrix_conjTranspose).matrix_trace
  have hclosed : IsClosed Kc := by
    have c1 : IsClosed {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ | p.1.det = 1} :=
      isClosed_eq continuous_fst.matrix_det continuous_const
    have c2 : IsClosed {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ | p.2.det = 1} :=
      isClosed_eq continuous_snd.matrix_det continuous_const
    have c3 : IsClosed {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ | ‖p.1‖ ≤ C} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have c4 : IsClosed {p : Matrix (Fin D) (Fin D) ℂ × Matrix (Fin D) (Fin D) ℂ | ‖p.2‖ ≤ C} :=
      isClosed_le (continuous_norm.comp continuous_snd) continuous_const
    have hset : Kc = {p | p.1.det = 1} ∩ {p | p.2.det = 1} ∩ {p | ‖p.1‖ ≤ C} ∩ {p | ‖p.2‖ ≤ C} := by
      rw [hKc]; ext p; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
    rw [hset]; exact ((c1.inter c2).inter c3).inter c4
  have hbdd : Bornology.IsBounded Kc := by
    refine (Metric.isBounded_closedBall (x := (0 : Matrix (Fin D) (Fin D) ℂ ×
      Matrix (Fin D) (Fin D) ℂ)) (r := C)).subset ?_
    intro p hp
    rw [hKc, Set.mem_setOf_eq] at hp
    rw [Metric.mem_closedBall]
    calc dist p 0 = max (dist p.1 0) (dist p.2 0) := Prod.dist_eq
      _ = max ‖p.1‖ ‖p.2‖ := by rw [dist_zero_right, dist_zero_right]
      _ ≤ C := max_le hp.2.2.1 hp.2.2.2
  have hKcompact : IsCompact Kc := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have h11mem : (1, 1) ∈ Kc := by
    rw [hKc, Set.mem_setOf_eq]
    obtain ⟨hc1, hc2⟩ := hbound 1 1 Matrix.det_one Matrix.det_one (le_of_eq hB.symm)
    exact ⟨Matrix.det_one, Matrix.det_one, hc1, hc2⟩
  obtain ⟨pmin, hpmin_mem, hpmin_min⟩ :=
    hKcompact.exists_isMinOn ⟨(1, 1), h11mem⟩ hgcont.continuousOn
  rw [hKc, Set.mem_setOf_eq] at hpmin_mem
  refine ⟨pmin.1, pmin.2, hpmin_mem.1, hpmin_mem.2.1, ?_⟩
  intro T₁ T₂ hT₁ hT₂
  by_cases hcase : g (T₁, T₂) ≤ B
  · have hmem : (T₁, T₂) ∈ Kc := by
      rw [hKc, Set.mem_setOf_eq]
      obtain ⟨hc1, hc2⟩ := hbound T₁ T₂ hT₁ hT₂ hcase
      exact ⟨hT₁, hT₂, hc1, hc2⟩
    exact isMinOn_iff.mp hpmin_min (T₁, T₂) hmem
  · have hpB : g pmin ≤ B := isMinOn_iff.mp hpmin_min (1, 1) h11mem
    exact le_trans hpB (le_of_lt (not_le.mp hcase))

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

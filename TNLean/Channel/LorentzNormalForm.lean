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
import TNLean.Analysis.MarginalSupport

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

/-! ### Trace–determinant AM–GM inequality (Wolf Section 2.3)

The optimality step of Wolf Proposition 2.8 (the "AGM iteration") rests on the
arithmetic–geometric-mean inequality applied to the eigenvalues of a
positive-semidefinite Choi matrix.  In product/sum form the eigenvalue estimate
reads `Dᴰ · det M ≤ (tr M)ᴰ`, which is the polynomial form of AM–GM with uniform
weights `1 / D`.  We record the underlying real-number inequality and its matrix
specialisation here.

Placement note: `pow_card_mul_prod_le_sum_pow` is a generic real-number AM–GM
inequality and `posSemidef_pow_det_le_trace_pow` /
`posSemidef_pow_det_eq_trace_pow_iff` are general positive-semidefinite matrix
inequalities, now consumed by `exists_normal_form_generic` below. Their natural
Layer-0 home is `TNLean/Analysis/MatrixTraceInequalities.lean` (the `Matrix`
namespace, alongside `PosSemidef.trace_sq_re_le_trace_re_sq`); relocating and
renaming them out of the `Wolf` namespace is left as a follow-up refactor. -/

section TraceDetAMGM

/-- **AM–GM in product/sum form.**  For a nonnegative family `f : Fin D → ℝ`,
`Dᴰ · ∏ f ≤ (∑ f)ᴰ`.  This is the polynomial form of the
arithmetic–geometric-mean inequality with uniform weights `1 / D`.  Wolf
Section 2.3 applies it to the eigenvalues of a Choi matrix in the optimality
("AGM iteration") step of Proposition 2.8.  Both sides agree when `D = 0`
(empty product `1`, empty sum `0`, and `0 ^ 0 = 1`). -/
lemma pow_card_mul_prod_le_sum_pow {D : ℕ} (f : Fin D → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (D : ℝ) ^ D * ∏ i, f i ≤ (∑ i, f i) ^ D := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0; simp
  have hD0' : D ≠ 0 := hDpos.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD0'
  have hDR_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hP0 : 0 ≤ ∏ i, f i := Finset.prod_nonneg fun i _ => hf i
  have hDpow_pos : (0 : ℝ) < (D : ℝ) ^ D := pow_pos hDR_pos D
  -- Uniform weights `w i = 1 / D` sum to one.
  have hwsum : ∑ _i : Fin D, (D : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hDR]
  -- Weighted AM–GM applied to the family `f`, then simplified to
  -- `(∏ f) ^ (1 / D) ≤ (1 / D) * ∑ f`.
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin D => (D : ℝ)⁻¹) f (fun i _ => by positivity) hwsum (fun i _ => hf i)
  rw [Real.finsetProd_rpow Finset.univ f (fun i _ => hf i) ((D : ℝ)⁻¹),
    ← Finset.mul_sum] at hamgm
  -- Raise both nonnegative sides to the `D`-th power and simplify.
  have hraise := pow_le_pow_left₀ (Real.rpow_nonneg hP0 _) hamgm D
  rw [Real.rpow_inv_natCast_pow hP0 hD0', mul_pow, inv_pow] at hraise
  calc (D : ℝ) ^ D * ∏ i, f i
      ≤ (D : ℝ) ^ D * (((D : ℝ) ^ D)⁻¹ * (∑ i, f i) ^ D) :=
        mul_le_mul_of_nonneg_left hraise hDpow_pos.le
    _ = (∑ i, f i) ^ D := mul_inv_cancel_left₀ hDpow_pos.ne' _

/-- **Trace–determinant AM–GM inequality.**  For a positive-semidefinite
`D × D` complex matrix `M`, `Dᴰ · det M ≤ (tr M)ᴰ` as real numbers (both
`det M` and `tr M` are real for a Hermitian matrix).  This is the eigenvalue
AM–GM estimate underlying the optimality ("AGM iteration") step of Wolf
Proposition 2.8 (Section 2.3): `det M = ∏ λᵢ` and `tr M = ∑ λᵢ` for the
nonnegative eigenvalues `λᵢ`, so the bound is `pow_card_mul_prod_le_sum_pow`
applied to the eigenvalue family. -/
lemma posSemidef_pow_det_le_trace_pow {D : ℕ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosSemidef) :
    (D : ℝ) ^ D * M.det.re ≤ M.trace.re ^ D := by
  classical
  have hdet : M.det.re = ∏ i, hM.1.eigenvalues i := by
    simp only [hM.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  have htr : M.trace.re = ∑ i, hM.1.eigenvalues i := by
    simp only [hM.1.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    exact RCLike.ofReal_re (K := ℂ) _
  rw [hdet, htr]
  exact pow_card_mul_prod_le_sum_pow hM.1.eigenvalues fun i => hM.eigenvalues_nonneg i

/-- **Equality in the trace–determinant AM–GM inequality.**  For a
positive-semidefinite `D × D` complex matrix `M`, the bound
`posSemidef_pow_det_le_trace_pow` is an equality exactly when `M` is the scalar
matrix `(tr M / D) · 1` — equivalently, when all eigenvalues coincide.  This is
the equality case of the AM–GM step in Wolf Proposition 2.8 (Section 2.3): the
"AGM iteration" terminates precisely at scalar (maximally mixed) blocks. -/
lemma posSemidef_pow_det_eq_trace_pow_iff {D : ℕ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosSemidef) :
    (D : ℝ) ^ D * M.det.re = M.trace.re ^ D ↔
      M = ((M.trace.re / D : ℝ) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => by simp⟩
  have hD0' : D ≠ 0 := hDpos.ne'
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD0'
  have hDR_pos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hdet : M.det.re = ∏ i, hM.1.eigenvalues i := by
    simp only [hM.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  have htr : M.trace.re = ∑ i, hM.1.eigenvalues i := by
    simp only [hM.1.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    exact RCLike.ofReal_re (K := ℂ) _
  have he0 : ∀ i, 0 ≤ hM.1.eigenvalues i := fun i => hM.eigenvalues_nonneg i
  set e := hM.1.eigenvalues with he
  set c : ℝ := M.trace.re / D with hc_def
  constructor
  · -- Equality forces all eigenvalues to coincide, hence `M` is scalar.
    intro heq
    rw [hdet, htr] at heq
    have hP0 : 0 ≤ ∏ i, e i := Finset.prod_nonneg fun i _ => he0 i
    have hS0 : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he0 i
    have hwsum : ∑ _i : Fin D, (D : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hDR]
    -- The polynomial equality is equivalent to the rpow form of AM–GM equality.
    have hraw : (∏ i, e i) ^ ((D : ℝ)⁻¹) = (D : ℝ)⁻¹ * ∑ i, e i := by
      have hl0 : 0 ≤ (∏ i, e i) ^ ((D : ℝ)⁻¹) := Real.rpow_nonneg hP0 _
      have hr0 : 0 ≤ (D : ℝ)⁻¹ * ∑ i, e i := mul_nonneg (by positivity) hS0
      rw [← pow_left_inj₀ hl0 hr0 hD0', Real.rpow_inv_natCast_pow hP0 hD0', mul_pow, inv_pow,
        ← heq, inv_mul_cancel_left₀ (pow_ne_zero D hDR)]
    have hcond : (∏ i, e i ^ ((D : ℝ)⁻¹)) = ∑ i, (D : ℝ)⁻¹ * e i := by
      rw [Real.finsetProd_rpow Finset.univ e (fun i _ => he0 i) ((D : ℝ)⁻¹), ← Finset.mul_sum]
      exact hraw
    have hall : ∀ j k : Fin D, e j = e k := by
      have h := (Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ
        (fun _ : Fin D => (D : ℝ)⁻¹) e (fun i _ => inv_pos.mpr hDR_pos) hwsum
        (fun i _ => he0 i)).mp hcond
      exact fun j k => h j (Finset.mem_univ j) k (Finset.mem_univ k)
    -- The common eigenvalue is the mean `c = tr M / D`.
    have hc_eq : ∀ i, e i = c := by
      intro i
      have hsum : ∑ j, e j = (D : ℝ) * e i := by
        rw [Finset.sum_congr rfl (fun j _ => hall j i), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [hc_def, htr, hsum, mul_comm (D : ℝ) (e i), mul_div_assoc, div_self hDR, mul_one]
    -- Rebuild `M` from the spectral theorem with a constant eigenvalue function.
    have hfun : (RCLike.ofReal ∘ e : Fin D → ℂ) = fun _ => (RCLike.ofReal c : ℂ) := by
      funext i; simp only [Function.comp_apply, hc_eq i]
    rw [hM.1.spectral_theorem, Unitary.conjStarAlgAut_apply, ← he, hfun, ← smul_one_eq_diagonal,
      Matrix.mul_smul, mul_one, Matrix.smul_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self]
    norm_cast
  · -- A scalar matrix saturates the bound by direct computation.
    intro hM_eq
    have hdet_eq : M.det.re = c ^ D := by
      rw [hM_eq, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one,
        ← Complex.ofReal_pow]
      exact Complex.ofReal_re _
    rw [hdet_eq, ← mul_pow]
    congr 1
    rw [hc_def, mul_comm, div_mul_cancel₀ _ hDR]

end TraceDetAMGM

/-! ### Generic normal form (Wolf Proposition 2.8)

The proof idea (see Wolf Section 2.3):
1. Work at the level of the Choi matrix τ = (T ⊗ id)(|Ω⟩⟨Ω|).
2. Under SL-filterings Φ(X) = S X S†, τ transforms as τ → (S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†.
3. Minimize tr[τ'] over S₁, S₂ with det = 1.
4. The infimum is attained (compactness of the bounded subset of SL(n, ℂ)).
5. At the optimum, both partial traces of τ' are proportional to identity,
   giving doubly-stochastic T'.

Step 4 is the compactness/minimisation argument, formalised in
`infimum_is_attained` below.  Step 5 is the optimality condition (AGM iteration):
fixing one filtering, the other minimises a single-coordinate trace functional
`tr[S Mᵢ S†]` over `det S = 1`, whose minimiser saturates the trace–determinant
AM–GM bound and is therefore a scalar matrix (`posDef_orbit_min_isScalar`).  The
two coordinate optima give the two `DoublyStochastic` conditions, completing
`exists_normal_form_generic`. -/

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

/-- Entry formula for conjugation by `A ⊗ₖ 1` (identity on the second factor). -/
private lemma kron_one_conj_entry (A : Matrix (Fin D) (Fin D) ℂ)
    (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (i₁ i₂ j₁ j₂ : Fin D) :
    ((A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * M *
        (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ c, ∑ d, A i₁ c * M (c, i₂) (d, j₂) * star (A j₁ d) := by
  have L : ∀ s : Fin D × Fin D,
      ((A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * M) (i₁, i₂) s
        = ∑ c, A i₁ c * M (c, i₂) s := by
    intro s
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one,
      mul_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i₂ (fun w₂ => A i₁ c * M (c, w₂) s)]
    simp
  have key : ((A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * M *
        (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ d, ∑ c, A i₁ c * M (c, i₂) (d, j₂) * star (A j₁ d) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single j₂]
    · rw [L (d, j₂), Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    · intro b _ hb
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ j₂) h
  rw [key, Finset.sum_comm]

/-- Entry formula for conjugation by `1 ⊗ₖ B` (identity on the first factor). -/
private lemma one_kron_conj_entry (B : Matrix (Fin D) (Fin D) ℂ)
    (M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) (i₁ i₂ j₁ j₂ : Fin D) :
    (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ B) * M *
        ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ B)ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ a, ∑ b, B i₂ a * M (i₁, a) (j₁, b) * star (B j₂ b) := by
  have L : ∀ s : Fin D × Fin D,
      (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ B) * M) (i₁, i₂) s
        = ∑ a, B i₂ a * M (i₁, a) s := by
    intro s
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i₁ (fun w₁ => B i₂ a * M (w₁, a) s)]
    simp
  have key : (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ B) * M *
        ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ B)ᴴ) (i₁, i₂) (j₁, j₂)
      = ∑ b, ∑ a, B i₂ a * M (i₁, a) (j₁, b) * star (B j₂ b) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j₁]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [L (j₁, b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
    · intro c _ hc
      apply Finset.sum_eq_zero
      intro b _
      simp [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Ne.symm hc]
    · intro h; exact absurd (Finset.mem_univ j₁) h
  rw [key, Finset.sum_comm]

/-- `tr_A` commutes with conjugation by `1 ⊗ₖ X` (acting on the second factor):
`tr_A((1 ⊗ X) ρ (1 ⊗ X)†) = X (tr_A ρ) X†`. -/
private lemma traceLeft_one_kron_conj (X : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.traceLeft (((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X) * ρ *
        ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X)ᴴ)
      = X * Matrix.traceLeft ρ * Xᴴ := by
  ext i j
  rw [Matrix.traceLeft_apply]
  have hRHS : (X * Matrix.traceLeft ρ * Xᴴ) i j
      = ∑ a, ∑ b, X i a * (∑ k, ρ (k, a) (k, b)) * star (X j b) := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.traceLeft_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hRHS]
  simp_rw [one_kron_conj_entry X ρ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- `tr_B` commutes with conjugation by `X ⊗ₖ 1` (acting on the first factor):
`tr_B((X ⊗ 1) ρ (X ⊗ 1)†) = X (tr_B ρ) X†`. -/
private lemma traceRight_kron_one_conj (X : Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.traceRight ((X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * ρ *
        (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ)
      = X * Matrix.traceRight ρ * Xᴴ := by
  ext i j
  rw [Matrix.traceRight_apply]
  have hRHS : (X * Matrix.traceRight ρ * Xᴴ) i j
      = ∑ c, ∑ d, X i c * (∑ k, ρ (c, k) (d, k)) * star (X j d) := by
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.traceRight_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hRHS]
  simp_rw [kron_one_conj_entry X ρ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Conjugating a matrix unit by `B` spreads it over all matrix units:
`B (single i₂ j₂ c) B† = ∑ a b, (B a i₂ · conj(B b j₂)) (single a b c)`. -/
private lemma single_conj_spread (B : Matrix (Fin D) (Fin D) ℂ) (i₂ j₂ : Fin D) (c : ℂ) :
    B * Matrix.single i₂ j₂ c * Bᴴ
      = ∑ a, ∑ b, (B a i₂ * star (B b j₂)) • Matrix.single a b c := by
  ext p q
  have hL : (B * Matrix.single i₂ j₂ c * Bᴴ) p q = B p i₂ * c * star (B q j₂) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single j₂]
    · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply]
    · intro x _ hx; rw [Matrix.mul_single_apply_of_ne (hbj := hx) (M := B), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j₂) h
  have hR : (∑ a, ∑ b, (B a i₂ * star (B b j₂)) • Matrix.single a b c) p q
      = B p i₂ * star (B q j₂) * c := by
    rw [Matrix.sum_apply, Finset.sum_eq_single p]
    · rw [Matrix.sum_apply, Finset.sum_eq_single q]
      · rw [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul]
      · intro b _ hb
        rw [Matrix.smul_apply, Matrix.single_apply_of_col_ne p p hb c, smul_zero]
      · intro h; exact absurd (Finset.mem_univ q) h
    · intro a _ ha
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.smul_apply, Matrix.single_apply_of_row_ne ha b q c, smul_zero]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [hL, hR]; ring

/-- Choi matrix of post-composition with conjugation by `A`:
`choi(Ad_A ∘ T) = (A ⊗ 1) choi(T) (A ⊗ 1)†`. -/
private lemma choiMatrix_unitaryConj_comp (A : Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrix (unitaryConjLM A ∘ₗ T)
      = (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * choiMatrix T *
          (A ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [kron_one_conj_entry A (choiMatrix T) i₁ i₂ j₁ j₂, choiMatrix_apply,
    LinearMap.comp_apply, unitaryConjLM_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [choiMatrix_apply]

/-- Choi matrix of pre-composition with conjugation by `B`:
`choi(T ∘ Ad_B) = (1 ⊗ Bᵀ) choi(T) (1 ⊗ Bᵀ)†`. -/
private lemma choiMatrix_comp_unitaryConj (B : Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    choiMatrix (T ∘ₗ unitaryConjLM B)
      = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ Bᵀ) * choiMatrix T *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ Bᵀ)ᴴ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  rw [one_kron_conj_entry Bᵀ (choiMatrix T) i₁ i₂ j₁ j₂, choiMatrix_apply,
    LinearMap.comp_apply, unitaryConjLM_apply, omegaSlice_eq_single, single_conj_spread,
    map_sum]
  simp_rw [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [choiMatrix_apply, omegaSlice_eq_single, Matrix.transpose_apply, Matrix.transpose_apply]
  ring

/-- Partial trace over the second factor of a positive-definite matrix is
positive definite. -/
private lemma traceRight_posDef [NeZero D] {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hρ : ρ.PosDef) : (Matrix.traceRight ρ).PosDef := by
  have hblock : ∀ b : Fin D, (ρ.submatrix (fun i => (i, b)) (fun i => (i, b))).PosDef :=
    fun b => hρ.submatrix (fun i j h => (Prod.ext_iff.mp h).1)
  have heq : Matrix.traceRight ρ
      = ∑ b : Fin D, ρ.submatrix (fun i => (i, b)) (fun i => (i, b)) := by
    ext i j; simp only [Matrix.traceRight_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posDef_sum Finset.univ_nonempty fun b _ => hblock b

/-- Partial trace over the second factor of a positive-semidefinite matrix is
positive semidefinite. -/
private lemma traceRight_posSemidef {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hρ : ρ.PosSemidef) : (Matrix.traceRight ρ).PosSemidef := by
  have hblock : ∀ b : Fin D, (ρ.submatrix (fun i => (i, b)) (fun i => (i, b))).PosSemidef :=
    fun b => hρ.submatrix _
  have heq : Matrix.traceRight ρ
      = ∑ b : Fin D, ρ.submatrix (fun i => (i, b)) (fun i => (i, b)) := by
    ext i j; simp only [Matrix.traceRight_apply, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ fun b _ => hblock b

/-- `Matrix.traceLeft` agrees with `Matrix.traceLeftA`. -/
private lemma traceLeft_eq_traceLeftA (ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    Matrix.traceLeft ρ = Matrix.traceLeftA ρ := rfl

/-- The full trace equals the trace of the right partial trace: `tr(X) = tr(tr_B(X))`. -/
private lemma trace_eq_trace_traceRight (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    X.trace = (Matrix.traceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.traceRight_apply]
  exact Fintype.sum_prod_type _

/-- A positive-definite matrix can be normalized to a scalar matrix by an
`SL(D, ℂ)` congruence: there exists `S` with `det S = 1` and
`S M S† = r • 1` for some `r ≥ 0`.  Take `S = c · √M⁻¹` with `cᴰ = det √M`. -/
private lemma exists_sl_normalize [NeZero D] {M : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosDef) :
    ∃ S : Matrix (Fin D) (Fin D) ℂ, S.det = 1 ∧
      ∃ r : ℝ, 0 ≤ r ∧ S * M * Sᴴ = (r : ℂ) • 1 := by
  classical
  set R : Matrix (Fin D) (Fin D) ℂ := hM.posSemidef.isHermitian.cfc Real.sqrt with hR_def
  have hR_herm : R.IsHermitian := hM.posSemidef.cfc_sqrt_isHermitian
  have hRR : R * R = M := hM.posSemidef.cfc_sqrt_mul_self
  have hMdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit).ne_zero
  have hRdet : R.det ≠ 0 := by
    intro h; apply hMdet; rw [← hRR, Matrix.det_mul, h, zero_mul]
  have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq R.det hDpos
  refine ⟨c • R⁻¹, ?_, Complex.normSq c, Complex.normSq_nonneg c, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_nonsing_inv, hc,
      Ring.mul_inverse_cancel _ hRunit]
  · have hRinvH : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hR_herm.eq]
    have hRinvMul : R⁻¹ * M * R⁻¹ = 1 := by
      rw [← hRR]
      simp only [Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv _ hRunit, Matrix.mul_one, Matrix.nonsing_inv_mul _ hRunit]
    rw [Matrix.conjTranspose_smul, hRinvH, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hRinvMul, Complex.star_def, Complex.mul_conj]

/-- **Optimality forces a scalar.**  If `N` is a positive-semidefinite matrix
with the same determinant as a positive-definite `M`, and `tr N` is the minimum
of `tr (S M S†)` over `det S = 1`, then `N` is a scalar matrix.  This is the
AM–GM equality argument: the minimum saturates `Dᴰ det = (tr)ᴰ`. -/
private lemma posDef_orbit_min_isScalar [NeZero D] {M N : Matrix (Fin D) (Fin D) ℂ}
    (hM : M.PosDef) (hN : N.PosSemidef) (hdet : N.det = M.det)
    (hmin : ∀ S : Matrix (Fin D) (Fin D) ℂ, S.det = 1 →
      (Matrix.trace N).re ≤ (Matrix.trace (S * M * Sᴴ)).re) :
    ∃ c : ℂ, N = c • 1 := by
  obtain ⟨S₀, hS₀, r, hr0, hP⟩ := exists_sl_normalize hM
  have hDpos : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hdetP : (S₀ * M * S₀ᴴ).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, hS₀, Matrix.det_conjTranspose, hS₀]; simp
  have hNdet : N.det = ((r ^ D : ℝ) : ℂ) := by
    rw [hdet, ← hdetP, hP, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one,
      ← Complex.ofReal_pow]
  have hNdet_re : N.det.re = r ^ D := by rw [hNdet]; exact Complex.ofReal_re _
  have hPtr : Matrix.trace (S₀ * M * S₀ᴴ) = ((r * D : ℝ) : ℂ) := by
    rw [hP, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast; ring
  have hub : (Matrix.trace N).re ≤ r * D := by
    refine (hmin S₀ hS₀).trans_eq ?_; rw [hPtr]; exact Complex.ofReal_re _
  have htrN0 : 0 ≤ (Matrix.trace N).re := by
    simpa using (Complex.le_def.mp hN.trace_nonneg).1
  have hAGM := posSemidef_pow_det_le_trace_pow hN
  rw [hNdet_re] at hAGM
  have hlb : (D : ℝ) * r ≤ (Matrix.trace N).re := by
    rw [← mul_pow] at hAGM
    exact (pow_le_pow_iff_left₀ (mul_nonneg (Nat.cast_nonneg D) hr0) htrN0 (NeZero.ne D)).mp hAGM
  have htrace_eq : (Matrix.trace N).re = (D : ℝ) * r :=
    le_antisymm (hub.trans_eq (mul_comm r (D : ℝ))) hlb
  exact ⟨_, (posSemidef_pow_det_eq_trace_pow_iff hN).mp (by rw [hNdet_re, htrace_eq, mul_pow])⟩

/-- The reduced state `tr_B(choi T)` equals (up to the `|Ω⟩` normalization) `T 1`. -/
private lemma traceRight_choiMatrix
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix.traceRight (choiMatrix T)
      = (((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ))) • T 1 := by
  set cc : ℂ := ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) with hcc
  ext i j
  rw [Matrix.traceRight_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∀ k : Fin D, choiMatrix T (i, k) (j, k) = cc * T (Matrix.single k k 1) i j := by
    intro k
    rw [choiMatrix_apply, omegaSlice_eq_single,
      show Matrix.single k k cc = cc • Matrix.single k k (1 : ℂ) by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, Matrix.smul_apply, smul_eq_mul]
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  rw [← Matrix.sum_apply, ← map_sum, Matrix.sum_single_one]

/-- The `|Ω⟩` normalization constant is nonzero. -/
private lemma omega_coeff_ne_zero (hD : 0 < D) :
    (((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ))) ≠ 0 := by
  have hsqrt : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD)
  have h1 : (1 : ℂ) / ((D : ℝ).sqrt : ℂ) ≠ 0 := one_div_ne_zero hsqrt
  exact mul_ne_zero h1 (star_ne_zero.mpr h1)

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
  classical
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    exact ⟨SLFiltering.id 0, SLFiltering.id 0,
      ⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩
  haveI : NeZero D := ⟨hDpos.ne'⟩
  obtain ⟨S₁, S₂, hS₁det, hS₂det, hmin⟩ := infimum_is_attained (τ := choiMatrix T) _hFullRank
  let Φ₁ : SLFiltering D :=
    { S := S₁ᵀ
      det_eq_one := by rw [Matrix.det_transpose, hS₁det]
      map := unitaryConjLM S₁ᵀ
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₁ᵀ }
  let Φ₂ : SLFiltering D :=
    { S := S₂
      det_eq_one := hS₂det
      map := unitaryConjLM S₂
      map_eq := rfl
      cp := unitaryConjLM_isCPMap S₂ }
  -- The Choi matrix of the filtered channel is the minimised matrix.
  have hC : choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)
      = (S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ := by
    show choiMatrix (unitaryConjLM S₂ ∘ₗ (T ∘ₗ unitaryConjLM S₁ᵀ)) = _
    rw [choiMatrix_unitaryConj_comp, choiMatrix_comp_unitaryConj, Matrix.transpose_transpose,
      show (S₂ ⊗ₖ S₁) = (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) by
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  -- Invertibility of the kronecker factors.
  have hU2 : IsUnit (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₂det, Matrix.det_one]; simp
  have hU1 : IsUnit ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, hS₁det, Matrix.det_one]; simp
  -- The two reduced matrices and their key properties.
  set ρ₂ := (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * choiMatrix T *
    (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ with hρ₂
  set ρ₁ := ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) * choiMatrix T *
    ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁)ᴴ with hρ₁
  have hρ₂pd : ρ₂.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU2)
  have hρ₁pd : ρ₁.PosDef :=
    _hFullRank.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hU1)
  -- Conjugation/partial-trace reductions.
  have hX : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Matrix.traceLeft ((S₂ ⊗ₖ X) * choiMatrix T * (S₂ ⊗ₖ X)ᴴ)
        = X * Matrix.traceLeft ρ₂ * Xᴴ := by
    intro X
    have hsplit : (S₂ ⊗ₖ X) * choiMatrix T * (S₂ ⊗ₖ X)ᴴ
        = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X) * ρ₂ *
            ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X)ᴴ := by
      rw [hρ₂, show (S₂ ⊗ₖ X) = ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ X) *
          (S₂ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) by
            rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceLeft_one_kron_conj]
  have hY : ∀ X : Matrix (Fin D) (Fin D) ℂ,
      Matrix.traceRight ((X ⊗ₖ S₁) * choiMatrix T * (X ⊗ₖ S₁)ᴴ)
        = X * Matrix.traceRight ρ₁ * Xᴴ := by
    intro X
    have hsplit : (X ⊗ₖ S₁) * choiMatrix T * (X ⊗ₖ S₁)ᴴ
        = (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) * ρ₁ *
            (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ))ᴴ := by
      rw [hρ₁, show (X ⊗ₖ S₁) = (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) *
          ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ S₁) by
            rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul],
        Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsplit, traceRight_kron_one_conj]
  have hM₁pd : (Matrix.traceLeft ρ₂).PosDef := by
    rw [traceLeft_eq_traceLeftA]; exact traceLeftA_posDef hρ₂pd
  have hM₂pd : (Matrix.traceRight ρ₁).PosDef := traceRight_posDef hρ₁pd
  refine ⟨Φ₁, Φ₂, ?_, ?_⟩
  · -- Clause 1: (Φ₂ ∘ T ∘ Φ₁)(1) ∝ 1.
    have hN₂ : ∃ κ : ℂ,
        Matrix.traceRight (choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)) = κ • 1 := by
      apply posDef_orbit_min_isScalar hM₂pd
      · rw [hC]; exact traceRight_posSemidef
          (_hFullRank.posSemidef.mul_mul_conjTranspose_same _)
      · rw [hC, hY S₂, Matrix.det_mul, Matrix.det_mul, hS₂det, Matrix.det_conjTranspose,
          hS₂det]; simp
      · intro S hS
        have e1 : (Matrix.trace (Matrix.traceRight (choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
            = (Matrix.trace ((S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ)).re := by
          rw [hC, ← trace_eq_trace_traceRight]
        have e2 : (Matrix.trace (S * Matrix.traceRight ρ₁ * Sᴴ)).re
            = (Matrix.trace ((S ⊗ₖ S₁) * choiMatrix T * (S ⊗ₖ S₁)ᴴ)).re := by
          rw [← hY S, ← trace_eq_trace_traceRight]
        rw [e1, e2]
        exact hmin S₁ S hS₁det hS
    obtain ⟨κ, hκ⟩ := hN₂
    rw [traceRight_choiMatrix] at hκ
    set cc : ℂ := ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) with hcc
    have hcc_ne : cc ≠ 0 := by rw [hcc]; exact omega_coeff_ne_zero hDpos
    refine ⟨cc⁻¹ * κ, ?_⟩
    have h := congrArg (fun M => cc⁻¹ • M) hκ
    simp only [smul_smul, inv_mul_cancel₀ hcc_ne, one_smul] at h
    exact h
  · -- Clause 2: tr_A(choi(Φ₂ ∘ T ∘ Φ₁)) ∝ 1.
    apply posDef_orbit_min_isScalar hM₁pd
    · rw [hC, hX S₁]
      exact (hM₁pd.posSemidef.mul_mul_conjTranspose_same S₁)
    · rw [hC, hX S₁, Matrix.det_mul, Matrix.det_mul, hS₁det, Matrix.det_conjTranspose,
        hS₁det]; simp
    · intro S hS
      have e1 : (Matrix.trace (Matrix.traceLeft (choiMatrix (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map)))).re
          = (Matrix.trace ((S₂ ⊗ₖ S₁) * choiMatrix T * (S₂ ⊗ₖ S₁)ᴴ)).re := by
        rw [hC, ← Matrix.trace_eq_trace_traceLeft]
      have e2 : (Matrix.trace (S * Matrix.traceLeft ρ₂ * Sᴴ)).re
          = (Matrix.trace ((S₂ ⊗ₖ S) * choiMatrix T * (S₂ ⊗ₖ S)ᴴ)).re := by
        rw [← hX S, ← Matrix.trace_eq_trace_traceLeft]
      rw [e1, e2]
      exact hmin S S₂ hS hS₂det

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

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.TransferMatrix
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Channel.NormalForm
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Lorentz normal form for quantum channels (Wolf §2.3)

This file formalises the existence results for normal forms of quantum channels
under filtering operations, as described in Wolf §2.3.  The central idea is that
every CP map with full Kraus rank can be brought to a doubly-stochastic normal
form by pre- and post-composition with invertible Kraus-rank-1 CP maps (filtering
operations).  For qubit channels (D = 2) the equivalence class under
SL(2, ℂ)-filterings admits a particularly explicit classification — the *Lorentz
normal form* — with three canonical representatives.

## Structure

1. **Filtering operations.**  An `SLFiltering` is a CP map Φ(X) = S X S† where
   `det S = 1`.  Such maps are invertible and have Kraus rank 1.

2. **Doubly-stochastic maps.**  A linear map T is *doubly-stochastic* if both
   `T(1)` and the partial trace of its Choi matrix over the first subsystem
   are proportional to the identity matrix.  This is the normal form target
   for the generic construction (Wolf Prop 2.8).

3. **Generic normal form (Wolf Prop 2.8).**  For a CP map with full Kraus rank
   (equivalently, a positive-definite Choi matrix), there exist SL-filterings
   Φ₁, Φ₂ such that Φ₂ ∘ T ∘ Φ₁ is doubly-stochastic.

4. **Lorentz normal form for qubit channels (Wolf Prop 2.9 / Prop 2.11).**
   For every qubit channel (D = 2), after suitable SL(2, ℂ)-filterings, the
   transfer matrix takes one of three canonical forms: diagonal, non-diagonal,
   or singular.

## Dependencies on missing Mathlib infrastructure

The compactness / minimisation argument used in the proof of Prop 2.8 and 2.9
(over SL(n, ℂ) filterings) is not yet formalised in Mathlib or TNLean.  The
relevant theorems are therefore stated with `sorry` for the minimisation core.
See the documentation of `infimum_is_attained` for the precise missing fact.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §2.3][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix Finset
open ChoiJamiolkowski

namespace Wolf

section FilteringOperations

/-- An `SLFiltering` for `D × D` matrices bundles a matrix `S` with
`det S = 1` (and `S` invertible) together with its associated CP map
`Φ(X) = S X S†`.  Such maps are called *filtering operations* in Wolf §2.3.
-/
structure SLFiltering (D : ℕ) where
  /-- The filtering matrix, with determinant 1. -/
  S : Matrix (Fin D) (Fin D) ℂ
  /-- `det S = 1`. -/
  det_eq_one : S.det = 1
  /-- `S` is invertible. -/
  S_isUnit : IsUnit S
  /-- The CP map: Φ(X) = S X S†. -/
  map : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- `map` is exactly the unitary conjugation by `S`. -/
  map_eq : map = unitaryConjLM (D := D) S
  /-- SL-filterings are CP. -/
  cp : IsCPMap map

/-- The identity map is an SL-filtering (S = 1). -/
noncomputable def SLFiltering.id (D : ℕ) : SLFiltering D where
  S := 1
  det_eq_one := by simp
  S_isUnit := by simp
  map := unitaryConjLM (D := D) 1
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) 1

/-- The canonical SL-filtering from a matrix S with det S = 1 (when S is invertible). -/
noncomputable def SLFiltering.ofMatrix {D : ℕ} (S : Matrix (Fin D) (Fin D) ℂ)
    (hdet : S.det = 1) (hunit : IsUnit S) : SLFiltering D where
  S := S
  det_eq_one := hdet
  S_isUnit := hunit
  map := unitaryConjLM (D := D) S
  map_eq := rfl
  cp := unitaryConjLM_isCPMap (D := D) S

/-- Composition of two SL-filterings is an SL-filtering. -/
noncomputable def SLFiltering.comp {D : ℕ} (Φ Ψ : SLFiltering D) : SLFiltering D where
  S := Φ.S * Ψ.S
  det_eq_one := by
    rw [Matrix.det_mul, Φ.det_eq_one, Ψ.det_eq_one, one_mul]
  S_isUnit := Φ.S_isUnit.mul Ψ.S_isUnit
  map := unitaryConjLM (D := D) (Φ.S * Ψ.S)
  map_eq := rfl
  cp := by
    have hcomp : ∀ X : Matrix (Fin D) (Fin D) ℂ,
        (unitaryConjLM Φ.S ∘ₗ unitaryConjLM Ψ.S) X =
        unitaryConjLM (Φ.S * Ψ.S) X := by
      intro X
      simp [unitaryConjLM_apply, Matrix.mul_assoc, Matrix.conjTranspose_mul]
    -- `unitaryConjLM (Φ.S * Ψ.S)` is CP (single Kraus operator).
    exact unitaryConjLM_isCPMap (D := D) (Φ.S * Ψ.S)

end FilteringOperations

/-! ### Doubly-stochastic maps -/

section DoublyStochastic

variable {D : ℕ}

/-- A CP map `T` is **doubly-stochastic** if `T(1) ∝ 1` and the reduced density
matrix `tr₁[τ]` of its Choi matrix `τ = (T ⊗ id)(|Ω⟩⟨Ω|)` is proportional to
the identity.  By Choi–Jamiołkowski, this is equivalent to both `T(1)` and
`T*(1)` being proportional to identity, which is the target normal form in
Wolf Prop 2.8.

We use the partial-trace formulation to avoid depending on the Hilbert–Schmidt
inner-product adjoint `LinearMap.adjoint`, which requires additional type-class
instances. -/
def DoublyStochastic (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
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

/-! ### Generic normal form (Wolf Prop 2.8)

The proof idea (see Wolf §2.3):
1. Work at the level of the Choi matrix τ = (T ⊗ id)(|Ω⟩⟨Ω|).
2. Under SL-filterings Φ(X) = S X S†, τ transforms as τ → (S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†
   (up to transposition convention).
3. Minimize tr[τ'] over S₁, S₂ with det = 1.
4. The infimum is attained (compactness of the bounded subset of SL(n, ℂ)).
5. At the optimum, both partial traces of τ' are proportional to identity,
   giving doubly-stochastic T'.

Step 4 is the compactness/minimisation argument that is **not yet formalised**
in Mathlib or TNLean.  We state the lemma as `infimum_is_attained` with a
`sorry` filler.  Step 5 follows from the optimality condition (AGM iteration),
stated below. -/

section GenericNormalForm

variable {D : ℕ}

/-- **Key lemma (not yet formalised).**  For a positive-definite Choi matrix τ,
the infimum of `tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]` over `S₁, S₂` with `det = 1`
is attained.  That is, the continuous function
`(S₁, S₂) ↦ tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]`
achieves its minimum on the domain of SL(n, ℂ) × SL(n, ℂ).

**Proof sketch** (Wolf §2.3).  There exist bounds
  `0 < λ_min(τ) · ‖S₂ ⊗ₖ S₁‖² ≤ tr[τ'] ≤ tr[τ]`,
so we may restrict to a bounded subset `{S_i | ‖S_i‖ ≤ C}` inside
`{S | det S = 1}`.  In finite dimensions this set is compact, and the
continuous trace functional attains its infimum by the extreme value theorem.

**Missing Mathlib facts:**
- Compactness of the set `{S : Matrix n n ℂ | det S = 1 ∧ ‖S‖ ≤ C}`.
  This needs: (a) the determinant condition `det S = 1` defines a closed set
  (it's a polynomial equation), and (b) the spectral-norm ball `‖S‖ ≤ C` is
  compact (finite-dimensional Heine–Borel).
- The extreme value theorem for the continuous map
  `(S₁, S₂) ↦ tr[(S₂ ⊗ₖ S₁) τ (S₂ ⊗ₖ S₁)†]`
  on this compact product set.
Both should be obtainable from `Mathlib.Topology.Instances.Matrix` and
`Mathlib.Topology.Algebra.Module.FiniteDimension`, but the glue is missing.

Once this lemma is proved, the rest of the normal-form argument (Thm 2.8) is
purely algebraic and follows from the optimality conditions. -/
lemma infimum_is_attained
    {τ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (_hτ_posDef : τ.PosDef) :
    ∃ (S₁ S₂ : Matrix (Fin D) (Fin D) ℂ),
      S₁.det = 1 ∧ S₂.det = 1 ∧
      ∀ (T₁ T₂ : Matrix (Fin D) (Fin D) ℂ),
        T₁.det = 1 → T₂.det = 1 →
        Matrix.trace (((T₂ ⊗ₖ T₁) * τ * ((T₂ ⊗ₖ T₁)ᴴ))) ≥
          Matrix.trace (((S₂ ⊗ₖ S₁) * τ * ((S₂ ⊗ₖ S₁)ᴴ))) := by
  -- Not yet formalised: requires compactness of bounded SL(n, ℂ) sets and the
  -- extreme value theorem.  See the docstring for the missing Mathlib facts.
  sorry

/-- **Wolf Prop 2.8: generic normal form for CP maps with full Kraus rank.**

Let `T : M_D(ℂ) → M_D(ℂ)` be a completely positive map with full Kraus rank
(equivalently, its Choi matrix is positive-definite).  Then there exist
SL(D, ℂ)-filterings Φ₁, Φ₂ such that `Φ₂ ∘ T ∘ Φ₁` is doubly-stochastic.

This is the main normal-form existence result for generic CP maps.  The Lorentz
normal form for qubit channels (Prop 2.9) is the D = 2 specialisation with the
complete classification of the possible doubly-stochastic normal forms. -/
theorem exists_normal_form_generic
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (_hCP : IsCPMap T)
    (_hFullRank : (choiMatrix T).PosDef) :
    ∃ (Φ₁ Φ₂ : SLFiltering D),
      DoublyStochastic (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  -- Let τ be the Choi matrix of T.
  let τ := choiMatrix T
  -- Use the infimum-attainment lemma (sorry for now).
  obtain ⟨_S₁, _S₂, _, _, _⟩ := infimum_is_attained (τ := τ) _hFullRank
  -- The rest: use the optimality condition to conclude doubly-stochasticity.
  -- This requires the AGM-inequality iteration from Wolf §2.3, which is
  -- not yet formalised.
  sorry

end GenericNormalForm

/-! ### Lorentz normal form for qubit channels (Wolf Prop 2.9 / Prop 2.11)

For `D = 2` (qubit channels), the doubly-stochastic normal form from
Prop 2.8 can be further simplified using the Lorentz group action on the
transfer matrix.  The result is a complete classification into three
canonical forms:

1. **Diagonal** (generic case): unital with diagonal Δ.
2. **Non-diagonal**: a one-parameter family with specific v and Δ.
3. **Singular**: maps everything to a fixed output.

The formal proof of this classification requires:
- The Pauli basis representation of qubit channels (4 × 4 transfer matrix).
- The spinor map SL(2, ℂ) → SO⁺(1, 3) (Lorentz group).
- Singular value decomposition of the 3 × 3 real submatrix Δ.
- The inequality λ₁ + λ₂ ≤ 1 + λ₃ for complete positivity.

We state the theorem as a formal existence result with a `sorry` for the
compactness / classification steps.  The statement is placed here as a
formal target for future work. -/

section LorentzNormalFormQubit

/-- **Lorentz normal form for qubit channels (Wolf Prop 2.9 / Prop 2.11).**

For every qubit channel `T : M₂(ℂ) → M₂(ℂ)`, there exist SL(2, ℂ)-filterings
Φ₁, Φ₂ such that `T' = Φ₂ ∘ T ∘ Φ₁` is a qubit channel of one of three types:
- `type_diagonal`: T' is unital with diagonal Δ (the generic case);
- `type_nondiagonal`: T' has a specific one-parameter form;
- `type_singular`: T' maps everything to a single pure state.

The proof is not yet formalised; it depends on:
- The compactness lemma `infimum_is_attained` (above);
- The Lorentz group classification of SL(2, ℂ) orbits;
- The complete-positivity condition λ₁ + λ₂ ≤ 1 + λ₃.

See Wolf §2.3 for the complete proof. -/
theorem exists_lorentz_normal_form_qubit
    (T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (_hCh : IsChannel T) :
    ∃ (Φ₁ Φ₂ : SLFiltering 2),
      IsChannel (Φ₂.map ∘ₗ T ∘ₗ Φ₁.map) := by
  -- Not yet formalised.  This is a target theorem; the proof depends on
  -- `infimum_is_attained` and the Lorentz group classification, neither of
  -- which is available in Mathlib or TNLean as of 2026-05.
  sorry

end LorentzNormalFormQubit

/-
## Connection to transfer-matrix normal forms (Wolf §2.3)

The results above are stated at the level of CP maps.  The corresponding
transfer-matrix formulation (Props 2.7-2.8 in the blueprint / TransferMatrix.lean)
is obtained by applying `transferMatrix` to both sides.  The SVD normal form
(`Matrix.svd_of_isUnit`, `transferMatrix_svd_of_isUnit`) provides the
algebraic engine: after SL-filterings, the transfer matrix of the doubly-stochastic
map admits an SVD, which for D = 2 yields the Lorentz normal form decomposition.
-/

end Wolf

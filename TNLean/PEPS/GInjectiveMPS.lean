/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDelta
import TNLean.MPS.Core.Blocking
import TNLean.PEPS.GInjective

/-!
# G-injective matrix product states and stability under concatenation

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 4,
`Papers/1001.3807/paper_v3.tex`:

* the map `𝒫(A) = ∑_{iαβ} A^i_{αβ} |i⟩⟨α,β|` from the virtual to the physical system,
  lines 501–510 (equation `eq:P-of-B`);
* Definition 4.2 (`def:Ug-inj`), lines 893–910: for a unitary representation `U_g` of a finite
  group, an MPS tensor `A` is `G`-injective if (i) `U_g A^i U_g† = A^i` for all `i` and `g`, and
  (ii) `𝒫(A)` has a left inverse on the commutant `𝒮 = {X | [X, U_g] = 0}`,
  `𝒫⁻¹(A) 𝒫(A) = 𝟙|_𝒮`;
* Lemma 4.7 (stability under concatenation), lines 1033–1063: if `A` and `B` are `G`-injective,
  then `C^{ij} = A^i B^j` is `G`-injective, with the left inverse of equation `eq:noninj:linv`
  obtained by joining the left inverses of `A` and `B` through the operator `Δ` of Lemma 4.4.

**Formalized here.** The bond space is a finite-dimensional complex vector space `V` carrying a
representation `ρ` of `G`, an MPS tensor is a family `A : ι → End V`, and the virtual system of
one site is `End V`, on which `G` acts by conjugation (`Representation.linHom ρ ρ`). The virtual
vector `∑ x_{αβ} |α,β⟩` is identified with the operator `X = ∑ x_{αβ} |β⟩⟨α|`, so that
`𝒫(A) X = ∑_i tr[A^i X] |i⟩` (`TNLean.PEPS.mpsSiteMap`). `G`-injectivity of an MPS tensor is the
general predicate `TNLean.PEPS.IsGInjective (linHom ρ ρ) (mpsSiteMap A)`;
`isGInjective_mpsSiteMap_iff` shows that it is exactly Definition 4.2. Lemma 4.7 is
`IsGInjective.mpsSiteMap_concatTensor`, with the explicit left inverse
`concatLeftInverse` of `eq:noninj:linv` and its left-inverse identity
`concatLeftInverse_comp_mpsSiteMap`. Words of any positive length and the blocked tensors
`MPSTensor.blockTensor A L` are `G`-injective as corollaries.

The source writes `U_g†`; for a unitary representation this is `ρ(g⁻¹)`, which is the form
stated here. No unitarity is used, and no semi-regularity: the source needs it only from
Theorem 4.12 on.

## Main definitions

* `TNLean.PEPS.mpsSiteMap`: the map `𝒫(A)` of an MPS tensor.
* `TNLean.PEPS.concatTensor`: the concatenated tensor `C^{ij} = A^i B^j`.
* `TNLean.PEPS.concatLeftInverse`: the left inverse of `eq:noninj:linv`.
* `TNLean.PEPS.wordTensor`: the tensor of words of a fixed length.

## Main results

* `TNLean.PEPS.isGInjective_mpsSiteMap_iff`: Definition 4.2 in the source's form.
* `TNLean.PEPS.concatLeftInverse_comp_mpsSiteMap`: the left inverse of the concatenation.
* `TNLean.PEPS.IsGInjective.mpsSiteMap_concatTensor`: Lemma 4.7.
* `TNLean.PEPS.IsGInjective.mpsSiteMap_wordTensor`,
  `MPSTensor.isGInjective_mpsSiteMap_blockTensor`: blocked tensors of a `G`-injective tensor.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation

namespace TNLean
namespace PEPS

section SiteMap

variable {G V ι κ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 501–510
(equation `eq:P-of-B`). The map `𝒫(A) = ∑_{iαβ} A^i_{αβ} |i⟩⟨α,β|` of an MPS tensor
`A : ι → End V`, from the virtual system `End V` of one site to the physical system: with the
virtual vector `∑ x_{αβ} |α,β⟩` identified with the operator `X = ∑ x_{αβ} |β⟩⟨α|`, it is
`X ↦ ∑_i tr[A^i X] |i⟩`. -/
noncomputable def mpsSiteMap (A : ι → Module.End ℂ V) : Module.End ℂ V →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun i => LinearMap.trace ℂ V ∘ₗ LinearMap.mulLeft ℂ (A i)

@[simp]
theorem mpsSiteMap_apply (A : ι → Module.End ℂ V) (X : Module.End ℂ V) (i : ι) :
    mpsSiteMap A X i = LinearMap.trace ℂ V (A i * X) :=
  rfl

/-- Conjugating the virtual operator conjugates the tensor the other way:
`𝒫(A)(U_g X U_g⁻¹) = 𝒫(U_g⁻¹ A U_g)(X)`. -/
theorem mpsSiteMap_comp_linHom (ρ : Representation ℂ G V) (A : ι → Module.End ℂ V) (g : G) :
    mpsSiteMap A ∘ₗ linHom ρ ρ g = mpsSiteMap fun i => ρ g⁻¹ * A i * ρ g := by
  refine LinearMap.ext fun X => funext fun i => ?_
  simp only [LinearMap.comp_apply, mpsSiteMap_apply, linHom_apply, ← Module.End.mul_eq_comp]
  rw [← mul_assoc, ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc, ← mul_assoc]

omit [Module ℂ V] in
/-- An operator composed with a rank-one operator is rank one: `M ∘ (v ⊗ f) = (M v) ⊗ f`. -/
theorem comp_smulRight_dual [Module ℂ V] (M : Module.End ℂ V) (f : Module.Dual ℂ V) (v : V) :
    M ∘ₗ f.smulRight v = f.smulRight (M v) :=
  LinearMap.ext fun w => by simp

omit [Module ℂ V] in
/-- Two operators with the same Hilbert–Schmidt pairings `tr[M X] = tr[N X]` against every `X`
are equal. -/
theorem eq_of_forall_trace_mul_eq [Module ℂ V] [FiniteDimensional ℂ V]
    {M N : Module.End ℂ V}
    (h : ∀ X : Module.End ℂ V, LinearMap.trace ℂ V (M * X) = LinearMap.trace ℂ V (N * X)) :
    M = N := by
  refine LinearMap.ext fun v => sub_eq_zero.1 ?_
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (M v - N v)).1 fun f => ?_
  have hf := h (f.smulRight v)
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, comp_smulRight_dual,
    comp_smulRight_dual, LinearMap.trace_smulRight, LinearMap.trace_smulRight] at hf
  rw [map_sub, hf, sub_self]

/-- Bridge: arXiv:1001.3807, Definition `def:Ug-inj` (i), `Papers/1001.3807/paper_v3.tex`
line 897. The map `𝒫(A)` is invariant under the conjugation action exactly when every
`A^i` commutes with the representation, `U_g A^i U_g⁻¹ = A^i`. -/
theorem mpsSiteMap_comp_linHom_eq_iff [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (A : ι → Module.End ℂ V) :
    (∀ g, mpsSiteMap A ∘ₗ linHom ρ ρ g = mpsSiteMap A) ↔
      ∀ g i, ρ g * A i * ρ g⁻¹ = A i := by
  have hconj : ∀ (g : G) (M : Module.End ℂ V), ρ g⁻¹ * (ρ g * M * ρ g⁻¹) * ρ g = M := by
    intro g M
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  constructor
  · intro h g i
    have hg := h g⁻¹
    rw [mpsSiteMap_comp_linHom, inv_inv] at hg
    refine eq_of_forall_trace_mul_eq fun X => ?_
    exact congr_fun (LinearMap.congr_fun hg X) i
  · intro h g
    rw [mpsSiteMap_comp_linHom]
    congr 1
    funext i
    conv_rhs => rw [← hconj g (A i), h g i]

/-- Bridge: arXiv:1001.3807, Definition `def:Ug-inj`, `Papers/1001.3807/paper_v3.tex`
lines 893–910. `G`-injectivity of the map `𝒫(A)` for the conjugation action on the virtual
system is the source's definition: (i) `U_g A^i U_g⁻¹ = A^i`, and (ii) `𝒫(A)` has a left inverse
on the commutant `𝒮 = {X | [X, U_g] = 0}` (equations `eq:mpssym:symspace` and
`eq:noninj-linv-eq`). For a unitary representation `U_g⁻¹ = U_g†`. -/
theorem isGInjective_mpsSiteMap_iff [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (A : ι → Module.End ℂ V) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap A) ↔
      (∀ g i, ρ g * A i * ρ g⁻¹ = A i) ∧
        ∃ L : (ι → ℂ) →ₗ[ℂ] Module.End ℂ V,
          ∀ X : Module.End ℂ V, (∀ g, ρ g * X = X * ρ g) → L (mpsSiteMap A X) = X := by
  have hS : ∀ X : Module.End ℂ V,
      X ∈ (linHom ρ ρ).invariants ↔ ∀ g, ρ g * X = X * ρ g := fun X => by
    rw [mem_invariants_linHom_iff]
    rfl
  rw [← mpsSiteMap_comp_linHom_eq_iff]
  constructor
  · rintro ⟨hinv, hinj⟩
    refine ⟨hinv, ?_⟩
    have hker : LinearMap.ker (mpsSiteMap A ∘ₗ (linHom ρ ρ).invariants.subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      exact Subtype.ext (hinj x.1 x.2 hx)
    obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective _ hker
    refine ⟨(linHom ρ ρ).invariants.subtype ∘ₗ L', fun X hX => ?_⟩
    have h := LinearMap.congr_fun hL' ⟨X, (hS X).2 hX⟩
    simpa using congrArg Subtype.val h
  · rintro ⟨hinv, L, hL⟩
    refine ⟨hinv, fun X hX h0 => ?_⟩
    rw [← hL X ((hS X).1 hX), h0, map_zero]

/-- A reindexing of the physical index preserves `G`-injectivity of `𝒫(A)`. -/
theorem IsGInjective.mpsSiteMap_reindex {ρ : Representation ℂ G V} {A : ι → Module.End ℂ V}
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A)) (e : κ ≃ ι) {A' : κ → Module.End ℂ V}
    (hA' : ∀ k, A' k = A (e k)) : IsGInjective (linHom ρ ρ) (mpsSiteMap A') := by
  refine ⟨fun g => LinearMap.ext fun X => funext fun k => ?_, fun X hX h0 => ?_⟩
  · simpa [hA'] using congr_fun (LinearMap.congr_fun (hA.invariant g) X) (e k)
  · refine hA.injOn_invariants X hX (funext fun i => ?_)
    simpa [hA'] using congr_fun h0 (e.symm i)

/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1036–1038.
The tensor `C^{ij} = A^i B^j` obtained by concatenating two MPS tensors. -/
def concatTensor (A : ι → Module.End ℂ V) (B : κ → Module.End ℂ V) :
    ι × κ → Module.End ℂ V :=
  fun p => A p.1 * B p.2

@[simp]
theorem concatTensor_apply (A : ι → Module.End ℂ V) (B : κ → Module.End ℂ V) (p : ι × κ) :
    concatTensor A B p = A p.1 * B p.2 :=
  rfl

/-- The tensor of words of length `n`: `w ↦ A^{w_0} A^{w_1} ⋯ A^{w_{n-1}}`, the tensor obtained
by blocking `n` sites. -/
def wordTensor (A : ι → Module.End ℂ V) (n : ℕ) : (Fin n → ι) → Module.End ℂ V :=
  fun w => (List.ofFn fun k => A (w k)).prod

end SiteMap

section Concatenation

variable {G V ι κ : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1038–1044
(equation `eq:noninj:linv`). The left inverse `C⁻¹` of `𝒫(C)` for `C^{ij} = A^i B^j`, built from
left inverses `L_A`, `L_B` of `𝒫(A)`, `𝒫(B)` by joining them through `Δ`:
`C⁻¹ |ij⟩ = |G| L_B|j⟩ Δ L_A|i⟩`. The factor `|G|` is the normalization the source omits in
diagrams (line 919). -/
noncomputable def concatLeftInverse (ρ : Representation ℂ G V)
    (LA : (ι → ℂ) →ₗ[ℂ] Module.End ℂ V) (LB : (κ → ℂ) →ₗ[ℂ] Module.End ℂ V) :
    (ι × κ → ℂ) →ₗ[ℂ] Module.End ℂ V :=
  (Fintype.card G : ℂ) • ∑ p : ι × κ, (LinearMap.proj p).smulRight
    (LB (Pi.single p.2 1) * deltaOperator ρ * LA (Pi.single p.1 1))

omit [FiniteDimensional ℂ V] in
/-- A linear map on the physical system of `A`, applied to `𝒫(A) X`, is
`∑_i tr[A^i X] L|i⟩`. -/
theorem apply_mpsSiteMap (L : (ι → ℂ) →ₗ[ℂ] Module.End ℂ V) (A : ι → Module.End ℂ V)
    (X : Module.End ℂ V) :
    L (mpsSiteMap A X) = ∑ i, LinearMap.trace ℂ V (A i * X) • L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

omit [FiniteDimensional ℂ V] [DecidableEq ι] [DecidableEq κ] in
/-- The twirl in multiplicative notation, `σ(X) = |G|⁻¹ ∑_g U_g X U_g⁻¹`. -/
theorem averageMap_linHom_apply_mul (ρ : Representation ℂ G V) (X : Module.End ℂ V) :
    (linHom ρ ρ).averageMap X = ⅟(Fintype.card G : ℂ) • ∑ g, ρ g * X * ρ g⁻¹ := by
  rw [averageMap_linHom_apply]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]

omit [DecidableEq ι] in
/-- Source: arXiv:1001.3807, proof of Lemma 4.7, `Papers/1001.3807/paper_v3.tex`
lines 1053–1061 (the first equality of the displayed diagram). If `L_B 𝒫(B) = σ`, then for every
operator `M`, `∑_j L_B|j⟩ M B^j = |G|⁻¹ ∑_h tr[U_h⁻¹ M] U_h`. -/
theorem sum_leftInverse_mul_mul (ρ : Representation ℂ G V) {B : κ → Module.End ℂ V}
    {LB : (κ → ℂ) →ₗ[ℂ] Module.End ℂ V} (hB : LB ∘ₗ mpsSiteMap B = (linHom ρ ρ).averageMap)
    (M : Module.End ℂ V) :
    ∑ j, LB (Pi.single j 1) * M * B j =
      ⅟(Fintype.card G : ℂ) • ∑ h, LinearMap.trace ℂ V (ρ h⁻¹ * M) • ρ h := by
  let b := Module.finBasis ℂ V
  -- The partial sums against the coordinate functionals of `b` are twirls of rank-one operators.
  have hcoord : ∀ (w : V) (k : Fin (Module.finrank ℂ V)),
      ∑ j, b.repr (B j w) k • LB (Pi.single j 1) =
        (linHom ρ ρ).averageMap ((b.coord k).smulRight w) := by
    intro w k
    rw [← hB, LinearMap.comp_apply, apply_mpsSiteMap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Module.End.mul_eq_comp, comp_smulRight_dual, LinearMap.trace_smulRight,
      Basis.coord_apply]
  have htrace : ∀ N : Module.End ℂ V,
      LinearMap.trace ℂ V N = ∑ k, b.repr (N (b k)) k := by
    intro N
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    simp [LinearMap.toMatrix_apply]
  refine LinearMap.ext fun w => ?_
  calc (∑ j, LB (Pi.single j 1) * M * B j) w
      = ∑ k, (∑ j, b.repr (B j w) k • LB (Pi.single j 1)) (M (b k)) := by
        simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hw := b.sum_repr (B j w)
        conv_lhs => rw [← hw]
        rw [map_sum, map_sum]
        simp only [map_smul]
    _ = ∑ k, ⅟(Fintype.card G : ℂ) • ∑ h, b.repr (ρ h⁻¹ (M (b k))) k • ρ h w := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcoord, averageMap_linHom_apply_mul]
        simp [Module.End.mul_apply, Basis.coord_apply]
    _ = (⅟(Fintype.card G : ℂ) • ∑ h, LinearMap.trace ℂ V (ρ h⁻¹ * M) • ρ h) w := by
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, htrace, Module.End.mul_apply,
          Finset.sum_smul, ← Finset.smul_sum]
        rw [Finset.sum_comm]

/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1036–1063
(equation `eq:noninj:linv` and the diagram on lines 1057–1061). If `L_A 𝒫(A) = σ` and
`L_B 𝒫(B) = σ`, with `σ` the twirl onto the commutant, then the operator `C⁻¹` of
`eq:noninj:linv` satisfies `C⁻¹ 𝒫(C) = σ` for `C^{ij} = A^i B^j`. The proof uses Lemma 4.4
(`Representation.sum_trace_inv_comp_deltaOperator_comp_smul`). -/
theorem concatLeftInverse_comp_mpsSiteMap (ρ : Representation ℂ G V)
    {A : ι → Module.End ℂ V} {B : κ → Module.End ℂ V}
    {LA : (ι → ℂ) →ₗ[ℂ] Module.End ℂ V} {LB : (κ → ℂ) →ₗ[ℂ] Module.End ℂ V}
    (hA : LA ∘ₗ mpsSiteMap A = (linHom ρ ρ).averageMap)
    (hB : LB ∘ₗ mpsSiteMap B = (linHom ρ ρ).averageMap) :
    concatLeftInverse ρ LA LB ∘ₗ mpsSiteMap (concatTensor A B) = (linHom ρ ρ).averageMap := by
  have hG : (Fintype.card G : ℂ) * ⅟(Fintype.card G : ℂ) = 1 := mul_invOf_self _
  have hA' : ∀ Y, ∑ i, LinearMap.trace ℂ V (A i * Y) • LA (Pi.single i 1) =
      (linHom ρ ρ).averageMap Y := fun Y => by
    rw [← apply_mpsSiteMap, ← LinearMap.comp_apply, hA]
  -- Lemma 4.4 turns each inner sum into `U_g`.
  have h44 : ∀ g, ∑ j, LB (Pi.single j 1) * (deltaOperator ρ * ρ g) * B j =
      ⅟(Fintype.card G : ℂ) • ρ g := fun g => by
    rw [sum_leftInverse_mul_mul ρ hB]
    congr 1
    simpa only [Module.End.mul_eq_comp, LinearMap.comp_assoc] using
      sum_trace_inv_comp_deltaOperator_comp_smul ρ g
  refine LinearMap.ext fun X => ?_
  calc concatLeftInverse ρ LA LB (mpsSiteMap (concatTensor A B) X)
      = (Fintype.card G : ℂ) • ∑ j, LB (Pi.single j 1) * deltaOperator ρ *
          ∑ i, LinearMap.trace ℂ V (A i * (B j * X)) • LA (Pi.single i 1) := by
        simp only [concatLeftInverse, LinearMap.smul_apply, LinearMap.sum_apply,
          LinearMap.smulRight_apply, LinearMap.proj_apply, mpsSiteMap_apply, concatTensor_apply,
          Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm, mul_assoc]
        rw [Finset.sum_comm]
    _ = (Fintype.card G : ℂ) • ∑ j, LB (Pi.single j 1) * deltaOperator ρ *
          (⅟(Fintype.card G : ℂ) • ∑ g, ρ g * (B j * X) * ρ g⁻¹) := by
        simp only [hA', averageMap_linHom_apply_mul]
    _ = ∑ g, (∑ j, LB (Pi.single j 1) * (deltaOperator ρ * ρ g) * B j) * X * ρ g⁻¹ := by
        simp only [mul_smul_comm, ← Finset.smul_sum, smul_smul, hG, one_smul, Finset.mul_sum,
          Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
    _ = (linHom ρ ρ).averageMap X := by
        simp only [h44, averageMap_linHom_apply_mul, smul_mul_assoc, ← Finset.smul_sum]

end Concatenation

section Finite

variable {G V ι κ : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [Finite ι] [Finite κ]

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Source: arXiv:1001.3807, Lemma 4.7 (stability under concatenation),
`Papers/1001.3807/paper_v3.tex` lines 1036–1063. If the MPS tensors `A` and `B` are
`G`-injective for the same representation, so is `C^{ij} = A^i B^j`. -/
theorem IsGInjective.mpsSiteMap_concatTensor {ρ : Representation ℂ G V}
    {A : ι → Module.End ℂ V} {B : κ → Module.End ℂ V}
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A))
    (hB : IsGInjective (linHom ρ ρ) (mpsSiteMap B)) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap (concatTensor A B)) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  obtain ⟨hAi, LA, hLA⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hA
  obtain ⟨hBi, LB, hLB⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hB
  rw [mpsSiteMap_comp_linHom_eq_iff] at hAi hBi
  refine (isGInjective_iff_exists_leftInverse _ _).2
    ⟨?_, _, concatLeftInverse_comp_mpsSiteMap ρ hLA hLB⟩
  rw [mpsSiteMap_comp_linHom_eq_iff]
  intro g p
  calc ρ g * (A p.1 * B p.2) * ρ g⁻¹
      = (ρ g * A p.1 * ρ g⁻¹) * (ρ g * B p.2 * ρ g⁻¹) := by
        have hinv : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        simp only [mul_assoc]
        rw [← mul_assoc (ρ g⁻¹) (ρ g), hinv, one_mul]
    _ = A p.1 * B p.2 := by rw [hAi, hBi]

omit [Finite κ] in
/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1036–1063,
iterated. Blocking any positive number of sites of a `G`-injective tensor gives a
`G`-injective tensor. -/
theorem IsGInjective.mpsSiteMap_wordTensor {ρ : Representation ℂ G V}
    {A : ι → Module.End ℂ V} (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A)) (n : ℕ) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap (wordTensor A (n + 1))) := by
  have := Fintype.ofFinite ι
  induction n with
  | zero =>
    exact hA.mpsSiteMap_reindex (Equiv.funUnique (Fin 1) ι) fun w => by
      simp [wordTensor]
  | succ n ih =>
    exact (hA.mpsSiteMap_concatTensor ih).mpsSiteMap_reindex (Fin.consEquiv _).symm fun w => by
      simp [wordTensor, List.ofFn_succ, Fin.consEquiv, Fin.tail]

end Finite

end PEPS
end TNLean

namespace MPSTensor

open TNLean.PEPS

variable {G : Type*} [Group G] [Finite G] {d D : ℕ}

/-- A product of the matrices of a word, as an operator, is the product of the operators. -/
theorem toLin'_evalWord (A : MPSTensor d D) (w : List (Fin d)) :
    Matrix.toLin' (Kraus.evalWord A w) = (w.map fun i => Matrix.toLin' (A i)).prod := by
  induction w with
  | nil => simp [Kraus.evalWord, Module.End.one_eq_id]
  | cons i w ih => simp [Kraus.evalWord, Matrix.toLin'_mul, ih, Module.End.mul_eq_comp]

/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1036–1063,
iterated. If the MPS tensor `A` is `G`-injective for a representation `ρ` on its bond space, so
is the blocked tensor `blockTensor A L` for every positive `L`. -/
theorem isGInjective_mpsSiteMap_blockTensor (ρ : Representation ℂ G (Fin D → ℂ))
    (A : MPSTensor d D)
    (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap fun i => Matrix.toLin' (A i)))
    {L : ℕ} (hL : 0 < L) :
    IsGInjective (linHom ρ ρ) (mpsSiteMap fun I => Matrix.toLin' (blockTensor A L I)) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  exact (hA.mpsSiteMap_wordTensor n).mpsSiteMap_reindex (decodeBlockEquiv d (n + 1))
    fun I => by
      simp only [Kraus.blockTensor, Kraus.wordOfBlock, toLin'_evalWord, List.map_ofFn,
        wordTensor, decodeBlockEquiv_apply]
      rfl

end MPSTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GInjectiveMPS

/-!
# Intersection and closure properties of G-injective matrix product states

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 4, "Parent
Hamiltonians", `Papers/1001.3807/paper_v3.tex`:

* Theorem 4.8 (`thm:noninj:intersection`), lines 1084–1123. For `G`-injective `A` and `B`
  (figures `figs2/trAAM`, `figs2/trNAA`, `figs2/trAAA`),
  `{tr[A^i B^j M^k] | M} ∩ {tr[N^i B^j A^k] | N} = {tr[A^i B^j A^k X] | X}`, where `M` and `N`
  are three-leg tensors (one physical and two virtual legs) and `X` is an operator on the bond.
  The proof twirls `M`, `N`, `X` (figures `figs2/trAAMsymM`, `figs2/twirledM`, lines 1098–1108)
  and applies the left inverses (figure `figs2/prove-N-eq-BX-sym`, lines 1112–1122).
* Theorem 4.9 (`thm:noninj:closure`), lines 1124–1162. For `G`-injective `A` and `B`
  (figures `figs2/trMAC`, `figs2/trNAC`, `figs2/trAC`),
  `{tr[B^i A^j M] | M} ∩ {tr[B^i N A^j] | N} = {∑_g λ_g tr[B^i A^j U_g] | λ_g}`: the operator `M`
  closes the ring on the outer bond, the operator `N` sits on the inner bond between `B` and `A`.
  The proof (figure `figs2/prove-1dsym-closure`, lines 1149–1161) gives
  `λ_g = tr[U_{g⁻¹} N Δ]` for the twirled `N`.

**Formalized here.** In the setting of `TNLean.PEPS.GInjectiveMPS`: a bond space `V` carrying a
representation `ρ` of a finite group, MPS tensors `A : ι → End V`, `B : κ → End V`, and
`G`-injectivity `IsGInjective (linHom ρ ρ) (mpsSiteMap A)`. The vectors on the right-hand sides
are the images of the existing map `mpsSiteMap` of concatenated tensors: `tr[A^i B^j A^k X]` is
`mpsSiteMap (concatTensor (concatTensor A B) A) X`, and `tr[B^i A^j U_g]` is
`mpsSiteMap (concatTensor B A) (ρ g)`, the two-site MPS with closure `U_g` of
Definition 4.10 (lines 1165–1176). Theorem 4.8 is `IsGInjective.intersection_property` and
Theorem 4.9 is `IsGInjective.closure_property`, with the explicit coefficients
`λ_g = tr[U_{g⁻¹} σ(N) Δ]` in `IsGInjective.eq_sum_of_closure`. The hypotheses are
`G`-injectivity of `A` and `B` for the same representation, as in the source; semi-regularity is
not used, and no unitarity is needed (`U_g†` is written `ρ(g⁻¹)`). The normalization factors
`|G|` that the source drops in diagrams (line 936) are kept, and the stated coefficients are
exact.

The proofs follow the source's route (twirl, then apply the left inverse of the concatenated
tensor `C^{jk} = B^j A^k` from Lemma 4.7), but evaluate the left inverse directly:
`σ(N^i) = X A^i` with `X = |G| ∑_k L_A|k⟩ Δ σ(M^k)` for Theorem 4.8, and
`σ(M) = ∑_h tr[U_h⁻¹ Δ σ(N)] U_h` for Theorem 4.9.

## Main results

* `TNLean.PEPS.mpsSiteMap_averageMap`: the twirl lemma of lines 1098–1108.
* `TNLean.PEPS.IsGInjective.intersection_property`: Theorem 4.8.
* `TNLean.PEPS.IsGInjective.eq_sum_of_closure`: the coefficients of Theorem 4.9.
* `TNLean.PEPS.IsGInjective.closure_property`: Theorem 4.9.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap Representation

namespace TNLean
namespace PEPS

variable {G V ι κ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

attribute [local instance] Representation.invertibleFintypeCardComplex

/-- Source: arXiv:1001.3807, proof of Theorem 4.8, `Papers/1001.3807/paper_v3.tex`
lines 1098–1108 (figures `figs2/trAAMsymM` and `figs2/twirledM`). If a tensor `C` is invariant,
`U_g C^i U_g⁻¹ = C^i`, then an operator closing it may be replaced by its twirl
`σ(X) = |G|⁻¹ ∑_g U_g X U_g⁻¹` without changing the vector: `𝒫(C) σ(X) = 𝒫(C) X`. -/
theorem mpsSiteMap_averageMap [Fintype G] [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {C : ι → Module.End ℂ V} (hC : ∀ g i, ρ g * C i * ρ g⁻¹ = C i) (X : Module.End ℂ V) :
    mpsSiteMap C ((linHom ρ ρ).averageMap X) = mpsSiteMap C X :=
  apply_averageMap_of_forall_comp_eq ((mpsSiteMap_comp_linHom_eq_iff ρ C).2 hC) X

/-- The twirl commutes with right multiplication by an invariant operator:
`σ(Y Z) = σ(Y) Z` when `U_g Z U_g⁻¹ = Z` for every `g`. -/
theorem averageMap_mul_of_conj_eq [Fintype G] (ρ : Representation ℂ G V) {Z : Module.End ℂ V}
    (hZ : ∀ g, ρ g * Z * ρ g⁻¹ = Z) (Y : Module.End ℂ V) :
    (linHom ρ ρ).averageMap (Y * Z) = (linHom ρ ρ).averageMap Y * Z := by
  rw [averageMap_linHom_apply_mul, averageMap_linHom_apply_mul, smul_mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  have hinv : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  conv_rhs => rw [← hZ g]
  simp only [mul_assoc]
  rw [← mul_assoc (ρ g⁻¹), hinv, one_mul]

/-- Source: arXiv:1001.3807, Lemma 4.7, `Papers/1001.3807/paper_v3.tex` lines 1038–1044
(equation `eq:noninj:linv`), evaluated on a vector of traces. For the left inverse
`L_C |j,k⟩ = |G| L_A|k⟩ Δ L_B|j⟩` of the concatenation `C^{jk} = B^j A^k`, applied to the vector
`(j, k) ↦ tr[B^j Y_k]`, the sum over `j` collapses to the twirl:
`L_C (tr[B^j Y_k])_{jk} = |G| ∑_k L_A|k⟩ Δ σ(Y_k)`. -/
theorem concatLeftInverse_apply_trace_mul [Fintype G] [FiniteDimensional ℂ V] [Fintype ι]
    [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : Representation ℂ G V) {B : κ → Module.End ℂ V}
    (LA : (ι → ℂ) →ₗ[ℂ] Module.End ℂ V) {LB : (κ → ℂ) →ₗ[ℂ] Module.End ℂ V}
    (hB : LB ∘ₗ mpsSiteMap B = (linHom ρ ρ).averageMap) (Y : ι → Module.End ℂ V) :
    concatLeftInverse ρ LB LA (fun p => LinearMap.trace ℂ V (B p.1 * Y p.2)) =
      (Fintype.card G : ℂ) • ∑ k, LA (Pi.single k 1) * deltaOperator ρ *
        (linHom ρ ρ).averageMap (Y k) := by
  have hσ : ∀ W, ∑ j, LinearMap.trace ℂ V (B j * W) • LB (Pi.single j 1) =
      (linHom ρ ρ).averageMap W := fun W => by
    rw [← apply_mpsSiteMap, ← LinearMap.comp_apply, hB]
  simp only [concatLeftInverse, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hσ, Finset.mul_sum]
  simp only [mul_smul_comm]

section Theorems

variable {ρ : Representation ℂ G V} {A : ι → Module.End ℂ V} {B : κ → Module.End ℂ V}

/-- An operator commuting with the representation commutes with every `U_g`, in the form
`U_g Z = Z U_g`. -/
theorem mul_comm_of_conj_eq {Z : Module.End ℂ V} (hZ : ∀ g, ρ g * Z * ρ g⁻¹ = Z) (g : G) :
    ρ g * Z = Z * ρ g := by
  conv_rhs => rw [← hZ g]
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

/-- Source: arXiv:1001.3807, Theorem 4.8 (intersection property, `thm:noninj:intersection`),
`Papers/1001.3807/paper_v3.tex` lines 1084–1123, figures `figs2/trAAM`, `figs2/trNAA` and
`figs2/trAAA`. For `G`-injective MPS tensors `A` and `B` with the same representation,
`{tr[A^i B^j M^k] | M} ∩ {tr[N^i B^j A^k] | N} = {tr[A^i B^j A^k X] | X}`,
where `M` and `N` range over all three-leg tensors `ι → End V` and `X` over all operators on the
bond. The right-hand side is the image of `𝒫(ABA)`. -/
theorem IsGInjective.intersection_property [Finite G] [FiniteDimensional ℂ V] [Finite ι]
    [Finite κ] (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A))
    (hB : IsGInjective (linHom ρ ρ) (mpsSiteMap B)) :
    {ψ : (ι × κ) × ι → ℂ | ∃ M : ι → Module.End ℂ V,
        ∀ i j k, ψ ((i, j), k) = LinearMap.trace ℂ V (A i * B j * M k)} ∩
      {ψ | ∃ N : ι → Module.End ℂ V,
        ∀ i j k, ψ ((i, j), k) = LinearMap.trace ℂ V (N i * B j * A k)} =
      Set.range (mpsSiteMap (concatTensor (concatTensor A B) A)) := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  obtain ⟨hAi, LA, hLA⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hA
  obtain ⟨hBi, LB, hLB⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hB
  rw [mpsSiteMap_comp_linHom_eq_iff] at hAi hBi
  ext ψ
  constructor
  · rintro ⟨⟨M, hM⟩, ⟨N, hN⟩⟩
    set X := (Fintype.card G : ℂ) • ∑ k, LA (Pi.single k 1) * deltaOperator ρ *
      (linHom ρ ρ).averageMap (M k) with hX
    refine ⟨X, funext fun ⟨⟨i, j⟩, k⟩ => ?_⟩
    -- The left inverse of `C^{jk} = B^j A^k` gives `σ(N^i) = X A^i`.
    have hkey : (linHom ρ ρ).averageMap (N i) = X * A i := by
      have h1 := LinearMap.congr_fun (concatLeftInverse_comp_mpsSiteMap ρ hLB hLA) (N i)
      rw [LinearMap.comp_apply] at h1
      have h2 : mpsSiteMap (concatTensor B A) (N i) =
          fun p => LinearMap.trace ℂ V (B p.1 * (M p.2 * A i)) := by
        funext p
        have := (hN i p.1 p.2).symm.trans (hM i p.1 p.2)
        rw [mpsSiteMap_apply, concatTensor_apply, LinearMap.trace_mul_comm ℂ _ (N i),
          ← mul_assoc, this, mul_assoc, LinearMap.trace_mul_comm ℂ (A i), mul_assoc]
      rw [← h1, h2, concatLeftInverse_apply_trace_mul ρ LA hLB fun k => M k * A i, hX]
      simp only [averageMap_mul_of_conj_eq ρ (fun g => hAi g i), smul_mul_assoc,
        Finset.sum_mul, mul_assoc]
    have h3 := congr_fun (mpsSiteMap_averageMap (concatTensor_conj_eq hBi hAi) (N i)) (j, k)
    simp only [mpsSiteMap_apply, concatTensor_apply, hkey] at h3
    symm
    calc ψ ((i, j), k) = LinearMap.trace ℂ V (B j * A k * N i) := by
          rw [hN, mul_assoc, LinearMap.trace_mul_comm]
      _ = LinearMap.trace ℂ V (A i * B j * A k * X) := by
          rw [← h3, ← mul_assoc, LinearMap.trace_mul_comm]
          simp only [mul_assoc]
  · rintro ⟨X, rfl⟩
    refine ⟨⟨fun k => A k * X, fun i j k => by simp [mul_assoc]⟩,
      ⟨fun i => X * A i, fun i j k => ?_⟩⟩
    rw [mpsSiteMap_apply, LinearMap.trace_mul_comm]
    simp only [concatTensor_apply, mul_assoc]

/-- Source: arXiv:1001.3807, proof of Theorem 4.9 (`thm:noninj:closure`),
`Papers/1001.3807/paper_v3.tex` lines 1144–1161, figure `figs2/prove-1dsym-closure`. For
`G`-injective `A` and `B` with the same representation, a vector
`ψ^{ji} = tr[B^j A^i M] = tr[B^j N A^i]` in both sets of Theorem 4.9 is
`ψ = ∑_g λ_g tr[B^j A^i U_g]` with `λ_g = tr[U_{g⁻¹} σ(N) Δ]`, where `σ(N)` is the twirl of `N`.
The source assumes `N` twirled and drops the factors `|G|` (line 936); with the twirl written
out the coefficients are exact. -/
theorem IsGInjective.eq_sum_of_closure [Fintype G] [FiniteDimensional ℂ V] [Finite ι]
    [Finite κ] (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A))
    (hB : IsGInjective (linHom ρ ρ) (mpsSiteMap B)) {ψ : κ × ι → ℂ} {M N : Module.End ℂ V}
    (hM : ψ = mpsSiteMap (concatTensor B A) M)
    (hN : ∀ j i, ψ (j, i) = LinearMap.trace ℂ V (B j * N * A i)) :
    ψ = ∑ g, LinearMap.trace ℂ V (ρ g⁻¹ * (linHom ρ ρ).averageMap N * deltaOperator ρ) •
      mpsSiteMap (concatTensor B A) (ρ g) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  obtain ⟨hAi, LA, hLA⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hA
  obtain ⟨hBi, LB, hLB⟩ := (isGInjective_iff_exists_leftInverse _ _).1 hB
  rw [mpsSiteMap_comp_linHom_eq_iff] at hAi hBi
  set σN := (linHom ρ ρ).averageMap N with hσN
  -- `σ(N)` commutes with the representation.
  have hσNc : ∀ g, ρ g * σN = σN * ρ g := fun g => by
    have h := (mem_invariants_linHom_iff ρ σN).1 ((linHom ρ ρ).averageMap_invariant N) g
    simpa only [Module.End.mul_eq_comp] using h
  -- The left inverse of `C^{ji} = B^j A^i` gives `σ(M) = ∑_h tr[U_h⁻¹ Δ σ(N)] U_h`.
  have hkey : (linHom ρ ρ).averageMap M =
      ∑ h, LinearMap.trace ℂ V (ρ h⁻¹ * (deltaOperator ρ * σN)) • ρ h := by
    have h1 := LinearMap.congr_fun (concatLeftInverse_comp_mpsSiteMap ρ hLB hLA) M
    rw [LinearMap.comp_apply] at h1
    have h2 : mpsSiteMap (concatTensor B A) M =
        fun p => LinearMap.trace ℂ V (B p.1 * (N * A p.2)) := by
      rw [← hM]
      funext p
      rw [hN, mul_assoc]
    rw [← h1, h2, concatLeftInverse_apply_trace_mul ρ LA hLB fun i => N * A i]
    simp only [averageMap_mul_of_conj_eq ρ (fun g => hAi g _), ← hσN]
    simp only [show ∀ i, LA (Pi.single i 1) * deltaOperator ρ * (σN * A i) =
        LA (Pi.single i 1) * (deltaOperator ρ * σN) * A i from fun i => by
          simp only [mul_assoc]]
    rw [sum_leftInverse_mul_mul ρ hLA, smul_smul, mul_invOf_self, one_smul]
  rw [hM, ← mpsSiteMap_averageMap (concatTensor_conj_eq hBi hAi), hkey, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, ← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc, ← hσNc g⁻¹]

/-- Source: arXiv:1001.3807, Theorem 4.9 (closure property, `thm:noninj:closure`),
`Papers/1001.3807/paper_v3.tex` lines 1124–1162, figures `figs2/trMAC`, `figs2/trNAC` and
`figs2/trAC`. For `G`-injective MPS tensors `A` and `B` with the same representation,
`{tr[B^j A^i M] | M} ∩ {tr[B^j N A^i] | N} = {∑_g λ_g tr[B^j A^i U_g] | λ_g}`,
where `M` closes the ring on the outer bond and `N` sits on the bond between `B` and `A`. The
first set is the image of `𝒫(BA)`, and `tr[B^j A^i U_g]` is the two-site MPS `𝒫(BA) U_g` with
closure `U_g` (Definition 4.10, lines 1165–1176). -/
theorem IsGInjective.closure_property [Fintype G] [FiniteDimensional ℂ V] [Finite ι]
    [Finite κ] (hA : IsGInjective (linHom ρ ρ) (mpsSiteMap A))
    (hB : IsGInjective (linHom ρ ρ) (mpsSiteMap B)) :
    Set.range (mpsSiteMap (concatTensor B A)) ∩
      {ψ : κ × ι → ℂ | ∃ N : Module.End ℂ V,
        ∀ j i, ψ (j, i) = LinearMap.trace ℂ V (B j * N * A i)} =
      {ψ | ∃ c : G → ℂ, ψ = ∑ g, c g • mpsSiteMap (concatTensor B A) (ρ g)} := by
  ext ψ
  constructor
  · rintro ⟨⟨M, hM⟩, ⟨N, hN⟩⟩
    exact ⟨_, hA.eq_sum_of_closure hB hM.symm hN⟩
  · rintro ⟨c, rfl⟩
    have hAi := (mpsSiteMap_comp_linHom_eq_iff ρ A).1 hA.invariant
    have hsum : ∑ g, c g • mpsSiteMap (concatTensor B A) (ρ g) =
        mpsSiteMap (concatTensor B A) (∑ g, c g • ρ g) := by
      rw [map_sum]
      simp only [map_smul]
    refine ⟨⟨_, hsum.symm⟩, ∑ g, c g • ρ g, fun j i => ?_⟩
    rw [hsum, mpsSiteMap_apply, concatTensor_apply, mul_assoc, mul_assoc]
    congr 2
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_comm_of_conj_eq (fun h => hAi h i) g]

end Theorems

end PEPS
end TNLean

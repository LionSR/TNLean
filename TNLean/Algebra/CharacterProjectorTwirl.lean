/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.ConjFinite
import TNLean.Algebra.RepresentationDelta

/-!
# Twirled representation operators and isotypic projectors

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), proof of Theorem 4.12,
`Papers/1001.3807/paper_v3.tex` lines 1219–1260. The proof uses three facts about a
representation `U_g` of a finite group, which are formalized here for a finite-dimensional
complex representation `ρ`:

* the closure `U_g` may be replaced by any conjugate `U_h U_g U_h†`, so only its twirl
  `σ(U_g) = |G|⁻¹ ∑_h U_{hgh⁻¹}` matters, and this twirl is a combination of the isotypic
  projectors `Π_i` (lines 1224–1238);
* the projectors `Π_i` of the irreducible representations occurring in `U_g` are linearly
  independent (lines 1240–1255);
* for a semi-regular representation, the operators `U_g` are linearly independent, by
  Lemma 4.6 (`lemma:noninj:semireg-trace-ug-delta`, lines 1015–1029), and hence so are the
  twirls of one representative `U_g` per conjugacy class (lines 1257–1259).

**Formalized here.** The source obtains the first fact from the completeness of the irreducible
characters in the space of class functions. Here it is the explicit formula
`σ(ρ(g)) = ∑_χ (χ(g)/χ(1)) P_χ` (`averageMap_linHom_rep`), proved from Schur's lemma on each
irreducible summand of `ρ`; it avoids the completeness of characters, which Mathlib does not
provide.

## Main results

* `Representation.rep_mul_charProjector`: a character projector of a class function commutes
  with the representation.
* `Representation.averageMap_linHom_rep`: `σ(ρ(g)) = ∑_χ (χ(g)/χ(1)) P_χ`.
* `Representation.linearIndependent_charProjector`: the projectors `P_χ` of the irreducible
  characters of `ρ` are linearly independent.
* `Representation.linearIndependent_of_isSemiRegular`: for a semi-regular representation the
  operators `ρ(g)` are linearly independent.
* `Representation.linearIndependent_averageMap_conjClasses`: for a semi-regular representation
  the twirls of one representative `ρ(g)` per conjugacy class are linearly independent.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

universe u v

open Module LinearMap

namespace Representation

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ G V)

/-- The order of a finite group is invertible in `ℂ`. -/
noncomputable local instance invertibleFintypeCardComplex' : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_pos.ne')

omit [FiniteDimensional ℂ V] in
/-- The character projector of a class function commutes with the representation:
`ρ(h) P_χ = P_χ ρ(h)`. -/
theorem rep_mul_charProjector {χ : G → ℂ} (hχ : ∀ g h, χ (h * g * h⁻¹) = χ g) (h : G) :
    ρ h * charProjector ρ χ = charProjector ρ χ * ρ h := by
  simp only [charProjector, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul,
    ← map_mul]
  congr 1
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  congr 1
  · rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group, hχ]
  · congr 1
    group

omit [Fintype G] [FiniteDimensional ℂ V] in
/-- An irreducible character of `ρ` is a class function. -/
theorem apply_conj_of_mem_irreducibleCharacters {χ : G → ℂ} (hχ : χ ∈ irreducibleCharacters ρ)
    (g h : G) :
    χ (h * g * h⁻¹) = χ g := by
  obtain ⟨S, -, rfl⟩ := hχ
  exact char_conj _ g h

/-- Schur's lemma for the class sum: on an irreducible subrepresentation `S` of `ρ` with
character `χ`, the operator `∑_h ρ(h g h⁻¹)` acts as the scalar `|G| χ(g) / χ(1)`. -/
theorem sum_rep_conj_apply_of_mem (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    (g : G) {v : V} (hv : v ∈ S) :
    ∑ h, ρ (h * g * h⁻¹) v =
      ((Fintype.card G : ℂ) * S.toRepresentation.character g /
        S.toRepresentation.character 1) • v := by
  set τ := S.toRepresentation
  set F : Module.End ℂ S.toSubmodule := ∑ h, τ (h * g * h⁻¹) with hF
  have hcomm : ∀ k : G, F ∘ₗ τ k = τ k ∘ₗ F := by
    intro k
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    simp only [hF, Finset.sum_mul, Finset.mul_sum, ← map_mul]
    refine (Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_).symm
    simp only [Equiv.coe_mulLeft]
    congr 1
    group
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
      (⟨F, hcomm⟩ : IntertwiningMap τ τ)
  have hFc : F = c • (1 : Module.End ℂ S.toSubmodule) := by
    have := congrArg IntertwiningMap.toLinearMap hc
    simp only [IntertwiningMap.algebraMap_apply] at this
    rw [← this]
    rfl
  have htr : (Fintype.card G : ℂ) * τ.character g = c * finrank ℂ S.toSubmodule := by
    have h1 := congrArg (LinearMap.trace ℂ _) hFc
    simp only [hF, map_sum, map_smul, LinearMap.trace_one, smul_eq_mul] at h1
    have h2 : ∑ h, τ.character (h * g * h⁻¹) = c * finrank ℂ S.toSubmodule := h1
    rw [← h2]
    simp only [char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hdim : (finrank ℂ S.toSubmodule : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (finrank_pos_of_isIrreducible τ).ne'
  have hc' : c = (Fintype.card G : ℂ) * τ.character g / τ.character 1 := by
    rw [char_one, htr]
    field_simp
  have happly : ∑ h, ρ (h * g * h⁻¹) v = ((F ⟨v, hv⟩ : S.toSubmodule) : V) := by
    simp only [hF, LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  rw [happly, hFc, ← hc']
  rfl

/-- Source: arXiv:1001.3807, proof of Theorem 4.12, `Papers/1001.3807/paper_v3.tex`
lines 1224–1238. The twirl of `ρ(g)` is a combination of the isotypic projectors:
`σ(ρ(g)) = |G|⁻¹ ∑_h ρ(h g h⁻¹) = ∑_χ (χ(g)/χ(1)) P_χ`, the sum running over the irreducible
characters of `ρ`. The source reaches the same span through the completeness of the characters
in the class functions; here the coefficients are computed by Schur's lemma. -/
theorem averageMap_linHom_rep (g : G) :
    (linHom ρ ρ).averageMap (ρ g) =
      ∑ χ ∈ irreducibleCharacterFinset ρ, (χ g / χ 1) • charProjector ρ χ := by
  classical
  apply linearMap_ext_on_irreducible ρ
  intro S hS v hv
  let := hS
  rw [sum_smul_charProjector_apply_of_mem ρ _ S hv,
    averageMap_linHom_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  have hsum : ∑ h, (ρ h ∘ₗ ρ g ∘ₗ ρ h⁻¹) v = ∑ h, ρ (h * g * h⁻¹) v := by
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  rw [hsum, sum_rep_conj_apply_of_mem ρ S g hv, smul_smul]
  congr 1
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_pos.ne'
  rw [invOf_eq_inv]
  field_simp

/-- Source: arXiv:1001.3807, proof of Theorem 4.12, `Papers/1001.3807/paper_v3.tex`
lines 1240–1255. The isotypic projectors `P_χ` of the irreducible characters `χ` of `ρ` are
linearly independent. The source concludes `μ_i = 0` from `∑_i μ_i Π_i = 0`; here the sum is
evaluated on a nonzero vector of an irreducible subrepresentation with character `χ`. -/
theorem linearIndependent_charProjector :
    LinearIndependent ℂ fun χ : irreducibleCharacterFinset ρ => charProjector ρ χ.1 := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro μ hμ χ
  obtain ⟨S, hS, hSχ⟩ := (mem_irreducibleCharacterFinset ρ).1 χ.2
  have := nontrivial_of_isIrreducible S.toRepresentation
  obtain ⟨w, hw⟩ := exists_ne (0 : S.toSubmodule)
  have hterm : ∀ χ' : irreducibleCharacterFinset ρ, (μ χ' • charProjector ρ χ'.1) (w : V) =
      if χ' = χ then μ χ' • (w : V) else 0 := by
    intro χ'
    obtain ⟨S', hS', hS'χ⟩ := (mem_irreducibleCharacterFinset ρ).1 χ'.2
    rw [LinearMap.smul_apply, ← hS'χ, charProjector_apply_of_mem ρ S'.toRepresentation S w.2,
      hS'χ, hSχ]
    by_cases h : χ' = χ
    · simp [h]
    · have h' : ¬ χ.1 = χ'.1 := fun h' => h (Subtype.ext h'.symm)
      simp [h, h']
  have h0 := LinearMap.congr_fun hμ (w : V)
  rw [LinearMap.sum_apply, Finset.sum_congr rfl fun χ' _ => hterm χ', Finset.sum_ite_eq'] at h0
  simp only [Finset.mem_univ, ite_true, LinearMap.zero_apply] at h0
  exact (smul_eq_zero.1 h0).resolve_right fun h => hw (Subtype.ext h)

/-- The linear functional `X ↦ tr[ρ(g⁻¹) X Δ]` of Lemma 4.6. -/
noncomputable def deltaPairing (g : G) : Module.End ℂ V →ₗ[ℂ] ℂ :=
  LinearMap.trace ℂ V ∘ₗ LinearMap.mulRight ℂ (deltaOperator ρ) ∘ₗ LinearMap.mulLeft ℂ (ρ g⁻¹)

theorem deltaPairing_apply (g : G) (X : Module.End ℂ V) :
    deltaPairing ρ g X = LinearMap.trace ℂ V (ρ g⁻¹ ∘ₗ X ∘ₗ deltaOperator ρ) := by
  simp [deltaPairing, Module.End.mul_eq_comp, LinearMap.comp_assoc]

open Classical in
/-- Source: arXiv:1001.3807, Lemma 4.6, `Papers/1001.3807/paper_v3.tex` lines 1015–1029. For a
semi-regular representation, `tr[U_g† U_h Δ] = δ_{g,h}`, so the functional `deltaPairing ρ g`
takes the value `δ_{g,h}` on `ρ(h)`. -/
theorem deltaPairing_rep_of_isSemiRegular (hρ : IsSemiRegular ρ) (g h : G) :
    deltaPairing ρ g (ρ h) = if g = h then 1 else 0 := by
  rw [deltaPairing_apply, trace_inv_comp_comp_deltaOperator_of_isSemiRegular ρ hρ]

omit [Fintype G] in
/-- Source: arXiv:1001.3807, Lemma 4.6, `Papers/1001.3807/paper_v3.tex` lines 1015–1029. For a
semi-regular representation the operators `ρ(g)` are linearly independent: the functional
`X ↦ tr[ρ(g⁻¹) X Δ]` extracts the coefficient of `ρ(g)`. -/
theorem linearIndependent_of_isSemiRegular [Finite G] (hρ : IsSemiRegular ρ) :
    LinearIndependent ℂ fun g => ρ g := by
  have := Fintype.ofFinite G
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc g
  have h := congrArg (deltaPairing ρ g) hc
  simp only [map_sum, map_smul, deltaPairing_rep_of_isSemiRegular ρ hρ, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_zero] at h
  exact h

/-- Source: arXiv:1001.3807, proof of Theorem 4.12, `Papers/1001.3807/paper_v3.tex`
lines 1257–1259, with Lemma 4.6 (lines 1015–1029). For a semi-regular representation and one
representative `r c` of each conjugacy class `c`, the twirls `σ(ρ(r c))` are linearly
independent. -/
theorem linearIndependent_averageMap_conjClasses (hρ : IsSemiRegular ρ)
    (r : ConjClasses G → G) (hr : ∀ c, ConjClasses.mk (r c) = c) :
    LinearIndependent ℂ fun c => (linHom ρ ρ).averageMap (ρ (r c)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro μ hμ c₀
  -- The functional of Lemma 4.6 at `r c₀` counts the conjugations of `r c` onto `r c₀`.
  have hval : ∀ c, deltaPairing ρ (r c₀) ((linHom ρ ρ).averageMap (ρ (r c))) =
      ⅟(Fintype.card G : ℂ) *
        ((Finset.univ.filter fun h : G => r c₀ = h * r c * h⁻¹).card : ℂ) := by
    intro c
    rw [averageMap_linHom_apply, map_smul, map_sum, smul_eq_mul, Finset.card_filter,
      Nat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    have : ρ h ∘ₗ ρ (r c) ∘ₗ ρ h⁻¹ = ρ (h * r c * h⁻¹) := by
      simp only [map_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    rw [this, deltaPairing_rep_of_isSemiRegular ρ hρ]
    split_ifs <;> simp
  have hzero : ∀ c, c ≠ c₀ →
      (Finset.univ.filter fun h : G => r c₀ = h * r c * h⁻¹).card = 0 := by
    intro c hc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro h _ hh
    apply hc
    rw [← hr c, ← hr c₀, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    exact ⟨h, hh.symm⟩
  have hpos : (Finset.univ.filter fun h : G => r c₀ = h * r c₀ * h⁻¹).card ≠ 0 := by
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨1, by simp⟩
  have h := congrArg (deltaPairing ρ (r c₀)) hμ
  simp only [map_sum, map_smul, hval, smul_eq_mul, map_zero] at h
  rw [Finset.sum_eq_single c₀ (fun c _ hc => by rw [hzero c hc]; simp)
    (fun h => absurd (Finset.mem_univ _) h)] at h
  have hG : ⅟(Fintype.card G : ℂ) ≠ 0 := by
    rw [invOf_eq_inv]
    exact inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_pos.ne')
  exact (mul_eq_zero.1 h).resolve_right (mul_ne_zero hG (Nat.cast_ne_zero.2 hpos))

end Representation

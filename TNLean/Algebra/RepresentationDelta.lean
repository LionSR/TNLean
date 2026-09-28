/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.RepresentationTheory.Invariants
import TNLean.Algebra.CharacterProjector

/-!
# Group averaging, the operator `Δ`, and semi-regular representations

**Source.** Schuch, Cirac, Pérez-García 2010 (arXiv:1001.3807), Section 4,
`Papers/1001.3807/paper_v3.tex`:

* Lemma 4.3, lines 923–955: for a unitary representation `U_g` of a finite group, the twirl
  `σ(X) = |G|⁻¹ ∑_g U_g X U_g†` is the orthogonal projector onto the `U_g`-invariant operators.
* Lemma 4.4 (`lemma:1d-ghh-anyrep`), lines 960–1006: for any unitary representation
  `U_g ≅ ⊕_i D^i(g) ⊗ 𝟙_{m_i}`, the operator `Δ ≅ |G|⁻¹ ⊕_i (d_i/m_i) 𝟙_{d_i} ⊗ 𝟙_{m_i}`
  satisfies `∑_h tr[U_h† Δ U_g] U_h = ∑_h tr[U_{gh⁻¹} Δ] U_h = U_g`.
* Definition 4.5, lines 1010–1013: `U_g` is semi-regular if it contains every irreducible
  representation of `G`.
* Lemma 4.6 (`lemma:noninj:semireg-trace-ug-delta`), lines 1015–1029: for semi-regular `U_g`,
  `tr[U_g† U_h Δ] = δ_{g,h}`; for the regular representation `Δ ∝ 𝟙`.

**Formalized here.** The twirl is Mathlib's `Representation.averageMap` of the conjugation
representation `Representation.linHom ρ ρ`; Lemma 4.3 is its projection property, its range (the
commutant), and its self-adjointness for the Hilbert–Schmidt pairing when `ρ` is unitary. The
operator `Δ` is defined without a basis, as `|G|⁻¹ ∑_χ (χ(1)/m_χ) P_χ` over the irreducible
characters `χ` of `ρ`, with `P_χ` the character projectors of `TNLean.Algebra.CharacterProjector`
and `m_χ` the multiplicities computed from characters; `deltaOperator_apply_of_mem` shows that it
acts on each irreducible subrepresentation with character `χ` as the scalar `χ(1)/(m_χ |G|)`,
which is the source's block formula. Lemmas 4.4 and 4.6 are proved from character orthogonality.
Lemmas 4.4 and 4.6 are stated with `U_h† = ρ(h⁻¹)`, which is the source's adjoint for a unitary
representation; no unitarity is needed for these trace identities.

## Main definitions

* `Representation.deltaOperator`: the operator `Δ` of `eq:noninj:deltadef`.
* `Representation.IsSemiRegular`: Definition 4.5.

## Main results

* `Representation.averageMap_linHom_apply`, `Representation.mem_invariants_linHom_iff`,
  `Representation.trace_adjoint_comp_averageMap_linHom`: Lemma 4.3.
* `Representation.deltaOperator_apply_of_mem`: the block formula `eq:noninj:deltadef`.
* `Representation.sum_trace_comp_deltaOperator_smul`,
  `Representation.sum_trace_inv_comp_deltaOperator_comp_smul`: Lemma 4.4.
* `Representation.deltaOperator_leftRegular`: `Δ = |G|⁻¹ 𝟙` for the regular representation.
* `Representation.trace_inv_comp_comp_deltaOperator_of_isSemiRegular`: Lemma 4.6.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap

universe u v

namespace Representation

section Twirl

variable {G : Type*} [Group G] [Fintype G]

/-- The order of a finite group is invertible in `ℂ`. -/
noncomputable local instance invertibleFintypeCardComplex : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_pos.ne')

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- Source: arXiv:1001.3807, Lemma 4.3, `Papers/1001.3807/paper_v3.tex` lines 923–929. The
averaging map of the conjugation representation `X ↦ ρ(g) X ρ(g)⁻¹` is the twirl
`σ(X) = |G|⁻¹ ∑_g ρ(g) X ρ(g)⁻¹`. -/
theorem averageMap_linHom_apply (X : V →ₗ[ℂ] V) :
    (linHom ρ ρ).averageMap X = ⅟(Fintype.card G : ℂ) • ∑ g, ρ g ∘ₗ X ∘ₗ ρ g⁻¹ := by
  simp [averageMap, GroupAlgebra.average, map_sum, linHom_apply]

omit [Fintype G] in
/-- The invariant operators of the conjugation representation are the operators commuting with
every `ρ(g)`, the subspace `𝒮` of `Papers/1001.3807/paper_v3.tex` line 924
(`eq:mpssym:symspace`). -/
theorem mem_invariants_linHom_iff (X : V →ₗ[ℂ] V) :
    X ∈ (linHom ρ ρ).invariants ↔ ∀ g, ρ g ∘ₗ X = X ∘ₗ ρ g := by
  refine forall_congr' fun g => ?_
  rw [linHom_apply]
  constructor
  · intro h
    conv_rhs => rw [← h]
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← Module.End.mul_eq_comp (ρ g⁻¹),
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id]
  · intro h
    rw [← LinearMap.comp_assoc, h, LinearMap.comp_assoc, ← Module.End.mul_eq_comp (ρ g),
      ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id, LinearMap.comp_id]

/-- Source: arXiv:1001.3807, Lemma 4.3, `Papers/1001.3807/paper_v3.tex` lines 923–955. The
twirl is a projection onto the operators commuting with the representation. -/
theorem isProj_averageMap_linHom :
    LinearMap.IsProj (linHom ρ ρ).invariants (linHom ρ ρ).averageMap :=
  isProj_averageMap _

end Algebraic

section Unitary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V)

/-- Source: arXiv:1001.3807, Lemma 4.3, `Papers/1001.3807/paper_v3.tex` lines 923–929. For a
unitary representation the twirl is `σ(X) = |G|⁻¹ ∑_g U_g X U_g†`. -/
theorem averageMap_linHom_apply_of_adjoint (hU : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (X : V →ₗ[ℂ] V) :
    (linHom ρ ρ).averageMap X =
      ⅟(Fintype.card G : ℂ) • ∑ g, ρ g ∘ₗ X ∘ₗ LinearMap.adjoint (ρ g) := by
  simp_rw [hU]
  exact averageMap_linHom_apply ρ X

/-- Source: arXiv:1001.3807, Lemma 4.3, `Papers/1001.3807/paper_v3.tex` lines 950–954. For a
unitary representation the twirl is Hermitian for the Hilbert–Schmidt pairing
`⟨Y, X⟩ = tr[Y† X]`; together with `isProj_averageMap_linHom` it is the orthogonal projector
onto the commutant. -/
theorem trace_adjoint_comp_averageMap_linHom (hU : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    (X Y : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V (LinearMap.adjoint Y ∘ₗ (linHom ρ ρ).averageMap X) =
      LinearMap.trace ℂ V (LinearMap.adjoint ((linHom ρ ρ).averageMap Y) ∘ₗ X) := by
  have hc : (starRingEnd ℂ) (⅟(Fintype.card G : ℂ)) = ⅟(Fintype.card G : ℂ) := by
    rw [invOf_eq_inv, map_inv₀, map_natCast]
  rw [averageMap_linHom_apply, averageMap_linHom_apply, map_smulₛₗ LinearMap.adjoint, hc,
    map_sum]
  simp only [← Module.End.mul_eq_comp, mul_smul_comm, smul_mul_assoc, Finset.mul_sum,
    Finset.sum_mul, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  simp only [Equiv.inv_apply, inv_inv]
  rw [Module.End.mul_eq_comp (ρ g⁻¹), Module.End.mul_eq_comp Y, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp, hU, hU, inv_inv, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp,
    show LinearMap.adjoint Y * (ρ g * (X * ρ g⁻¹)) = LinearMap.adjoint Y * ρ g * X * ρ g⁻¹ by
      simp only [mul_assoc], LinearMap.trace_mul_comm]
  simp only [mul_assoc]

end Unitary

end Twirl

section Delta

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (ρ : Representation ℂ G V)

/-- Source: arXiv:1001.3807, Lemma `lemma:1d-ghh-anyrep`, `Papers/1001.3807/paper_v3.tex`
lines 970–976 (equation `eq:noninj:deltadef`). The operator
`Δ = |G|⁻¹ ∑_χ (χ(1)/m_χ) P_χ`, the sum running over the irreducible characters `χ` of `ρ`,
with `P_χ` the projector onto the `χ`-isotypic component and `m_χ` the multiplicity. It is
defined from characters, without a basis; `deltaOperator_apply_of_mem` shows that it acts on each
irreducible subrepresentation `D^i` as `d_i/(m_i |G|)`, the source's block formula
`Δ ≅ |G|⁻¹ ⊕_i (d_i/m_i) 𝟙_{d_i} ⊗ 𝟙_{m_i}`. -/
noncomputable def deltaOperator : Module.End ℂ V :=
  (Nat.card G : ℂ)⁻¹ • ∑ χ ∈ irreducibleCharacterFinset ρ,
    (χ 1 / characterMultiplicity ρ χ) • charProjector ρ χ

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 970–976
(equation `eq:noninj:deltadef`). On an irreducible subrepresentation with character `χ`, of
dimension `d = χ(1)` and multiplicity `m_χ`, the operator `Δ` is the scalar `d/(m_χ |G|)`. -/
theorem deltaOperator_apply_of_mem (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible]
    {v : V} (hv : v ∈ S) :
    deltaOperator ρ v =
      (S.toRepresentation.character 1 /
        (characterMultiplicity ρ S.toRepresentation.character * Nat.card G)) • v := by
  classical
  have hχ : ∀ χ ∈ irreducibleCharacterFinset ρ, (χ 1 / characterMultiplicity ρ χ) •
      charProjector ρ χ v =
        if S.toRepresentation.character = χ then
          (χ 1 / characterMultiplicity ρ χ) • v else 0 := by
    intro χ hχ
    obtain ⟨S', hS', rfl⟩ := (mem_irreducibleCharacterFinset ρ).1 hχ
    rw [charProjector_apply_of_mem ρ S'.toRepresentation S hv]
    split_ifs <;> simp
  rw [deltaOperator, LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [Finset.sum_congr rfl hχ, Finset.sum_ite_eq,
    ite_eq_left ((mem_irreducibleCharacterFinset ρ).2 ⟨S, inferInstance, rfl⟩), smul_smul]
  congr 1
  field_simp

/-- The trace `tr[ρ(k) Δ] = |G|⁻¹ ∑_χ χ(1) χ(k)`, the sum running over the irreducible characters
of `ρ` (arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 997–998 and 1026–1027). -/
theorem trace_comp_deltaOperator (k : G) :
    LinearMap.trace ℂ V (ρ k ∘ₗ deltaOperator ρ) =
      (Nat.card G : ℂ)⁻¹ * ∑ χ ∈ irreducibleCharacterFinset ρ, χ 1 * χ k := by
  rw [deltaOperator, LinearMap.comp_smul, ← Module.End.mul_eq_comp, Finset.mul_sum, map_smul,
    map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun χ hχ => ?_
  obtain ⟨S, hS, rfl⟩ := (mem_irreducibleCharacterFinset ρ).1 hχ
  rw [mul_smul_comm, map_smul, Module.End.mul_eq_comp,
    trace_comp_charProjector ρ S.toRepresentation, smul_eq_mul]
  have hm := characterMultiplicity_ne_zero ρ ⟨S, hS, rfl⟩
  field_simp

/-- The coefficients `tr[ρ(k⁻¹) Δ]` reproduce the identity: `∑_k tr[ρ(k⁻¹) Δ] ρ(k) = 𝟙`. -/
theorem sum_trace_inv_comp_deltaOperator_smul :
    ∑ k, LinearMap.trace ℂ V (ρ k⁻¹ ∘ₗ deltaOperator ρ) • ρ k = 1 := by
  simp_rw [trace_comp_deltaOperator, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm, ← sum_charProjector_irreducibleCharacters ρ]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [charProjector, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  ring

/-- Source: arXiv:1001.3807, Lemma `lemma:1d-ghh-anyrep`, `Papers/1001.3807/paper_v3.tex`
lines 960–1006 (equation `eq:noninj:tr-ghdeltaUh-is-Ug`, second form). For every
finite-dimensional complex representation of a finite group,
`∑_h tr[U_{gh⁻¹} Δ] U_h = U_g`. -/
theorem sum_trace_comp_deltaOperator_smul (g : G) :
    ∑ h, LinearMap.trace ℂ V (ρ (g * h⁻¹) ∘ₗ deltaOperator ρ) • ρ h = ρ g := by
  rw [← Fintype.sum_equiv (Equiv.mulRight g) (fun k =>
      LinearMap.trace ℂ V (ρ k⁻¹ ∘ₗ deltaOperator ρ) • (ρ k * ρ g)) _ fun k => by
    simp [mul_inv_rev, map_mul]]
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul, sum_trace_inv_comp_deltaOperator_smul, one_mul]

/-- Source: arXiv:1001.3807, Lemma `lemma:1d-ghh-anyrep`, `Papers/1001.3807/paper_v3.tex`
lines 960–1006 (equation `eq:noninj:tr-ghdeltaUh-is-Ug`, first form, with `U_h† = ρ(h⁻¹)`).
`∑_h tr[U_h† Δ U_g] U_h = U_g`. -/
theorem sum_trace_inv_comp_deltaOperator_comp_smul (g : G) :
    ∑ h, LinearMap.trace ℂ V (ρ h⁻¹ ∘ₗ deltaOperator ρ ∘ₗ ρ g) • ρ h = ρ g := by
  convert sum_trace_comp_deltaOperator_smul ρ g using 3 with h
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc,
    ← Module.End.mul_eq_comp (ρ g), ← map_mul]

/-- Source: arXiv:1001.3807, Definition 4.5, `Papers/1001.3807/paper_v3.tex` lines 1010–1013.
A representation of a finite group is semi-regular if it contains every irreducible
representation: every irreducible representation admits a nonzero intertwining map into it.
Irreducible representations of a finite group are finite-dimensional, so it suffices to quantify
over finite-dimensional ones. -/
def IsSemiRegular : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W), σ.IsIrreducible → ∃ f : IntertwiningMap σ ρ, f ≠ 0

section Regular

omit [Fintype G] in
open Classical in
/-- The character of the left regular representation is `|G| δ_{k,1}`. -/
theorem character_leftRegular [Finite G] (k : G) :
    (leftRegular ℂ G).character k = if k = 1 then (Nat.card G : ℂ) else 0 := by
  classical
  have := Fintype.ofFinite G
  rw [character, LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    ofMulAction_single, smul_eq_mul]
  simp [MonoidAlgebra.basis, Finsupp.single_apply]

/-- The multiplicity of a character `χ` in the regular representation is `χ(1)`. -/
theorem characterMultiplicity_leftRegular (χ : G → ℂ) :
    characterMultiplicity (leftRegular ℂ G) χ = χ 1 := by
  classical
  simp only [characterMultiplicity, character_leftRegular, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (1 : G) fun x => (Nat.card G : ℂ) * χ x⁻¹]
  simp

omit [Fintype G] in
/-- An irreducible representation occurs in the regular representation. -/
theorem exists_intertwiningMap_leftRegular_ne_zero [Finite G] (σ : Representation ℂ G W)
    [σ.IsIrreducible] : ∃ f : IntertwiningMap σ (leftRegular ℂ G), f ≠ 0 := by
  have := Fintype.ofFinite G
  by_contra! h
  have : Subsingleton (IntertwiningMap σ (leftRegular ℂ G)) := ⟨fun f g => by rw [h f, h g]⟩
  have hfin := characterMultiplicity_eq_finrank (leftRegular ℂ G) σ
  rw [characterMultiplicity_leftRegular, char_one,
    Module.finrank_zero_of_subsingleton (M := IntertwiningMap σ (leftRegular ℂ G)),
    Nat.cast_zero, Nat.cast_eq_zero] at hfin
  exact (finrank_pos_of_isIrreducible σ).ne' hfin

omit [Fintype G] in
/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1010–1013. The regular
representation is semi-regular. -/
theorem isSemiRegular_leftRegular [Finite G] : IsSemiRegular (leftRegular ℂ G) :=
  fun _ _ _ _ σ _ => exists_intertwiningMap_leftRegular_ne_zero σ

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1021–1022. For the regular
representation `Δ ∝ 𝟙`; precisely `Δ = |G|⁻¹ 𝟙`. -/
theorem deltaOperator_leftRegular :
    deltaOperator (leftRegular ℂ G) = (Nat.card G : ℂ)⁻¹ • 1 := by
  rw [deltaOperator, ← sum_charProjector_irreducibleCharacters (leftRegular ℂ G)]
  congr 1
  refine Finset.sum_congr rfl fun χ hχ => ?_
  obtain ⟨S, hS, rfl⟩ := (mem_irreducibleCharacterFinset _).1 hχ
  have hd : S.toRepresentation.character 1 ≠ 0 := by
    rw [char_one, Nat.cast_ne_zero]
    exact (finrank_pos_of_isIrreducible S.toRepresentation).ne'
  rw [characterMultiplicity_leftRegular, div_self hd, one_smul]

omit [Fintype G] in
/-- Every irreducible character of a representation is an irreducible character of the regular
representation. -/
theorem irreducibleCharacters_subset_leftRegular [Finite G] :
    irreducibleCharacters ρ ⊆ irreducibleCharacters (leftRegular ℂ G) := by
  rintro _ ⟨S, hS, rfl⟩
  obtain ⟨f, hf⟩ := exists_intertwiningMap_leftRegular_ne_zero S.toRepresentation
  exact character_mem_irreducibleCharacters_of_ne_zero _ _ f hf

omit [Fintype G] in
/-- A semi-regular representation has the same irreducible characters as the regular
representation. -/
theorem irreducibleCharacters_eq_leftRegular_of_isSemiRegular [Finite G] (hρ : IsSemiRegular ρ) :
    irreducibleCharacters ρ = irreducibleCharacters (leftRegular ℂ G) := by
  refine (irreducibleCharacters_subset_leftRegular ρ).antisymm ?_
  rintro _ ⟨S, hS, rfl⟩
  obtain ⟨f, hf⟩ := hρ S.toSubmodule S.toRepresentation hS
  exact character_mem_irreducibleCharacters_of_ne_zero _ _ f hf

open Classical in
/-- For a semi-regular representation, `∑_χ χ(1) χ(k) = |G| δ_{k,1}`, the sum running over its
irreducible characters: `|G| tr[U_k Δ]` is the character of the regular representation
(arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1026–1028). -/
theorem sum_irreducibleCharacters_mul_of_isSemiRegular (hρ : IsSemiRegular ρ) (k : G) :
    ∑ χ ∈ irreducibleCharacterFinset ρ, χ 1 * χ k =
      if k = 1 then (Nat.card G : ℂ) else 0 := by
  have hfin : irreducibleCharacterFinset ρ = irreducibleCharacterFinset (leftRegular ℂ G) := by
    ext χ
    simp [irreducibleCharacters_eq_leftRegular_of_isSemiRegular ρ hρ]
  have h := trace_comp_deltaOperator (leftRegular ℂ G) k
  rw [deltaOperator_leftRegular, LinearMap.comp_smul, map_smul, Module.End.one_eq_id,
    LinearMap.comp_id, ← character, character_leftRegular, smul_eq_mul] at h
  have hG := natCard_ne_zero_complex (G := G)
  rw [hfin]
  have := congrArg (fun x => (Nat.card G : ℂ) * x) h
  simp only [← mul_assoc, mul_inv_cancel₀ hG, one_mul] at this
  exact this.symm

open Classical in
/-- Source: arXiv:1001.3807, Lemma `lemma:noninj:semireg-trace-ug-delta`,
`Papers/1001.3807/paper_v3.tex` lines 1015–1029, with `U_g† = ρ(g⁻¹)`. For a semi-regular
representation, `tr[U_g† U_h Δ] = δ_{g,h}`. -/
theorem trace_inv_comp_comp_deltaOperator_of_isSemiRegular (hρ : IsSemiRegular ρ) (g h : G) :
    LinearMap.trace ℂ V (ρ g⁻¹ ∘ₗ ρ h ∘ₗ deltaOperator ρ) = if g = h then 1 else 0 := by
  rw [← LinearMap.comp_assoc, ← Module.End.mul_eq_comp (ρ g⁻¹), ← map_mul,
    trace_comp_deltaOperator, sum_irreducibleCharacters_mul_of_isSemiRegular ρ hρ]
  by_cases hgh : g = h
  · subst hgh
    simp
  · have : g⁻¹ * h ≠ 1 := fun h' => hgh (inv_mul_eq_one.1 h')
    simp [this, hgh]

end Regular

end Delta

end Representation

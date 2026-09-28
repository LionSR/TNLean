/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke

/-!
# Character projectors of a complex representation of a finite group

For a complex representation `ρ` of a finite group `G` and an irreducible character `χ`, the
operator

`P_χ = (χ(1) / |G|) ∑_g χ(g⁻¹) ρ(g)`

acts as the identity on every irreducible subrepresentation of `ρ` with character `χ` and as zero
on every other irreducible subrepresentation. For an irreducible target this is the identity
`∑_g χ_i(g⁻¹) D^j(g) = (|G| / d_i) δ_{ij} 𝟙` printed in the proof of Lemma
`lemma:1d-ghh-anyrep` of Schuch, Cirac, and Pérez-García, `Papers/1001.3807/paper_v3.tex`
lines 983–990 (equation `eq:noninj:sum-CHIi-Di-is-PROJi`), which the source derives from the
group orthogonality theorem. Here it is derived from Mathlib's orthogonality of characters
`Representation.char_orthonormal` and Schur's lemma
`Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed`.

The operators `P_χ` are basis-free: they are built from the character alone. Together with the
decomposition of `ρ` into irreducible subrepresentations (Maschke's theorem, through Mathlib's
`ComplementedLattice (Subrepresentation ρ)` instance), they give the isotypic decomposition used
to define the operator `Δ` of the source, lines 970–976, in
`TNLean.Algebra.RepresentationDelta`.

## Main definitions

* `Representation.charProjector ρ χ`: the operator `(χ(1)/|G|) ∑_g χ(g⁻¹) ρ(g)`.
* `Representation.irreducibleCharacters ρ`: the characters of the irreducible
  subrepresentations of `ρ`, a finite set.

## Main results

* `Representation.sum_character_inv_smul_eq`: the source's identity
  `∑_g χ_σ(g⁻¹) τ(g) = (|G|/d_σ) [σ ≅ τ] 𝟙` for irreducible `σ` and `τ`.
* `Representation.exists_isInternal_isAtom`: every finite-dimensional complex representation of a
  finite group is an internal direct sum of irreducible subrepresentations.
* `Representation.charProjector_apply_of_mem`: the action of `P_χ` on an irreducible
  subrepresentation.
* `Representation.sum_charProjector_irreducibleCharacters`: `∑_χ P_χ = 𝟙`.
* `Representation.trace_comp_charProjector`: `tr[ρ(k) P_χ] = m_χ χ(k)`, with `m_χ` the
  multiplicity computed from characters.
* `Representation.character_mem_irreducibleCharacters_of_ne_zero`: an irreducible
  representation admitting a nonzero intertwining map into `ρ` has its character in
  `irreducibleCharacters ρ`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open Module LinearMap

namespace Representation

section Irreducible

variable {k G W : Type*} [Field k] [Monoid G] [AddCommGroup W] [Module k W]

/-- The carrier of an irreducible representation is nontrivial. -/
theorem nontrivial_of_isIrreducible (σ : Representation k G W) [σ.IsIrreducible] :
    Nontrivial W := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

/-- The carrier of a finite-dimensional irreducible representation has positive dimension. -/
theorem finrank_pos_of_isIrreducible [FiniteDimensional k W] (σ : Representation k G W)
    [σ.IsIrreducible] : 0 < finrank k W := by
  have := nontrivial_of_isIrreducible σ
  exact Module.finrank_pos

end Irreducible

end Representation

namespace Subrepresentation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- An atom of the lattice of subrepresentations of `ρ` carries an irreducible
representation. -/
theorem isIrreducible_toRepresentation_of_isAtom {T : Subrepresentation ρ} (hT : IsAtom T) :
    T.toRepresentation.IsIrreducible := by
  let lift : Subrepresentation T.toRepresentation → Subrepresentation ρ := fun τ =>
    { toSubmodule := τ.toSubmodule.map T.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨T.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩ }
  have hle : ∀ τ, lift τ ≤ T := by
    rintro τ _ ⟨w, -, rfl⟩
    exact w.2
  obtain ⟨v, hvT, hv0⟩ : ∃ v ∈ T, v ≠ 0 := by
    by_contra! h
    exact hT.1 (toSubmodule_injective ((Submodule.eq_bot_iff _).2 h))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun τ => ?_ }
  · have hmem : (⟨v, hvT⟩ : T.toSubmodule) ∈ (⊤ : Subrepresentation T.toRepresentation) :=
      Submodule.mem_top (R := k)
    rw [← h] at hmem
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot k).1 hmem))
  · rcases hT.le_iff.1 (hle τ) with h | h
    · left
      apply toSubmodule_injective
      refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
      have hmem : (w : V) ∈ lift τ := ⟨w, hw, rfl⟩
      rw [h] at hmem
      exact Subtype.ext ((Submodule.mem_bot k).1 hmem)
    · right
      apply toSubmodule_injective
      refine Submodule.eq_top_iff'.2 fun w => ?_
      have hmem : (w : V) ∈ lift τ := by rw [h]; exact w.2
      obtain ⟨w', hw', hww'⟩ := hmem
      rwa [Subtype.ext hww'] at hw'

end Subrepresentation

namespace Representation

section Decomposition

variable {k G V : Type*} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

open Classical in
/-- Maschke's theorem in decomposed form: a finite-dimensional representation of a finite group,
over a field whose characteristic does not divide the order of the group, is an internal direct
sum of finitely many irreducible subrepresentations (atoms of the lattice of
subrepresentations). -/
theorem exists_isInternal_isAtom (ρ : Representation k G V) :
    ∃ s : Finset (Subrepresentation ρ), (∀ T ∈ s, IsAtom T) ∧
      DirectSum.IsInternal fun T : s => T.1.toSubmodule := by
  classical
  have hmono : StrictMono fun p : Subrepresentation ρ => finrank k p.toSubmodule :=
    fun _ _ h => Submodule.finrank_lt_finrank_of_lt h
  have : WellFoundedLT (Subrepresentation ρ) := hmono.wellFoundedLT
  have key : ∀ p : Subrepresentation ρ, ∃ s : Finset (Subrepresentation ρ),
      (∀ T ∈ s, IsAtom T) ∧ s.SupIndep Subrepresentation.toSubmodule ∧
        s.sup Subrepresentation.toSubmodule = p.toSubmodule := by
    intro p
    induction p using WellFoundedLT.induction with
    | ind p ih =>
      rcases eq_bot_or_exists_atom_le p with hp | ⟨T, hT, hTp⟩
      · exact ⟨∅, by simp, Finset.supIndep_empty _, by simp [hp]; rfl⟩
      obtain ⟨r', hr'⟩ := exists_isCompl T
      have hinf : T.toSubmodule ⊓ r'.toSubmodule = ⊥ :=
        congrArg Subrepresentation.toSubmodule hr'.inf_eq_bot
      have hsup : T.toSubmodule ⊔ r'.toSubmodule = ⊤ :=
        congrArg Subrepresentation.toSubmodule hr'.sup_eq_top
      have hTr : ¬ T ≤ r' := fun h => hT.1 (hr'.disjoint.eq_bot_of_le h)
      have hrp : r' ⊓ p < p := by
        refine lt_of_le_of_ne inf_le_right fun h => hTr ?_
        rw [← h] at hTp
        exact hTp.trans inf_le_left
      obtain ⟨s, hsA, hsI, hss⟩ := ih _ hrp
      refine ⟨insert T s, ?_, hsI.insert ?_, ?_⟩
      · simpa [Finset.forall_mem_insert] using ⟨hT, hsA⟩
      · rw [hss, disjoint_iff]
        change T.toSubmodule ⊓ (r'.toSubmodule ⊓ p.toSubmodule) = ⊥
        rw [← inf_assoc, hinf, bot_inf_eq]
      · rw [Finset.sup_insert, hss]
        change T.toSubmodule ⊔ (r'.toSubmodule ⊓ p.toSubmodule) = p.toSubmodule
        rw [← sup_inf_assoc_of_le _ (show T.toSubmodule ≤ p.toSubmodule from hTp), hsup,
          top_inf_eq]
  obtain ⟨s, hsA, hsI, hss⟩ := key ⊤
  refine ⟨s, hsA, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_comp_coe_iff_supIndep.2 hsI) ?_⟩
  rw [Finset.sup_eq_iSup] at hss
  rw [iSup_subtype]
  exact hss

omit [Finite G] [NeZero (Nat.card G : k)] [FiniteDimensional k V] in
/-- Two endomorphisms agreeing on every summand of an internal direct sum are equal. -/
theorem _root_.DirectSum.IsInternal.linearMap_ext {ι : Type*} [DecidableEq ι]
    {N : ι → Submodule k V}
    (h : DirectSum.IsInternal N) {f g : Module.End k V} (hfg : ∀ i, ∀ v ∈ N i, f v = g v) :
    f = g := by
  ext v
  have hv : v ∈ ⨆ i, N i := by rw [h.submodule_iSup_eq_top]; exact Submodule.mem_top
  exact Submodule.iSup_induction N (motive := fun v => f v = g v) hv hfg (by simp)
    fun v w hv hw => by simp [hv, hw]

end Decomposition

section Characters

variable {G : Type*} [Group G] [Fintype G]
variable {V W T : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]

/-- The order of a finite group is invertible in `ℂ`. -/
noncomputable local instance invertibleNatCardComplex : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')

omit [Fintype G] [FiniteDimensional ℂ V] in
/-- The order of a finite group is nonzero in `ℂ`. -/
theorem natCard_ne_zero_complex [Finite G] : (Nat.card G : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Nat.card_pos.ne'

omit [Fintype G] in
/-- Two irreducible complex representations of a finite group are equivalent exactly when their
characters agree. -/
theorem nonempty_equiv_iff_character_eq [Finite G] (σ : Representation ℂ G W)
    (τ : Representation ℂ G T)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    Nonempty (σ.Equiv τ) ↔ σ.character = τ.character := by
  classical
  have := Fintype.ofFinite G
  refine ⟨fun ⟨φ⟩ => char_iso φ, fun h => ?_⟩
  have h1 := char_orthonormal τ σ
  have h2 := char_orthonormal σ σ
  rw [← h] at h1
  rw [ite_eq_left ⟨Equiv.refl σ⟩] at h2
  rw [h2] at h1
  by_contra hne
  rw [ite_eq_right hne] at h1
  simp at h1

open Classical in
/-- Source: arXiv:1001.3807, proof of Lemma `lemma:1d-ghh-anyrep`,
`Papers/1001.3807/paper_v3.tex` lines 983–990 (equation `eq:noninj:sum-CHIi-Di-is-PROJi`).
For irreducible representations `σ = D^i` and `τ = D^j`,
`∑_g tr[D^i(g⁻¹)] D^j(g) = (|G|/d_i) δ_{ij} 𝟙`, where `δ_{ij}` is equivalence of `σ` and `τ`.
The source derives this from the group orthogonality theorem; here it follows from Schur's lemma
and Mathlib's orthogonality of characters. -/
theorem sum_character_inv_smul_eq (σ : Representation ℂ G W) (τ : Representation ℂ G T)
    [σ.IsIrreducible] [τ.IsIrreducible] :
    ∑ g, σ.character g⁻¹ • τ g =
      if Nonempty (σ.Equiv τ) then ((Nat.card G : ℂ) / finrank ℂ W) • (1 : Module.End ℂ T)
      else 0 := by
  set F : Module.End ℂ T := ∑ g, σ.character g⁻¹ • τ g with hF
  have hcomm : ∀ h : G, F ∘ₗ τ h = τ h ∘ₗ F := by
    intro h
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    simp only [hF, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv,
      mul_inv_rev]
    congr 1
    · rw [← char_conj σ g⁻¹ h⁻¹, inv_inv, mul_assoc]
    · congr 1
      group
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
      (⟨F, hcomm⟩ : IntertwiningMap τ τ)
  have hFc : F = c • (1 : Module.End ℂ T) := by
    have := congrArg IntertwiningMap.toLinearMap hc
    simp only [IntertwiningMap.algebraMap_apply] at this
    rw [← this]
    rfl
  have htr : ∑ g, τ.character g * σ.character g⁻¹ = c * finrank ℂ T := by
    have := congrArg (LinearMap.trace ℂ T) hFc
    simp only [hF, map_sum, map_smul, LinearMap.trace_one, smul_eq_mul] at this
    simpa [character, mul_comm] using this
  have horth := char_orthonormal τ σ
  rw [htr] at horth
  have hT : (finrank ℂ T : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (finrank_pos_of_isIrreducible τ).ne'
  have hG := natCard_ne_zero_complex (G := G)
  rw [hFc]
  split_ifs with hiso
  · obtain ⟨φ⟩ := hiso
    rw [φ.toLinearEquiv.finrank_eq]
    rw [ite_eq_left ⟨φ⟩] at horth
    congr 1
    field_simp at horth ⊢
    simpa using horth
  · rw [ite_eq_right hiso] at horth
    have : c = 0 := by simpa [hG, hT] using horth
    simp [this]

variable (ρ : Representation ℂ G V)

/-- The character projector `P_χ = (χ(1)/|G|) ∑_g χ(g⁻¹) ρ(g)`. For an irreducible character
`χ` it is the projector onto the `χ`-isotypic component of `ρ`
(`charProjector_apply_of_mem`); the source writes it with `\overline{χ(g)} = χ(g⁻¹)` in
`Papers/1001.3807/paper_v3.tex` lines 983–990. -/
noncomputable def charProjector (χ : G → ℂ) : Module.End ℂ V :=
  (χ 1 / Nat.card G) • ∑ g, χ g⁻¹ • ρ g

omit [FiniteDimensional ℂ V] in
theorem charProjector_apply (χ : G → ℂ) (v : V) :
    charProjector ρ χ v = (χ 1 / Nat.card G) • ∑ g, χ g⁻¹ • ρ g v := by
  simp [charProjector]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 983–990. The character
projector of an irreducible character `χ_σ` acts on an irreducible subrepresentation `T` of `ρ`
as the identity when `T` has character `χ_σ`, and as zero otherwise. -/
theorem charProjector_apply_of_mem (σ : Representation ℂ G W) [σ.IsIrreducible]
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible] {v : V} (hv : v ∈ S) :
    charProjector ρ σ.character v =
      if S.toRepresentation.character = σ.character then v else 0 := by
  classical
  have hsum : ∑ g, σ.character g⁻¹ • ρ g v =
      ((∑ g, σ.character g⁻¹ • S.toRepresentation g) ⟨v, hv⟩ : S.toSubmodule) := by
    simp [LinearMap.sum_apply]
    rfl
  rw [charProjector_apply, hsum, sum_character_inv_smul_eq σ S.toRepresentation]
  have hW : (finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (finrank_pos_of_isIrreducible σ).ne'
  have hG := natCard_ne_zero_complex (G := G)
  by_cases h : S.toRepresentation.character = σ.character
  · rw [ite_eq_left ((nonempty_equiv_iff_character_eq _ _).2 h.symm), ite_eq_left h]
    simp only [LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, smul_smul,
      char_one]
    rw [div_mul_div_comm, mul_comm (finrank ℂ W : ℂ), div_self (mul_ne_zero hG hW), one_smul]
  · rw [ite_eq_right (fun h' => h ((nonempty_equiv_iff_character_eq _ _).1 h').symm),
      ite_eq_right h]
    simp

/-- The characters of the irreducible subrepresentations of `ρ`. These are the characters
`χ_i` of the irreducible representations `D^i` occurring in `U_g ≅ ⊕_i D^i ⊗ 𝟙_{m_i}`,
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 970–976. -/
def irreducibleCharacters : Set (G → ℂ) :=
  {χ | ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible ∧
    S.toRepresentation.character = χ}

omit [Fintype G] in
open Classical in
/-- The character of `ρ` is the sum of the characters of the summands of a decomposition into
subrepresentations. -/
theorem character_eq_sum_of_isInternal {s : Finset (Subrepresentation ρ)}
    (hs : DirectSum.IsInternal fun S : s => S.1.toSubmodule) (g : G) :
    ρ.character g = ∑ S : s, S.1.toRepresentation.character g := by
  classical
  rw [character, LinearMap.trace_eq_sum_trace_restrict hs
    (f := ρ g) (fun S _ hv => S.1.apply_mem_toSubmodule g hv)]
  rfl

/-- The character projector of an irreducible character preserves every irreducible
subrepresentation. -/
theorem charProjector_mapsTo (σ : Representation ℂ G W) [σ.IsIrreducible]
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible] :
    Set.MapsTo (charProjector ρ σ.character) S S := by
  intro v hv
  rw [SetLike.mem_coe, charProjector_apply_of_mem ρ σ S hv]
  split_ifs
  · exact hv
  · exact S.toSubmodule.zero_mem

omit [Fintype G] in
open Classical in
/-- Every irreducible character of `ρ` is the character of one of the summands of any
decomposition of `ρ` into irreducible subrepresentations. -/
theorem exists_mem_character_eq_of_mem_irreducibleCharacters [Finite G]
    {s : Finset (Subrepresentation ρ)}
    (hsA : ∀ S ∈ s, IsAtom S) (hs : DirectSum.IsInternal fun S : s => S.1.toSubmodule)
    {χ : G → ℂ} (hχ : χ ∈ irreducibleCharacters ρ) :
    ∃ S ∈ s, S.toRepresentation.character = χ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨S₀, hS₀, rfl⟩ := hχ
  by_contra! hne
  obtain ⟨v, hvS, hv0⟩ : ∃ v ∈ S₀, v ≠ 0 := by
    by_contra! h
    have := nontrivial_of_isIrreducible S₀.toRepresentation
    obtain ⟨w, hw⟩ := exists_ne (0 : S₀.toSubmodule)
    exact hw (Subtype.ext (h w w.2))
  have hzero : charProjector ρ S₀.toRepresentation.character = 0 := by
    refine hs.linearMap_ext fun S v hv => ?_
    have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
    rw [charProjector_apply_of_mem ρ S₀.toRepresentation S.1 hv, ite_eq_right (hne S.1 S.2)]
    rfl
  have := charProjector_apply_of_mem ρ S₀.toRepresentation S₀ hvS
  rw [ite_eq_left rfl, hzero] at this
  exact hv0 this.symm

omit [Fintype G] in
/-- The set of irreducible characters of a finite-dimensional representation is finite. -/
theorem irreducibleCharacters_finite [Finite G] : (irreducibleCharacters ρ).Finite := by
  classical
  obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom ρ
  refine ((s.image fun S => S.toRepresentation.character).finite_toSet).subset fun χ hχ => ?_
  obtain ⟨S, hS, rfl⟩ := exists_mem_character_eq_of_mem_irreducibleCharacters ρ hsA hs hχ
  exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hS)

/-- The irreducible characters of `ρ`, as a finite set. -/
noncomputable def irreducibleCharacterFinset : Finset (G → ℂ) :=
  (irreducibleCharacters_finite ρ).toFinset

@[simp]
theorem mem_irreducibleCharacterFinset {χ : G → ℂ} :
    χ ∈ irreducibleCharacterFinset ρ ↔ χ ∈ irreducibleCharacters ρ :=
  Set.Finite.mem_toFinset _

/-- The multiplicity `m_χ = |G|⁻¹ ∑_g χ_ρ(g) χ(g⁻¹)` of a character `χ` in `ρ`, computed from
characters. For an irreducible `σ` it is the dimension of the space of intertwining maps from `σ`
to `ρ` (`characterMultiplicity_eq_finrank`), the multiplicity `m_i` of
arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 970–976. -/
noncomputable def characterMultiplicity (χ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g, ρ.character g * χ g⁻¹

/-- Bridge: the multiplicity of an irreducible character computed from characters is the
dimension of the space of intertwining maps. -/
theorem characterMultiplicity_eq_finrank (σ : Representation ℂ G W) :
    characterMultiplicity ρ σ.character = finrank ℂ (IntertwiningMap σ ρ) :=
  card_inv_mul_sum_char_mul_char_eq_finrank σ ρ

open Classical in
/-- The multiplicity of an irreducible character of `ρ` counts the summands with that character
in any decomposition into irreducible subrepresentations. -/
theorem characterMultiplicity_eq_card {s : Finset (Subrepresentation ρ)}
    (hsA : ∀ S ∈ s, IsAtom S) (hs : DirectSum.IsInternal fun S : s => S.1.toSubmodule)
    (σ : Representation ℂ G W) [σ.IsIrreducible] [DecidablePred fun S : s =>
      S.1.toRepresentation.character = σ.character] :
    characterMultiplicity ρ σ.character =
      ((Finset.univ.filter fun S : s => S.1.toRepresentation.character = σ.character).card :
        ℂ) := by
  classical
  unfold characterMultiplicity
  simp_rw [character_eq_sum_of_isInternal ρ hs, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
  rw [char_orthonormal S.1.toRepresentation σ]
  by_cases h : S.1.toRepresentation.character = σ.character
  · rw [ite_eq_left ((nonempty_equiv_iff_character_eq _ _).2 h.symm), ite_eq_left h]
    simp
  · rw [ite_eq_right (fun h' => h ((nonempty_equiv_iff_character_eq _ _).1 h').symm),
      ite_eq_right h]
    simp

/-- The multiplicity of every irreducible character of `ρ` is nonzero. -/
theorem characterMultiplicity_ne_zero {χ : G → ℂ} (hχ : χ ∈ irreducibleCharacters ρ) :
    characterMultiplicity ρ χ ≠ 0 := by
  classical
  obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom ρ
  obtain ⟨S₀, hS₀, rfl⟩ := hχ
  rw [characterMultiplicity_eq_card ρ hsA hs S₀.toRepresentation, Nat.cast_ne_zero,
    ← Nat.pos_iff_ne_zero, Finset.card_pos]
  obtain ⟨S, hS, hSχ⟩ :=
    exists_mem_character_eq_of_mem_irreducibleCharacters ρ hsA hs ⟨S₀, hS₀, rfl⟩
  exact ⟨⟨S, hS⟩, by simpa using hSχ⟩

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 991–1005 (the second display
of the proof of Lemma `lemma:1d-ghh-anyrep`). The isotypic projectors of the irreducible
characters of `ρ` sum to the identity, `∑_i P_i = 𝟙`. -/
theorem sum_charProjector_irreducibleCharacters :
    ∑ χ ∈ irreducibleCharacterFinset ρ, charProjector ρ χ = 1 := by
  classical
  obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom ρ
  refine hs.linearMap_ext fun S v hv => ?_
  have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
  rw [LinearMap.sum_apply, Module.End.one_apply]
  have hχ : ∀ χ ∈ irreducibleCharacterFinset ρ, charProjector ρ χ v =
      if S.1.toRepresentation.character = χ then v else 0 := by
    intro χ hχ
    obtain ⟨S', hS', rfl⟩ := (mem_irreducibleCharacterFinset ρ).1 hχ
    exact charProjector_apply_of_mem ρ S'.toRepresentation S.1 hv
  rw [Finset.sum_congr rfl hχ, Finset.sum_ite_eq]
  rw [ite_eq_left ((mem_irreducibleCharacterFinset ρ).2 ⟨S.1, this, rfl⟩)]

/-- Source: arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex` lines 1026–1028 (the proof of
Lemma `lemma:noninj:semireg-trace-ug-delta`), in the form `tr[U_k P_i] = m_i χ_i(k)`: the trace
of `ρ(k)` on the `χ`-isotypic component is the multiplicity of `χ` times `χ(k)`. -/
theorem trace_comp_charProjector (σ : Representation ℂ G W) [σ.IsIrreducible] (k : G) :
    LinearMap.trace ℂ V (ρ k ∘ₗ charProjector ρ σ.character) =
      characterMultiplicity ρ σ.character * σ.character k := by
  classical
  obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom ρ
  have hmaps : ∀ S : s, Set.MapsTo (ρ k ∘ₗ charProjector ρ σ.character) S.1 S.1 := by
    intro S v hv
    have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
    exact S.1.apply_mem_toSubmodule k (charProjector_mapsTo ρ σ S.1 hv)
  rw [LinearMap.trace_eq_sum_trace_restrict hs hmaps,
    characterMultiplicity_eq_card ρ hsA hs σ, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA S.1 S.2)
  by_cases h : S.1.toRepresentation.character = σ.character
  · have hres : (ρ k ∘ₗ charProjector ρ σ.character).restrict (hmaps S) =
        S.1.toRepresentation k := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change ρ k (charProjector ρ σ.character v) = ρ k v
      rw [charProjector_apply_of_mem ρ σ S.1 v.2, ite_eq_left h]
    rw [hres, ite_eq_left h, Nat.cast_one, one_mul, ← h]
    rfl
  · have hres : (ρ k ∘ₗ charProjector ρ σ.character).restrict (hmaps S) = 0 := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change ρ k (charProjector ρ σ.character v) = 0
      rw [charProjector_apply_of_mem ρ σ S.1 v.2, ite_eq_right h, map_zero]
    rw [hres, ite_eq_right h]
    simp

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- An irreducible representation admitting a nonzero intertwining map into `ρ` occurs in `ρ`:
its character is the character of an irreducible subrepresentation of `ρ`, the image of the
map. -/
theorem character_mem_irreducibleCharacters_of_ne_zero (σ : Representation ℂ G W)
    [σ.IsIrreducible] (f : IntertwiningMap σ ρ) (hf : f ≠ 0) :
    σ.character ∈ irreducibleCharacters ρ := by
  have hinj : Function.Injective f := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let S := f.range
  have hatom : IsAtom S := by
    refine ⟨fun h => hf ?_, fun q hq => ?_⟩
    · ext w
      have hmem : f w ∈ S := ⟨w, rfl⟩
      rw [h] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem
    · let q' : Subrepresentation σ :=
        { toSubmodule := q.toSubmodule.comap f.toLinearMap
          apply_mem_toSubmodule := by
            intro g w hw
            change f (σ g w) ∈ q
            rw [IntertwiningMap.isIntertwining]
            exact q.apply_mem_toSubmodule g hw }
      rcases IsSimpleOrder.eq_bot_or_eq_top q' with h | h
      · apply Subrepresentation.toSubmodule_injective
        refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
        obtain ⟨w, rfl⟩ := hq.le hv
        have hw : w ∈ q' := hv
        rw [h] at hw
        rw [(Submodule.mem_bot ℂ).1 hw, map_zero]
      · exact absurd (fun v ⟨w, hw⟩ => by
          have : w ∈ q' := by rw [h]; exact Submodule.mem_top
          rw [← hw]; exact this) (not_le_of_gt hq)
  have hirr := Subrepresentation.isIrreducible_toRepresentation_of_isAtom hatom
  refine ⟨S, hirr, ?_⟩
  let e : W ≃ₗ[ℂ] S.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hinj
  let φ : σ.Equiv S.toRepresentation := Equiv.mk e fun g => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact IntertwiningMap.isIntertwining σ ρ f g w
  exact (char_iso φ).symm

end Characters

end Representation

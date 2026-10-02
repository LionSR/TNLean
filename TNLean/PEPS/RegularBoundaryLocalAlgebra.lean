/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularSiteGram
import Mathlib.Logic.Equiv.Prod

/-!
# Local operators on the invariant regular boundary

An operator on a proper subset of regular boundary legs preserves the globally
invariant boundary space precisely when it commutes with the simultaneous
group action on that subset. The complement must contain at least one leg.
No self-adjointness assumption on the local operator is required.

Source: auxiliary algebraic consequence of the regular invariant boundary in
SCP10, arXiv:1001.3807, Theorem 6.9, lines 2043–2076. This describes the
local algebras compatible with that support. It makes no decay estimate for
the logarithm in arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Extend an operator on the selected boundary legs by the identity on
the complementary legs. Source: auxiliary local-algebra construction on
the regular boundary of SCP10, Theorem 6.9, lines 2043–2076. -/
noncomputable def regularBoundaryLocalMap (A : Matrix (ι → G) (ι → G) ℂ) :
    ((ι ⊕ κ → G) → ℂ) →ₗ[ℂ] ((ι ⊕ κ → G) → ℂ) where
  toFun x η := ∑ θ : ι → G, A (η ∘ Sum.inl) θ * x (Sum.elim θ (η ∘ Sum.inr))
  map_add' x y := by
    funext η
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext η
    simp [Finset.mul_sum, mul_left_comm]

omit [Fintype G] [DecidableEq G] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] in
private theorem smul_sumElim (g : G) (a : ι → G) (b : κ → G) :
    g • Sum.elim a b = Sum.elim (g • a) (g • b) := by
  funext i
  cases i <;> rfl

private noncomputable def regularBoundaryOrbitIndicator (θ : ι ⊕ κ → G) :
    (ι ⊕ κ → G) → ℂ :=
  fun η => if ∃ g : G, η = g • θ then 1 else 0

private theorem regularBoundaryOrbitIndicator_mem_invariants (θ : ι ⊕ κ → G) :
    regularBoundaryOrbitIndicator θ ∈
      (regularLegRepresentation (ι ⊕ κ)).invariants := by
  intro h
  funext η
  simp only [regularLegRepresentation_apply, regularBoundaryOrbitIndicator]
  have he : (∃ g : G, h⁻¹ • η = g • θ) ↔ ∃ g : G, η = g • θ := by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨h * g, ?_⟩
      simpa only [smul_smul, mul_inv_cancel, one_smul] using congrArg (h • ·) hg
    · rintro ⟨g, rfl⟩
      exact ⟨h⁻¹ * g, smul_smul _ _ _⟩
  simp only [he]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem regularBoundaryOrbitIndicator_reference [Nonempty κ]
    (a c : ι → G) (g : G) :
    regularBoundaryOrbitIndicator (Sum.elim c (fun _ : κ => 1))
        (Sum.elim a (fun _ : κ => g)) = if a = g • c then 1 else 0 := by
  classical
  simp only [regularBoundaryOrbitIndicator]
  congr 1
  apply propext
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨j⟩ := ‹Nonempty κ›
    have hgh : g = h := by
      have hj := congrFun hh (Sum.inr j)
      simpa only [Pi.smul_apply, Sum.elim_inr, smul_eq_mul, mul_one] using hj
    subst h
    exact funext fun i => congrFun hh (Sum.inl i)
  · intro ha
    refine ⟨g, ?_⟩
    rw [smul_sumElim]
    simp [ha, Pi.smul_def, smul_eq_mul]

omit [DecidableEq κ] in
private theorem regularBoundaryLocalMap_orbitIndicator [Nonempty κ]
    (A : Matrix (ι → G) (ι → G) ℂ) (a c : ι → G) (g : G) :
    regularBoundaryLocalMap A
        (regularBoundaryOrbitIndicator (Sum.elim c (fun _ : κ => 1)))
        (Sum.elim a (fun _ : κ => g)) = A a (g • c) := by
  classical
  change (∑ θ : ι → G, A a θ *
    regularBoundaryOrbitIndicator (Sum.elim c (fun _ : κ => 1))
      (Sum.elim θ (fun _ : κ => g))) = _
  simp [regularBoundaryOrbitIndicator_reference]

omit [DecidableEq G] in
/-- An operator supported on a proper subset of regular boundary legs
preserves the globally invariant space exactly when its matrix entries are
invariant under common translations of their two configurations.
Source: auxiliary local-algebra consequence of SCP10, Theorem 6.9,
lines 2043–2076. The complementary leg set is nonempty. -/
theorem regularBoundaryLocalMap_preserves_invariants_iff [Nonempty κ]
    (A : Matrix (ι → G) (ι → G) ℂ) :
    (∀ x ∈ (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants,
      regularBoundaryLocalMap A x ∈
        (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants) ↔
      ∀ g : G, ∀ a c : ι → G, A (g • a) (g • c) = A a c := by
  classical
  constructor
  · intro h g a c
    have hv := h _ (regularBoundaryOrbitIndicator_mem_invariants
      (Sum.elim c (fun _ : κ => 1)))
    have he := congrFun (hv g) (Sum.elim (g • a) (fun _ : κ => g))
    have hη : g⁻¹ • Sum.elim (g • a) (fun _ : κ => g) =
        Sum.elim a (fun _ : κ => 1) := by
      rw [smul_sumElim, inv_smul_smul]
      simp [Pi.smul_def, smul_eq_mul]
    simp only [regularLegRepresentation_apply, hη,
      regularBoundaryLocalMap_orbitIndicator, one_smul] at he
    exact he.symm
  · intro h x hx g
    funext η
    rw [regularLegRepresentation_apply]
    change (∑ θ : ι → G, A (g⁻¹ • (η ∘ Sum.inl)) θ *
      x (Sum.elim θ (g⁻¹ • (η ∘ Sum.inr)))) =
        ∑ θ : ι → G, A (η ∘ Sum.inl) θ * x (Sum.elim θ (η ∘ Sum.inr))
    rw [← Equiv.sum_comp (MulAction.toPermHom G (ι → G) g⁻¹)
      (fun θ => A (g⁻¹ • (η ∘ Sum.inl)) θ *
        x (Sum.elim θ (g⁻¹ • (η ∘ Sum.inr))))]
    apply Finset.sum_congr rfl
    intro θ hθ
    change A (g⁻¹ • (η ∘ Sum.inl)) (g⁻¹ • θ) *
      x (Sum.elim (g⁻¹ • θ) (g⁻¹ • (η ∘ Sum.inr))) = _
    have he := congrFun (hx g) (Sum.elim θ (η ∘ Sum.inr))
    simp only [regularLegRepresentation_apply, smul_sumElim] at he
    rw [h, he]

omit [Fintype κ] [DecidableEq κ] in
private theorem regularLegRepresentation_single (g : G) (c : ι → G) :
    regularLegRepresentation ι g (Pi.single c 1) = Pi.single (g • c) 1 := by
  classical
  funext a
  simp only [regularLegRepresentation_apply, Pi.single_apply, inv_smul_eq_iff]

omit [Fintype κ] [DecidableEq κ] in
/-- Common-translation invariance of matrix entries is equivalent to
commutation with the regular action. Source: auxiliary commutant calculation
for the regular boundary of SCP10, Theorem 6.9, lines 2043–2076. -/
theorem regularLeg_commute_iff_entries (A : Matrix (ι → G) (ι → G) ℂ) :
    (∀ g : G, Commute (Matrix.toLin' A) (regularLegRepresentation ι g)) ↔
      ∀ g : G, ∀ a c : ι → G, A (g • a) (g • c) = A a c := by
  constructor
  · intro h g a c
    have he := congrFun (LinearMap.congr_fun (h g).eq (Pi.single c 1)) (g • a)
    simp only [Module.End.mul_apply, regularLegRepresentation_single,
      Matrix.toLin'_apply, Matrix.mulVec_single_one, regularLegRepresentation_apply,
      inv_smul_smul] at he
    exact he
  · intro h g
    change Matrix.toLin' A * regularLegRepresentation ι g =
      regularLegRepresentation ι g * Matrix.toLin' A
    apply (Pi.basisFun ℂ (ι → G)).ext
    intro c
    funext a
    simp only [Pi.basisFun_apply, Module.End.mul_apply, regularLegRepresentation_single,
      Matrix.toLin'_apply, Matrix.mulVec_single_one, regularLegRepresentation_apply]
    change A a (g • c) = A (g⁻¹ • a) c
    simpa only [smul_inv_smul] using h g (g⁻¹ • a) c

/-- The algebra of operators on a selected set of boundary legs that preserve
the global invariant support is exactly the commutant of its local regular
group action, provided the complement is nonempty. Source: auxiliary
local-algebra consequence of SCP10, Theorem 6.9, lines 2043–2076. -/
theorem regularBoundaryLocalMap_preserves_invariants_iff_commute [Nonempty κ]
    (A : Matrix (ι → G) (ι → G) ℂ) :
    (∀ x ∈ (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants,
      regularBoundaryLocalMap A x ∈
        (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants) ↔
      ∀ g : G, Commute (Matrix.toLin' A) (regularLegRepresentation ι g) := by
  rw [regularBoundaryLocalMap_preserves_invariants_iff, regularLeg_commute_iff_entries]

/-- For a nontrivial group, the projector onto the identity configuration
of a nonempty proper set of boundary legs does not preserve the global
invariant support. Thus the full local matrix algebra cannot restrict to
that support. Source: auxiliary support obstruction from SCP10, Theorem 6.9,
lines 2043–2076; relevant to arXiv:1903.09439, Conjecture
`gap2Dboundary1dlocal`, but not an obstruction to a local Gibbs logarithm. -/
theorem not_regularBoundaryLocalMap_single_preserves_invariants
    [Nonempty ι] [Nonempty κ] [Nontrivial G] :
    ¬ (∀ x ∈ (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants,
      regularBoundaryLocalMap (Matrix.single (1 : ι → G) 1 (1 : ℂ)) x ∈
        (regularLegRepresentation (G := G) (ι ⊕ κ)).invariants) := by
  intro h
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hconfig : g • (1 : ι → G) ≠ 1 := by
    intro he
    apply hg
    simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] using congrFun he i
  have he := (regularBoundaryLocalMap_preserves_invariants_iff _).mp h g 1 1
  simp [Matrix.single_apply] at he
  exact hconfig he.symm

end TNLean.PEPS

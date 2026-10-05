/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleGlobalPermutation
import TNLean.Algebra.ConjClassesConjugation

/-!
# A double exchange in three plaquette coordinates

Three directed vertical operators t₀,t₁,t₂ give plaquette labels
(a,b,c) = (t₀⁻¹t₁,t₁⁻¹t₂,t₂⁻¹). The exchange H(a,b) = (aba⁻¹,a)
is a conjugation-equivariant permutation. Applying it twice gives
(abab⁻¹a⁻¹,aba⁻¹,c), preserving the ordered product abc and the individual
conjugacy classes. At (g,h,h⁻¹), the last two labels have product ghg⁻¹h⁻¹.
The controlling label changes as well, providing the algebraic backreaction.

A common orientation correction converts ordered vertical labels into directed
ones. The resulting cycle permutation therefore has one original physical
unitary acting on every actual regional column and every actual global state,
with arbitrary common crossing and exterior operators.

Source: SCP10, arXiv:1001.3807, `eq:anyons:fluxon-braiding-lazy` and the
joint-flux discussion, lines 2360–2415. These are auxiliary algebraic and
contraction results; identifying their convention with the prescribed native
string routing is separate.

**Scope restriction (chosen three-cycle physical realization):** The physical
realization theorem takes a spanning tree, root, three distinct internal non-tree
bonds, and their common orientation flag. It does not assert a prescribed
lattice braid or a parent-Hamiltonian interpretation; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {J G : Type*} [DecidableEq J] [Group G]

/-- Convert three vertical operators into their successive plaquette holonomies.
This auxiliary coordinate change is used for SCP10, joint flux, lines 2380–2415. -/
def regularThreeCyclePlaquetteCoordinates (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) : Equiv.Perm (J → G) where
  toFun z e := if e = e₀ then (z e₀)⁻¹ * z e₁ else
    if e = e₁ then (z e₁)⁻¹ * z e₂ else if e = e₂ then (z e₂)⁻¹ else z e
  invFun z e := if e = e₀ then (z e₂)⁻¹ * (z e₁)⁻¹ * (z e₀)⁻¹ else
    if e = e₁ then (z e₂)⁻¹ * (z e₁)⁻¹ else if e = e₂ then (z e₂)⁻¹ else z e
  left_inv z := by
    funext e
    by_cases h₀ : e = e₀
    · subst e
      simp only [ite_true, ite_eq_right (Ne.symm h₀₁), ite_eq_right (Ne.symm h₀₂),
        ite_eq_right (Ne.symm h₁₂)]
      group
    · by_cases h₁ : e = e₁
      · subst e
        simp only [ite_eq_right (Ne.symm h₀₁), ite_true, ite_eq_right (Ne.symm h₀₂),
          ite_eq_right (Ne.symm h₁₂)]
        group
      · by_cases h₂ : e = e₂
        · subst e
          simp only [ite_eq_right (Ne.symm h₀₂), ite_eq_right (Ne.symm h₁₂), ite_true]
          exact inv_inv _
        · simp only [ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]
  right_inv z := by
    funext e
    by_cases h₀ : e = e₀
    · subst e
      simp only [ite_true, ite_eq_right (Ne.symm h₀₁), ite_eq_right (Ne.symm h₀₂),
        ite_eq_right (Ne.symm h₁₂)]
      group
    · by_cases h₁ : e = e₁
      · subst e
        simp only [ite_eq_right (Ne.symm h₀₁), ite_true, ite_eq_right (Ne.symm h₀₂),
          ite_eq_right (Ne.symm h₁₂)]
        group
      · by_cases h₂ : e = e₂
        · subst e
          simp only [ite_eq_right (Ne.symm h₀₂), ite_eq_right (Ne.symm h₁₂), ite_true]
          exact inv_inv _
        · simp only [ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]

/-- The plaquette coordinate change commutes with common conjugation.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularThreeCyclePlaquetteCoordinates_conjugation (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) (x : G) :
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
        (fun e => x * z e * x⁻¹) =
      fun e => x * regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e * x⁻¹ := by
  funext e
  simp only [regularThreeCyclePlaquetteCoordinates, Equiv.coe_fn_mk]
  split_ifs <;> group

private theorem coordinates_symm_conjugation (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) (x : G) :
    (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).symm
        (fun e => x * z e * x⁻¹) =
      fun e => x * (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).symm z e * x⁻¹ := by
  apply (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).injective
  rw [Equiv.apply_symm_apply, regularThreeCyclePlaquetteCoordinates_conjugation,
    Equiv.apply_symm_apply]

/-- Exchange two labels by (a,b) ↦ (aba⁻¹,a). This auxiliary permutation is
used for the SCP10 braiding discussion, lines 2360–2415. -/
def regularTwoCycleExchange (e₀ e₁ : J) (hne : e₀ ≠ e₁) : Equiv.Perm (J → G) :=
  (regularTwoCycleConjugation e₀ e₁ hne).trans
    ((Equiv.swap e₀ e₁).arrowCongr (Equiv.refl G))

/-- The exchange commutes with simultaneous conjugation.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularTwoCycleExchange_conjugation (e₀ e₁ : J) (hne : e₀ ≠ e₁)
    (z : J → G) (x : G) :
    regularTwoCycleExchange e₀ e₁ hne (fun e => x * z e * x⁻¹) =
      fun e => x * regularTwoCycleExchange e₀ e₁ hne z e * x⁻¹ := by
  funext e
  exact congrFun (regularTwoCycleConjugation_conjugation e₀ e₁ hne z x)
    ((Equiv.swap e₀ e₁).symm e)

/-- The selected exchange labels are aba⁻¹ and a. Auxiliary exchange for
SCP10, braiding discussion, lines 2360–2415. -/
theorem regularTwoCycleExchange_apply (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) :
    regularTwoCycleExchange e₀ e₁ hne z e₀ = z e₀ * z e₁ * (z e₀)⁻¹ ∧
      regularTwoCycleExchange e₀ e₁ hne z e₁ = z e₀ := by
  constructor
  · change regularTwoCycleConjugation e₀ e₁ hne z (Equiv.swap e₀ e₁ e₀) = _
    rw [Equiv.swap_apply_left, regularTwoCycleConjugation_apply_selected]
  · change regularTwoCycleConjugation e₀ e₁ hne z (Equiv.swap e₀ e₁ e₁) = _
    rw [Equiv.swap_apply_right, regularTwoCycleConjugation_apply_other _ _ _ _ _ hne]

/-- The exchange retains every other label. Auxiliary exchange for
SCP10, braiding discussion, lines 2360–2415. -/
theorem regularTwoCycleExchange_apply_other (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G)
    (e : J) (h₀ : e ≠ e₀) (h₁ : e ≠ e₁) :
    regularTwoCycleExchange e₀ e₁ hne z e = z e := by
  change regularTwoCycleConjugation e₀ e₁ hne z (Equiv.swap e₀ e₁ e) = _
  rw [Equiv.swap_apply_of_ne_of_ne h₀ h₁,
    regularTwoCycleConjugation_apply_other _ _ _ _ _ h₁]

/-- The double exchange includes conjugation of the target and backreaction
on the control. Auxiliary calculation for SCP10, lines 2360–2415. -/
theorem regularTwoCycleExchange_twice_apply (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) :
    regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₀ =
      z e₀ * z e₁ * z e₀ * (z e₁)⁻¹ * (z e₀)⁻¹ ∧
    regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₁ =
      z e₀ * z e₁ * (z e₀)⁻¹ := by
  have h := regularTwoCycleExchange_apply e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z)
  have h' := regularTwoCycleExchange_apply e₀ e₁ hne z
  constructor
  · rw [h.1, h'.1, h'.2]
    group
  · exact h.2.trans h'.1

/-- The double exchange preserves the ordered product of the two labels.
Auxiliary calculation for SCP10, braiding discussion, lines 2360–2415. -/
theorem regularTwoCycleExchange_twice_product (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) :
    regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₀ *
        regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₁ =
      z e₀ * z e₁ := by
  have h := regularTwoCycleExchange_twice_apply e₀ e₁ hne z
  rw [h.1, h.2]
  group

/-- The double exchange preserves both individual conjugacy classes.
Auxiliary calculation for SCP10, braiding discussion, lines 2360–2415. -/
theorem regularTwoCycleExchange_twice_classes (e₀ e₁ : J) (hne : e₀ ≠ e₁) (z : J → G) :
    ConjClasses.mk
        (regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₀) =
      ConjClasses.mk (z e₀) ∧
    ConjClasses.mk
        (regularTwoCycleExchange e₀ e₁ hne (regularTwoCycleExchange e₀ e₁ hne z) e₁) =
      ConjClasses.mk (z e₁) := by
  have h := regularTwoCycleExchange_twice_apply e₀ e₁ hne z
  constructor
  · rw [h.1]
    simpa only [mul_inv_rev, mul_assoc] using
      ConjClasses.mk_conjugate (z e₀) (z e₀ * z e₁)
  · rw [h.2]
    exact ConjClasses.mk_conjugate (z e₁) (z e₀)

/-- Transport the double exchange from plaquette labels back to vertical cycle
operators. Auxiliary coordinate operation for SCP10, lines 2360–2415. -/
def regularThreePlaquetteDoubleExchange (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) : Equiv.Perm (J → G) :=
  (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).trans
    (((regularTwoCycleExchange e₀ e₁ h₀₁).trans
      (regularTwoCycleExchange e₀ e₁ h₀₁)).trans
      (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).symm)

/-- The transported double exchange is conjugation-equivariant.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularThreePlaquetteDoubleExchange_conjugation (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) (x : G) :
    regularThreePlaquetteDoubleExchange e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ (fun e => x * z e * x⁻¹) =
      fun e => x * regularThreePlaquetteDoubleExchange e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e * x⁻¹ := by
  simp only [regularThreePlaquetteDoubleExchange, Equiv.trans_apply]
  rw [regularThreeCyclePlaquetteCoordinates_conjugation,
    regularTwoCycleExchange_conjugation, regularTwoCycleExchange_conjugation,
    coordinates_symm_conjugation]

/-- In plaquette coordinates the transported operation is exactly two exchanges.
Auxiliary operation for SCP10, joint flux discussion, lines 2380–2415. -/
theorem regularThreePlaquetteDoubleExchange_coordinates (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) :
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
        (regularThreePlaquetteDoubleExchange e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z) =
      regularTwoCycleExchange e₀ e₁ h₀₁
        (regularTwoCycleExchange e₀ e₁ h₀₁
          (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z)) := by
  simp only [regularThreePlaquetteDoubleExchange, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- The selected plaquette labels are t₀⁻¹t₁, t₁⁻¹t₂ and t₂⁻¹.
Auxiliary coordinates for SCP10, joint flux discussion, lines 2380–2415. -/
theorem regularThreeCyclePlaquetteCoordinates_apply (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) :
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e₀ = (z e₀)⁻¹ * z e₁ ∧
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e₁ = (z e₁)⁻¹ * z e₂ ∧
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e₂ = (z e₂)⁻¹ := by
  simp only [regularThreeCyclePlaquetteCoordinates, Equiv.coe_fn_mk, ite_true,
    ite_eq_right (Ne.symm h₀₁), ite_eq_right (Ne.symm h₀₂), ite_eq_right (Ne.symm h₁₂), and_self]

/-- Convert ordered cycle operators to directed ones using a common reversal
flag. Auxiliary finite-lattice convention for SCP10, lines 2360–2415. -/
def regularCycleOrientation (reversed : Bool) : Equiv.Perm (J → G) :=
  if reversed then Equiv.inv (J → G) else Equiv.refl _

omit [DecidableEq J] in
/-- Orientation reversal commutes with common conjugation.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularCycleOrientation_conjugation (reversed : Bool) (z : J → G) (x : G) :
    regularCycleOrientation reversed (fun e => x * z e * x⁻¹) =
      fun e => x * regularCycleOrientation reversed z e * x⁻¹ := by
  cases reversed
  · rfl
  · funext e
    change (x * z e * x⁻¹)⁻¹ = x * (z e)⁻¹ * x⁻¹
    group

omit [DecidableEq J] in
private theorem orientation_symm (reversed : Bool) :
    (regularCycleOrientation (J := J) (G := G) reversed).symm =
      regularCycleOrientation reversed := by
  cases reversed <;> rfl

/-- Correct both sides of the double exchange for the common edge orientation.
Auxiliary finite-lattice operation for SCP10, lines 2360–2415. -/
def regularOrientedThreePlaquetteDoubleExchange (reversed : Bool) (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) : Equiv.Perm (J → G) :=
  (regularCycleOrientation reversed).trans
    ((regularThreePlaquetteDoubleExchange e₀ e₁ e₂ h₀₁ h₀₂ h₁₂).trans
      (regularCycleOrientation reversed).symm)

/-- The orientation-corrected operation remains conjugation-equivariant.
Source: SCP10, accessible coordinates, lines 1765–1920. -/
theorem regularOrientedThreePlaquetteDoubleExchange_conjugation (reversed : Bool) (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) (x : G) :
    regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
        (fun e => x * z e * x⁻¹) =
      fun e => x *
        regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e * x⁻¹ := by
  simp only [regularOrientedThreePlaquetteDoubleExchange, Equiv.trans_apply, orientation_symm]
  rw [regularCycleOrientation_conjugation, regularThreePlaquetteDoubleExchange_conjugation,
    regularCycleOrientation_conjugation]

/-- The directed plaquette coordinates have exactly the double-exchange action.
Auxiliary finite-lattice operation for SCP10, lines 2360–2415. -/
theorem regularOrientedThreePlaquetteDoubleExchange_coordinates (reversed : Bool) (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G) :
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
        (regularCycleOrientation reversed
          (regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z)) =
      regularTwoCycleExchange e₀ e₁ h₀₁
        (regularTwoCycleExchange e₀ e₁ h₀₁
          (regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
            (regularCycleOrientation reversed z))) := by
  simp only [regularOrientedThreePlaquetteDoubleExchange, Equiv.trans_apply,
    Equiv.apply_symm_apply, regularThreePlaquetteDoubleExchange_coordinates]

private theorem coordinates_apply_other (e₀ e₁ e₂ : J)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G)
    (e : J) (h₀ : e ≠ e₀) (h₁ : e ≠ e₁) (h₂ : e ≠ e₂) :
    regularThreeCyclePlaquetteCoordinates e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e = z e := by
  simp only [regularThreeCyclePlaquetteCoordinates, Equiv.coe_fn_mk,
    ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂]

/-- Every cycle outside the selected triple is retained.
Auxiliary finite-lattice operation for SCP10, lines 2360–2415. -/
theorem regularOrientedThreePlaquetteDoubleExchange_apply_other (reversed : Bool)
    (e₀ e₁ e₂ : J) (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) (z : J → G)
    (e : J) (h₀ : e ≠ e₀) (h₁ : e ≠ e₁) (h₂ : e ≠ e₂) :
    regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z e = z e := by
  have h := congrFun
    (regularOrientedThreePlaquetteDoubleExchange_coordinates reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂ z) e
  rw [coordinates_apply_other _ _ _ _ _ _ _ _ h₀ h₁ h₂,
    regularTwoCycleExchange_apply_other _ _ _ _ _ h₀ h₁,
    regularTwoCycleExchange_apply_other _ _ _ _ _ h₀ h₁,
    coordinates_apply_other _ _ _ _ _ _ _ _ h₀ h₁ h₂] at h
  cases reversed
  · exact h
  · change _⁻¹ = _⁻¹ at h
    exact inv_injective h

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ} [Fintype G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]

/-- One original physical unitary implements the oriented double exchange on all
actual regional columns and global states. The same unitary is chosen before
all cycle labels, boundary configurations and common exterior operators.
Source: auxiliary accessible-coordinate realization for SCP10,
lines 1765–1920 and braiding discussion, lines 2360–2415. -/
theorem exists_unitary_regularOrientedThreePlaquetteDoubleExchange
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (reversed : Bool) (e₀ e₁ e₂ : RC (Γ := Γ) R T)
    (h₀₁ : e₀ ≠ e₁) (h₀₂ : e₀ ≠ e₂) (h₁₂ : e₁ ≠ e₂) :
    let φ := regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      regionLocalTerm R W ∈ Matrix.unitaryGroup (V → Fin d) ℂ ∧
      (∀ (ω : RC (Γ := Γ) R T → G)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T ω))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (φ ω)))) R
          (fun f => Fintype.equivFin G (θ f))) ∧
      ∀ (ω : RC (Γ := Γ) R T → G) (u : Edge Γ → G),
        regionLocalTerm R W *ᵥ stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T ω) u))) =
        stateCoeff (groupBondTensor (regularTwistedSite a
          (regularRegionBondExtension R (regularTreeCycleAssignment R T (φ ω)) u))) :=
  exists_unitary_regularCycleGlobalPermutation R T a ha hT htree o
    (regularOrientedThreePlaquetteDoubleExchange reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂)
    (regularOrientedThreePlaquetteDoubleExchange_conjugation reversed e₀ e₁ e₂ h₀₁ h₀₂ h₁₂)

end TNLean.PEPS

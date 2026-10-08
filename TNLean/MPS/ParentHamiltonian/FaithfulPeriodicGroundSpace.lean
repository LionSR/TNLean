/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.FaithfulStationaryClosure
import TNLean.MPS.CanonicalForm.ProjectorClosureDecomposition
import TNLean.MPS.Periodic.BlockDecomposition
import TNLean.MPS.ParentHamiltonian.PeriodicBlockedGroundSpace

/-!
# Periodic support presentations of faithful normalized generators

A trace-preserving tensor with a positive-definite stationary matrix has a
finite reducing decomposition into irreducible corners. The corner tensors
remain trace preserving and therefore have finite periods. Resolving the
virtual identity through the support isometries identifies every finite MPS
boundary space with the joint space of the periodic corners, including at
length zero. The isometries and both letterwise intertwining identities are
retained; repeated corners are not assumed inequivalent.

**Scope restriction (supplied faithful generating data):** The periodic
presentation theorem assumes a normalized tensor and a faithful stationary
matrix. It does not derive generating data from an arbitrary GVBS boundary
limit or invoke the minimality condition of Nachtergaele, Section 3. That
separate passage is recorded in
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.

Source context: Nachtergaele, arXiv:cond-mat/9410110, Section 3,
lines 1394--1483, and the finite support spaces at lines 1724--1738.
The reducing decomposition uses the faithful stationary-weight argument of
Wolf, Proposition 6.11 and Theorem 6.13; periodicity follows from the irreducible
channel peripheral-spectrum theorem and DCCSP17, arXiv:1708.00029, Section 2.1.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D E : ℕ}

/-- Left-canonical normalization passes through an isometric intertwiner.
This is the trace-preserving compression identity used in DCCSP17,
arXiv:1708.00029, Section 2.1, equation eq:unital. -/
theorem IsLeftCanonical.of_isometry_intertwine
    {A : MPSTensor d D} (hA : IsLeftCanonical A)
    (B : MPSTensor d E) (V : Matrix (Fin D) (Fin E) ℂ)
    (hV : Vᴴ * V = 1) (hInt : ∀ i, A i * V = V * B i) :
    IsLeftCanonical B := by
  change (∑ i : Fin d, (B i)ᴴ * B i) = 1
  have hGram (i : Fin d) : (B i)ᴴ * B i = Vᴴ * ((A i)ᴴ * A i) * V := by
    have h := congrArg (fun T => Tᴴ * T) (hInt i)
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ V (B i), hV, Matrix.one_mul] at h
    simpa only [Matrix.mul_assoc] using h.symm
  simp_rw [hGram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA, Matrix.mul_one, hV]

/-- Normalized generators with a faithful stationary matrix have a literal
periodic-sector presentation of every finite MPS support space. The isometries
and both intertwining directions are retained. No sector separation or
minimality is assumed. This is a consequence for supplied generating data in
Nachtergaele, arXiv:cond-mat/9410110, Section 3, lines 1394--1483, and the finite
support spaces at lines 1724--1738; it does not construct generators from a
GVBS boundary limit. -/
theorem exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.transferMap A ρ = ρ) :
    ∃ r : ℕ, 0 < r ∧ ∃ (dim : Fin r → ℕ), (∀ j, 0 < dim j) ∧
      ∃ (B : ∀ j, MPSTensor d (dim j))
        (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ) (period : Fin r → ℕ),
        (∀ j, IsPeriodic (period j) (B j)) ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∑ j, V j * (V j)ᴴ) = 1 ∧
        (∀ i j, i ≠ j → (V i)ᴴ * V j = 0) ∧
        (∀ j i, A i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * A i = B j i * (V j)ᴴ) ∧
        (∀ j i, B j i = (V j)ᴴ * A i * V j) ∧
        ∀ N, groundSpaceES A N =
          groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N := by
  obtain ⟨r, dim, B, V, hdim, hiso, hsum, horth, hint, hco, hcorner, hirr, _hmpv⟩ :=
    exists_irreducible_blockDecomp_with_isometry_of_hasInvariantProjectorClosure A
      (hasInvariantProjectorClosure_of_leftCanonical_of_posDef_fixedPoint A hA hρ hFix)
  have hr : 0 < r := by
    by_contra hr
    have hzero : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    simp at hsum
  let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hperiod : ∀ j, ∃ m, IsPeriodic m (B j) := fun j =>
    exists_isPeriodic_of_irreducible_of_isLeftCanonical (B j) (hirr j)
      (hA.of_isometry_intertwine (B j) (V j) (hiso j) (hint j))
  choose period hperiod using hperiod
  refine ⟨r, hr, dim, hdim, B, V, period, hperiod, hiso, hsum, horth,
    hint, hco, hcorner, ?_⟩
  intro N
  rw [groundSpaceES_toTensorFromBlocks_eq_iSup _ B (fun _ => one_ne_zero)]
  exact groundSpaceES_eq_iSup_of_isometric_sector_resolution A B V hiso hsum hint N

end MPSTensor

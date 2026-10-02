/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs
import TNLean.Algebra.FinKronecker
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Matrix product operators with a commuting boundary

The operator at length \(L\) has entries
\(\rho^{(L)}(X,M)_{\sigma,\tau}
=\operatorname{tr}(X M^{\sigma_1\tau_1}\cdots M^{\sigma_L\tau_L})\).
The admissible translation-invariant boundaries form the centralizer of all
tensor letters. Commutation does not imply positivity; the density-operator
condition is stated separately.

## Main definitions

* `mpoWithBoundary`: the boundary-weighted operator family.
* `commutingBoundaryAlgebra`: the centralizer of the tensor letters.
* `IsMPDOWithBoundary`: positivity at every positive length.

## References

* Sun, *Anomalous matrix product operator symmetries and 1D mixed-state phases*,
  arXiv:2504.16985, lines 175–182.
-/

open scoped Matrix ComplexOrder BigOperators

namespace Matrix

/-- Expansion of a boundary-weighted trace through a product of linear combinations. -/
theorem trace_mul_prod_ofFn_sum_smul {n J : Type*} [Fintype n] [DecidableEq n]
    [Fintype J] {L : ℕ} (X : Matrix n n ℂ)
    (f : Fin L → J → ℂ) (B : Fin L → J → Matrix n n ℂ) :
    trace (X * (List.ofFn fun l => ∑ j, f l j • B l j).prod) =
      ∑ ch : Fin L → J, (∏ l, f l (ch l)) *
        trace (X * (List.ofFn fun l => B l (ch l)).prod) := by
  rw [List.prod_ofFn_sum, Matrix.mul_sum, trace_sum]
  simp only [List.prod_ofFn_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

end Matrix

namespace MPSTensor

/-- The boundary-weighted vector coefficient of a tensor.
Source: arXiv:2504.16985, lines 175–181. -/
noncomputable def mpvWithBoundary {d D L : ℕ} (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (w : Fin L → Fin d) : ℂ :=
  Matrix.trace (X * Kraus.evalWord A (List.ofFn w))

/-- Identity-boundary coefficients are ordinary periodic vector coefficients. -/
@[simp] theorem mpvWithBoundary_one {d D L : ℕ} (A : MPSTensor d D)
    (w : Fin L → Fin d) : mpvWithBoundary A 1 w = mpv A w := by
  simp [mpvWithBoundary, mpv, coeff]

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- The boundary-weighted periodic operator, as in arXiv:2504.16985,
lines 175–181. The definition itself permits any virtual boundary. -/
noncomputable def mpoWithBoundary (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (L : ℕ) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ :=
  fun σ τ => Matrix.trace (X * evalWord M (List.ofFn σ) (List.ofFn τ))

/-- The boundary matrices commuting with every tensor letter. Source:
arXiv:2504.16985, line 182. -/
def commutingBoundaryAlgebra (M : MPOTensor d D) :
    Subalgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Subalgebra.centralizer ℂ (Set.range M.toMPSTensor)

/-- Positivity of the boundary-weighted operator at every positive length.
Source: arXiv:2504.16985, lines 175–182. -/
def IsMPDOWithBoundary (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ L, 0 < L → (mpoWithBoundary M X L).PosSemidef

/-- The identity boundary gives the ordinary periodic operator. -/
@[simp] theorem mpoWithBoundary_one (M : MPOTensor d D) (L : ℕ) :
    mpoWithBoundary M 1 L = mpo M L := by
  ext σ τ
  simp [mpoWithBoundary, mpo_apply, mpoMatrixEntry]

/-- The identity-boundary density condition is the ordinary MPDO condition. -/
@[simp] theorem isMPDOWithBoundary_one_iff (M : MPOTensor d D) :
    IsMPDOWithBoundary M 1 ↔ IsMPDO M := by
  simp [IsMPDOWithBoundary, IsMPDO]

/-- Membership of the boundary algebra is precisely letterwise commutation. -/
@[simp] theorem mem_commutingBoundaryAlgebra_iff (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    X ∈ commutingBoundaryAlgebra M ↔ ∀ i j, Commute X (M i j) := by
  simp only [commutingBoundaryAlgebra, Subalgebra.mem_centralizer_iff, Set.forall_mem_range]
  constructor
  · intro h i j
    have h' := h (finProdFinEquiv (i, j))
    simpa [toMPSTensor, Commute, SemiconjBy, eq_comm] using h'
  · intro h i
    exact (h i.divNat i.modNat).eq.symm

/-- An admissible boundary commutes with every virtual word. -/
theorem commute_evalWord_of_mem_commutingBoundaryAlgebra (M : MPOTensor d D)
    {X : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ commutingBoundaryAlgebra M)
    {L : ℕ} (σ τ : Fin L → Fin d) :
    Commute X (evalWord M (List.ofFn σ) (List.ofFn τ)) := by
  rw [evalWord_ofFn]
  apply Commute.list_prod_right
  intro B hB
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hB
  exact (mem_commutingBoundaryAlgebra_iff M X).mp hX (σ l) (τ l)

end MPOTensor

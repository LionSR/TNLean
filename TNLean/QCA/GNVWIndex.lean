/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.CanonicalAdjacentSupportGeneration
import Mathlib.Algebra.Order.Positive.Field

/-!
# The positive-rational homogeneous GNVW index

Choose the positive matrix-size family of the actual support algebras
already derived from the nearest-neighbour automorphism. The index is its
even size at the fixed cut zero, divided by the physical one-site size.
Both actual adjacent-generation size identities imply all three source
ratio formulas and independence of the integer cut.

Source: GNVW, arXiv:0910.3675v2, equation dimtransfer, lines 1317--1329.
This does not prove independence of arbitrary regrouping, a composition
law, a tensor-product law, or either direct translation normalization.

**Scope restriction (homogeneous chain):** The on-site size is one fixed
positive integer. GNVW also permit site-dependent cell dimensions; see
`docs/paper-gaps/gnvw12_site_dependent_adjacent_generation_scope.tex`.
The already supplied nearest-neighbour presentation is retained.
-/

namespace SpinChain
namespace PropagatesWithin

variable {d : ℕ} [NeZero d]
  {ω : QuasiLocalAlgebra d ≃⋆ₐ[ℂ] QuasiLocalAlgebra d}

/-- One coherent positive matrix-size family of the actual support
algebras, chosen from their derived presentations and size identities;
GNVW, arXiv:0910.3675v2, equations AARReven and AARRodd, lines 1276--1318. -/
noncomputable def supportAlgebraMatrixSize
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) : ℤ → ℕ :=
  Classical.choose (exists_supportAlgebra_matrixSizes_mul hω)

/-- The chosen actual matrix-size family retains positivity, explicit
star-algebra presentations and both derived product identities;
GNVW, arXiv:0910.3675v2, equations AARReven and AARRodd, lines 1276--1318. -/
theorem supportAlgebraMatrixSize_spec
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    (∀ y, NeZero (supportAlgebraMatrixSize hω y)) ∧
      (∀ x, Nonempty (↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (supportAlgebraMatrixSize hω (2 * x)))
          (Fin (supportAlgebraMatrixSize hω (2 * x))) ℂ)) ∧
      (∀ x, Nonempty (↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ]
        Matrix (Fin (supportAlgebraMatrixSize hω (2 * x + 1)))
          (Fin (supportAlgebraMatrixSize hω (2 * x + 1))) ℂ)) ∧
      (∀ x, supportAlgebraMatrixSize hω (2 * x) *
        supportAlgebraMatrixSize hω (2 * x + 1) = d * d) ∧
      (∀ x, supportAlgebraMatrixSize hω (2 * x + 1) *
        supportAlgebraMatrixSize hω (2 * x + 2) = d * d) :=
  Classical.choose_spec (exists_supportAlgebra_matrixSizes_mul hω)

/-- Actual support matrix sizes are positive, rather than possibly zero
vector-space dimensions; GNVW, arXiv:0910.3675v2, lines 1278--1282. -/
instance supportAlgebraMatrixSize_neZero
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (y : ℤ) :
    NeZero (supportAlgebraMatrixSize hω y) :=
  (supportAlgebraMatrixSize_spec hω).1 y

/-- Consecutive cuts give the same even support size, by the two actual
adjacent-generation size identities. This is the homogeneous arithmetic
in GNVW equation dimtransfer, arXiv:0910.3675v2, lines 1317--1324. -/
theorem supportAlgebraMatrixSize_even_add_one
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    supportAlgebraMatrixSize hω (2 * (x + 1)) = supportAlgebraMatrixSize hω (2 * x) := by
  have hE := (supportAlgebraMatrixSize_spec hω).2.2.2.1 x
  have hO := (supportAlgebraMatrixSize_spec hω).2.2.2.2 x
  have hmul : supportAlgebraMatrixSize hω (2 * x) *
      supportAlgebraMatrixSize hω (2 * x + 1) =
      supportAlgebraMatrixSize hω (2 * x + 2) *
        supportAlgebraMatrixSize hω (2 * x + 1) := by
    rw [hE, Nat.mul_comm (supportAlgebraMatrixSize hω (2 * x + 2)), hO]
  have hsize := Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (NeZero.ne (supportAlgebraMatrixSize hω (2 * x + 1)))) hmul
  simpa only [show 2 * (x + 1) = 2 * x + 2 by ring] using hsize.symm

/-- The actual even support size is independent of the integer cut,
including negative cuts. This uses the two size identities, without
translation covariance; GNVW equation dimtransfer, lines 1317--1324. -/
theorem supportAlgebraMatrixSize_even_eq_zero
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    supportAlgebraMatrixSize hω (2 * x) = supportAlgebraMatrixSize hω 0 := by
  induction x using Int.induction_on with
  | zero => simp only [mul_zero]
  | succ i hi => rw [supportAlgebraMatrixSize_even_add_one, hi]
  | pred i hi =>
      have hstep := supportAlgebraMatrixSize_even_add_one hω (-(i : ℤ) - 1)
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at hstep
      have harg : -((i + 1 : ℕ) : ℤ) = -(i : ℤ) - 1 := by omega
      rw [harg]
      exact hstep.symm.trans hi

/-- The homogeneous GNVW index at the fixed cut zero, in exactly the
multiplicative group of positive rationals. The group structure alone
does not assert a composition law for automorphisms.
Source: GNVW, arXiv:0910.3675v2, equation dimtransfer, lines 1317--1329. -/
noncomputable def gnvwIndex (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) :
    {q : ℚ // 0 < q} :=
  ⟨(supportAlgebraMatrixSize hω 0 : ℚ) / (d : ℚ), by
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero
      (NeZero.ne (supportAlgebraMatrixSize hω 0)))
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))⟩

/-- The fixed-cut index has the even ratio at every integer cut;
GNVW, arXiv:0910.3675v2, equation dimtransfer, lines 1317--1324. -/
theorem coe_gnvwIndex_eq_even
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (gnvwIndex hω : ℚ) = (supportAlgebraMatrixSize hω (2 * x) : ℚ) / (d : ℚ) := by
  change (supportAlgebraMatrixSize hω 0 : ℚ) / (d : ℚ) = _
  rw [supportAlgebraMatrixSize_even_eq_zero]

/-- The ratio is explicitly independent of any two integer cuts, as a
consequence of the single fixed-cut index. Source: GNVW,
arXiv:0910.3675v2, equation dimtransfer, lines 1317--1324. -/
theorem gnvwIndex_ratio_eq
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x y : ℤ) :
    (supportAlgebraMatrixSize hω (2 * x) : ℚ) / (d : ℚ) =
      (supportAlgebraMatrixSize hω (2 * y) : ℚ) / (d : ℚ) :=
  (coe_gnvwIndex_eq_even hω x).symm.trans (coe_gnvwIndex_eq_even hω y)

/-- The reciprocal odd-size presentation of the same index, using the
same ordered support family; it is not a reconstruction after changing
cell pairing. GNVW equation dimtransfer, arXiv:0910.3675v2, lines 1317--1324. -/
theorem coe_gnvwIndex_eq_odd
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (gnvwIndex hω : ℚ) = (d : ℚ) / (supportAlgebraMatrixSize hω (2 * x + 1) : ℚ) := by
  rw [coe_gnvwIndex_eq_even hω x]
  apply (div_eq_div_iff
    (by exact_mod_cast NeZero.ne d : (d : ℚ) ≠ 0)
    (by exact_mod_cast NeZero.ne (supportAlgebraMatrixSize hω (2 * x + 1)) :
      (supportAlgebraMatrixSize hω (2 * x + 1) : ℚ) ≠ 0)).mpr
  exact_mod_cast (supportAlgebraMatrixSize_spec hω).2.2.2.1 x

/-- The next-cut even presentation is the same fixed index. No covariance
is assumed; GNVW equation dimtransfer, arXiv:0910.3675v2, lines 1317--1324. -/
theorem coe_gnvwIndex_eq_next_even
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) :
    (gnvwIndex hω : ℚ) = (supportAlgebraMatrixSize hω (2 * x + 2) : ℚ) / (d : ℚ) := by
  simpa only [show 2 * (x + 1) = 2 * x + 2 by ring]
    using coe_gnvwIndex_eq_even hω (x + 1)

/-- Matrix-size uniqueness for an explicit presentation of an actual even
support factor; GNVW, arXiv:0910.3675v2, lines 1278--1324. -/
theorem supportAlgebraMatrixSize_even_eq_of_equiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) {s : ℕ}
    (e : ↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    supportAlgebraMatrixSize hω (2 * x) = s := by
  obtain ⟨eChosen⟩ := (supportAlgebraMatrixSize_spec hω).2.1 x
  exact Matrix.matrixAlgEquiv_fin_eq (eChosen.symm.trans e).toAlgEquiv

/-- Matrix-size uniqueness for an explicit presentation of an actual odd
support factor; GNVW, arXiv:0910.3675v2, lines 1278--1324. -/
theorem supportAlgebraMatrixSize_odd_eq_of_equiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) {s : ℕ}
    (e : ↥(oddSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    supportAlgebraMatrixSize hω (2 * x + 1) = s := by
  obtain ⟨eChosen⟩ := (supportAlgebraMatrixSize_spec hω).2.2.1 x
  exact Matrix.matrixAlgEquiv_fin_eq (eChosen.symm.trans e).toAlgEquiv

/-- Any explicit full-matrix presentation of an actual even support
factor computes the same index. Matrix-size uniqueness removes the
choice of presentation; GNVW, arXiv:0910.3675v2, lines 1278--1324. -/
theorem coe_gnvwIndex_eq_of_evenSupportAlgebra_equiv
    (hω : PropagatesWithin ω (Finset.Icc (-1) 1)) (x : ℤ) {s : ℕ}
    (e : ↥(evenSupportAlgebra hω x) ≃⋆ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ) :
    (gnvwIndex hω : ℚ) = (s : ℚ) / (d : ℚ) := by
  rw [coe_gnvwIndex_eq_even hω x, supportAlgebraMatrixSize_even_eq_of_equiv hω x e]

end PropagatesWithin
end SpinChain

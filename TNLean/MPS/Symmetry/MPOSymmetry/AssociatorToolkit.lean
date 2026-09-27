/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.MPDO.IdentityTensor
import TNLean.MPS.Symmetry.MPOSymmetry.Associator

/-!
# Tools for computing anomaly three-cochains of explicit representations

General facts used when the anomaly three-cochain of
`MPOTensor.GroupFamily.FusionData.omega` is computed for an explicit group of
matrix product operators, such as the decorated CZX representation of `ℤ₂` or
the phase-decorated shift representation of `ℤ₃`.

* The bond-one identity tensor `MPOTensor.idTensor d` is normal, its doubled-index
  words are scalar multiples of the identity, and stacking it with a tensor `M`
  on either side gives `M` back up to the canonical identification of the bond
  spaces `Fin (1 * D)` and `Fin (D * 1)` with `Fin D`.
* Casting identifications of bond spaces: `MPOTensor.mulTensorAssocEquiv` and
  `MPOTensor.GroupFamily.castMat` preserve the value of an index, so both are
  identities once the bond dimensions are explicit numerals.
* Products with identity factors commute with the entrywise image of a ring
  homomorphism into `ℂ` (`MPOTensor.kronId_complexOfRing`,
  `MPOTensor.idKron_complexOfRing`).
* Two-letter intertwining identities of two fusion trees with the target tensor,
  together with a one-letter relation, give the dressed identity of the anomaly
  three-cochain on every nonempty word
  (`MPSTensor.IsDressedProportional.of_forall_mul_mul`). For explicit tensors
  these finitely many identities can be checked by `decide`.

Source: arXiv:2502.20257, display preceding `eq:3-cocycle`, `main.tex` lines
1506--1535, for the dressed identity defining the three-cochain.
-/

open scoped Matrix Kronecker

namespace MPSTensor

variable {d D m k : ℕ}

/-- **Dressed identities from local identities.** Let two left boundaries `L` and
`R` of a tensor `T` both intertwine two letters with a tensor `A`,
`X T^a T^b = A^a X T^b`, and satisfy `L T^a = z R T^a` on every letter. Then
`L T^w = z R T^w` for every nonempty word `w`; in particular `L` and `R` are
dressed proportional with scalar `z`.

For the two fusion trees of a triple product, `A` is the tensor of the product of
the three group elements, and the conclusion is the dressed identity that
characterizes the anomaly three-cochain (arXiv:2502.20257, display preceding
`eq:3-cocycle`, `main.tex` lines 1506--1535). -/
theorem mul_evalWord_eq_smul_of_forall_mul_mul {T : MPSTensor d D} {A : MPSTensor d m}
    {L R : Matrix (Fin m) (Fin D) ℂ} {z : ℂ}
    (hL : ∀ a b, L * T a * T b = A a * L * T b) (hR : ∀ a b, R * T a * T b = A a * R * T b)
    (h1 : ∀ a, L * T a = z • (R * T a)) (w : List (Fin d)) (hw : w ≠ []) :
    L * Kraus.evalWord T w = z • (R * Kraus.evalWord T w) := by
  induction w with
  | nil => exact absurd rfl hw
  | cons a w ih =>
      cases w with
      | nil => simpa using h1 a
      | cons b w =>
          have ih' := ih (List.cons_ne_nil _ _)
          rw [Kraus.evalWord_cons] at ih'
          calc
            L * Kraus.evalWord T (a :: b :: w) = L * T a * T b * Kraus.evalWord T w := by
              simp only [Kraus.evalWord_cons, Matrix.mul_assoc]
            _ = A a * (L * (T b * Kraus.evalWord T w)) := by
              rw [hL]; simp only [Matrix.mul_assoc]
            _ = z • (R * T a * T b * Kraus.evalWord T w) := by
              rw [ih', hR, Matrix.mul_smul]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Kraus.evalWord_cons, Matrix.mul_assoc]

/-- The dressed-proportionality form of `mul_evalWord_eq_smul_of_forall_mul_mul`. -/
theorem IsDressedProportional.of_forall_mul_mul {T : MPSTensor d D} {A : MPSTensor d m}
    {L R : Matrix (Fin m) (Fin D) ℂ} {z : ℂ}
    (hL : ∀ a b, L * T a * T b = A a * L * T b) (hR : ∀ a b, R * T a * T b = A a * R * T b)
    (h1 : ∀ a, L * T a = z • (R * T a)) : IsDressedProportional T L R z :=
  ⟨1, fun w hw ↦ mul_evalWord_eq_smul_of_forall_mul_mul hL hR h1 w
    (List.ne_nil_of_length_pos hw)⟩

/-- A tensor reduces onto an equal tensor through the identity matrices. -/
theorem isReduction_one_one_of_eq {B A : MPSTensor d D} (h : B = A) :
    IsReduction B A 1 1 := by
  subst h
  exact ⟨Matrix.one_mul 1, fun w ↦ by rw [Matrix.one_mul, Matrix.mul_one]⟩

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-! ### Explicit bond identifications -/

/-- A permutation matrix of `finCongr` from `Fin n` to itself is the identity. For
explicit numerals `n` this applies to `finCongr h` with `h : n₁ = n₂` whenever `n₁`
and `n₂` reduce to the same numeral. -/
theorem finCongr_toMatrix_eq_one {n : ℕ} (h : n = n) :
    (finCongr h).toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [finCongr_refl, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/-- The bond reassociation preserves the value of an index: with row-major product
encodings, `((a, b), c)` and `(a, (b, c))` have the same position. -/
theorem mulTensorAssocEquiv_val (D₁ D₂ D₃ : ℕ) (x : Fin (D₁ * D₂ * D₃)) :
    (mulTensorAssocEquiv D₁ D₂ D₃ x : ℕ) = x := by
  simp only [mulTensorAssocEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.prodAssoc_apply, Equiv.refl_apply, finProdFinEquiv_apply_val,
    finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]
  have h1 := Nat.div_add_mod (x / D₃) D₂
  have h2 := Nat.div_add_mod' (x : ℕ) D₃
  calc
    _ = (D₂ * (x / D₃ / D₂) + x / D₃ % D₂) * D₃ + x % D₃ := by ring
    _ = x := by rw [h1, h2]

/-- The bond reassociation is the identification `finCongr` of `Fin (D₁ * D₂ * D₃)` with
`Fin (D₁ * (D₂ * D₃))`. -/
theorem mulTensorAssocEquiv_eq_finCongr (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocEquiv D₁ D₂ D₃ = finCongr (mul_assoc D₁ D₂ D₃) :=
  Equiv.ext fun x ↦ Fin.ext (by rw [mulTensorAssocEquiv_val, finCongr_apply, Fin.val_cast])

/-- The inverse bond associator is the permutation matrix of `finCongr`; for explicit
bond dimensions it is the identity by `finCongr_toMatrix_eq_one`. -/
theorem mulTensorAssocInvMatrix_eq_finCongr (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocInvMatrix D₁ D₂ D₃ =
      (finCongr (mul_assoc D₁ D₂ D₃).symm).toPEquiv.toMatrix := by
  rw [mulTensorAssocInvMatrix, mulTensorAssocEquiv_eq_finCongr, finCongr_symm]

/-- The bond associator is the permutation matrix of `finCongr`. -/
theorem mulTensorAssocMatrix_eq_finCongr (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocMatrix D₁ D₂ D₃ =
      (finCongr (mul_assoc D₁ D₂ D₃)).toPEquiv.toMatrix := by
  rw [mulTensorAssocMatrix, mulTensorAssocEquiv_eq_finCongr]

/-- The bond identification of `GroupFamily.castMat` is the permutation matrix of
`finCongr`; for explicit bond dimensions it is the identity by
`finCongr_toMatrix_eq_one`. -/
theorem GroupFamily.castMat_eq_finCongr {G : Type*} [Group G] (F : GroupFamily G d)
    {a b : G} (e : a = b) :
    F.castMat e = (finCongr (congrArg F.bondDim e.symm)).toPEquiv.toMatrix := rfl

/-! ### Identity factors and entrywise images -/

section ComplexOfRing

variable {R : Type*} [CommRing R] (f : R →+* ℂ)

/-- `X ⊗ 1` commutes with the entrywise image of a ring homomorphism into `ℂ`. -/
theorem kronId_complexOfRing {m n : ℕ} (X : Matrix (Fin m) (Fin n) R) (D : ℕ) :
    kronId (MPSTensor.complexOfRing f X) D =
      MPSTensor.complexOfRing f ((X ⊗ₖ (1 : Matrix (Fin D) (Fin D) R)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext r c
  simp only [kronId, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    MPSTensor.complexOfRing_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

/-- `1 ⊗ X` commutes with the entrywise image of a ring homomorphism into `ℂ`. -/
theorem idKron_complexOfRing {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) R) :
    idKron D (MPSTensor.complexOfRing f X) =
      MPSTensor.complexOfRing f (((1 : Matrix (Fin D) (Fin D) R) ⊗ₖ X).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  ext r c
  simp only [idKron, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    MPSTensor.complexOfRing_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

end ComplexOfRing

end MPOTensor

namespace Multiplicative

/-- A statement about every element of `ℤ₂`, written multiplicatively, follows from its
two instances. -/
theorem forall_zmod_two {P : Multiplicative (ZMod 2) → Prop}
    (h0 : P (ofAdd 0)) (h1 : P (ofAdd 1)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1]

/-- A statement about every element of `ℤ₃`, written multiplicatively, follows from its
three instances. -/
theorem forall_zmod_three {P : Multiplicative (ZMod 3) → Prop}
    (h0 : P (ofAdd 0)) (h1 : P (ofAdd 1)) (h2 : P (ofAdd 2)) : ∀ x, P x := by
  intro x
  fin_cases x
  exacts [h0, h1, h2]

end Multiplicative

namespace MPOTensor

variable {d D : ℕ}

/-! ### The bond-one identity tensor -/

/-- The doubled-index letters of the identity tensor: the letter `(i, j)` is `δ_{ij}`
times the identity. -/
theorem idTensor_toMPSTensor (a : Fin (d * d)) :
    (idTensor d).toMPSTensor a = (if a.divNat = a.modNat then (1 : ℂ) else 0) • 1 := by
  ext r c
  simp only [toMPSTensor, idTensor, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Doubled-index words of the identity tensor are the product of the weights
`δ_{ij}` of their letters times the identity. -/
theorem evalWord_idTensor_toMPSTensor (w : List (Fin (d * d))) :
    Kraus.evalWord (idTensor d).toMPSTensor w =
      (w.map fun a ↦ if a.divNat = a.modNat then (1 : ℂ) else 0).prod • 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [Kraus.evalWord_cons, ih, idTensor_toMPSTensor, smul_mul_smul_comm, Matrix.one_mul]
      simp

/-- The bond-one identity tensor on a nonempty physical alphabet is normal: its
letter `(0, 0)` is the identity, which spans the one-by-one matrices. -/
theorem idTensor_isNormal [NeZero d] : Kraus.IsNormal (idTensor d).toMPSTensor := by
  refine ⟨1, one_pos, Submodule.eq_top_of_forall_single_mem _ fun i j ↦ ?_⟩
  have hij : Matrix.single i j (1 : ℂ) = 1 := by
    ext r c
    simp [Subsingleton.elim i r, Subsingleton.elim j c, Subsingleton.elim r c, Matrix.one_apply]
  rw [hij]
  refine Submodule.subset_span ⟨fun _ ↦ finProdFinEquiv (0, 0), ?_⟩
  simp [idTensor_toMPSTensor]

/-- Stacking the identity tensor on the left of `M` gives `M`, up to the canonical
identification of `Fin (1 * D)` with `Fin D`. -/
theorem mulTensor_idTensor_left (M : MPOTensor d D) :
    mulTensor (idTensor d) M =
      fun i j ↦ (M i j).submatrix (finCongr (one_mul D)) (finCongr (one_mul D)) := by
  have h : ∀ r : Fin (1 * D),
      finProdFinEquiv.symm r = ((0 : Fin 1), finCongr (one_mul D) r) := fun r ↦ by
    refine Prod.ext (Subsingleton.elim _ _) (Fin.ext ?_)
    simp only [finProdFinEquiv_symm_apply, Fin.coe_modNat, finCongr_apply, Fin.val_cast]
    exact Nat.mod_eq_of_lt (by simpa using r.isLt)
  funext i j
  ext r c
  simp only [mulTensor_apply, idTensor, Matrix.submatrix_apply, h, Matrix.sum_apply,
    Matrix.kroneckerMap_apply]
  simp only [apply_ite (fun X : Matrix (Fin 1) (Fin 1) ℂ ↦ X 0 0), Matrix.one_apply_eq,
    Matrix.zero_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- Stacking the identity tensor on the right of `M` gives `M`, up to the canonical
identification of `Fin (D * 1)` with `Fin D`. -/
theorem mulTensor_idTensor_right (M : MPOTensor d D) :
    mulTensor M (idTensor d) =
      fun i j ↦ (M i j).submatrix (finCongr (mul_one D)) (finCongr (mul_one D)) := by
  have h : ∀ r : Fin (D * 1),
      finProdFinEquiv.symm r = (finCongr (mul_one D) r, (0 : Fin 1)) := fun r ↦ by
    refine Prod.ext (Fin.ext ?_) (Subsingleton.elim _ _)
    simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, finCongr_apply, Fin.val_cast]
    exact Nat.div_one _
  funext i j
  ext r c
  simp only [mulTensor_apply, idTensor, Matrix.submatrix_apply, h, Matrix.sum_apply,
    Matrix.kroneckerMap_apply]
  simp only [apply_ite (fun X : Matrix (Fin 1) (Fin 1) ℂ ↦ X 0 0), Matrix.one_apply_eq,
    Matrix.zero_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

end MPOTensor

/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.CZY.CZYFusion

/-!
# Associativity of the CZY fusion maps on the physical images

**Local fix (associativity):** The printed relation of arXiv:2509.03600, Section II and
Appendix B, for every triple fails on the full virtual space. At `(0,0,0)` no complex scalar
relates the two maps. After a change of normalization the expected phase relation holds on the
images of the three-layer physical letters. This corrected statement is proved over the integers
and complexes and extends to all nonempty physical words; the scalar is `-1` exactly at
`(1,1,1)`. The source assertion, counterexample and corrected formulation are recorded in
`docs/paper-gaps/lmsvkl25_czy_associator.tex`.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators

namespace CZYCompression

open MPSTensor CZXCompression

/-- Bond dimensions of the existing tensors `A₀` and `A₁`. -/
def czyDim : Fin 2 → ℕ
  | 0 => 3
  | 1 => 2

/-- The existing integer tensors of arXiv:2509.03600, Section II, main.tex lines 203–240. -/
def czyFamilyInt (a : Fin 2) : Fin 2 → Fin 2 → Matrix (Fin (czyDim a)) (Fin (czyDim a)) ℤ :=
  match a with
  | 0 => czyReducedIntTensor
  | 1 => czyIntTensor

/-- An integer normalization of the fusion maps: `F₀₀ = Y₀₀`, `F₀₁ = 2Y₀₁`,
`F₁₀ = 2Y₁₀`, and `F₁₁ = 2√2 Y₁₁`, with product bond coordinates.
The scalar associator relation holds after one physical-site contraction; see
`docs/paper-gaps/lmsvkl25_czy_associator.tex` for the correction to arXiv:2509.03600,
Section II, main.tex lines 283–294. -/
def czyFusionInt (a b : Fin 2) :
    Matrix (Fin (czyDim (a + b))) (Fin (czyDim a) × Fin (czyDim b)) ℤ :=
  match a, b with
  | 0, 0 => czyY00Int.submatrix id finProdFinEquiv
  | 0, 1 => (2 • czyY01Int).submatrix id finProdFinEquiv
  | 1, 0 => (2 • czyY10Int).submatrix id finProdFinEquiv
  | 1, 1 => (2 • czyY11Int).submatrix id finProdFinEquiv

/-- The three-layer tensor with bond order `((a,b),c)`. -/
def czyTripleInt (a b c i k : Fin 2) :
    Matrix ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  ∑ j : Fin 2, ∑ l : Fin 2,
    (czyFamilyInt a i j ⊗ₖ czyFamilyInt b j l) ⊗ₖ czyFamilyInt c l k

/-- The left fusion `Fₐ₊ᵦ,𝒸 (Fₐ,ᵦ ⊗ I𝒸)` in the product bond coordinates. -/
def czyLeftInt (a b c : Fin 2) :
    Matrix (Fin (czyDim (a + b + c)))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  czyFusionInt (a + b) c * (czyFusionInt a b ⊗ₖ (1 : Matrix (Fin (czyDim c)) _ ℤ))

/-- The right fusion `Fₐ,ᵦ₊𝒸 (Iₐ ⊗ Fᵦ,𝒸)`, with both bond orders identified. -/
def czyRightInt (a b c : Fin 2) :
    Matrix (Fin (czyDim (a + b + c)))
      ((Fin (czyDim a) × Fin (czyDim b)) × Fin (czyDim c)) ℤ :=
  (czyFusionInt a (b + c) * ((1 : Matrix (Fin (czyDim a)) _ ℤ) ⊗ₖ czyFusionInt b c)).submatrix
    (Fin.cast (congrArg czyDim (add_assoc a b c))) (fun x => (x.1.1, x.1.2, x.2))

private theorem czyFusion_supported_associativity_int_000 (i k : Fin 2) :
    czyLeftInt 0 0 0 * czyTripleInt 0 0 0 i k =
      (1 : ℤ) • (czyRightInt 0 0 0 * czyTripleInt 0 0 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_001 (i k : Fin 2) :
    czyLeftInt 0 0 1 * czyTripleInt 0 0 1 i k =
      (1 : ℤ) • (czyRightInt 0 0 1 * czyTripleInt 0 0 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_010 (i k : Fin 2) :
    czyLeftInt 0 1 0 * czyTripleInt 0 1 0 i k =
      (1 : ℤ) • (czyRightInt 0 1 0 * czyTripleInt 0 1 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_011 (i k : Fin 2) :
    czyLeftInt 0 1 1 * czyTripleInt 0 1 1 i k =
      (1 : ℤ) • (czyRightInt 0 1 1 * czyTripleInt 0 1 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_100 (i k : Fin 2) :
    czyLeftInt 1 0 0 * czyTripleInt 1 0 0 i k =
      (1 : ℤ) • (czyRightInt 1 0 0 * czyTripleInt 1 0 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_101 (i k : Fin 2) :
    czyLeftInt 1 0 1 * czyTripleInt 1 0 1 i k =
      (1 : ℤ) • (czyRightInt 1 0 1 * czyTripleInt 1 0 1 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_110 (i k : Fin 2) :
    czyLeftInt 1 1 0 * czyTripleInt 1 1 0 i k =
      (1 : ℤ) • (czyRightInt 1 1 0 * czyTripleInt 1 1 0 i k) := by
  revert_decide_kernel i k

private theorem czyFusion_supported_associativity_int_111 (i k : Fin 2) :
    czyLeftInt 1 1 1 * czyTripleInt 1 1 1 i k =
      ((-1 : ℤ) : ℤ) • (czyRightInt 1 1 1 * czyTripleInt 1 1 1 i k) := by
  revert_decide_kernel i k

/-- The normalized fusion maps have phase `-1` exactly at the nontrivial triple
after contraction with a physical letter. This is the restricted correction to
arXiv:2509.03600, Section II, main.tex lines 283–294, described in
`docs/paper-gaps/lmsvkl25_czy_associator.tex`.

The finite certificate is split by fusion triple, so that the eight kernel checks are
independent declarations. -/
theorem czyFusion_supported_associativity_int (a b c i k : Fin 2) :
    czyLeftInt a b c * czyTripleInt a b c i k =
      (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℤ) else 1) •
        (czyRightInt a b c * czyTripleInt a b c i k) := by
  match a, b, c with
  | 0, 0, 0 => exact czyFusion_supported_associativity_int_000 i k
  | 0, 0, 1 => exact czyFusion_supported_associativity_int_001 i k
  | 0, 1, 0 => exact czyFusion_supported_associativity_int_010 i k
  | 0, 1, 1 => exact czyFusion_supported_associativity_int_011 i k
  | 1, 0, 0 => exact czyFusion_supported_associativity_int_100 i k
  | 1, 0, 1 => exact czyFusion_supported_associativity_int_101 i k
  | 1, 1, 0 => exact czyFusion_supported_associativity_int_110 i k
  | 1, 1, 1 => exact czyFusion_supported_associativity_int_111 i k

/-- Complex form of the normalized associator relation on one physical-site image.
This is the corrected formulation documented in
`docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_supported_associativity (a b c i k : Fin 2) :
    complexOfInt (czyLeftInt a b c) * complexOfInt (czyTripleInt a b c i k) =
      (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℂ) else 1) •
        (complexOfInt (czyRightInt a b c) * complexOfInt (czyTripleInt a b c i k)) := by
  have h := congrArg complexOfInt (czyFusion_supported_associativity_int a b c i k)
  split_ifs at h ⊢ <;>
    simpa only [complexOfInt_zsmul, complexOfInt_mul, Int.cast_neg, Int.cast_one] using h

/-- The corrected scalar relation holds after contraction with every nonempty physical
word. Thus it holds on the sum of their image subspaces; see
`docs/paper-gaps/lmsvkl25_czy_associator.tex`. -/
theorem czyFusion_supported_associativity_word (a b c : Fin 2) (w : List (Fin 2 × Fin 2))
    (hw : w ≠ []) :
    complexOfInt (czyLeftInt a b c) *
      (w.map fun p => complexOfInt (czyTripleInt a b c p.1 p.2)).prod =
    (if a = 1 ∧ b = 1 ∧ c = 1 then (-1 : ℂ) else 1) •
      (complexOfInt (czyRightInt a b c) *
      (w.map fun p => complexOfInt (czyTripleInt a b c p.1 p.2)).prod) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons p w =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, czyFusion_supported_associativity,
      Matrix.smul_mul, Matrix.mul_assoc]

end CZYCompression

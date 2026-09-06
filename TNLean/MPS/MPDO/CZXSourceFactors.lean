/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXDaggerGauge
import TNLean.MPS.MPU.SourceFactors

/-!
# Displayed CZX source factors

Explicit factors from arXiv:2502.20257, lines 4559–4659 (`eq:modif_XY`),
for the shared, output-Z-decorated `CZX.tensor`. Physical indices use the
ordering `2a+b`. The first empty factor uses `Y β t`, not `Y t β`.
These are explicit witnesses, not identifications with choice-selected SVD factors.
-/

noncomputable section

open scoped Matrix BigOperators Kronecker

namespace MPOTensor.CZX

/-- Filled left factor, arXiv:2502.20257, lines 4559–4610. -/
def displayedX₂ : Matrix (Fin 2 × Fin 4) (Fin 4) ℂ := fun (α, i) k ↦
  if i = k ∧ α = (Fin.divNat (m := 2) (n := 2) i) then
    (-1 : ℂ) ^ ((Fin.divNat (m := 2) (n := 2) i).val +
      (Fin.modNat (m := 2) (n := 2) i).val) else 0

/-- Filled right factor: the two flips and unnormalized Hadamard weights,
arXiv:2502.20257, lines 4559–4610. -/
def displayedY₂ : Matrix (Fin 4) (Fin 4 × Fin 2) ℂ := fun k (j, β) ↦
  if k = j.rev then
    (-1 : ℂ) ^ ((Fin.divNat (m := 2) (n := 2) k).val *
      (Fin.modNat (m := 2) (n := 2) k).val + (Fin.modNat (m := 2) (n := 2) k).val * β.val)
  else 0

/-- Empty left factor with the Pauli gauge on the right virtual leg,
arXiv:2502.20257, lines 4611–4659. The order `β t` is essential. -/
def displayedX₁ : Matrix (Fin 4 × Fin 2) (Fin 4) ℂ := fun (i, β) k ↦
  ∑ t : Fin 2, daggerGauge β t * star (displayedY₂ k (i, t))

/-- Empty right factor, arXiv:2502.20257, lines 4611–4659. -/
def displayedY₁ : Matrix (Fin 4) (Fin 2 × Fin 4) ℂ := fun k (α, j) ↦
  ∑ t : Fin 2, star (displayedX₂ (t, j) k) * daggerGauge t α

/-- Both displayed decompositions recover the exact shared tensor,
arXiv:2502.20257, lines 4559–4659. -/
theorem displayed_cuts :
    displayedX₁ * displayedY₁ = sourceCutM₁ tensor ∧
    displayedX₂ * displayedY₂ = sourceCutM₂ tensor := by
  have hc : ∀ j : Fin 4, complementSite j = j.rev := by decide
  have hb : ∀ i : Fin 4, siteBits i =
      (show ZMod 2 from Fin.divNat (m := 2) (n := 2) i,
        show ZMod 2 from Fin.modNat (m := 2) (n := 2) i) := by decide
  constructor <;> ext ⟨a, b⟩ ⟨c, d⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_four, sourceCutM₁, sourceCutM₂,
      tensor_apply, hc, edgeExponent, hb] <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num +decide [displayedX₁, displayedY₁, displayedX₂, displayedY₂,
      Fin.sum_univ_two, daggerGauge, SpinCover.pauli_one,
      Fin.divNat, Fin.modNat, Fin.rev, ZMod.val, Fin.reduceEq]

/-- The four Gram identities for the displayed factors in
arXiv:2502.20257, lines 4559–4659, with unnormalized Hadamard weights.
The Pauli-gauge identities `displayedX₁ = (1 ⊗ₖ daggerGauge) * displayedY₂ᴴ` and
`displayedY₁ = displayedX₂ᴴ * (daggerGauge ⊗ₖ 1)` reduce the first and third
conjuncts to the second and fourth via unitarity of the dagger gauge. -/
theorem displayed_grams :
    displayedX₁ᴴ * displayedX₁ = (2 : ℂ) • 1 ∧
    displayedX₂ᴴ * displayedX₂ = 1 ∧
    displayedY₁ * displayedY₁ᴴ = 1 ∧
    displayedY₂ * displayedY₂ᴴ = (2 : ℂ) • 1 := by
  have hX₂ : displayedX₂ᴴ * displayedX₂ = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num +decide [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_four, displayedX₂, Fin.divNat, Fin.modNat,
        Matrix.one_apply, Fin.reduceEq]
  have hY₂ : displayedY₂ * displayedY₂ᴴ = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num +decide [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_four, displayedY₂, Fin.divNat, Fin.modNat, Fin.rev,
        Matrix.one_apply, Fin.reduceEq]
  have hK1 : ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge)ᴴ *
      ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge) = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, daggerGauge_conjTranspose,
      ← Matrix.mul_kronecker_mul, one_mul, daggerGauge_mul_self, Matrix.one_kronecker_one]
  have hK2 : (daggerGauge ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ)) *
      (daggerGauge ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, daggerGauge_conjTranspose,
      ← Matrix.mul_kronecker_mul, daggerGauge_mul_self, one_mul, Matrix.one_kronecker_one]
  have hX₁ : displayedX₁ = ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge) * displayedY₂ᴴ := by
    ext ⟨i, β⟩ k
    simp [displayedX₁, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]
  have hY₁ : displayedY₁ = displayedX₂ᴴ * (daggerGauge ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ)) := by
    ext k ⟨α, j⟩
    simp [displayedY₁, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply]
  refine ⟨?_, hX₂, ?_, hY₂⟩
  · rw [hX₁, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge)ᴴ
        ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ daggerGauge) displayedY₂ᴴ,
      hK1, Matrix.one_mul, Matrix.conjTranspose_conjTranspose]
    exact hY₂
  · rw [hY₁, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (daggerGauge ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))
        (daggerGauge ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))ᴴ (displayedX₂ᴴ)ᴴ,
      hK2, Matrix.one_mul, Matrix.conjTranspose_conjTranspose]
    exact hX₂

/-- Explicit right inverses of the displayed right factors, compatible with
arXiv:1703.09188, `Z1Z2`, for arXiv:2502.20257, lines 4559–4659. -/
def displayedZ₁ : Matrix (Fin 2 × Fin 4) (Fin 4) ℂ := displayedY₁ᴴ

/-- The second right inverse has the factor one half because the Hadamard
weights in arXiv:2502.20257, lines 4559–4659 are unnormalized. -/
def displayedZ₂ : Matrix (Fin 4 × Fin 2) (Fin 4) ℂ := (1 / 2 : ℂ) • displayedY₂ᴴ

/-- The inverse identities and the first weighted normalization for the
explicit factors, arXiv:2502.20257, lines 4559–4659 (`eq:modif_XY`). -/
theorem displayed_normalizations :
    displayedY₁ * displayedZ₁ = 1 ∧
    displayedY₂ * displayedZ₂ = 1 ∧
    displayedX₁ᴴ * sourceWeight (d := 4) (D := 2) ((1 / 2 : ℂ) • 1) * displayedX₁ = 1 := by
  refine ⟨displayed_grams.2.2.1, ?_, ?_⟩
  · rw [displayedZ₂, Matrix.mul_smul, displayed_grams.2.2.2, smul_smul]
    norm_num
  · rw [sourceWeight, Matrix.kronecker_smul, Matrix.one_kronecker_one,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, displayed_grams.1, smul_smul]
    norm_num

private theorem rank_factorization {m n : Type*} [Fintype m] [Fintype n]
    (X : Matrix m (Fin 4) ℂ) (Y : Matrix (Fin 4) n ℂ)
    (L : Matrix (Fin 4) m ℂ) (Z : Matrix n (Fin 4) ℂ)
    (hL : L * X = 1) (hZ : Y * Z = 1) : (X * Y).rank = 4 := by
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left X Y).trans (Matrix.rank_le_card_width X)
  · have h : L * (X * Y) * Z = 1 := by
      rw [← Matrix.mul_assoc L X Y, hL, Matrix.one_mul, hZ]
    have hb := (Matrix.rank_mul_le_left (L * (X * Y)) Z).trans
      (Matrix.rank_mul_le_right L (X * Y))
    simpa only [h, Matrix.rank_one, Fintype.card_fin] using hb

/-- Both source ranks of the exact CZX tensor are four. The proof uses the
explicit inverses, not an SVD computation (arXiv:2502.20257, lines 4559–4659). -/
theorem displayed_ranks : rightRank tensor = 4 ∧ leftRank tensor = 4 := by
  constructor
  · rw [rightRank, ← displayed_cuts.1]
    apply rank_factorization displayedX₁ displayedY₁ ((1 / 2 : ℂ) • displayedX₁ᴴ)
      displayedZ₁ _ displayed_normalizations.1
    rw [Matrix.smul_mul, displayed_grams.1, smul_smul]
    norm_num
  · rw [leftRank, ← displayed_cuts.2]
    exact rank_factorization displayedX₂ displayedY₂ displayedX₂ᴴ displayedZ₂
      displayed_grams.2.1 displayed_normalizations.2.1

/-- Identify the first displayed four-dimensional leg with the actual source
rank, arXiv:2502.20257, lines 4559–4659. -/
def displayedRightEquiv : Fin (rightRank tensor) ≃ Fin 4 := finCongr displayed_ranks.1

/-- Identify the second displayed four-dimensional leg with the actual source
rank, arXiv:2502.20257, lines 4559–4659. -/
def displayedLeftEquiv : Fin (leftRank tensor) ≃ Fin 4 := finCongr displayed_ranks.2

/-- The displayed CZX factors as an explicit witness of the existing source
factorization predicate, with virtual density `ρ = I₂/2`.
Source: arXiv:2502.20257, lines 4559–4659; arXiv:1703.09188, `eq:sf-svd`–`YZ=1`.
No equality with choice-selected factors is asserted. -/
def displayedSourceFactors : SourceFactors tensor ((1 / 2 : ℂ) • 1) := by
  refine {
    X₁ := displayedX₁.submatrix (Equiv.refl _) displayedRightEquiv
    Y₁ := displayedY₁.submatrix displayedRightEquiv (Equiv.refl _)
    Z₁ := displayedZ₁.submatrix (Equiv.refl _) displayedRightEquiv
    X₂ := displayedX₂.submatrix (Equiv.refl _) displayedLeftEquiv
    Y₂ := displayedY₂.submatrix displayedLeftEquiv (Equiv.refl _)
    Z₂ := displayedZ₂.submatrix (Equiv.refl _) displayedLeftEquiv
    sourceCutM₁_eq := ?_
    sourceCutM₂_eq := ?_
    X₁_weighted_isometry := ?_
    X₂_isometry := ?_
    Y₁_mul_Z₁ := ?_
    Y₂_mul_Z₂ := ?_ }
  case refine_3 =>
    rw [Matrix.conjTranspose_submatrix]
    change displayedX₁ᴴ.submatrix displayedRightEquiv (Equiv.refl _) *
      (sourceWeight (d := 4) (D := 2) ((1 / 2 : ℂ) • 1)).submatrix
        (Equiv.refl _) (Equiv.refl _) *
      displayedX₁.submatrix (Equiv.refl _) displayedRightEquiv = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      displayed_normalizations.2.2, Matrix.submatrix_one_equiv]
  all_goals
    simp only [Matrix.IsIsometry, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, displayed_cuts.1, displayed_cuts.2,
      displayed_grams.2.1, displayed_normalizations.1, displayed_normalizations.2.1,
      Matrix.submatrix_one_equiv] <;> rfl

/-- All six coordinates of the explicit witness, with the factor leg pulled
back to the displayed four-dimensional space. Source: arXiv:2502.20257,
lines 4559–4659, and arXiv:1703.09188, `Z1Z2`. -/
theorem displayedSourceFactors_coordinates (k : Fin 4) (i : Fin 4) (α : Fin 2) :
    displayedSourceFactors.X₁ (i, α) (displayedRightEquiv.symm k) =
      displayedX₁ (i, α) k ∧
    displayedSourceFactors.Y₁ (displayedRightEquiv.symm k) (α, i) =
      displayedY₁ k (α, i) ∧
    displayedSourceFactors.Z₁ (α, i) (displayedRightEquiv.symm k) =
      displayedZ₁ (α, i) k ∧
    displayedSourceFactors.X₂ (α, i) (displayedLeftEquiv.symm k) =
      displayedX₂ (α, i) k ∧
    displayedSourceFactors.Y₂ (displayedLeftEquiv.symm k) (i, α) =
      displayedY₂ k (i, α) ∧
    displayedSourceFactors.Z₂ (i, α) (displayedLeftEquiv.symm k) =
      displayedZ₂ (i, α) k := by
  simp [displayedSourceFactors, Matrix.submatrix_apply]

/-- The empty/filled gauge identities and right-inverse coordinates survive
transport to the actual source ranks. In particular the first gauge entry
is `Y β t`, not its transpose. Source: arXiv:2502.20257, lines 4611–4659,
and arXiv:1703.09188, `Z1Z2`. -/
theorem displayedSourceFactors_inverse_coordinates (k : Fin 4) (i : Fin 4) (β : Fin 2) :
    displayedSourceFactors.X₁ (i, β) (displayedRightEquiv.symm k) =
      ∑ t : Fin 2, daggerGauge β t *
        star (displayedSourceFactors.Y₂ (displayedLeftEquiv.symm k) (i, t)) ∧
    displayedSourceFactors.Y₁ (displayedRightEquiv.symm k) (β, i) =
      ∑ t : Fin 2, star (displayedSourceFactors.X₂ (t, i) (displayedLeftEquiv.symm k)) *
        daggerGauge t β ∧
    displayedSourceFactors.Z₁ (β, i) (displayedRightEquiv.symm k) =
      star (displayedSourceFactors.Y₁ (displayedRightEquiv.symm k) (β, i)) ∧
    displayedSourceFactors.Z₂ (i, β) (displayedLeftEquiv.symm k) =
      (1 / 2 : ℂ) * star (displayedSourceFactors.Y₂ (displayedLeftEquiv.symm k) (i, β)) := by
  simp [displayedSourceFactors, Matrix.submatrix_apply, displayedX₁, displayedY₁,
    displayedZ₁, displayedZ₂, Matrix.conjTranspose_apply]

end MPOTensor.CZX

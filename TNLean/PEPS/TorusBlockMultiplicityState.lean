/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusMultiplicityBondState
import TNLean.PEPS.SemiRegularBondProductIsometry
/-!
# The explicit fourth-root block construction on the native torus

Choose positive matrix dimensions dᵢ and matrix representations Dᵢ. Form their
block sum U and the block-scalar weight W with coefficients dᵢ^(1/4).
The actual averaging-site tensor dressed by W on its virtual legs contracts
into matching-sector physical bond vectors. Multiplicity restoration on those
bonds sends the actual torus state to the native averaging-site state of
⊕ᵢ Dᵢ ⊗ I_{dᵢ}.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2947–3019. The tensor,
contraction, support, and transformation all use the existing native operators.
No coefficient or Gram identity is a hypothesis.

**Scope restriction (chosen blocks):** The algebraic construction takes chosen
matrix representations of positive dimensions. It does not assert that they
are an enumeration of all irreducibles. Deriving that enumeration and its
unitary Fourier identification with the regular representation is separate;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker
namespace TNLean.PEPS
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]
variable (d : I → ℕ)

/-- The direct sum of the chosen representation matrices.
Source: SCP10, Section 7, lines 2955–2961. -/
noncomputable def blockMatrixRepresentation
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    G →* Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ where
  toFun g := Matrix.blockDiagonal' (fun i => D i g)
  map_one' := by
    simp only [map_one]
    exact Matrix.blockDiagonal'_one
  map_mul' g h := by
    simp only [map_mul]
    exact Matrix.blockDiagonal'_mul _ _

/-- The source fourth-root dimension weight in the explicit block basis.
Source: SCP10, Section 7, lines 2962–2972. -/
noncomputable def blockFourthRootWeight : Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) ℂ :=
  Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) •
    (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))

/-- The two endpoint fourth-root weights give the actual square-root bond weights.
Source: SCP10, Section 7, lines 2992–3007. -/
theorem blockFourthRootWeight_sq_mul (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) :
    blockFourthRootWeight d ^ 2 * blockMatrixRepresentation d D g =
      Matrix.blockDiagonal' (fun i => (Real.sqrt (d i : ℝ) : ℂ) • D i g) := by
  change Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) •
      (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) ^ 2 *
      Matrix.blockDiagonal' (fun i => D i g) = _
  rw [pow_two, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [← pow_two, Complex.ofReal_sqrt_sq _ (Real.sqrt_nonneg _)]

/-- The scalar dimension weights commute with the block representation.
Source: SCP10, Section 7, lines 2962–2977. -/
theorem blockFourthRootWeight_commute (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) : Commute (blockFourthRootWeight d) (blockMatrixRepresentation d D g) := by
  change Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) •
      (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) *
      Matrix.blockDiagonal' (fun i => D i g) =
    Matrix.blockDiagonal' (fun i => D i g) *
      Matrix.blockDiagonal' (fun i => (Real.sqrt (Real.sqrt (d i : ℝ)) : ℂ) •
        (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
variable [Fintype G]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Multiplicity restoration acts on the actual dressed-site torus state, with
matching-sector support derived from its coefficients.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondRegrouping_blockFourthRootWeight
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let Ψ := torusBondRegrouping (width := width) (height := height)
      (fun σ => torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1)
    (∃ χ, physicalProductMap (TorusVertex width height × Bool)
      (blockBondInclusion (fun i => Fin (d i))) χ = Ψ) ∧
    physicalProductMap (TorusVertex width height × Bool)
      (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) Ψ =
    torusBondRegrouping (fun σ => torusBondNetwork
      (fun v t => averagingSite (multiplicityRestoredRepresentation d D)
        t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1) := by
  exact torusBondRegrouping_dressedAveragingSite_of_weightedBlocks
    d (blockMatrixRepresentation d D) (blockFourthRootWeight d) D hd
    (blockFourthRootWeight_commute d D) (blockFourthRootWeight_sq_mul d D)
end TNLean.PEPS

namespace TNLean.PEPS
open scoped Matrix
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]
variable {width height : ℕ} [NeZero width] [NeZero height]
/-- The actual native weighted-site and repeated-block torus states have the
same squared norm, by multiplicity restoration on their derived bond support.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem torusBondNetwork_blockFourthRootWeight_norm (d : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (hd : ∀ i, 0 < d i) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let H : (TorusVertex width height → (Σ i, Fin (d i)) × (Σ i, Fin (d i)) ×
        (Σ i, Fin (d i)) × (Σ i, Fin (d i))) → ℂ :=
      fun σ => torusBondNetwork (fun v t => torusDress W W
        (fun a => averagingSite U a.1 a.2.1 a.2.2.1 a.2.2.2 (σ v)) t) 1 1
    let K : (TorusVertex width height →
        (Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i)) ×
        (Σ i, Fin (d i) × Fin (d i)) × (Σ i, Fin (d i) × Fin (d i))) → ℂ :=
      fun σ => torusBondNetwork
        (fun v t => averagingSite (multiplicityRestoredRepresentation d D)
          t.1 t.2.1 t.2.2.1 t.2.2.2 (σ v)) 1 1
    star K ⬝ᵥ K = star H ⬝ᵥ H := by
  let : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd i⟩⟩
  obtain ⟨⟨χ, hχ⟩, hF⟩ :=
    torusBondRegrouping_blockFourthRootWeight (width := width) (height := height) d D hd
  let Ψ := physicalProductMap (TorusVertex width height × Bool)
    (blockBondInclusion (fun i => Fin (d i))) χ
  have hnorm := physicalProductMap_fullMultiplicityBondMap_dotProduct
    (fun i => Fin (d i)) (fun i => Fin (d i)) Ψ Ψ ⟨χ, rfl⟩
  dsimp only [Ψ] at hnorm
  rw [hχ, hF] at hnorm
  simpa only [torusBondRegrouping_dotProduct] using hnorm
end TNLean.PEPS

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.PreparedMatrix
import QICLean.Circuit.Party.Source.PartyMaps
import QICLean.Circuit.Party.Source.PreparedSourceGate

/-!
# Operator norms of prepared branches

Preparing normalized pair sources and then applying an allowed word is a
contraction. Its matrix in any input and output coordinates of norm at most one,
for instance orthonormal bases, therefore has Euclidean operator norm at most one.
In particular, this holds for the operators obtained by assigning a unit vector
to every source half, including vectors from an orthonormal family that spans only
a proper subspace.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source-gate expansion and source-entry separation,
lines 233–267 and 409–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

## Density coefficients of an actual source-only gate

Starting from a finite family of allowed words, construct its common finite
source spaces and the remaining local operations. The density of the original
weighted gate is then the explicit sum of the source-coordinate coefficients
and the matrices obtained by preparing endpoint basis vectors. These prepared
matrices are contractions. The factorization and the coefficient operators are
constructed from the words. The input and output coordinates are given by matrices `E` and `F`
whose columns are the coordinate vectors, so the matrix of an operator `T` is `Fᴴ * T * E`;
the coordinate matrix of an orthonormal basis `b` of `EuclideanSpace ℂ κ` is the unitary
`(EuclideanSpace.basisFun κ ℂ).toBasis.toMatrix b`.

This is the exact density identity preceding Gaussian source replacement. It
does not give the corrected-position error estimate, which must retain the
exterior aggregate gates as contractions.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, `eq:compression-source-gate` and the density-source
expansion, lines 233–355.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator
open Matrix ManyBody

namespace QuantumCircuit.Party.Word

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]

/-- Moving the input and output coordinates of the two prepared matrices into the input matrix
and around the coefficient. -/
private theorem conj_mul_mul_conjTranspose {k l m n : Type} [Fintype k] [Fintype m]
    [Fintype n] (E : Matrix k n ℂ) (F : Matrix m l ℂ) (M M' : Matrix m k ℂ)
    (ρ : Matrix n n ℂ) :
    Fᴴ * M * E * ρ * (Fᴴ * M' * E)ᴴ = Fᴴ * (M * (E * ρ * Eᴴ) * M'ᴴ) * F := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Normalized source preparation followed by allowed operations has matrix operator norm at
most one in any input and output coordinates `E` and `F` of norm at most one, for instance
orthonormal bases: the matrix in these coordinates is `Fᴴ * K * E`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 409–427. -/
theorem norm_preparedMatrix_le_one {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (hη : ∀ i, ‖η i‖ = 1)
    (v : Word (SourceInventory.slotSystem R B X) Y) (hv : v.IsAllowed)
    (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖Fᴴ * v.preparedMatrix R B η X * E‖ ≤ 1 := by
  classical
  refine l2_opNorm_mul_le_one _ _ (l2_opNorm_mul_le_one _ _ ?_ ?_) hE
  · rwa [l2_opNorm_conjTranspose]
  · exact l2_opNorm_mul_le_one _ _ (PartyCircuit.norm_op_le_one _ hv)
      (PartyCircuit.norm_op_le_one _ (SourceInventory.isAllowed_prepareSlots R B η hη))

/-- Assigning a unit vector to each source half gives a contraction, in any input and output
coordinates of norm at most one. This applies both to orthonormal bases and to orthonormal
families spanning proper subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_preparedMatrix_tmul_le_one {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (R : SourceInventory P)
    (B : SourceInventory.SlotBases R.length) {K L : Fin R.length → Type}
    (u : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (u' : ∀ i, L i → EuclideanSpace ℂ (B.right i))
    (hu : ∀ i a, ‖u i a‖ = 1) (hu' : ∀ i b, ‖u' i b‖ = 1)
    (v : Word (SourceInventory.slotSystem R B X) Y) (hv : v.IsAllowed) (a : ∀ i, K i × L i)
    (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ‖Fᴴ * v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron (u i (a i).1) (u' i (a i).2)) X *
      E‖ ≤ 1 :=
  norm_preparedMatrix_le_one R B _ (fun i ↦ by
    rw [EuclideanSpace.norm_vecKron, hu, hu', one_mul]) v hv E F hE hF

/-- Construct the finite source coordinates and the exact density coefficients of
the original weighted gate, in any input and output coordinates `E` and `F` of norm at most one,
for instance orthonormal bases. The elementary preparation operators `Fᴴ * K_ξ(x) * E` are
contractions, and the ket and bra retain the coefficients `c ξ` and `conj (c ζ)`, respectively;
the density coefficient in the coordinates `E`, `F` of the input matrix `ρ` is
`Fᴴ * C(E * ρ * Eᴴ) * F`, that is `(Fᴴ * K_ξ(x) * E) * ρ * (Fᴴ * K_ζ(y) * E)ᴴ`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–355. -/
theorem exists_finite_density_expansion {ι m n : Type} [Fintype ι] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (w : ι → Word X Y) (hw : ∀ ξ, (w ξ).IsAllowed) (c : ι → ℂ)
    (E : Matrix (Config X) n ℂ) (F : Matrix (Config Y) m ℂ) (hE : ‖E‖ ≤ 1) (hF : ‖F‖ ≤ 1) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)), (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ v : ι → Word (SourceInventory.slotSystem R B X) Y,
          (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
          (∀ ξ, (w ξ).op = (v ξ).op * (SourceInventory.prepareSlots R B (η ξ) X).op) ∧
          (∀ ξ (x : ∀ i, B.left i × B.right i),
            ‖Fᴴ * (v ξ).preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
              (EuclideanSpace.single (x i).1 1) (EuclideanSpace.single (x i).2 1)) X * E‖ ≤ 1) ∧
          ∀ ρ : Matrix n n ℂ,
            (∑ ξ, c ξ • (Fᴴ * (w ξ).op * E)) * ρ * (∑ ξ, c ξ • (Fᴴ * (w ξ).op * E))ᴴ =
              ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
                ∑ x : ∀ i, B.left i × B.right i, ∑ y : ∀ i, B.left i × B.right i,
                  (∏ i, η ξ i (x i) * conj (η ζ i (y i))) •
                    (Fᴴ * (v ξ).preparedDensityCoefficient R B X
                      (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
                      (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
                      (v ζ) (E * ρ * Eᴴ) x y * F) := by
  classical
  obtain ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he⟩ := exists_common_source_preparation w hw
  refine ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he, fun ξ x ↦ ?_, fun ρ ↦ ?_⟩
  · exact norm_preparedMatrix_tmul_le_one R B (fun _ a ↦ EuclideanSpace.single a (1 : ℂ))
      (fun _ a ↦ EuclideanSpace.single a (1 : ℂ))
      (fun _ a ↦ (PiLp.norm_single 2 _ a 1).trans norm_one)
      (fun _ a ↦ (PiLp.norm_single 2 _ a 1).trans norm_one) (v ξ) (hv ξ) x E F hE hF
  · have hM : ∀ ξ, (w ξ).op = (v ξ).preparedMatrix R B (η ξ) X := he
    have hsum : ∑ ξ, c ξ • (Fᴴ * (w ξ).op * E) =
        Fᴴ * (∑ ξ, c ξ • (v ξ).preparedMatrix R B (η ξ) X) * E := by
      simp only [hM, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hsum, conj_mul_mul_conjTranspose,
      preparedMatrix_gate_density_eq_sum_single R B X c η v (E * ρ * Eᴴ)]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end QuantumCircuit.Party.Word

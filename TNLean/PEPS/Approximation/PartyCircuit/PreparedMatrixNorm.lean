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
contraction. Its matrix in configuration coordinates therefore has Euclidean
operator norm at most one. In particular, this holds for the operators
obtained by assigning a unit vector to every source half, including vectors
from an orthonormal family that spans only a proper subspace.

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
constructed from the words.

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

/-- Normalized source preparation followed by allowed operations has matrix
operator norm at most one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 409–427. -/
theorem norm_preparedMatrix_le_one (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (hη : ∀ i, ‖η i‖ = 1)
    (v : Word (SourceInventory.slotSystem R B X) Y) (hv : v.IsAllowed) :
    ‖v.preparedMatrix R B η X‖ ≤ 1 :=
  l2_opNorm_mul_le_one _ _ (PartyCircuit.norm_op_le_one _ hv)
    (PartyCircuit.norm_op_le_one _ (SourceInventory.isAllowed_prepareSlots R B η hη))

/-- Assigning a unit vector to each source half gives a contraction. This applies
both to orthonormal bases and to orthonormal families spanning proper subspaces.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem norm_preparedMatrix_tmul_le_one (R : SourceInventory P)
    (B : SourceInventory.SlotBases R.length) {K L : Fin R.length → Type}
    (u : ∀ i, K i → EuclideanSpace ℂ (B.left i)) (u' : ∀ i, L i → EuclideanSpace ℂ (B.right i))
    (hu : ∀ i a, ‖u i a‖ = 1) (hu' : ∀ i b, ‖u' i b‖ = 1)
    (v : Word (SourceInventory.slotSystem R B X) Y) (hv : v.IsAllowed) (a : ∀ i, K i × L i) :
    ‖v.preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron (u i (a i).1) (u' i (a i).2)) X‖ ≤ 1 :=
  norm_preparedMatrix_le_one R B _ (fun i ↦ by
    rw [EuclideanSpace.norm_vecKron, hu, hu', one_mul]) v hv

/-- Construct the finite source coordinates and the exact density coefficients of
the original weighted gate. The elementary preparation operators are contractions,
and the ket and bra retain the coefficients `c ξ` and `conj (c ζ)`, respectively.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–355. -/
theorem exists_finite_density_expansion {ι : Type} [Fintype ι]
    (w : ι → Word X Y) (hw : ∀ ξ, (w ξ).IsAllowed) (c : ι → ℂ) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)), (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ v : ι → Word (SourceInventory.slotSystem R B X) Y,
          (∀ ξ, (v ξ).IsAllowed) ∧ (∀ ξ, (v ξ).sources = []) ∧
          (∀ ξ, (w ξ).op = (v ξ).op * (SourceInventory.prepareSlots R B (η ξ) X).op) ∧
          (∀ ξ (x : ∀ i, B.left i × B.right i),
            ‖(v ξ).preparedMatrix R B (fun i ↦ EuclideanSpace.vecKron
              (EuclideanSpace.single (x i).1 1) (EuclideanSpace.single (x i).2 1)) X‖ ≤ 1) ∧
          ∀ ρ : Matrix (Config X) (Config X) ℂ,
            (∑ ξ, c ξ • (w ξ).op) * ρ * (∑ ξ, c ξ • (w ξ).op)ᴴ =
              ∑ ξ, ∑ ζ, (c ξ * conj (c ζ)) •
                ∑ x : ∀ i, B.left i × B.right i, ∑ y : ∀ i, B.left i × B.right i,
                  (∏ i, η ξ i (x i) * conj (η ζ i (y i))) •
                    (v ξ).preparedDensityCoefficient R B X
                      (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
                      (fun _ a ↦ EuclideanSpace.single a 1) (fun _ a ↦ EuclideanSpace.single a 1)
                      (v ζ) ρ x y := by
  classical
  obtain ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he⟩ := exists_common_source_preparation w hw
  refine ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he, fun ξ x ↦ ?_, fun ρ ↦ ?_⟩
  · exact norm_preparedMatrix_tmul_le_one R B (fun _ a ↦ EuclideanSpace.single a (1 : ℂ))
      (fun _ a ↦ EuclideanSpace.single a (1 : ℂ))
      (fun _ a ↦ (PiLp.norm_single 2 _ a 1).trans norm_one)
      (fun _ a ↦ (PiLp.norm_single 2 _ a 1).trans norm_one) (v ξ) (hv ξ) x
  · have hM : ∀ ξ, (w ξ).op = (v ξ).preparedMatrix R B (η ξ) X := he
    simp only [hM]
    exact preparedMatrix_gate_density_eq_sum_single R B X c η v ρ

end QuantumCircuit.Party.Word

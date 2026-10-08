/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlap
import TNLean.MPS.ParentHamiltonian.PeriodicPrimitiveGroundSpace

/-!
# Primitive sectors with their cyclic support projections

A normalized periodic tensor has a cyclic isometric resolution whose blocked
sectors are normalized primitive tensors with faithful invariant matrices.
Different cyclic sectors are inequivalent up to similarity and phase.
The resolution retains both block intertwiners, so it identifies literal
word contractions as well as periodic matrix product vectors.

The projection labels here follow the inverse convention
\(P_{u+1}A_i=A_iP_u\). Replacing the label by its negative gives
the word-degree convention \(P_uA_i=A_iP_{u+1}\).

Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675.
-/

open scoped Matrix BigOperators ComplexOrder
namespace MPSTensor
variable {d D m : ℕ}

/-- Periodicity supplies a primitive faithful inequivalent cyclic sector
resolution, including its support projections and both rectangular block
intertwiners. Every sector dimension is positive.
Source: arXiv:1708.00029, Lemma bdcf and equation Aoffdiag;
Nachtergaele, arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem IsPeriodic.exists_cyclic_primitive_sector_resolution
    {A : MPSTensor d D} (hA : IsPeriodic m A) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (dim : Fin m → ℕ) (hdim : ∀ j, 0 < dim j),
      let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
      ∃ (B : (j : Fin m) → MPSTensor (blockPhysDim d m) (dim j))
        (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
        (V : (j : Fin m) → Matrix (Fin D) (Fin (dim j)) ℂ)
        (ρ : (j : Fin m) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ),
        (∀ j, IsPrimitiveMPS (B j) (ρ j)) ∧ (∀ j, (ρ j).PosDef) ∧
        BlocksNotGaugePhaseEquiv B ∧
        (∀ j, IsOrthogonalProjection (P j)) ∧ (∑ j, P j) = 1 ∧
        (∀ j i, P (j + 1) * A i = A i * P j) ∧
        (∀ j, (V j)ᴴ * V j = 1) ∧ (∀ j, V j * (V j)ᴴ = P j) ∧
        (∀ j i, blockTensor A m i * V j = V j * B j i) ∧
        (∀ j i, (V j)ᴴ * blockTensor A m i = B j i * (V j)ᴴ) := by
  classical
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨dim, B, P, φ, V, hTP, hMPV, hproj, hsum, hcycle, hComm, hTrace,
    hTransfer, hMul, hStar, hdim, hLetter, hiso, hV, hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hA
  have hcycle' : ∀ k : Fin m,
      Kraus.transferMap (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hcycle k
  have hData : IsCyclicSectorDecomp A B :=
    ⟨P, φ, hproj, hsum, hcycle', hComm, hTrace, hTransfer, hMul, hStar⟩
  let : ∀ j, NeZero (dim j) := fun j => ⟨hdim j⟩
  have hPrim (j : Fin m) :=
    primitive_and_irreducible_sectorBlocks_of_cyclicDecomp A hA B hTP hMPV hData j (hdim j)
  have hOne (j : Fin m) : IsPeriodic 1 (B j) :=
    (IsPeriodic.one_iff_primitive (B j)).2 ⟨(hPrim j).2, hTP j, (hPrim j).1⟩
  have hDistinct : BlocksNotGaugePhaseEquiv B := fun j k hjk e =>
    sectorBlocks_not_gaugePhaseEquiv_of_ne A hA B hTP hMPV hproj hsum hcycle'
      hComm hTrace hTransfer hMul hStar hLetter hiso hV hEmbed hdim hjk e
  have hShift : ∀ j i, P (j + 1) * A i = A i * P j :=
    offDiag_shift_of_adjoint_cyclic_shift A hA.leftCanonical hproj hcycle'
  choose ρ hP hρ using fun j => exists_isPrimitiveMPS_of_isPeriodic_one (hOne j)
  have hCorner (j : Fin m) (i : Fin (blockPhysDim d m)) :
      V j * B j i * (V j)ᴴ = P j * blockTensor A m i * P j :=
    (hEmbed j (B j i)).symm.trans (hLetter j i)
  have hVPleft (j : Fin m) : (V j)ᴴ * P j = (V j)ᴴ := by
    rw [← hV, ← Matrix.mul_assoc, hiso, Matrix.one_mul]
  have hVPright (j : Fin m) : P j * V j = V j := by
    rw [← hV, Matrix.mul_assoc, hiso, Matrix.mul_one]
  have hInt (j : Fin m) (i : Fin (blockPhysDim d m)) :
      blockTensor A m i * V j = V j * B j i := by
    have h := congrArg (fun X => X * V j) (hCorner j i)
    simp only [Matrix.mul_assoc, hiso, Matrix.mul_one, hVPright] at h
    rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, hVPright] at h
    exact h.symm
  have hCoInt (j : Fin m) (i : Fin (blockPhysDim d m)) :
      (V j)ᴴ * blockTensor A m i = B j i * (V j)ᴴ := by
    have h := congrArg (fun X => (V j)ᴴ * X) (hCorner j i)
    simp only [← Matrix.mul_assoc, hiso, Matrix.one_mul, hVPleft] at h
    rw [Matrix.mul_assoc, ← hComm, ← Matrix.mul_assoc, hVPleft] at h
    exact h.symm
  exact ⟨dim, (fun j => Nat.pos_of_ne_zero (hdim j)), B, P, V, ρ, hP, hρ,
    hDistinct, hproj, hsum, hShift, hiso, hV, hInt, hCoInt⟩
end MPSTensor


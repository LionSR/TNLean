/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Matrix spaces separated by a directed sector cut

For a physical-sector factorization, the matrices belonging to a set of
sectors are the span of the corresponding one-site MPO matrices.  If every
neighboring operator from one set of sectors to another vanishes, then every
matrix in the first span annihilates every matrix in the second span on the
left.

Only this one-sided conclusion is used in the local-orthogonality argument of
the source.  No vanishing in the reverse order and no recurrence of the sector
graph are asserted here.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equation `P1KP2` and lines 1463--1470
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The virtual matrix of the sector-coordinate tensor obtained from one
matrix entry inside a fixed physical sector.

Source: arXiv:1606.00608, Appendix C.2, lines 1463--1467, where these are the
generators of the spaces denoted by $\mathcal A_1$ and $\mathcal A_2$. -/
noncomputable def oneSiteSectorMatrix (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) (x y : SectorIndex F k) :
    Matrix (Fin D) (Fin D) ℂ :=
  F.sectorCoordinateTensor
    (F.sectorFinEquiv.symm ⟨k, x⟩) (F.sectorFinEquiv.symm ⟨k, y⟩)

/-- A vanishing neighboring operator makes the corresponding one-site sector
matrices vanish in the directed product order.

Source: arXiv:1606.00608, Appendix C.2, equation `P1KP2` and lines 1463--1470.
The source uses precisely the product $\mathcal A_1\mathcal A_2=0$. -/
theorem oneSiteSectorMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
    (F : PhysicalSectorFactorization K) (k h : Fin F.sectorCount)
    (hkh : F.neighboringOperator k h = 0)
    (x y : SectorIndex F k) (u v : SectorIndex F h) :
    F.oneSiteSectorMatrix k x y * F.oneSiteSectorMatrix h u v = 0 := by
  ext beta alpha
  simp only [Matrix.mul_apply, oneSiteSectorMatrix,
    sectorCoordinateTensor_apply_same, Matrix.zero_apply]
  have heta :
      (∑ gamma : Fin D,
        F.rightTensor k gamma x.2 y.2 * F.leftTensor h gamma u.1 v.1) = 0 := by
    have hentry := congrArg
      (fun M ↦ M (x.2, u.1) (y.2, v.1)) hkh
    simpa only [neighboringOperator_apply, Matrix.zero_apply] using hentry
  calc
    ∑ gamma : Fin D,
        F.leftTensor k beta x.1 y.1 * F.rightTensor k gamma x.2 y.2 *
          (F.leftTensor h gamma u.1 v.1 * F.rightTensor h alpha u.2 v.2) =
      F.leftTensor k beta x.1 y.1 *
        (∑ gamma : Fin D,
          F.rightTensor k gamma x.2 y.2 * F.leftTensor h gamma u.1 v.1) *
        F.rightTensor h alpha u.2 v.2 := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro gamma _
          ring
    _ = 0 := by rw [heta]; simp

/-- The span of the one-site virtual matrices whose physical entries belong
to sectors in `S`.

Source: arXiv:1606.00608, Appendix C.2, lines 1463--1467, where the two
instances associated with complementary physical projections are denoted by
$\mathcal A_1$ and $\mathcal A_2$. -/
noncomputable def oneSiteSectorSpace (F : PhysicalSectorFactorization K)
    (S : Set (Fin F.sectorCount)) : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.span ℂ {A | ∃ k ∈ S, ∃ x y, A = F.oneSiteSectorMatrix k x y}

/-- If there are no neighboring operators directed from `S` to `C`, then
every matrix belonging to the one-site sector space of `S` annihilates every
matrix belonging to the one-site sector space of `C` on the left.

This is the source-faithful directed-cut conclusion
$\mathcal A_S\mathcal A_C=0$.  It neither assumes nor concludes the reverse
product vanishing.

Source: arXiv:1606.00608, Appendix C.2, equation `P1KP2` and lines 1463--1470.
-/
theorem oneSiteSectorSpace_mul_eq_zero
    (F : PhysicalSectorFactorization K) (S C : Set (Fin F.sectorCount))
    (hcut : ∀ k ∈ S, ∀ h ∈ C, F.neighboringOperator k h = 0)
    {A B : Matrix (Fin D) (Fin D) ℂ}
    (hA : A ∈ F.oneSiteSectorSpace S) (hB : B ∈ F.oneSiteSectorSpace C) :
    A * B = 0 := by
  refine Submodule.span_induction₂
    (s := {M | ∃ k ∈ S, ∃ x y, M = F.oneSiteSectorMatrix k x y})
    (t := {M | ∃ h ∈ C, ∃ u v, M = F.oneSiteSectorMatrix h u v})
    (p := fun A B _ _ ↦ A * B = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (by simpa only [oneSiteSectorSpace] using hA)
    (by simpa only [oneSiteSectorSpace] using hB)
  · intro A B hAmem hBmem
    rcases hAmem with ⟨k, hkS, x, y, rfl⟩
    rcases hBmem with ⟨h, hhC, u, v, rfl⟩
    exact F.oneSiteSectorMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      k h (hcut k hkS h hhC) x y u v
  · intro B _
    simp
  · intro A _
    simp
  · intro A₁ A₂ B _ _ _ h₁ h₂
    rw [Matrix.add_mul, h₁, h₂, add_zero]
  · intro A B₁ B₂ _ _ _ h₁ h₂
    rw [Matrix.mul_add, h₁, h₂, add_zero]
  · intro r A B _ _ hAB
    rw [smul_mul_assoc, hAB, smul_zero]
  · intro r A B _ _ hAB
    rw [mul_smul_comm, hAB, smul_zero]

end MPOTensor.PhysicalSectorFactorization

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CPSVPeriodicExclusion
import TNLean.MPS.MPDO.VerticalBNT

/-!
# Literal CPSV sector compression and vertical BNT grouping

For an MPDO in literal CPSV canonical form, every nonzero vertical corner has
a nonzero finite-chain compression. The normalized vertical corners also
split into matrix-product-vector phase classes whose normal representatives
form a basis of normal tensors. Their grouped coefficients are positive, and
the physical isometries preserve the reducing identities and exact vertical
reconstruction.

## Main statements

* `MPSTensor.IsCPSVCanonicalForm.exists_sectorCompression_ne_zero_of_corner`:
  every nonzero vertical corner has a nonzero finite-chain compression.
* `MPSTensor.IsCPSVCanonicalForm.exists_verticalBNTGrouping_with_isometry`:
  the literal vertical normal corners grouped into BNT representatives.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.3,
  Lemma L, lines 1835--1858, and Proposition 4.13, lines 1898--1902.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor.IsCPSVCanonicalForm

open MPOTensor

variable {d D : ℕ}

/-- A nonzero vertical corner of a literal CPSV canonical-form tensor has a
nonzero first-site sector compression at some finite chain length.

If every compression vanished, the resulting equality of first-site actions
would make the two-sided insertion by the corner matrix zero by Lemma L.  This
would force the original vertical corner to vanish.  The theorem is the
separation step used for $0 \ne P_{\alpha,k}H^{(N)}P_{\alpha,k}$ in the proof
of Proposition 4.13 of arXiv:1606.00608, lines 1898--1902, using Appendix C.3,
Lemma L, lines 1835--1858. -/
theorem exists_sectorCompression_ne_zero_of_corner
    (M : MPOTensor d D)
    (hCanonical : MPSTensor.IsCPSVCanonicalForm M.toMPSTensor)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hcorner : ∃ v, P * MPOTensor.verticalTensor M v * P ≠ 0) :
    ∃ N, MPOTensor.sectorCompression M P N ≠ 0 := by
  exact MPOTensor.exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq M
    (hCanonical.insertedTensor_eq_of_firstSiteActionAgree M.toMPSTensor) P hcorner


/-- Group the normal vertical corners of a literal CPSV canonical-form MPDO by
matrix-product-vector phase class while retaining their physical isometries.

The representatives form a basis of normal tensors, every grouped coefficient
is positive, and the two intertwining identities, exact corner compression,
representative-loop identity, finite-chain nonvanishing, and letterwise
reconstruction all hold. This is the grouping and positivity step of
arXiv:1606.00608, Proposition 4.13, lines 1898--1902. The grouped Figure-8 Gram
normalization and final ambient coisometry are not asserted here. -/
theorem exists_verticalBNTGrouping_with_isometry
    (M : MPOTensor d D) (hCanonical : IsCPSVCanonicalForm M.toMPSTensor) (hM : IsMPDO M) :
    ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
      (blocks : (k : Fin r) → MPSTensor (D * D) (dim k))
      (V : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ),
      (∀ k, 0 < dim k) ∧
      (∀ k, (0 : ℂ) < μ k) ∧
      (∀ k, MPSTensor.IsNormalTensor (blocks k)) ∧
      (∀ k, (V k)ᴴ * V k = 1) ∧
      (∀ k l, k ≠ l → (V k)ᴴ * V l = 0) ∧
      (∀ k v, verticalTensor M v * V k = V k * (μ k • blocks k v)) ∧
      (∀ k v, (V k)ᴴ * verticalTensor M v = (μ k • blocks k v) * (V k)ᴴ) ∧
      (∀ k v, μ k • blocks k v = (V k)ᴴ * verticalTensor M v * V k) ∧
      (∀ v, verticalTensor M v = ∑ k, V k * (μ k • blocks k v) * (V k)ᴴ) ∧
      let classes := MPSTensor.mpvPhaseClassData blocks
      ∃ (hdim : ∀ j q,
          dim (classes.repr j) = dim (classes.enum j q))
        (X : (j : Fin classes.g) → (q : Fin (classes.copies j)) →
          GL (Fin (dim (classes.enum j q))) ℂ)
        (ζ : (j : Fin classes.g) → Fin (classes.copies j) → ℂ),
        (∀ j q, ‖ζ j q‖ = 1) ∧
        (∀ j q, ζ j q ≠ 0) ∧
        (∀ j, X j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j, ζ j ⟨0, classes.copies_pos j⟩ = 1) ∧
        (∀ j q v,
          blocks (classes.enum j q) v =
            ζ j q •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ))) ∧
        MPSTensor.IsCPSVBasisOfNormalTensors
          (MPSTensor.toTensorFromBlocks (d := D * D) (μ := μ) blocks)
          (fun j => ⟨dim (classes.repr j), blocks (classes.repr j)⟩) ∧
        MPSTensor.BlocksNotGaugePhaseEquiv
          (d := D * D) (fun j => blocks (classes.repr j)) ∧
        (∀ j q, μ (classes.enum j q) * ζ j q ≠ 0) ∧
        (∀ j q, SectorProjectorData M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ)
          (μ (classes.enum j q) * ζ j q)
          (representativeLoop (blocks (classes.repr j)))) ∧
        (∀ j q, ∃ N, sectorCompression M
          (V (classes.enum j q) * (V (classes.enum j q))ᴴ) N ≠ 0) ∧
        (∀ j q, (0 : ℂ) < μ (classes.enum j q) * ζ j q) ∧
        (∀ j q, (V (classes.enum j q))ᴴ * V (classes.enum j q) = 1) ∧
        (∀ j q l p, classes.enum j q ≠ classes.enum l p →
          (V (classes.enum j q))ᴴ * V (classes.enum l p) = 0) ∧
        (∀ j q v,
          verticalTensor M v * V (classes.enum j q) =
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ)))) ∧
        (∀ j q v,
          (V (classes.enum j q))ᴴ * verticalTensor M v =
            ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ) ∧
        (∀ j q v,
          (μ (classes.enum j q) * ζ j q) •
              ((X j q : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ) *
                (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                  (blocks (classes.repr j))) v *
                (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                  (Fin (dim (classes.enum j q))) ℂ)) =
            (V (classes.enum j q))ᴴ * verticalTensor M v * V (classes.enum j q)) ∧
        ∀ v, verticalTensor M v =
          ∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
            V (classes.enum j q) *
              ((μ (classes.enum j q) * ζ j q) •
                ((X j q : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ) *
                  (cast (congr_arg (MPSTensor (D * D)) (hdim j q))
                    (blocks (classes.repr j))) v *
                  (↑((X j q)⁻¹) : Matrix (Fin (dim (classes.enum j q)))
                    (Fin (dim (classes.enum j q))) ℂ))) *
              (V (classes.enum j q))ᴴ := by
  exact MPOTensor.exists_verticalBNTGrouping_with_isometry_of_decomposition M hM
    (hCanonical.exists_normal_verticalBlockDecomp_with_isometry M hM)
    (fun P hRange =>
      hCanonical.exists_sectorCompression_ne_zero_of_corner M P hRange)

end MPSTensor.IsCPSVCanonicalForm

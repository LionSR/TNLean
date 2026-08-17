/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixReducedProjection
import TNLean.Analysis.MatrixSqrt
import TNLean.MPS.MPU.VirtualSandwich

/-!
# Source-rank comparison for the reduced and hatted representatives

This module proves the matrix identity comparing the paper's hatted tensor
$\widehat W=LWR$ with the reduced tensor $\widetilde W=\widetilde P W\widetilde P$,
and then compares their two raw source-cut ranks.

**Scope restriction (supplied fixed pair):** the identities defining the outer
factors and the letterwise support absorptions are explicit hypotheses. They are
not inferred from the bare MPU predicate. The source derives them after blocking
and constructing a positive fixed pair. See
`docs/paper-gaps/mpu_reduced_representative_supplied_fixed_pair.tex`.

Source: `Papers/1703.09188/paper_v2.tex:786-804`.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The exact comparison between the hatted tensor $\widehat W=LWR$ and the reduced
representative $\widetilde W=\widetilde P W\widetilde P$:
$$
  X\widehat W(ZY)=PW(QY)=PQW(PQY)=\widetilde P W\widetilde P.
$$
All identities involving the fixed pair and its support absorptions are supplied.

Source: `Papers/1703.09188/paper_v2.tex:786-804`. -/
theorem virtualSandwich_hat_eq_reducedProjection
    (W : MPOTensor d D) (L R P Q X Z Y : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hXL : X * L = P) (hRZ : R * Z = Q)
    (hPQY : P * Q * Y = Matrix.reducedProjection P Q)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j) :
    virtualSandwich X (virtualSandwich L W R) (Z * Y) =
      virtualSandwich (Matrix.reducedProjection P Q) W
        (Matrix.reducedProjection P Q) := by
  let T := Matrix.reducedProjection P Q
  have hTQ : T * Q = P * Q := Matrix.reducedProjection_mul_second hP
  funext i j
  simp only [virtualSandwich_apply]
  calc
    X * (L * W i j * R) * (Z * Y) = P * W i j * Q * Y := by
      calc
        _ = (X * L) * W i j * (R * Z) * Y := by noncomm_ring
        _ = P * W i j * Q * Y := by rw [hXL, hRZ]
    _ = P * Q * W i j * P * Q * Y := by
      symm
      calc
        _ = P * (Q * W i j) * P * Q * Y := by noncomm_ring
        _ = P * W i j * P * Q * Y := by rw [hQW]
        _ = P * (W i j * P) * Q * Y := by noncomm_ring
        _ = P * W i j * Q * Y := by rw [hWP]
    _ = T * W i j * T := by
      calc
        _ = (P * Q) * W i j * (P * Q * Y) := by noncomm_ring
        _ = (T * Q) * W i j * T := by rw [hTQ, hPQY]
        _ = T * (Q * W i j) * T := by noncomm_ring
        _ = T * W i j * T := by rw [hQW]

/-- If the three outer factors are invertible, the right source rank of the hatted
representative equals that of the reduced representative.

Source: `Papers/1703.09188/paper_v2.tex:786-804`. -/
theorem rightRank_hat_eq_reducedProjection
    (W : MPOTensor d D) (L R P Q X Z Y : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hXL : X * L = P) (hRZ : R * Z = Q)
    (hPQY : P * Q * Y = Matrix.reducedProjection P Q)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (hX : IsUnit X) (hZ : IsUnit Z) (hY : IsUnit Y) :
    r[virtualSandwich L W R] =
      r[virtualSandwich (Matrix.reducedProjection P Q) W
        (Matrix.reducedProjection P Q)] := by
  rw [← virtualSandwich_hat_eq_reducedProjection W L R P Q X Z Y
    hP hXL hRZ hPQY hWP hQW]
  exact (rightRank_virtualSandwich X (virtualSandwich L W R) (Z * Y)
    hX (hZ.mul hY)).symm

/-- If the three outer factors are invertible, the left source rank of the hatted
representative equals that of the reduced representative.

Source: `Papers/1703.09188/paper_v2.tex:786-804`. -/
theorem leftRank_hat_eq_reducedProjection
    (W : MPOTensor d D) (L R P Q X Z Y : Matrix (Fin D) (Fin D) ℂ)
    (hP : IsOrthogonalProjection P)
    (hXL : X * L = P) (hRZ : R * Z = Q)
    (hPQY : P * Q * Y = Matrix.reducedProjection P Q)
    (hWP : ∀ i j, W i j * P = W i j)
    (hQW : ∀ i j, Q * W i j = W i j)
    (hX : IsUnit X) (hZ : IsUnit Z) (hY : IsUnit Y) :
    ℓ[virtualSandwich L W R] =
      ℓ[virtualSandwich (Matrix.reducedProjection P Q) W
        (Matrix.reducedProjection P Q)] := by
  rw [← virtualSandwich_hat_eq_reducedProjection W L R P Q X Z Y
    hP hXL hRZ hPQY hWP hQW]
  exact (leftRank_virtualSandwich X (virtualSandwich L W R) (Z * Y)
    hX (hZ.mul hY)).symm

/-- Positive semidefinite fixed matrices supply invertible outer factors $X,Z,Y$
with
$$
  XL=P,\qquad RZ=Q,\qquad PQY=\widetilde P,
$$
where $P$ and $Q$ are their support projections.

Source: `Papers/1703.09188/paper_v2.tex:786-804`. -/
theorem exists_units_for_hat_reducedProjection
    {L R : Matrix (Fin D) (Fin D) ℂ} (hL : L.PosSemidef) (hR : R.PosSemidef) :
    ∃ X Z Y : Matrix (Fin D) (Fin D) ℂ,
      IsUnit X ∧ IsUnit Z ∧ IsUnit Y ∧
      X * L = hL.supportProj ∧ R * Z = hR.supportProj ∧
      hL.supportProj * hR.supportProj * Y =
        Matrix.reducedProjection hL.supportProj hR.supportProj := by
  have hP : IsOrthogonalProjection hL.supportProj :=
    hL.isOrthogonalProjection_supportProj
  obtain ⟨Y, hY, hTQY⟩ := Matrix.exists_reducedProjection_rightFactor
    (P := hL.supportProj) (Q := hR.supportProj) hP
  have hPQY : hL.supportProj * hR.supportProj * Y =
      Matrix.reducedProjection hL.supportProj hR.supportProj := by
    rw [← Matrix.reducedProjection_mul_second hP, hTQY]
  exact ⟨hL.supportInvExtension, hR.supportInvExtension, Y,
    hL.isUnit_supportInvExtension, hR.isUnit_supportInvExtension, hY,
    hL.supportInvExtension_mul_self, hR.self_mul_supportInvExtension, hPQY⟩

end MPOTensor

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Defs
import TNLean.MPS.Operator.Periodic.LPDO

/-!
# Local contraction pattern for a square-lattice PEPS boundary tensor

Under the PEPS RFP hypothesis, arXiv:1606.00608, lines 716--724, identifies the
contraction in FigureDavid1 with the tensor of the boundary theory. This module
records only that algebraic contraction pattern for an arbitrary rank-five
component function; without the RFP hypothesis, it is not asserted to be a
boundary-theory tensor.

The component function has one physical leg and four virtual legs in left,
right, up, down order. The FigureDavid1 contraction contracts both the physical
leg and the inward (down) virtual leg between the ket and bra copies. The
remaining up indices are the two physical indices of the resulting MPO tensor,
while its left and right bond indices each group the corresponding ket and bra
indices.

The source diagram does not label the virtual directions. The names `up` and
`down` are local to each copy: after choosing the matching inward legs, the
project represents their common contracted coordinate by the fourth (`down`)
argument in both component functions.

The contraction is defined unconditionally. It is not a selected transfer fixed
point or, without the source's RFP hypothesis, a complete boundary theory.

The source diagram does not require the horizontal and vertical virtual spaces
to have the same dimension. This module therefore allows dimensions `Dh` and
`Dv` as a project generalization permitted by the diagram, not as a claim that
CPSV16 explicitly states separate dimensions.

FigureDavid2 and the trace-preserving completely positive maps `T` and `S` at
arXiv:1606.00608, lines 725--729 require the PEPS renormalization fixed-point
blocking equation from FigureDavid0. No such equation or channel theorem is
asserted here.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  boundary theories, lines 694--729; especially the PEPS tensor at lines
  696--704 and the local boundary tensor in FigureDavid1 at lines 721--724.

## Positivity of the local square-lattice PEPS boundary tensor

Under the PEPS renormalization hypothesis, arXiv:1606.00608, lines 716--724,
identifies the contraction in FigureDavid1 with the tensor of the boundary
theory. The same algebraic contraction is a Gram contraction for every
rank-five tensor: the contracted PEPS physical and inward virtual indices form
its local purification ancilla, and the horizontal PEPS virtual space is its
purifying bond. Consequently this contraction is an LPDO and hence an MPDO.

These are stronger algebraic positivity results for the displayed contraction,
not a formalization of the RFP-dependent identification with the boundary
theory. They do not select a row-transfer fixed point or assert the
under-specified boundary renormalization equations shown later in FigureDavid2.
-/

section

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The FigureDavid1 contraction pattern of a translationally invariant
square-lattice PEPS component function.

The arguments of `A` are the left and right indices in `Fin Dh`, the up and down
indices in `Fin Dv`, and the physical index in `Fin d`. One component function
is used at every lattice site. With the down leg chosen as the inward leg, the
component formula is

`E[u,u']_[(l,l'),(r,r')]
  = sum_s sum_b A[l,r,u,b,s] * conj(A[l',r',u',b,s])`.

Thus the common physical index `s` and inward virtual index `b` are contracted,
the MPO physical coordinates are `u` and `u'`, and its bonds are `(l,l')` and
`(r,r')`. This is the component form of FigureDavid1 in arXiv:1606.00608,
lines 721--724. The source identifies it with the boundary-theory tensor under
the PEPS RFP hypothesis introduced at lines 716--720; for arbitrary `A`, this
definition records only the algebraic contraction pattern.

The source diagram does not label the virtual directions. The names `up` and
`down` are local to each copy, and choosing the fourth argument of both
component functions for the matching inward leg is the project's coordinate
convention.

Allowing `Dh` and `Dv` to differ is a project generalization permitted by the
diagram. The definition does not assert a fixed-point relation, a distinguished
boundary fixed point, or the `T` and `S` maps shown later in FigureDavid2. -/
noncomputable def localBoundaryMPOTensor
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor Dv (Dh * Dh) :=
  fun (upKet, upBra) left right ↦
    ∑ s : Fin d, ∑ down : Fin Dv,
      A left.divNat right.divNat upKet down s *
        (starRingEnd ℂ) (A left.modNat right.modNat upBra down s)

/-- The local boundary MPO at arbitrary packed project coordinates.
This is the component contraction depicted in FigureDavid1 of
arXiv:1606.00608, lines 721--724; the `divNat`/`modNat` packing order is the
project's coordinate convention rather than additional source content. -/
@[simp]
theorem localBoundaryMPOTensor_apply
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ)
    (upKet upBra : Fin Dv)
    (left right : Fin (Dh * Dh)) :
    localBoundaryMPOTensor A (upKet, upBra) left right =
      ∑ s : Fin d, ∑ down : Fin Dv,
        A left.divNat right.divNat upKet down s *
          (starRingEnd ℂ) (A left.modNat right.modNat upBra down s) :=
  rfl

/-- **Project-derived coordinate formula.** Using the project's standard
`finProdFinEquiv` coordinates, the two MPO bonds are `(lKet,lBra)` and
`(rKet,rBra)`. The physical coordinates `uKet` and `uBra` are not packed: they
are the two uncontracted vertical legs of FigureDavid1.

The ket-times-conjugate-bra contraction is FigureDavid1 in arXiv:1606.00608,
lines 721--724. The order of each packed pair and the left, right, up, down order
of the rank-five function are project coordinate conventions. -/
@[simp]
theorem localBoundaryMPOTensor_finProdFinEquiv_apply
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ)
    (uKet uBra : Fin Dv)
    (lKet lBra rKet rBra : Fin Dh) :
    localBoundaryMPOTensor A (uKet, uBra)
        (finProdFinEquiv (lKet, lBra)) (finProdFinEquiv (rKet, rBra)) =
      ∑ s : Fin d, ∑ down : Fin Dv,
        A lKet rKet uKet down s *
          (starRingEnd ℂ) (A lBra rBra uBra down s) := by
  simp only [localBoundaryMPOTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

end PEPS
end TNLean

end

section

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The contraction pattern displayed in FigureDavid1 is a locally purifiable
density operator for every rank-five tensor. Its ancillary coordinate is the
pair consisting of the contracted PEPS physical index and the contracted
inward virtual index, while its purifying bond is the horizontal PEPS virtual
space.

ArXiv:1606.00608, lines 716--724, uses the PEPS RFP hypothesis to identify this
contraction with the boundary-theory tensor. The theorem proves the stronger
algebraic positivity statement for arbitrary `A`; it does not formalize that
identification, select a row-transfer fixed point, or assert the boundary
renormalization equations of FigureDavid2. -/
theorem localBoundaryMPOTensor_isLPDO
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor.IsLPDO (localBoundaryMPOTensor A) := by
  refine ⟨d * Dv, Dh,
    (fun up k ↦ Matrix.of fun left right ↦
      A left right up k.modNat k.divNat),
    (finProdFinEquiv (m := Dh) (n := Dh)).symm, ?_⟩
  intro upKet upBra
  ext left right
  rw [localBoundaryMPOTensor_apply, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin d × Fin Dv ≃ Fin (d * Dv))]
  rw [Fintype.sum_prod_type]
  simp_rw [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.of_apply,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
  rfl

/-- The contraction pattern displayed in FigureDavid1 generates a positive
semidefinite matrix product operator on every nonempty chain for every
rank-five tensor.

ArXiv:1606.00608, lines 716--724, invokes the PEPS RFP hypothesis when it
identifies this contraction with the boundary-theory tensor. The present
result concerns only the algebraic contraction and follows from its explicit
local purification; it is independent of the under-specified fixed-point and
channel constructions at lines 725--729. -/
theorem localBoundaryMPOTensor_isMPDO
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor.IsMPDO (localBoundaryMPOTensor A) :=
  (localBoundaryMPOTensor_isLPDO A).isMPDO

end PEPS
end TNLean

end

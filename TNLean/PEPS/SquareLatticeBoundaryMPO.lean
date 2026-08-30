/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs

/-!
# Boundary MPO tensor from a square-lattice PEPS tensor

This module records the local boundary tensor in the boundary-theory construction
of Cirac--Perez-Garcia--Schuch--Verstraete. A rank-five component function gives
one physical leg and four virtual legs in left, right, up, down order. The tensor
in FigureDavid1 is obtained by contracting both the physical leg and the inward
(down) virtual leg between the ket and bra copies. The remaining up indices are
the two physical indices of the boundary MPO, while its left and right bond
indices each group the corresponding ket and bra indices.

The bra copy is labelled after reflection into the ket coordinate frame. Thus
the contracted inward leg is called `down` in both component functions. In the
unreflected stacked picture, this is the ket-down leg joined to the bra-up leg.

This is an unconditional local contraction only. It is not a selected transfer
fixed point or a complete boundary theory.

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
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The boundary MPO tensor associated with a translationally invariant
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
lines 721--724.

The bra copy is labelled after reflection into the ket coordinate frame, so its
inward leg is also the fourth argument of `A`. Without this reflected coordinate
convention, the displayed contraction joins the ket-down leg to the bra-up leg.

Allowing `Dh` and `Dv` to differ is a project generalization permitted by the
diagram. The definition does not assert a fixed-point relation, a distinguished
boundary fixed point, or the `T` and `S` maps shown later in FigureDavid2. -/
noncomputable def localBoundaryMPOTensor
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor Dv (Dh * Dh) :=
  fun upKet upBra left right ↦
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
    localBoundaryMPOTensor A upKet upBra left right =
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
of the rank-five function, including reflection of the bra coordinates into the
ket frame, are project coordinate conventions. -/
@[simp]
theorem localBoundaryMPOTensor_finProdFinEquiv_apply
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ)
    (uKet uBra : Fin Dv)
    (lKet lBra rKet rBra : Fin Dh) :
    localBoundaryMPOTensor A uKet uBra
        (finProdFinEquiv (lKet, lBra)) (finProdFinEquiv (rKet, rBra)) =
      ∑ s : Fin d, ∑ down : Fin Dv,
        A lKet rKet uKet down s *
          (starRingEnd ℂ) (A lBra rBra uBra down s) := by
  simp only [localBoundaryMPOTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

end PEPS
end TNLean

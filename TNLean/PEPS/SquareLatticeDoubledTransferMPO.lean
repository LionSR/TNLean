/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Defs

/-!
# Doubled local transfer MPO of a square-lattice PEPS tensor

This module records the local doubled tensor in the boundary-theory construction
of Cirac--Perez-Garcia--Schuch--Verstraete. A rank-five component function gives
one physical leg and four virtual legs in left, right, up, down order. Contracting
the physical leg with its conjugate gives the doubled tensor in FigureDavid1.

As an `MPOTensor`, its first physical index groups the up and down ket indices,
its second physical index groups the up and down bra indices, and its left and
right bond indices each group the corresponding ket and bra indices. This is an
unconditional local transfer tensor only. It is not a selected transfer fixed
point or a complete boundary theory.

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
  696--704 and the doubled local tensor in FigureDavid1 at lines 721--724.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {d Dh Dv : ℕ}

/-- The doubled local transfer tensor associated with a translationally
invariant square-lattice PEPS component function.

The arguments of `A` are the left and right indices in `Fin Dh`, the up and down
indices in `Fin Dv`, and the physical index in `Fin d`. One component function
is used at every lattice site. For packed coordinates, the doubled tensor is

`E[(u,d),(u',d')]_[(l,l'),(r,r')]
  = sum_s A[l,r,u,d,s] * conj(A[l',r',u',d',s])`.

Thus the MPO physical ket coordinate is `(u,d)`, its physical bra coordinate is
`(u',d')`, and its bonds are `(l,l')` and `(r,r')`. This is the component form
of FigureDavid1 in arXiv:1606.00608, lines 721--724.

Allowing `Dh` and `Dv` to differ is a project generalization permitted by the
diagram. The definition does not assert a fixed-point relation, a distinguished
boundary fixed point, or the `T` and `S` maps shown later in FigureDavid2. -/
noncomputable def doubledLocalTransferMPOTensor
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ) :
    MPOTensor (Dv * Dv) (Dh * Dh) :=
  fun verticalKet verticalBra left right ↦
    ∑ s : Fin d,
      A left.divNat right.divNat verticalKet.divNat verticalKet.modNat s *
        (starRingEnd ℂ)
          (A left.modNat right.modNat verticalBra.divNat verticalBra.modNat s)

/-- The doubled local transfer MPO at arbitrary packed project coordinates.
This is the component contraction depicted in FigureDavid1 of
arXiv:1606.00608, lines 721--724; the `divNat`/`modNat` packing order is the
project's coordinate convention rather than additional source content. -/
@[simp]
theorem doubledLocalTransferMPOTensor_apply
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ)
    (verticalKet verticalBra : Fin (Dv * Dv))
    (left right : Fin (Dh * Dh)) :
    doubledLocalTransferMPOTensor A verticalKet verticalBra left right =
      ∑ s : Fin d,
        A left.divNat right.divNat verticalKet.divNat verticalKet.modNat s *
          (starRingEnd ℂ)
            (A left.modNat right.modNat verticalBra.divNat verticalBra.modNat s) :=
  rfl

/-- **Project-derived coordinate formula.** Using the project's standard
`finProdFinEquiv` coordinates, the first MPO physical index is `(uKet,dKet)`,
the second is `(uBra,dBra)`, and the two MPO bonds are `(lKet,lBra)` and
`(rKet,rBra)`.

The ket-times-conjugate-bra contraction is FigureDavid1 in arXiv:1606.00608,
lines 721--724. The order of each packed pair and the left, right, up, down order
of the rank-five function are project coordinate conventions. -/
@[simp]
theorem doubledLocalTransferMPOTensor_finProdFinEquiv_apply
    (A : Fin Dh → Fin Dh → Fin Dv → Fin Dv → Fin d → ℂ)
    (uKet dKet uBra dBra : Fin Dv)
    (lKet lBra rKet rBra : Fin Dh) :
    doubledLocalTransferMPOTensor A
        (finProdFinEquiv (uKet, dKet)) (finProdFinEquiv (uBra, dBra))
        (finProdFinEquiv (lKet, lBra)) (finProdFinEquiv (rKet, rBra)) =
      ∑ s : Fin d,
        A lKet rKet uKet dKet s *
          (starRingEnd ℂ) (A lBra rBra uBra dBra s) := by
  simp only [doubledLocalTransferMPOTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat]

end PEPS
end TNLean

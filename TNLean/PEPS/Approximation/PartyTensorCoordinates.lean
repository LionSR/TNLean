/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyTensorMaps
import TNLean.PEPS.Approximation.FamilyPhysicalReadout

/-! # Orthonormal coordinates of ordered party tensor products

The matrix of a tensor product of local maps is the product of their local
matrix entries, with each coordinate indexed by its original party.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579.
-/
noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type} {I J : P → Type} [∀ p, Fintype (I p)] [∀ p, Fintype (J p)]

/-- The tensor basis in the prescribed order of party memories.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
def partyListBasis (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a))) :
    (ps : List P) → OrthonormalBasis ((i : Fin ps.length) → I (ps.get i)) ℂ
      (Mem (partyLayout ps a))
  | [] => (OrthonormalBasis.singleton Unit ℂ).reindex
      (Equiv.ofUnique Unit ((i : Fin 0) → I (([] : List P).get i)))
  | p :: ps => ((b p).tensorProduct (partyListBasis a b ps)).reindex
      (Fin.consEquiv (fun i => I ((p :: ps).get i)))

/-- The empty tensor basis is the scalar unit.
Source: polynomial-PEPS, `01-preliminaries.tex`, line 7. -/
theorem partyListBasis_nil_apply (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (y : (i : Fin 0) → I (([] : List P).get i)) : partyListBasis a b [] y = (1 : ℂ) :=
  ((OrthonormalBasis.singleton Unit ℂ).reindex_apply
    (Equiv.ofUnique Unit ((i : Fin 0) → I (([] : List P).get i))) y).trans
      (OrthonormalBasis.singleton_apply _)

/-- Empty tensor coordinates are scalar coordinates.
Source: polynomial-PEPS, `01-preliminaries.tex`, line 7. -/
theorem partyListBasis_repr_nil (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (u : Mem (partyLayout [] a)) (x : (i : Fin 0) → I (([] : List P).get i)) :
    (partyListBasis a b []).repr u x = u :=
  ((OrthonormalBasis.singleton Unit ℂ).repr_reindex
    (Equiv.ofUnique Unit ((i : Fin 0) → I (([] : List P).get i))) u x).trans
      (OrthonormalBasis.singleton_repr _ _)

/-- The first coordinate gives the first tensor factor.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
theorem partyListBasis_cons_apply (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (p : P) (ps : List P) (y : (i : Fin (p :: ps).length) → I ((p :: ps).get i)) :
    partyListBasis a b (p :: ps) y = b p (y 0) ⊗ₜ
      partyListBasis a b ps (fun i => y i.succ) := by
  exact (((b p).tensorProduct (partyListBasis a b ps)).reindex_apply
    (Fin.consEquiv (fun i => I ((p :: ps).get i))) y).trans
      (OrthonormalBasis.tensorProduct_apply _ _ _ _)

/-- Tensor coordinates multiply on a simple tensor.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
theorem partyListBasis_repr_cons_tmul (a : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (p : P) (ps : List P) (u : Mem (Layout.atParty p a))
    (v : Mem (partyLayout ps a))
    (x : (i : Fin (p :: ps).length) → I ((p :: ps).get i)) :
    (partyListBasis a b (p :: ps)).repr (u ⊗ₜ v) x =
      (partyListBasis a b ps).repr v (fun i => x i.succ) * (b p).repr u (x 0) :=
  (((b p).tensorProduct (partyListBasis a b ps)).repr_reindex
    (Fin.consEquiv (fun i => I ((p :: ps).get i))) (u ⊗ₜ v) x).trans
      (OrthonormalBasis.tensorProduct_repr_tmul_apply _ _ _ _ _ _)

set_option maxRecDepth 2048 in
/-- Coordinates of an ordered tensor map factor into local coordinates.
Source: polynomial-PEPS, `04-compression.tex`, lines 565–579. -/
theorem partyListBasis_repr_tensorPartyMaps (a z : Layout P)
    (b : (p : P) → OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (c : (p : P) → OrthonormalBasis (J p) ℂ (Mem (Layout.atParty p z)))
    (B : (p : P) → Mem (Layout.atParty p a) →L[ℂ] Mem (Layout.atParty p z))
    (ps : List P) (x : (i : Fin ps.length) → J (ps.get i))
    (y : (i : Fin ps.length) → I (ps.get i)) :
    (partyListBasis z c ps).repr
      (tensorPartyMaps a z B ps ((partyListBasis a b ps) y)) x =
      ∏ i : Fin ps.length, (c (ps.get i)).repr
        (B (ps.get i) (b (ps.get i) (y i))) (x i) := by
  classical
  induction ps with
  | nil =>
      calc
        _ = (1 : ℂ) := (partyListBasis_repr_nil z c ((partyListBasis a b []) y) x).trans
          (partyListBasis_nil_apply a b y)
        _ = _ := (Fin.prod_univ_zero _).symm
  | cons p ps ih =>
      have hv := congrArg (tensorPartyMaps a z B (p :: ps))
        (partyListBasis_cons_apply a b p ps y)
      have ht := hv.trans (tensorPartyMaps_cons_tmul a z B p ps _ _)
      calc
        _ = (partyListBasis z c (p :: ps)).repr
          (B p (b p (y 0)) ⊗ₜ tensorPartyMaps a z B ps
            (partyListBasis a b ps (fun i => y i.succ))) x :=
          congrArg (fun v => (partyListBasis z c (p :: ps)).repr v x) ht
        _ = _ := by
          rw [partyListBasis_repr_cons_tmul, ih]
          let F : Fin (ps.length + 1) → ℂ := fun i =>
            (c ((p :: ps).get i)).repr
              (B ((p :: ps).get i) (b ((p :: ps).get i) (y i))) (x i)
          calc
            _ = F 0 * ∏ i : Fin ps.length, F i.succ := mul_comm _ _
            _ = ∏ i, F i := (Fin.prod_univ_succ F).symm
end TNLean.PEPS.PairEffect

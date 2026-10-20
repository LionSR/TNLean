/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentBondNetwork
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Diagonal

/-!
# Party networks

A *party network* is a finite tensor network whose nodes, the parties, are joined by
links carrying finite virtual alphabets. Every party has one tensor, which reads the
labels of its incident links and one physical index. No graph, position or geometry of the
parties is involved.

A link joining a party to itself is read once by that party's tensor, so it contributes a
diagonal trace. The coefficient of a party network is the endpoint contraction
`TNLean.PEPS.DependentBondNetwork.network` on the party graph with identity bond matrices,
which forces the two endpoint labels of every link, including a self-link, to agree
(`TNLean.PEPS.Approximation.PartyNetwork.coeff_eq_network`). The routing of a party network
through a graph is in `TNLean.PEPS.Approximation.RoutedContraction`.

## Main results

* `TNLean.PEPS.Approximation.PartyNetwork`: a party network and its coefficient.
* `TNLean.PEPS.Approximation.PartyNetwork.coeff_eq_network`: the party-network coefficient
  is the endpoint contraction of the party graph with identity bond matrices.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §8.1–8.2, the party operator network and the
  ket network on the party graph, `07-assembly.tex:53–99`.
-/

noncomputable section
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- The links incident to a party `p`: those having `p` as first or second endpoint.
A link joining `p` to itself occurs once. -/
abbrev IncidentLink {P Λ : Type*} (src tgt : Λ → P) (p : P) : Type _ :=
  {ℓ : Λ // src ℓ = p ∨ tgt ℓ = p}

/-- A finite party network with physical alphabet `Fin d`.

Every link `ℓ` joins the parties `src ℓ` and `tgt ℓ` and carries the virtual alphabet
`Fin (dim ℓ)`; the orientation is arbitrary bookkeeping. Every party tensor reads the labels
of its incident links and one physical index.

Source: Polynomial-PEPS manuscript (Sept 24 2026), §8.1–8.2, the party operator network and
the ket network on the party graph obtained from it by Lemma 8.1 `lem:columns`,
`07-assembly.tex:53–99`. -/
structure PartyNetwork (P Λ : Type*) (d : ℕ) where
  /-- The dimension of the virtual alphabet of a link. -/
  dim : Λ → ℕ
  /-- The first endpoint party of a link. -/
  src : Λ → P
  /-- The second endpoint party of a link. -/
  tgt : Λ → P
  /-- The tensor of a party. -/
  tensor : (p : P) → ((i : IncidentLink src tgt p) → Fin (dim i.1)) → Fin d → ℂ

namespace PartyNetwork

variable {P Λ : Type*} [Fintype P] [Fintype Λ] [DecidableEq Λ] {d : ℕ}
variable {V : Type*}

/-- The coefficient of the party network when the physical index of party `p` is read at
the site `site p`: the sum over all link labellings of the product of the party tensors. -/
def coeff (N : PartyNetwork P Λ d) (site : P → V) (σ : V → Fin d) : ℂ :=
  ∑ lab : (ℓ : Λ) → Fin (N.dim ℓ), ∏ p, N.tensor p (fun i => lab i.1) (σ (site p))

open DependentBondNetwork Classical in
/-- The party tensors read on endpoint incidences of the party graph: a link incident to `p`
reads the label at its first endpoint when `p` is its first party, and the label at its second
endpoint otherwise. -/
def endpointTensor (N : PartyNetwork P Λ d) (p : P)
    (η : LocalConfig N.src N.tgt (fun ℓ => Fin (N.dim ℓ)) p) (s : Fin d) : ℂ :=
  N.tensor p (fun i => if h : N.src i.1 = p then η ⟨(i.1, false), by simp [endpointVertex, h]⟩
    else η ⟨(i.1, true), by simpa [endpointVertex] using i.2.resolve_left h⟩) s

open DependentBondNetwork in
/-- The coefficient of a party network is the endpoint contraction of the party graph, in
which both endpoints of every link carry independent labels, joined by identity bond
matrices. -/
theorem coeff_eq_network (N : PartyNetwork P Λ d) (site : P → V) (σ : V → Fin d) :
    N.coeff site σ = network N.src N.tgt (fun ℓ => Fin (N.dim ℓ)) N.endpointTensor
      (fun _ => 1) (fun p => σ (site p)) := by
  classical
  unfold network bondWeight coeff
  simp only [Matrix.one_apply, Fintype.prod_ite_zero, Finset.prod_const_one, ite_mul,
    one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun lab pt => lab pt.1) (fun β ℓ => β (ℓ, false))
    (fun _ _ => by simp) (fun _ _ => Finset.mem_univ _) (fun _ _ => rfl) ?_ ?_
  · intro β hβ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
    funext pt
    rcases pt with ⟨ℓ, _ | _⟩
    · rfl
    · exact (hβ ℓ).symm
  · intro lab _
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [endpointTensor]

end PartyNetwork

end TNLean.PEPS.Approximation

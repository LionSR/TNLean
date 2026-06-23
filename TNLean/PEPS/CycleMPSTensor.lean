import TNLean.PEPS.CycleArcRegion
import TNLean.PEPS.Defs
import TNLean.MPS.Defs
import TNLean.MPS.Core.CyclicTrace

/-!
# The cycle-graph tensor of a translation-invariant MPS tensor

The closed-chain corollaries of the Fundamental Theorem for normal PEPS
(arXiv:1804.04964, Section 3, the two corollaries after the theorem labelled
`normal`, lines 1585--1668 of `Papers/1804.04964/paper_normal.tex`) are
statements about matrix product states: site tensors are families of `D × D`
matrices and the closed-chain state coefficient is the trace of the matrix
product.  The development's graph-level corollary
(`fundamentalTheorem_normalMPS_cycle`) is phrased for tensors on the cycle
graph.  This file builds the dictionary between the two settings for one
site-independent tensor: the cycle-graph tensor of a matrix tensor
(`cycleTensorOfMPS`), placing one copy of the matrix family at every site of
the closed chain, and the identification of the graph-level state coefficient
with the matrix-product trace `mpv` (`stateCoeff_cycleTensorOfMPS`).

The dictionary rests on the edge geometry of the cycle graph: every edge joins
a vertex to its cyclic successor (`cycleSuccEdge`, a bijection from sites to
edges), and every vertex has exactly two incident edges, the bond shared with
its cyclic predecessor and the bond shared with its cyclic successor
(`cycleLeftIncident`, `cycleRightIncident`, classified by
`incidentEdge_eq_left_or_right`).  The ordered-edge convention stores an edge
with its smaller endpoint first, so the seam edge (between the last and the
zeroth site) is stored with its endpoints in the opposite cyclic order; the
endpoint computations record both cases.

The state-coefficient identification goes through a closed-form path
expansion of matrix-product entries: an entry of a word product is a sum
over paths of bond indices pinned
at the two ends (`MPSTensor.evalWord_ofFn_apply`), and the trace of a closed
word product is a sum over cyclic bond configurations
(`MPSTensor.trace_evalWord_eq_sum_cyclic`).  Summing the per-site matrix
entries of the cycle tensor over all virtual configurations produces exactly
that cyclic sum.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, corollaries after the theorem labelled `normal`, lines
  1585--1668 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace TNLean
namespace PEPS

variable {n d D : ℕ}

section EdgeGeometry

variable [NeZero n]

/-!
### Edges of the cycle graph as cyclic successor pairs

Every edge of the cycle graph joins a site to its cyclic successor.  The
ordered-edge convention stores the smaller endpoint first, so the seam edge
(joining the last site to the zeroth) is stored with its endpoints in the
opposite cyclic order.
-/

/-- Every site of a cycle with at least three sites is adjacent to its cyclic
successor. -/
theorem cycleGraph_adj_succ (hn : 3 ≤ n) (u : Fin n) :
    (SimpleGraph.cycleGraph n).Adj u (u + 1) :=
  (cycleGraph_adj_iff_add_one hn).mpr (Or.inl rfl)

/-- The edge of the cycle graph joining a site `u` to its cyclic successor
`u + 1`.  This is the bond between sites `u` and `u + 1` of the closed chain
of the source corollaries (arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`). -/
def cycleSuccEdge (hn : 3 ≤ n) (u : Fin n) : Edge (SimpleGraph.cycleGraph n) :=
  Edge.ofAdj (cycleGraph_adj_succ hn u)

/-- Away from the seam, the bond from `u` to `u + 1` is stored as the ordered
pair `(u, u + 1)`. -/
theorem cycleSuccEdge_val_of_lt (hn : 3 ≤ n) {u : Fin n} (h : u.val + 1 < n) :
    (cycleSuccEdge hn u).1 = (u, u + 1) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hlt : u < u + 1 := by
    rw [Fin.lt_def, Fin.val_add_eq_ite, h1]
    split_ifs <;> omega
  rw [cycleSuccEdge, Edge.ofAdj_of_lt _ hlt]

/-- The seam bond, from the last site to the zeroth, is stored with its
endpoints in the opposite cyclic order. -/
theorem cycleSuccEdge_val_of_eq (hn : 3 ≤ n) {u : Fin n} (h : u.val + 1 = n) :
    (cycleSuccEdge hn u).1 = (u + 1, u) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hgt : u + 1 < u := by
    rw [Fin.lt_def, Fin.val_add_eq_ite, h1]
    split_ifs <;> omega
  rw [cycleSuccEdge, Edge.ofAdj_of_gt _ hgt]

/-- Distinct sites give distinct successor bonds. -/
theorem cycleSuccEdge_injective (hn : 3 ≤ n) :
    Function.Injective (cycleSuccEdge (n := n) hn) := by
  intro u u' h
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hval : (cycleSuccEdge hn u).1 = (cycleSuccEdge hn u').1 := congrArg Subtype.val h
  have hu := u.isLt
  have hu' := u'.isLt
  rcases (show u.val + 1 < n ∨ u.val + 1 = n by omega) with hcase | hcase <;>
    rcases (show u'.val + 1 < n ∨ u'.val + 1 = n by omega) with hcase' | hcase'
  · rw [cycleSuccEdge_val_of_lt hn hcase, cycleSuccEdge_val_of_lt hn hcase'] at hval
    exact congrArg Prod.fst hval
  · rw [cycleSuccEdge_val_of_lt hn hcase, cycleSuccEdge_val_of_eq hn hcase'] at hval
    have h1eq := congrArg (fun p : Fin n × Fin n => (p.1.val, p.2.val)) hval
    simp only [Prod.mk.injEq, Fin.val_add_eq_ite, h1] at h1eq
    exfalso
    rcases h1eq with ⟨ha, hb⟩
    split_ifs at ha hb <;> omega
  · rw [cycleSuccEdge_val_of_eq hn hcase, cycleSuccEdge_val_of_lt hn hcase'] at hval
    have h1eq := congrArg (fun p : Fin n × Fin n => (p.1.val, p.2.val)) hval
    simp only [Prod.mk.injEq, Fin.val_add_eq_ite, h1] at h1eq
    exfalso
    rcases h1eq with ⟨ha, hb⟩
    split_ifs at ha hb <;> omega
  · exact Fin.ext (by omega)

/-- Every edge of the cycle graph is the successor bond of one of its
endpoints. -/
theorem cycleSuccEdge_surjective (hn : 3 ≤ n) :
    Function.Surjective (cycleSuccEdge (n := n) hn) := by
  intro e
  rcases (cycleGraph_adj_iff_add_one hn).mp e.2.2 with h | h
  · refine ⟨e.1.1, Subtype.ext ?_⟩
    have hlt : e.1.1 < e.1.1 + 1 := h ▸ e.2.1
    rw [cycleSuccEdge, Edge.ofAdj_of_lt _ hlt]
    exact Prod.ext rfl h
  · refine ⟨e.1.2, Subtype.ext ?_⟩
    have hgt : e.1.2 + 1 < e.1.2 := h ▸ e.2.1
    rw [cycleSuccEdge, Edge.ofAdj_of_gt _ hgt]
    exact Prod.ext h rfl

/-- Sites and bonds of the closed chain are in bijection: the bond attached to
a site on its cyclic-successor side. -/
noncomputable def cycleEdgeEquiv (hn : 3 ≤ n) : Fin n ≃ Edge (SimpleGraph.cycleGraph n) :=
  Equiv.ofBijective _ ⟨cycleSuccEdge_injective hn, cycleSuccEdge_surjective hn⟩

@[simp] theorem cycleEdgeEquiv_apply (hn : 3 ≤ n) (u : Fin n) :
    cycleEdgeEquiv hn u = cycleSuccEdge hn u := rfl

/-!
### The two bonds at a site

Each site of the closed chain has exactly two incident bonds: the bond shared
with its cyclic predecessor and the bond shared with its cyclic successor.
-/

/-- The bond between a site and its cyclic successor, as an incident edge of
the site. -/
def cycleRightIncident (hn : 3 ≤ n) (v : Fin n) :
    IncidentEdge (SimpleGraph.cycleGraph n) v :=
  ⟨cycleSuccEdge hn v, by
    rcases Edge.ofAdj_endpoints (cycleGraph_adj_succ hn v) with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h⟩

/-- The bond between a site and its cyclic predecessor, as an incident edge of
the site. -/
def cycleLeftIncident (hn : 3 ≤ n) (v : Fin n) :
    IncidentEdge (SimpleGraph.cycleGraph n) v :=
  ⟨cycleSuccEdge hn (v - 1), by
    rcases Edge.ofAdj_endpoints (cycleGraph_adj_succ hn (v - 1)) with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr (h.trans (sub_add_cancel v 1))
    · exact Or.inl (h.trans (sub_add_cancel v 1))⟩

@[simp] theorem cycleLeftIncident_fst (hn : 3 ≤ n) (v : Fin n) :
    (cycleLeftIncident hn v).1 = cycleSuccEdge hn (v - 1) := rfl

@[simp] theorem cycleRightIncident_fst (hn : 3 ≤ n) (v : Fin n) :
    (cycleRightIncident hn v).1 = cycleSuccEdge hn v := rfl

/-- The two incident bonds of a site are distinct. -/
theorem cycleLeftIncident_ne_cycleRightIncident (hn : 3 ≤ n) (v : Fin n) :
    cycleLeftIncident hn v ≠ cycleRightIncident hn v := by
  intro h
  have hedge : cycleSuccEdge hn (v - 1) = cycleSuccEdge hn v :=
    congrArg (fun ie : IncidentEdge (SimpleGraph.cycleGraph n) v => ie.1) h
  have hone : (1 : Fin n) = 0 := by
    have := sub_eq_self.mp (cycleSuccEdge_injective hn hedge)
    exact this
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have h0 := congrArg Fin.val hone
  rw [h1] at h0
  simp at h0

/-- Every incident edge of a site is its predecessor bond or its successor
bond. -/
theorem incidentEdge_eq_left_or_right (hn : 3 ≤ n) (v : Fin n)
    (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) :
    ie = cycleLeftIncident hn v ∨ ie = cycleRightIncident hn v := by
  obtain ⟨u, hu⟩ := cycleSuccEdge_surjective hn ie.1
  have hinc := ie.2
  rw [← hu] at hinc
  have hv : u = v ∨ u + 1 = v := by
    rcases Edge.ofAdj_endpoints (cycleGraph_adj_succ hn u) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hinc with h | h
    · exact Or.inl (h1.symm.trans h)
    · exact Or.inr (h2.symm.trans h)
    · exact Or.inr (h1.symm.trans h)
    · exact Or.inl (h2.symm.trans h)
  rcases hv with h | h
  · exact Or.inr (Subtype.ext (hu.symm.trans (congrArg (cycleSuccEdge hn) h)))
  · refine Or.inl (Subtype.ext (hu.symm.trans (congrArg (cycleSuccEdge hn) ?_)))
    exact eq_sub_of_add_eq h

/-- The incident edges of a site are exactly its two bonds. -/
theorem univ_incidentEdge_eq_pair (hn : 3 ≤ n) (v : Fin n) :
    (Finset.univ : Finset (IncidentEdge (SimpleGraph.cycleGraph n) v)) =
      {cycleLeftIncident hn v, cycleRightIncident hn v} := by
  ext ie
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact incidentEdge_eq_left_or_right hn v ie

/-- Reading a bond-index assignment at the two bonds of a site identifies
assignments on the incident edges of the site with pairs of bond indices. -/
def cycleIncidentPairEquiv (hn : 3 ≤ n) (v : Fin n) :
    ((ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) ≃ Fin D × Fin D where
  toFun η := (η (cycleLeftIncident hn v), η (cycleRightIncident hn v))
  invFun p ie := if ie = cycleLeftIncident hn v then p.1 else p.2
  left_inv η := by
    funext ie
    rcases incidentEdge_eq_left_or_right hn v ie with h | h <;> subst h
    · simp
    · simp [(cycleLeftIncident_ne_cycleRightIncident hn v).symm]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [(cycleLeftIncident_ne_cycleRightIncident hn v).symm]

end EdgeGeometry

/-!
### The cycle tensor of a matrix tensor and its state coefficients
-/

section CycleTensor

variable [NeZero n]

/-- The cycle-graph tensor of a translation-invariant MPS tensor: one copy of
the matrix family `A` at every site of the closed chain, with every bond of
dimension `D`, the row index read from the bond shared with the cyclic
predecessor and the column index from the bond shared with the cyclic
successor.

Source: arXiv:1804.04964, Section 3, the closed-chain corollaries after the
theorem labelled `normal`, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`, where a translation-invariant MPS on a
closed chain is the tensor network with one tensor per site and one bond per
nearest-neighbour pair. -/
def cycleTensorOfMPS (hn : 3 ≤ n) (A : MPSTensor d D) :
    Tensor (SimpleGraph.cycleGraph n) d where
  bondDim _ := D
  component v η σ := A σ (η (cycleLeftIncident hn v)) (η (cycleRightIncident hn v))

@[simp] theorem cycleTensorOfMPS_bondDim (hn : 3 ≤ n) (A : MPSTensor d D)
    (e : Edge (SimpleGraph.cycleGraph n)) :
    (cycleTensorOfMPS hn A).bondDim e = D := rfl

theorem cycleTensorOfMPS_component (hn : 3 ≤ n) (A : MPSTensor d D) (v : Fin n)
    (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) (σ : Fin d) :
    (cycleTensorOfMPS hn A).component v η σ =
      A σ (η (cycleLeftIncident hn v)) (η (cycleRightIncident hn v)) := rfl

/-- **State coefficients of the cycle tensor.**  The state coefficient of the
cycle tensor of `A` is
the matrix-product coefficient of `A` on the closed chain: the trace of the
word product `A^{σ_0} ⋯ A^{σ_{n-1}}`.

Source: arXiv:1804.04964, Section 3, lines 1585--1668 of
`Papers/1804.04964/paper_normal.tex`: the state generated by an MPS on a
closed chain has the cyclic trace of the matrix product as its coefficients. -/
theorem stateCoeff_cycleTensorOfMPS (hn : 3 ≤ n) (A : MPSTensor d D)
    (σ : Fin n → Fin d) :
    stateCoeff (cycleTensorOfMPS hn A) σ = MPSTensor.mpv A σ := by
  rw [MPSTensor.mpv_eq, MPSTensor.coeff_eq, MPSTensor.trace_evalWord_eq_sum_cyclic A σ]
  simp only [stateCoeff]
  -- Reindex the virtual configurations by the site-to-bond bijection, then
  -- shift the cyclic bond labels by one step.
  refine (Fintype.sum_equiv
    (Equiv.arrowCongr (cycleEdgeEquiv hn).symm (Equiv.refl (Fin D)))
    (fun η : VirtualConfig (cycleTensorOfMPS hn A) =>
      ∏ v : Fin n, (cycleTensorOfMPS hn A).component v (fun ie => η ie.1) (σ v))
    (fun g : Fin n → Fin D => ∏ v : Fin n, A (σ v) (g (v - 1)) (g v))
    (fun η => Finset.prod_congr rfl fun v _ => rfl)).trans
    (Fintype.sum_equiv
      (Equiv.arrowCongr (Equiv.subRight (1 : Fin n)).symm (Equiv.refl (Fin D)))
      (fun g : Fin n → Fin D => ∏ v : Fin n, A (σ v) (g (v - 1)) (g v))
      (fun g : Fin n → Fin D => ∏ v : Fin n, A (σ v) (g v) (g (v + 1)))
      (fun g => Finset.prod_congr rfl fun v _ => ?_))
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_apply,
    Equiv.subRight_apply, id_eq]
  rw [add_sub_cancel_right]

end CycleTensor

end PEPS
end TNLean

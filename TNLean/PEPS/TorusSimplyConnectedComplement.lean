/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellBoundaryContour
import TNLean.PEPS.NormalPairBlocking
import TNLean.PEPS.TorusComplementPathReplacement
import TNLean.PEPS.TorusRegionIntegerCellLift
import TNLean.PEPS.TorusRectangleConnectivity

/-!
# Connectivity of the complement of a contiguous simply connected torus block

Every complementary site is joined, within the complement, to an outside
endpoint of a boundary bond. Exterior collar paths join all these endpoints.
Thus the complementary induced lattice graph is connected. Its spanning tree
is a choice rather than a further geometric hypothesis.

The occupied induced graph is assumed connected: simple connectedness of a
closed-cell union permits corner contacts, which do not join lattice sites by
bonds. This expresses the contiguous block in SCP10, Section 6.3, lines
1931–1944.

**Scope restriction (nondegenerate torus):** Both torus periods are at least
three, as required by the simple lattice graph; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
proof of Theorem 6.9, local source lines 1935–1990.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

namespace TNLean.PEPS

private theorem walk_reaches_crossing {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) (R : Finset V) {u v : V} (p : Γ.Walk u v)
    (hu : u ∉ R) (hv : v ∈ R) :
    ∃ w : {v // v ∈ Finset.univ \ R},
      (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Reachable
        ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩⟩ w ∧
      ∃ r : {v // v ∈ R}, Γ.Adj r.1 w.1 := by
  induction p with
  | nil => exact (hu hv).elim
  | @cons u z v h p ih =>
    by_cases hz : z ∈ R
    · exact ⟨⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩⟩,
        .rfl, ⟨⟨z, hz⟩, h.symm⟩⟩
    · obtain ⟨w, hw, r, hr⟩ := ih hz hv
      exact ⟨w, (SimpleGraph.Adj.reachable (G := Γ.induce
        ((Finset.univ \ R : Finset V) : Set V))
          (u := ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩⟩)
          (v := ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩⟩) h).trans hw,
        r, hr⟩

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

private theorem ambient_connected : (Γₜ).Connected := by
  have h := torusGraph_rectangle_connected (width := width) (height := height)
    0 0 width height (NeZero.pos width) (NeZero.pos height) (by omega) (by omega)
  have heq : (torusContiguousRectangle 0 0 width height : Finset X) = Finset.univ := by
    ext v
    simp only [mem_torusContiguousRectangle, Finset.mem_univ, iff_true, zero_le,
      true_and, zero_add]
    exact ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  rw [heq, Finset.coe_univ] at h
  exact h.map (SimpleGraph.induceUnivIso Γₜ).toHom
    (SimpleGraph.induceUnivIso Γₜ).surjective

omit [Fact (2 < width)] [Fact (2 < height)] in
private theorem complement_nonempty_of_collar
    (R : Finset X) (L : {v // v ∈ R} → ℤ × ℤ)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (hconn : (integerExteriorCollarGraph (Finset.univ.image L)).Connected) :
    Nonempty {v : X // v ∈ Finset.univ \ R} := by
  obtain ⟨a⟩ := hconn.nonempty
  let v : X := ((a.1.1 : ZMod width), (a.1.2 : ZMod height))
  have hv : v ∉ R := by
    intro hv
    apply hπ (integerCellCenter a.1)
      ((integerCellCenter_mem_exteriorCollar_iff _ _).mpr a.2)
    simpa only [v, torusVertexPoint_intCast, integerCellCenter] using
      torusVertexPoint_mem_torusRegionRealization R v hv
  exact ⟨⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩⟩⟩

private theorem complement_connected_of_collar
    (R : Finset X)
    (hR : ((Γₜ).induce (R : Set X)).Connected)
    (L : {v // v ∈ R} → ℤ × ℤ) (hL : IsTorusRegionIntegerLift R L)
    (hπ : ∀ x ∈ integerExteriorCollar (Finset.univ.image L),
      torusRealProjection width height x ∉ torusRegionRealization R)
    (hconn : (integerExteriorCollarGraph (Finset.univ.image L)).Connected) :
    ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Connected := by
  obtain ⟨r₀⟩ := hR.nonempty
  refine { preconnected := ?_, nonempty := complement_nonempty_of_collar R L hπ hconn }
  intro u v
  obtain ⟨pu⟩ := ambient_connected.preconnected u.1 r₀.1
  obtain ⟨pv⟩ := ambient_connected.preconnected v.1 r₀.1
  obtain ⟨w₀, huw, r₁, h₀⟩ := walk_reaches_crossing Γₜ R pu
    (Finset.mem_sdiff.mp u.2).2 r₀.2
  obtain ⟨w, hvw, r₂, h₂⟩ := walk_reaches_crossing Γₜ R pv
    (Finset.mem_sdiff.mp v.2).2 r₀.2
  obtain ⟨p⟩ := hR.preconnected r₁ r₂
  obtain ⟨q, -⟩ := exists_complementWalk_of_integerExteriorCollarGraph_connected
    R L hL hπ hconn p w₀ w h₀ h₂
  exact huw.trans (q.reachable.trans hvw.symm)

/-- A contiguous torus block with simply connected closed-cell realization has
connected induced complement. In particular its complementary spanning tree
can be chosen without an additional connectivity premise. Source: SCP10,
Section 6.3 and proof of Theorem 6.9, lines 1931–1990. -/
theorem torusGraph_compl_connected_of_isSimplyConnected
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (hR : ((Γₜ).induce (R : Set X)).Connected) :
    ((Γₜ).induce ((Finset.univ \ R : Finset X) : Set X)).Connected := by
  obtain ⟨L, hL, hA, hπ⟩ :=
    exists_integerLift_simplyConnected_exteriorCollar_of_isSimplyConnected R hSC
  exact complement_connected_of_collar R hR L hL hπ
    (integerExteriorCollarGraph_connected_of_isSimplyConnected _ hA)

/-- A contiguous simply connected torus block has a boundary bond. Hence its
finite boundary can be numbered by a positive number of labels. Source: SCP10,
Theorem 6.9, lines 2027–2072; the boundary counts crossing bonds. -/
theorem nonempty_torusRegionBoundaryEdge_of_isSimplyConnected
    (R : Finset X) (hSC : IsSimplyConnected (torusRegionRealization R))
    (hR : ((Γₜ).induce (R : Set X)).Connected) :
    Nonempty {f : Edge Γₜ // IsRegionBoundaryEdge R f} := by
  obtain ⟨r⟩ := hR.nonempty
  obtain ⟨s⟩ := (torusGraph_compl_connected_of_isSimplyConnected R hSC hR).nonempty
  apply nonempty_regionBoundaryEdge_of_connected ambient_connected ⟨r.1, r.2⟩
  intro heq
  exact (Finset.mem_sdiff.mp s.2).2 (heq.symm ▸ Finset.mem_univ s.1)

end TNLean.PEPS

import TNLean.PEPS.Blocking

/-!
# Middle physical indices for edge-blocked PEPS

This file gives the middle tensor in the edge-centered three-site decomposition
its own physical index.  For an edge \(e=(u,v)\), the middle physical
configuration is the family of physical indices on \(V\setminus\{u,v\}\).

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3, `eq:block_to_mps`](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 981--1009.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [DecidableRel G.Adj] in
private theorem edge_ne_of_middle_incident_for_physical (e : Edge G) {v : V}
    (hv : v ∈ edgeMiddleVertices e) (ie : IncidentEdge G v) : ie.1 ≠ e := by
  intro hie
  have hvne := (mem_edgeMiddleVertices_iff e v).mp hv
  rcases ie.2 with hleft | hright
  · exact hvne.1 (hleft.symm.trans (congrArg (fun f : Edge G => f.1.1) hie))
  · exact hvne.2 (hright.symm.trans (congrArg (fun f : Edge G => f.1.2) hie))

/-- Physical configurations on the middle block \(V\setminus\{u,v\}\) in the
edge-centered three-site decomposition at the edge \(e=(u,v)\).

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
abbrev EdgeMiddlePhysicalConfig (e : Edge G) : Type _ :=
  (v : {v : V // v ∈ edgeMiddleVertices e}) → Fin d

/-- Restrict a global physical configuration to the middle block of the
edge-centered three-site decomposition.

Source: arXiv:1804.04964, Section 3, `eq:block_to_mps`,
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
def edgeMiddlePhysicalConfigOf (e : Edge G) (σ : V → Fin d) :
    EdgeMiddlePhysicalConfig (G := G) (d := d) e :=
  fun v => σ v.1

/-- The blocked middle tensor with the distinguished edge left open, written
with its own middle physical index.

The endpoint residual data are fixed, while the matrix index on the
distinguished edge is absent from the middle region. This is the middle block
of the edge-centered three-site chain in arXiv:1804.04964, Section 3. -/
noncomputable def edgeOpenMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    ℂ :=
  ∑ ζ : EdgeOpenMiddleConfig (G := G) A e leftResidual rightResidual,
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
        (τ v)

/-- The ordinary blocked middle tensor, written with its own middle physical
index. -/
noncomputable def edgeMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (β : EdgeBoundaryConfig (G := G) A e) : ℂ :=
  ∑ η : EdgeMiddleConfig (G := G) A e β,
    ∏ v : {v : V // v ∈ edgeMiddleVertices e},
      A.component v.1 (fun ie => η.1 ie.1) (τ v)

/-- The full-configuration form of the open middle tensor is the
middle-indexed tensor evaluated on the restricted physical configuration. -/
theorem edgeOpenMiddleWeight_eq_on (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (leftResidual : ResidualLocalConfig (G := G) A (edgeLeftIncident (G := G) e))
    (rightResidual : ResidualLocalConfig (G := G) A (edgeRightIncident (G := G) e)) :
    edgeOpenMiddleWeight (G := G) A e σ leftResidual rightResidual =
      edgeOpenMiddleWeightOn (G := G) A e
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e σ)
        leftResidual rightResidual :=
  rfl

/-- The full-configuration form of the ordinary middle tensor is the
middle-indexed tensor evaluated on the restricted physical configuration. -/
theorem edgeMiddleWeight_eq_on (A : Tensor G d) (e : Edge G) (σ : V → Fin d)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeMiddleWeight (G := G) A e σ β =
      edgeMiddleWeightOn (G := G) A e
        (edgeMiddlePhysicalConfigOf (G := G) (d := d) e σ) β := by
  classical
  rw [edgeMiddleWeight, edgeMiddleWeightOn]
  refine Finset.sum_congr rfl ?_
  intro η _
  rw [Finset.prod_subtype (F := inferInstance) (s := edgeMiddleVertices e)
    (p := fun v => v ∈ edgeMiddleVertices e) (h := by intro v; rfl)]
  rfl

/-- The ordinary blocked middle tensor is the open middle tensor after restoring
the fixed distinguished-edge index and reindexing the finite sum.

This is the coefficient-level reindexing behind the identity specialization of
an edge insertion, with the physical index already restricted to the middle
block. -/
theorem edgeMiddleWeightOn_eq_edgeOpenMiddleWeightOn (A : Tensor G d) (e : Edge G)
    (τ : EdgeMiddlePhysicalConfig (G := G) (d := d) e)
    (β : EdgeBoundaryConfig (G := G) A e) :
    edgeMiddleWeightOn (G := G) A e τ β =
      edgeOpenMiddleWeightOn (G := G) A e τ β.leftResidual β.rightResidual := by
  classical
  rw [edgeMiddleWeightOn, edgeOpenMiddleWeightOn]
  let φ := edgeMiddleConfigEquivOpenMiddleConfig (G := G) A e β
  calc
    (∑ η : EdgeMiddleConfig (G := G) A e β,
        ∏ v : {v : V // v ∈ edgeMiddleVertices e},
          A.component v.1 (fun ie => η.1 ie.1) (τ v))
        = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
            ∏ v : {v : V // v ∈ edgeMiddleVertices e},
              A.component v.1 (fun ie => (φ.symm ζ).1 ie.1) (τ v) := by
          refine Fintype.sum_equiv φ
            (fun η : EdgeMiddleConfig (G := G) A e β =>
              ∏ v : {v : V // v ∈ edgeMiddleVertices e},
                A.component v.1 (fun ie => η.1 ie.1) (τ v))
            (fun ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual =>
              ∏ v : {v : V // v ∈ edgeMiddleVertices e},
                A.component v.1 (fun ie => (φ.symm ζ).1 ie.1) (τ v)) ?_
          intro η
          simp [φ]
    _ = ∑ ζ : EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual,
          ∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ.1 v.2 ie)
              (τ v) := by
        refine Finset.sum_congr rfl ?_
        intro ζ _
        refine Fintype.prod_congr _ _ ?_
        intro v
        apply congrArg (fun cfg => A.component v.1 cfg (τ v))
        funext ie
        have hne := edge_ne_of_middle_incident_for_physical (G := G) e v.2 ie
        simpa [φ, edgeComplementValue, edgeMiddleConfigEquivOpenMiddleConfig] using
          edgeOpenMiddleConfigToMiddleConfig_apply_ne (G := G) A e β ζ ⟨ie.1, hne⟩

end PEPS
end TNLean

import TNLean.PEPS.AreaLaw.VertexBoundaryCorollaries

/-!
Concrete cuts for the vertex-boundary conventions: a site with four neighbors,
negative coordinates, a disconnected pair, and empty and full cuts. The entropy
examples use precisely the supplied edge-boundary inequality or uniform theorem.
-/

open TNLean.PEPS.AreaLaw

private def crossDomain : Finset (ℤ × ℤ) :=
  {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

private def center : Site crossDomain := ⟨(0, 0), by simp [crossDomain]⟩

private def east : Site crossDomain := ⟨(1, 0), by simp [crossDomain]⟩

example : (domainGraph crossDomain).degree center = 4 := by decide

example : (domainGraph crossDomain).Adj center east := by decide

example : innerBoundary crossDomain {center} = {center} := by
  classical
  have h : ∃ y ∉ ({center} : Finset (Site crossDomain)),
      (domainGraph crossDomain).Adj center y := ⟨east, by decide, by decide⟩
  simp only [innerBoundary, Finset.filter_singleton, h, ↓reduceIte]

private def disconnectedDomain : Finset (ℤ × ℤ) := {(0, 0), (2, 0)}

example (A : Finset (Site disconnectedDomain)) :
    innerBoundary disconnectedDomain A = ∅ ∧
      endpointBoundary disconnectedDomain A = ∅ := by
  classical
  have h : ∀ x y, ¬ (domainGraph disconnectedDomain).Adj x y := by decide
  have he : edgeBoundary disconnectedDomain A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x, y⟩ := e
    exact h x y ((SimpleGraph.mem_edgeSet (domainGraph disconnectedDomain)).mp
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp he).1))
  simp [innerBoundary, endpointBoundary, h, he]

example (Λ : Finset (ℤ × ℤ)) :
    innerBoundary Λ ∅ = ∅ ∧ endpointBoundary Λ ∅ = ∅ := by simp

example (Λ : Finset (ℤ × ℤ)) :
    innerBoundary Λ Finset.univ = ∅ ∧ endpointBoundary Λ Finset.univ = ∅ :=
  ⟨innerBoundary_univ Λ, endpointBoundary_univ Λ⟩

example {Λ : Finset (ℤ × ℤ)} {q : ℕ} {Ω : StateSpace Λ q}
    {A : Finset (Site Λ)} {C : ℝ} (hC : 0 ≤ C)
    (h : regionalEntropy Λ q Ω A ≤ C * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤ 4 * C * (innerBoundary Λ A).card ∧
    regionalEntropy Λ q Ω A ≤ 2 * C * (endpointBoundary Λ A).card :=
  ⟨regionalEntropy_le_four_mul_innerBoundary_card hC h,
    regionalEntropy_le_two_mul_endpointBoundary_card hC h⟩

example (h : UniformAreaLaw) := h.vertex_boundary_bounds

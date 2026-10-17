/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PinnedZeroFloorOptimizer

/-! Same-family, original-boundary and vacuous negative-bound regressions. -/

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

open Pinned Pinned.NestedFilter Pinned.NestedFilter.Energy

-- Empty families pass through the public theorem with zero energy and fidelity budgets.
example {L q : ℕ} {J E₀ Δ : ℝ} (h : SquareHamiltonian L q J)
    {Ω : State L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    ∃ F : FilterFamily q 0 (fun j ↦ Fin.elim0 j),
      IsMaximizer Ω (fun _ ↦ 1) F ∧ 0 < ‖output F Ω‖ ∧
      ‖normalizedOutput F Ω‖ = 1 ∧
      |(⟪normalizedOutput F Ω, toEuclideanLin h.operator (normalizedOutput F Ω)⟫_ℂ).re - E₀| ≤ 0 ∧
      Δ * (1 - ‖⟪Ω, normalizedOutput F Ω⟫_ℂ‖ ^ 2) ≤ 0 := by
  simpa using h.exists_pinned_maximizer_energy_fidelity hΩ
    (fun j : Fin 0 ↦ Fin.elim0 j)
    (by intro i; exact Fin.elim0 i) (by intro _ i; exact Fin.elim0 i)
    (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun _ ↦ le_rfl)

-- Repeated empty regions and endpoint weights a = 1 retain the same global maximum.
example {L q : ℕ} {J E₀ Δ : ℝ} (h : SquareHamiltonian L q J)
    {Ω : State L q} (hΩ : h.IsGappedGroundState E₀ Ω Δ) :
    ∃ F : FilterFamily q 2 (fun _ ↦ (∅ : Finset (Vertex L))),
      IsMaximizer Ω (fun _ ↦ 1) F ∧ 0 < ‖output F Ω‖ := by
  obtain ⟨F, hF, hpos, _⟩ := h.exists_pinned_maximizer_energy_fidelity hΩ
    (fun _ : Fin 2 ↦ ∅) (fun _ _ _ ↦ le_rfl)
    (by intro _ _ _ hi; simpa [Crosses] using hi)
    (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun _ ↦ le_rfl)
  exact ⟨F, hF, hpos⟩

private def emptyHamiltonian (q : ℕ) : SquareHamiltonian 0 q (-1) where
  siteTerm := fun _ ↦ 0
  edgeTerm := fun _ ↦ 0
  site_supported := fun _ ↦ Submodule.zero_mem _
  edge_supported := fun _ ↦ Submodule.zero_mem _
  site_norm_le := fun v ↦ Fin.elim0 v.1
  edge_norm_le := fun e ↦ Fin.elim0 e.1.1.1
  hermitian := by
    simpa using (Matrix.isHermitian_zero :
      (0 : Matrix (Configuration 0 q) (Configuration 0 q) ℂ).IsHermitian)

private def emptyConfiguration (q : ℕ) : Configuration 0 q :=
  fun v ↦ Fin.elim0 v.1

private def emptyState (q : ℕ) : State 0 q :=
  PiLp.single 2 (emptyConfiguration q) 1

private theorem emptyState_apply (q : ℕ) (σ : Configuration 0 q) : emptyState q σ = 1 := by
  have hσ : σ = emptyConfiguration q := Subsingleton.elim _ _
  simp [emptyState, hσ]

private theorem emptyHamiltonian_gapped (q : ℕ) (Δ : ℝ) :
    (emptyHamiltonian q).IsGappedGroundState 0 (emptyState q) Δ := by
  have hH : (emptyHamiltonian q).operator = 0 := by
    simp [SquareHamiltonian.operator, emptyHamiltonian]
  have hP : vecMulVec (WithLp.ofLp (emptyState q)) (star (WithLp.ofLp (emptyState q))) =
      (1 : Matrix (Configuration 0 q) (Configuration 0 q) ℂ) := by
    ext x y
    have hxy : x = y := Subsingleton.elim _ _
    simp [vecMulVec_apply, emptyState_apply, Matrix.one_apply, hxy]
  refine ⟨by simp [emptyState], ?_, ?_⟩
  · simp [hH]
  · simpa [hH, hP] using
      (Matrix.PosSemidef.zero : (0 : Matrix (Configuration 0 q) (Configuration 0 q) ℂ).PosSemidef)

-- The empty-grid construction works for q = 0 and every positive q, at any real gap.
example (q : ℕ) (Δ : ℝ) :
    ∃ F : FilterFamily q 1 (fun _ ↦ (∅ : Finset (Vertex 0))),
      IsMaximizer (emptyState q) (fun _ ↦ 1) F ∧
      0 < ‖output F (emptyState q)‖ ∧ ‖normalizedOutput F (emptyState q)‖ = 1 ∧
      |(⟪normalizedOutput F (emptyState q),
          toEuclideanLin (emptyHamiltonian q).operator
            (normalizedOutput F (emptyState q))⟫_ℂ).re| ≤ 0 ∧
      Δ * (1 - ‖⟪emptyState q, normalizedOutput F (emptyState q)⟫_ℂ‖ ^ 2) ≤ 0 := by
  have h := (emptyHamiltonian q).exists_pinned_maximizer_energy_fidelity
    (emptyHamiltonian_gapped q Δ) (fun _ : Fin 1 ↦ ∅) (fun _ _ _ ↦ le_rfl)
    (by intro _ _ _ hi; simpa [Crosses] using hi)
    (fun _ ↦ 1) (fun _ ↦ zero_lt_one) (fun _ ↦ le_rfl)
  simpa [crossingCount, Crosses] using h

-- A one-site square forces J ≥ 0 from the site field, despite having no edges.
example {q : ℕ} {J : ℝ} (h : SquareHamiltonian 1 q J) : 0 ≤ J :=
  (norm_nonneg (h.siteTerm (0, 0))).trans (h.site_norm_le (0, 0))

-- Both empty/full cuts and a nontrivial one-site cut count forward edges only once.
example {L : ℕ} : crossingCount (∅ : Finset (Vertex L)) = 0 ∧
    crossingCount (Finset.univ : Finset (Vertex L)) = 0 := by
  simp [crossingCount, Crosses]

example : Crosses ({(0, 0)} : Finset (Vertex 2))
    ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩ := by
  decide

example : (AreaLaw.edgeBoundary (AreaLaw.rectangularDomain 2 2)
    (({(0, 0)} : Finset (Vertex 2)).map (AreaLaw.rectangleSiteEquiv 2 2).toEmbedding)).card =
      crossingCount ({(0, 0)} : Finset (Vertex 2)) :=
  card_edgeBoundary_eq_crossingCount _

-- The noncomputable inherited Fintype is bypassed by an explicit two-edge enumeration.
example : crossingCount ({(0, 0)} : Finset (Vertex 2)) = 2 := by
  classical
  let eh : ForwardEdge 2 := ⟨((0, 0), (1, 0)), Or.inl ⟨rfl, rfl⟩⟩
  let ev : ForwardEdge 2 := ⟨((0, 0), (0, 1)), Or.inr ⟨rfl, rfl⟩⟩
  have hc (e : ForwardEdge 2) :
      Crosses ({(0, 0)} : Finset (Vertex 2)) e ↔ e = eh ∨ e = ev := by
    rcases e with ⟨⟨⟨x, y⟩, ⟨u, v⟩⟩, he⟩
    fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
      simp_all [ForwardAdjacent, Crosses, eh, ev, Subtype.ext_iff]
  have hf : Finset.univ.filter (Crosses ({(0, 0)} : Finset (Vertex 2))) = {eh, ev} := by
    ext e
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] using hc e
  rw [crossingCount, hf]
  simp [eh, ev]

end TNLean.PEPS.Approximation

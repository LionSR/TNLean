import TNLean.PEPS.FundamentalTheorem.GaugeAction

/-!
# Open-edge gauge action for PEPS

This file contains the open-edge version of gauge cancellation used in the
post-absorption edge-insertion identity of arXiv:1804.04964, Section 3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}


/-- The gauge-matrix product over all vertices and incident edges factors into one
two-endpoint factor per edge: the left gauge `X_g` and the right gauge
`(X_g⁻¹)ᵀ`, evaluated against the outer and inner configurations. -/
private lemma prod_edgeGaugeAt_eq_prod_edge (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) (ξ ω : OpenLocalConfig (G := G) A) :
    (∏ v : V, ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ξ v ie) (ω v ie)) =
      ∏ g : Edge G,
        (X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)
            (ξ g.1.1 (edgeLeftIncident (G := G) g)) (ω g.1.1 (edgeLeftIncident (G := G) g)) *
          ((X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)⁻¹)
            (ω g.1.2 (edgeRightIncident (G := G) g))
            (ξ g.1.2 (edgeRightIncident (G := G) g)) := by
  rw [prod_incident_eq_prod_edge
    (fun v ie => edgeGaugeAt A X v ie (ξ v ie) (ω v ie))]
  refine Finset.prod_congr rfl ?_
  intro g _
  rw [← Matrix.GeneralLinearGroup.coe_inv (X g)]
  have hne : ¬ g.1.1 = g.1.2 := ne_of_lt g.2.1
  simp only [edgeGaugeAt, edgeLeftIncident, edgeRightIncident, hne,
    ↓reduceIte, Matrix.transpose_apply]
  rfl

/-- **Open-edge gauge sum.** Summing the gauge factors over the outer
configuration, weighted by the inserted matrix on the open edge and constrained
by consistency on every other edge, cancels the gauges on all edges other than
`e` and conjugates the inserted matrix by the open-edge gauge `(X_e)ᵀ`.

This is the open-edge analog of `gauge_sum_over_virtual`: the consistent-off-`e`
outer configurations reindex to the two open indices and a free complement, the
gauge product factors edgewise, the complement edges cancel to consistency deltas
on the inner configuration, and the two open indices conjugate the inserted
matrix. -/
private lemma open_gauge_sum_over_outer (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) (e : Edge G)
    (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (ω : OpenLocalConfig (G := G) A) :
    (∑ ξ : OpenLocalConfig (G := G) A,
      (∏ f : {f : Edge G // f ≠ e},
        if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
            ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
        N (ξ e.1.1 (edgeLeftIncident (G := G) e))
          (ξ e.1.2 (edgeRightIncident (G := G) e)) *
        ∏ v : V, ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ξ v ie) (ω v ie)) =
      (∏ f : {f : Edge G // f ≠ e},
        if ω f.1.1.1 (edgeLeftIncident (G := G) f.1) =
            ω f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
        ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)ᵀ * N *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)ᵀ)
          (ω e.1.1 (edgeLeftIncident (G := G) e)) (ω e.1.2 (edgeRightIncident (G := G) e)) := by
  classical
  -- Factor the gauge product edgewise inside the outer sum.
  simp_rw [prod_edgeGaugeAt_eq_prod_edge A X]
  -- Collapse the consistency deltas and restrict to configurations consistent off `e`.
  set G' : OpenLocalConfig (G := G) A → ℂ := fun ξ =>
    N (ξ e.1.1 (edgeLeftIncident (G := G) e)) (ξ e.1.2 (edgeRightIncident (G := G) e)) *
      ∏ g : Edge G,
        (X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)
            (ξ g.1.1 (edgeLeftIncident (G := G) g)) (ω g.1.1 (edgeLeftIncident (G := G) g)) *
          ((X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)⁻¹)
            (ω g.1.2 (edgeRightIncident (G := G) g)) (ξ g.1.2 (edgeRightIncident (G := G) g))
    with hG'
  have hcollapse :
      (∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ g : Edge G,
            (X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)
                (ξ g.1.1 (edgeLeftIncident (G := G) g)) (ω g.1.1 (edgeLeftIncident (G := G) g)) *
              ((X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)⁻¹)
                (ω g.1.2 (edgeRightIncident (G := G) g))
                (ξ g.1.2 (edgeRightIncident (G := G) g))) =
        ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, G' ξ.1 := by
    calc
      _ = ∑ ξ : OpenLocalConfig (G := G) A,
            if IsConsistentOff (G := G) A e ξ then G' ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) A e ξ <;> simp [h, hG']
      _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ},
            G' ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (OpenLocalConfig (G := G) A)))
              (f := G') (p := IsConsistentOff (G := G) A e)]
            simp
  rw [hcollapse]
  -- Reindex the consistent-off-`e` outer configurations to the two open indices
  -- and a free complement configuration.
  rw [show (∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ},
        G' ξ.1) =
      ∑ y : Fin (A.bondDim e) × Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e,
        G' ((consistentOffEquivDoubled (G := G) A e).symm y) from
    (Equiv.sum_comp (consistentOffEquivDoubled (G := G) A e).symm
      (fun ξ => G' ξ.1)).symm]
  -- Compute the summand on the doubled data, splitting the edge product into the
  -- open-edge factor and the complement factors.
  have hsummand : ∀ (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e),
      G' ((consistentOffEquivDoubled (G := G) A e).symm (i, k, ζ)) =
        (N i k *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
              i (ω e.1.1 (edgeLeftIncident (G := G) e)) *
            ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
              (ω e.1.2 (edgeRightIncident (G := G) e)) k)) *
          ∏ g : {g : Edge G // g ≠ e},
            (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                (ζ g) (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
              ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) (ζ g) := by
    intro i k ζ
    have heq : (consistentOffEquivDoubled (G := G) A e).symm (i, k, ζ) =
        localOfDoubled (G := G) A e i k ζ := rfl
    rw [heq]
    simp only [hG']
    rw [localOfDoubled_left_e, localOfDoubled_right_e]
    set F : Edge G → ℂ := fun g =>
      (X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)
          (localOfDoubled (G := G) A e i k ζ g.1.1 (edgeLeftIncident (G := G) g))
          (ω g.1.1 (edgeLeftIncident (G := G) g)) *
        ((X g : Matrix (Fin (A.bondDim g)) (Fin (A.bondDim g)) ℂ)⁻¹)
          (ω g.1.2 (edgeRightIncident (G := G) g))
          (localOfDoubled (G := G) A e i k ζ g.1.2 (edgeRightIncident (G := G) g)) with hFdef
    have hsplit : (∏ g : Edge G, F g) = F e * ∏ g : {g : Edge G // g ≠ e}, F g.1 := by
      rw [← Finset.prod_compl_mul_prod {e} F, Finset.prod_singleton, mul_comm]
      congr 1
      rw [← Finset.prod_subtype (Finset.univ.filter (· ≠ e))]
      · apply Finset.prod_congr
        · ext g; simp
        · intros; rfl
      · intro g; simp
    rw [hsplit]
    have hFe : F e =
        (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
            i (ω e.1.1 (edgeLeftIncident (G := G) e)) *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
            (ω e.1.2 (edgeRightIncident (G := G) e)) k := by
      simp only [hFdef, localOfDoubled_left_e, localOfDoubled_right_e]
    have hFg : ∀ g : {g : Edge G // g ≠ e}, F g.1 =
        (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
            (ζ g) (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
          ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
            (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) (ζ g) := by
      intro g
      simp only [hFdef, localOfDoubled_left_ne, localOfDoubled_right_ne]
    rw [hFe, Finset.prod_congr rfl (fun g _ => hFg g)]
    ring
  -- Rewrite each summand and split the doubled sum into the open-index part and
  -- the complement part.
  simp_rw [hsummand]
  rw [Fintype.sum_prod_type]
  -- The complement factor is independent of `i`; pull the product out.
  have hsep : ∀ i : Fin (A.bondDim e),
      (∑ p : Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e,
        (N i p.1 *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
              i (ω e.1.1 (edgeLeftIncident (G := G) e)) *
            ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
              (ω e.1.2 (edgeRightIncident (G := G) e)) p.1)) *
          ∏ g : {g : Edge G // g ≠ e},
            (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                (p.2 g) (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
              ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) (p.2 g)) =
      (∑ k : Fin (A.bondDim e),
        N i k *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
              i (ω e.1.1 (edgeLeftIncident (G := G) e)) *
            ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
              (ω e.1.2 (edgeRightIncident (G := G) e)) k)) *
        ∏ f : {f : Edge G // f ≠ e},
          if ω f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ω f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0 := by
    intro i
    -- the complement sum factors into one per-edge sum, each cancelling to a delta.
    have hQ :
        (∑ ζ : EdgeComplementConfig (G := G) A e,
          ∏ g : {g : Edge G // g ≠ e},
            (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                (ζ g) (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
              ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) (ζ g)) =
          ∏ f : {f : Edge G // f ≠ e},
            if ω f.1.1.1 (edgeLeftIncident (G := G) f.1) =
                ω f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0 := by
      rw [show (∑ ζ : EdgeComplementConfig (G := G) A e,
          ∏ g : {g : Edge G // g ≠ e},
            (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                (ζ g) (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
              ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) (ζ g)) =
          ∏ g : {g : Edge G // g ≠ e},
            ∑ c : Fin (A.bondDim g.1),
              (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                  c (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
                ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                  (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) c from by
        simpa [Fintype.piFinset_univ, EdgeComplementConfig] using
          (Finset.prod_univ_sum (fun g : {g : Edge G // g ≠ e} => Finset.univ)
            (fun g c =>
              (X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)
                  c (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) *
                ((X g.1 : Matrix (Fin (A.bondDim g.1)) (Fin (A.bondDim g.1)) ℂ)⁻¹)
                  (ω g.1.1.2 (edgeRightIncident (G := G) g.1)) c)).symm]
      refine Finset.prod_congr rfl ?_
      intro g _
      exact gauge_sum_left_right_matrix_inv (X g.1)
        (ω g.1.1.1 (edgeLeftIncident (G := G) g.1)) (ω g.1.1.2 (edgeRightIncident (G := G) g.1))
    rw [Fintype.sum_prod_type, ← hQ, Finset.sum_mul_sum]
  simp_rw [hsep]
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  -- the open-edge double sum is the conjugation `(X_eᵀ N (X_e⁻¹)ᵀ)`.
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- **Open-edge gauge action on an inserted-edge coefficient.**

Applying an oriented edge-gauge family `Z` to a PEPS tensor and inserting `N` on
edge `e` equals inserting the conjugated matrix `(Z_e)ᵀ N ((Z_e)⁻¹)ᵀ` on the
ungauged tensor: the internal-edge gauges cancel pairwise, while the two endpoint
gauges on the open edge conjugate the inserted matrix by the transpose of the
open-edge gauge.

This is the open-edge analog of `applyGauge_stateCoeff`, used in the
post-absorption edge-insertion identity (arXiv:1804.04964, Section 3,
`eq:inj_equal_edge`). The transpose placement is forced by the orientation
convention of `edgeGaugeAt`. -/
theorem edgeInsertedCoeff_applyGauge (B : Tensor G d)
    (Z : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) (e : Edge G) (σ : V → Fin d)
    (N : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) (applyGauge B Z) e σ N =
      edgeInsertedCoeff (G := G) B e σ
        ((Z e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)ᵀ * N *
          ((Z e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)⁻¹)ᵀ) := by
  classical
  rw [edgeInsertedCoeff_eq_sum_local (applyGauge B Z) e σ N,
    edgeInsertedCoeff_eq_sum_local B e σ _]
  -- The gauged components are `gaugeVertex`; expand the vertex product.
  have hcomp : ∀ (ξ : OpenLocalConfig (G := G) (applyGauge B Z)),
      (∏ v : V, (applyGauge B Z).component v (ξ v) (σ v)) =
        ∑ ω : OpenLocalConfig (G := G) B,
          ∏ v : V,
            (∏ ie : IncidentEdge G v, edgeGaugeAt B Z v ie (ξ v ie) (ω v ie)) *
              B.component v (ω v) (σ v) := by
    intro ξ
    exact prod_gaugeVertex_eq_sum_local_open B Z ξ σ
  -- Rewrite the left sum into the doubled outer/inner double sum, then sum over the
  -- outer configuration using the open-edge gauge sum.
  simp_rw [hcomp]
  -- Distribute the delta/insert weight into the inner sum and swap the order.
  rw [Finset.sum_congr rfl (fun ξ _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ω _
  -- For fixed inner `ω`, pull `∏ v B.component v (ω v)` out and apply the gauge sum.
  have hpull : ∀ ξ : OpenLocalConfig (G := G) (applyGauge B Z),
      (∏ f : {f : Edge G // f ≠ e},
        if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
            ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
        N (ξ e.1.1 (edgeLeftIncident (G := G) e))
          (ξ e.1.2 (edgeRightIncident (G := G) e)) *
        ∏ v : V,
          ((∏ ie : IncidentEdge G v, edgeGaugeAt B Z v ie (ξ v ie) (ω v ie)) *
            B.component v (ω v) (σ v)) =
      ((∏ f : {f : Edge G // f ≠ e},
        if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
            ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
        N (ξ e.1.1 (edgeLeftIncident (G := G) e))
          (ξ e.1.2 (edgeRightIncident (G := G) e)) *
        ∏ v : V, ∏ ie : IncidentEdge G v, edgeGaugeAt B Z v ie (ξ v ie) (ω v ie)) *
        ∏ v : V, B.component v (ω v) (σ v) := by
    intro ξ
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl (fun ξ _ => hpull ξ)]
  rw [← Finset.sum_mul]
  congr 1
  exact open_gauge_sum_over_outer B Z e N ω

/-- Gauge equivalence implies the same PEPS state. -/
theorem GaugeEquiv.sameState {A B : Tensor G d} (h : GaugeEquiv A B) :
    SameState A B := by
  classical
  rcases h with ⟨hDim, X, hX⟩
  intro σ
  let φ : VirtualConfig A ≃ VirtualConfig B := {
    toFun := fun η e => Fin.cast (congr_fun hDim e) (η e)
    invFun := fun η e => Fin.cast (Eq.symm (congr_fun hDim e)) (η e)
    left_inv := fun η => by
      funext e
      simp
    right_inv := fun η => by
      funext e
      simp
  }
  have hB : stateCoeff B σ = stateCoeff (applyGauge A X) σ := by
    unfold stateCoeff
    rw [← φ.sum_comp (fun η : VirtualConfig B =>
      ∏ v : V, B.component v (fun ie => η ie.1) (σ v))]
    dsimp [φ, applyGauge]
    refine Finset.sum_congr rfl ?_
    intro η hη
    refine Finset.prod_congr rfl ?_
    intro v hv
    simpa using (hX v (fun ie => η ie.1) (σ v))
  exact (applyGauge_stateCoeff A X σ).symm.trans hB.symm


end PEPS
end TNLean

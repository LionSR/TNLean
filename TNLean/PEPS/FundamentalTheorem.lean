import TNLean.PEPS.Blocking
import TNLean.PEPS.LocalGauge
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

-- This is a **scaffold** file: the forward direction and contraction algebra
-- are formalized, while the converse PEPS fundamental theorem remains as
-- `sorry` placeholders marking proof obligations for future PRs (see #128).
--
-- Provability note: `IsVertexInjective` in `PEPS.Defs` is the
-- linear-independence formulation `∀ v, LinearIndependent ℂ (A.component v)`
-- (see issue #633 for the switch away from function-level injectivity, which
-- is strictly weaker). Linear independence gives each vertex tensor a left
-- inverse on its image, removes the old definitional blocker, and is the
-- correct hypothesis for the repaired uniqueness endpoint
-- `gauge_unique_mod_edge_scalars`.
--
-- The remaining `sorry`s split into two groups:
-- * `gaugeConsistency` and the `hDim` step in `fundamentalTheorem_PEPS` still
--   require the full edge-centred reduction from arXiv:1804.04964 §3. The
--   local left inverse and the elementary blocking data now live in
--   `PEPS/VirtualInsertion` and `PEPS/Blocking`, and `localGauge_exists` has
--   been reduced to the sharper local hypothesis `HasLocalGaugeLift`. The new
--   wrapper `BlockedMiddleGaugeHyp` isolates the exact remaining bridge: build
--   the blocked middle tensor, compare it with the 3-site MPS theorem, and
--   derive that explicit local gauge formula from `SameState`.
-- * `gauge_unique_mod_edge_scalars` is the repaired endpoint, but its proof
--   still needs the same blocking infrastructure together with a local
--   tensor-factor uniqueness lemma for the balanced edge-scalar quotient.

/-!
# Fundamental Theorem for injective PEPS (scaffold)

This file scaffolds the Fundamental Theorem for injective PEPS on simple graphs
(arXiv:1804.04964, Theorem 2, Section 3):

> Two injective PEPS defined on a graph (no double edges/self-loops) generate
> the same state iff the generating tensors are related by local gauges on each
> edge, with uniqueness understood modulo balanced edge scalars on the graph.

## Strategy

The proof (from the paper) generalises the 1D MPS Fundamental Theorem
(`TNLean.MPS.FundamentalTheorem.Basic`) to arbitrary graph geometries:

1. At each vertex `v`, injectivity gives a left inverse for the local tensor map.
2. `SameState` plus contraction over all vertices except `v` yields a local
   gauge relation at `v`.
3. Consistency across adjacent vertices forces the gauges to be compatible,
   giving a global gauge equivalence.

This parallels the MPS proof's linear-extension → multiplicativity →
Skolem–Noether proof chain, but replaces chain algebra with graph-local reasoning.

## References

* [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Gauge matrices at oriented endpoints -/

/-- The gauge matrix to apply at vertex `v` for an incident edge `ie`.

For an edge `(u, w)` with `u < w` and gauge `X_e`:
* at endpoint `u`: apply `X_e`,
* at endpoint `w`: apply `(X_e⁻¹)ᵀ`.

This ensures that when contracting the virtual index along `e`, the gauge
matrices cancel: `∑_j X(i,j) · (X⁻¹)ᵀ(j,k) = δ(i,k)`. -/
noncomputable def edgeGaugeAt (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (v : V) (ie : IncidentEdge G v) :
    Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ :=
  if ie.1.1.1 = v then ↑(X ie.1)
  else (↑((X ie.1)⁻¹))ᵀ

/-! ### Gauge action on a vertex tensor -/

/-- Apply gauge matrices to a single vertex tensor. This sums over all original
virtual configurations, weighted by the product of gauge-matrix entries on each
incident edge:

`(gaugeVertex X A v)(η, σ) = ∑_{η'} (∏_{ie} M_{ie}(η(ie), η'(ie))) · A_v(η', σ)`

where `M_{ie}` is `X_e` or `(X_e⁻¹)ᵀ` depending on orientation. -/
noncomputable def gaugeVertex (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
    (σ : Fin d) : ℂ :=
  ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
    (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie)) *
      A.component v η' σ

/-- The PEPS tensor obtained by applying edge-gauge matrices to `A`. -/
noncomputable def applyGauge (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) : Tensor G d where
  bondDim := A.bondDim
  component v := gaugeVertex A X v

/-! ### Gauge equivalence -/

/-- Two PEPS tensors are gauge-equivalent if they have the same bond dimensions
and `B` is obtained from `A` by applying invertible gauge matrices on each edge.

This is the PEPS generalisation of `MPSTensor.GaugeEquiv`: instead of a single
global `X ∈ GL(D, ℂ)`, we have one `X_e ∈ GL(D_e, ℂ)` per edge. -/
def GaugeEquiv (A B : Tensor G d) : Prop :=
  ∃ (hDim : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
    ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A X v η σ

/-! ### Gauge invariance of PEPS state -/

/-- Incidences of vertices with edges are the same as choosing an edge and one
of its two ordered endpoints. -/
private noncomputable def incidentSigmaEquivEdgeSide :
    (Sigma fun v : V => IncidentEdge G v) ≃ Edge G × Fin 2 where
  toFun x :=
    let e := x.2.1
    ⟨e, if e.1.1 = x.1 then 0 else 1⟩
  invFun y :=
    match y.2 with
    | 0 => ⟨y.1.1.1, edgeLeftIncident (G := G) y.1⟩
    | 1 => ⟨y.1.1.2, edgeRightIncident (G := G) y.1⟩
  left_inv x := by
    rcases x with ⟨v, ie⟩
    rcases ie with ⟨e, hinc⟩
    dsimp
    by_cases hleft : e.1.1 = v
    · subst v
      simp only [↓reduceIte, Fin.isValue, Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext rfl
    · have hright : e.1.2 = v := by
        rcases hinc with h | h
        · exact False.elim (hleft h)
        · exact h
      subst v
      have hne : ¬e.1.1 = e.1.2 := ne_of_lt e.2.1
      simp only [hne, ↓reduceIte, Fin.isValue, Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext rfl
  right_inv y := by
    rcases y with ⟨e, side⟩
    fin_cases side
    · dsimp [edgeLeftIncident]
      simp
    · have hne : ¬e.1.1 = e.1.2 := ne_of_lt e.2.1
      dsimp [edgeRightIncident]
      simp [hne]

/-- A vertex-wise assignment of virtual indices before imposing edge
compatibility. -/
private abbrev LocalConfig (A : Tensor G d) : Type _ :=
  (v : V) → (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)

private lemma gauge_sum_left_right {n : Type*} [Fintype n] [DecidableEq n]
    (X : GL n ℂ) (a b : n) :
    (∑ j, (X : Matrix n n ℂ) j a * (↑X⁻¹ : Matrix n n ℂ) b j) =
      if a = b then 1 else 0 := by
  have h := congr_fun
    (congr_fun (show (↑X⁻¹ : Matrix n n ℂ) * (↑X : Matrix n n ℂ) = 1 by simp) b) a
  calc
    (∑ j, (X : Matrix n n ℂ) j a * (↑X⁻¹ : Matrix n n ℂ) b j)
        = ∑ j, (↑X⁻¹ : Matrix n n ℂ) b j * (X : Matrix n n ℂ) j a := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = ((↑X⁻¹ : Matrix n n ℂ) * (↑X : Matrix n n ℂ)) b a := by
          simp [Matrix.mul_apply]
    _ = if a = b then 1 else 0 := by
          rw [h]
          simp [Matrix.one_apply, eq_comm]

private lemma gauge_sum_left_right_matrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    (X : GL n ℂ) (a b : n) :
    (∑ j, (X : Matrix n n ℂ) j a * ((X : Matrix n n ℂ)⁻¹) b j) =
      if a = b then 1 else 0 := by
  simpa [Matrix.GeneralLinearGroup.coe_inv] using gauge_sum_left_right X a b

private lemma prod_incident_eq_prod_edge (f : (v : V) → IncidentEdge G v → ℂ) :
    (∏ v : V, ∏ ie : IncidentEdge G v, f v ie) =
      ∏ e : Edge G,
        f e.1.1 (edgeLeftIncident (G := G) e) *
          f e.1.2 (edgeRightIncident (G := G) e) := by
  rw [← Fintype.prod_sigma']
  calc
    (∏ x : Sigma fun v : V => IncidentEdge G v, f x.1 x.2)
        = ∏ y : Edge G × Fin 2,
            f ((incidentSigmaEquivEdgeSide (G := G)).symm y).1
              ((incidentSigmaEquivEdgeSide (G := G)).symm y).2 := by
          let e := incidentSigmaEquivEdgeSide (G := G)
          calc
            (∏ x : Sigma fun v : V => IncidentEdge G v, f x.1 x.2)
                = ∏ x : Sigma fun v : V => IncidentEdge G v,
                    f (e.symm (e x)).1 (e.symm (e x)).2 := by
                  refine Finset.prod_congr rfl ?_
                  intro x hx
                  rw [Equiv.symm_apply_apply]
            _ = ∏ y : Edge G × Fin 2, f (e.symm y).1 (e.symm y).2 := by
                  exact e.prod_comp
                    (fun y : Edge G × Fin 2 => f (e.symm y).1 (e.symm y).2)
    _ = ∏ e : Edge G, ∏ side : Fin 2,
            f ((incidentSigmaEquivEdgeSide (G := G)).symm (e, side)).1
              ((incidentSigmaEquivEdgeSide (G := G)).symm (e, side)).2 := by
          rw [Fintype.prod_prod_type]
    _ = ∏ e : Edge G,
        f e.1.1 (edgeLeftIncident (G := G) e) *
          f e.1.2 (edgeRightIncident (G := G) e) := by
          refine Finset.prod_congr rfl ?_
          intro e he
          rw [Fin.prod_univ_two]
          simp [incidentSigmaEquivEdgeSide]

private lemma gauge_sum_over_virtual (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (ξ : LocalConfig (G := G) A) :
    (∑ η : VirtualConfig A,
      ∏ v : V, ∏ ie : IncidentEdge G v,
        edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) =
      ∏ e : Edge G,
        if ξ e.1.1 (edgeLeftIncident (G := G) e) =
            ξ e.1.2 (edgeRightIncident (G := G) e) then 1 else 0 := by
  classical
  have hinc : ∀ η : VirtualConfig A,
      (∏ v : V, ∏ ie : IncidentEdge G v,
        edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) =
      ∏ e : Edge G,
        (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
            (η e) (ξ e.1.1 (edgeLeftIncident (G := G) e)) *
          ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
            (ξ e.1.2 (edgeRightIncident (G := G) e)) (η e) := by
    intro η
    rw [prod_incident_eq_prod_edge]
    refine Finset.prod_congr rfl ?_
    intro e he
    rw [← Matrix.GeneralLinearGroup.coe_inv (X e)]
    have hne : ¬e.1.1 = e.1.2 := ne_of_lt e.2.1
    simp only [edgeGaugeAt, edgeLeftIncident, edgeRightIncident, hne,
      ↓reduceIte, Matrix.transpose_apply]
    rfl
  simp_rw [hinc]
  rw [show
      (∑ x : VirtualConfig A,
        ∏ e : Edge G,
          (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
              (x e) (ξ e.1.1 (edgeLeftIncident (G := G) e)) *
            ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
              (ξ e.1.2 (edgeRightIncident (G := G) e)) (x e)) =
        ∏ e : Edge G,
          ∑ j : Fin (A.bondDim e),
            (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
                j (ξ e.1.1 (edgeLeftIncident (G := G) e)) *
              ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
                (ξ e.1.2 (edgeRightIncident (G := G) e)) j by
      simpa [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun e : Edge G => Finset.univ)
          (fun e j =>
            (X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
                j (ξ e.1.1 (edgeLeftIncident (G := G) e)) *
              ((X e : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)⁻¹)
                (ξ e.1.2 (edgeRightIncident (G := G) e)) j)).symm]
  simp only [gauge_sum_left_right_matrix_inv]
  rfl

/-- Project a global virtual configuration to a local (vertex-wise) one by
reading off the index assigned to each incident edge. -/
private def localConfigOfGlobal (A : Tensor G d) (η : VirtualConfig A) : LocalConfig (G := G) A :=
  fun _ ie => η ie.1

/-- A local configuration is *consistent* when the two endpoints of every edge
agree on the virtual index assigned to that edge. -/
private def IsConsistent (A : Tensor G d) (ξ : LocalConfig (G := G) A) : Prop :=
  ∀ e : Edge G,
    ξ e.1.1 (edgeLeftIncident (G := G) e) =
      ξ e.1.2 (edgeRightIncident (G := G) e)

/-- A global virtual configuration is the same data as a consistent local one:
the forward direction reads off per-vertex indices, and the inverse recovers
the global assignment from the lower-endpoint index of each edge. -/
private noncomputable def virtualConfigEquivConsistentLocal (A : Tensor G d) :
    VirtualConfig A ≃ {ξ : LocalConfig (G := G) A // IsConsistent A ξ} where
  toFun η := ⟨localConfigOfGlobal A η, by intro e; rfl⟩
  invFun ξ e := ξ.1 e.1.1 (edgeLeftIncident (G := G) e)
  left_inv η := by
    funext e
    rfl
  right_inv ξ := by
    rcases ξ with ⟨ξ, hξ⟩
    apply Subtype.ext
    funext v ie
    rcases ie with ⟨e, hinc⟩
    dsimp [localConfigOfGlobal]
    by_cases hleft : e.1.1 = v
    · subst v
      have hEq : (⟨e, hinc⟩ : IncidentEdge G e.1.1) =
          edgeLeftIncident (G := G) e :=
        Subtype.ext rfl
      cases hEq
      rfl
    · have hright : e.1.2 = v := by
        rcases hinc with h | h
        · exact False.elim (hleft h)
        · exact h
      subst v
      have hEq : (⟨e, hinc⟩ : IncidentEdge G e.1.2) =
          edgeRightIncident (G := G) e :=
        Subtype.ext rfl
      simpa [hEq] using hξ e

private lemma sum_local_with_edge_deltas (A : Tensor G d) (σ : V → Fin d) :
    (∑ ξ : LocalConfig (G := G) A,
      (∏ e : Edge G,
        if ξ e.1.1 (edgeLeftIncident (G := G) e) =
            ξ e.1.2 (edgeRightIncident (G := G) e) then (1 : ℂ) else 0) *
        ∏ v : V, A.component v (ξ v) (σ v)) =
      stateCoeff A σ := by
  classical
  let F : LocalConfig (G := G) A → ℂ :=
    fun ξ => ∏ v : V, A.component v (ξ v) (σ v)
  have hfilter :
      (∑ ξ : LocalConfig (G := G) A,
        (∏ e : Edge G,
          if ξ e.1.1 (edgeLeftIncident (G := G) e) =
              ξ e.1.2 (edgeRightIncident (G := G) e) then (1 : ℂ) else 0) * F ξ) =
        ∑ ξ : {ξ : LocalConfig (G := G) A // IsConsistent A ξ}, F ξ.1 := by
    calc
      (∑ ξ : LocalConfig (G := G) A,
        (∏ e : Edge G,
          if ξ e.1.1 (edgeLeftIncident (G := G) e) =
              ξ e.1.2 (edgeRightIncident (G := G) e) then (1 : ℂ) else 0) * F ξ)
          = ∑ ξ : LocalConfig (G := G) A, if IsConsistent A ξ then F ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ hξ
            have hprod :
                (∏ e : Edge G,
                  if ξ e.1.1 (edgeLeftIncident (G := G) e) =
                      ξ e.1.2 (edgeRightIncident (G := G) e) then (1 : ℂ) else 0) =
                  if IsConsistent A ξ then 1 else 0 := by
              simpa [IsConsistent] using
                (Fintype.prod_boole
                  (p := fun e : Edge G =>
                    ξ e.1.1 (edgeLeftIncident (G := G) e) =
                      ξ e.1.2 (edgeRightIncident (G := G) e)) :
                  (∏ e : Edge G,
                    ite
                      (ξ e.1.1 (edgeLeftIncident (G := G) e) =
                        ξ e.1.2 (edgeRightIncident (G := G) e))
                      (1 : ℂ) 0) =
                    ite
                      (∀ e : Edge G,
                        ξ e.1.1 (edgeLeftIncident (G := G) e) =
                          ξ e.1.2 (edgeRightIncident (G := G) e))
                      (1 : ℂ) 0)
            rw [hprod]
            by_cases h : IsConsistent A ξ <;> simp [h]
      _ = ∑ ξ : {ξ : LocalConfig (G := G) A // IsConsistent A ξ}, F ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (LocalConfig (G := G) A)))
              (f := F) (p := IsConsistent A)]
            simp
  rw [hfilter, stateCoeff]
  symm
  calc
    (∑ η : VirtualConfig A, ∏ v : V, A.component v (fun ie => η ie.1) (σ v))
        = ∑ ξ : {ξ : LocalConfig (G := G) A // IsConsistent A ξ}, F ξ.1 := by
          let e := virtualConfigEquivConsistentLocal (G := G) A
          calc
            (∑ η : VirtualConfig A, ∏ v : V, A.component v (fun ie => η ie.1) (σ v))
                = ∑ η : VirtualConfig A, F ((e η).1) := by
                  rfl
            _ = ∑ ξ : {ξ : LocalConfig (G := G) A // IsConsistent A ξ}, F ξ.1 := by
                  exact e.sum_comp
                    (fun ξ : {ξ : LocalConfig (G := G) A // IsConsistent A ξ} => F ξ.1)

private lemma prod_gaugeVertex_eq_sum_local (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (η : VirtualConfig A) (σ : V → Fin d) :
    (∏ v : V, gaugeVertex A X v (fun ie => η ie.1) (σ v)) =
      ∑ ξ : LocalConfig (G := G) A,
        ∏ v : V,
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
            A.component v (ξ v) (σ v) := by
  classical
  simp_rw [gaugeVertex]
  rw [show
      (∏ v : V,
        ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie.1) (η' ie)) *
            A.component v η' (σ v)) =
        ∑ ξ : LocalConfig (G := G) A,
          ∏ v : V,
            (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
              A.component v (ξ v) (σ v) by
    simpa [Fintype.piFinset_univ, LocalConfig] using
      (Finset.prod_univ_sum (fun v : V => Finset.univ)
        (fun v η' =>
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie.1) (η' ie)) *
            A.component v η' (σ v)))]

/-- Applying a gauge to a PEPS tensor preserves the state coefficients.

The proof relies on the fact that for each edge, the gauge matrix and its
inverse-transpose cancel upon contraction of the shared virtual index:
`∑_j X(i,j) · (X⁻¹)ᵀ(j,k) = δ(i,k)`. -/
theorem applyGauge_stateCoeff (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (σ : V → Fin d) :
    stateCoeff (applyGauge A X) σ = stateCoeff A σ := by
  classical
  unfold stateCoeff applyGauge
  dsimp
  simp_rw [prod_gaugeVertex_eq_sum_local]
  rw [Finset.sum_comm]
  trans ∑ ξ : LocalConfig (G := G) A,
      (∑ η : VirtualConfig A,
        ∏ v : V, ∏ ie : IncidentEdge G v,
          edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
        ∏ v : V, A.component v (ξ v) (σ v)
  · refine Finset.sum_congr rfl ?_
    intro ξ hξ
    calc
      (∑ η : VirtualConfig A,
        ∏ v : V,
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
            A.component v (ξ v) (σ v))
          = ∑ η : VirtualConfig A,
              (∏ v : V, ∏ ie : IncidentEdge G v,
                edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
                ∏ v : V, A.component v (ξ v) (σ v) := by
            refine Finset.sum_congr rfl ?_
            intro η hη
            rw [Finset.prod_mul_distrib]
      _ = (∑ η : VirtualConfig A,
            ∏ v : V, ∏ ie : IncidentEdge G v,
              edgeGaugeAt A X v ie (η ie.1) (ξ v ie)) *
            ∏ v : V, A.component v (ξ v) (σ v) := by
            rw [Finset.sum_mul]
  · simp_rw [gauge_sum_over_virtual]
    exact sum_local_with_edge_deltas A σ

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

/-! ### Local gauge extraction -/

/-- The local tensor evaluated at vertex `v` with virtual-index weighting `f`.

This computes `∑_η (∏_{ie} f(ie)(η(ie))) · A_v(η, σ)`. The map is
*multilinear* in the components of `f` (one factor per incident edge), not
linear in the full tuple — hence this is a plain function, not a `LinearMap`. -/
noncomputable def localTensorEval (A : Tensor G d) (v : V)
    (f : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1) → ℂ)
    (σ : Fin d) : ℂ :=
  ∑ η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
    (∏ ie : IncidentEdge G v, f ie (η ie)) * A.component v η σ

/-- Under the sharper local hypothesis `HasLocalGaugeLift`, one obtains a
factorized local gauge relation at `v`.

The local left inverse and the canonical candidate operator now live in
`PEPS/LocalGauge`. The remaining PEPS-Fundamental-Theorem gap is to prove
`BlockedMiddleGaugeHyp` from `SameState` via the blocked-middle / three-site-MPS
reduction, then convert it to `HasLocalGaugeLift` by
`HasLocalGaugeLift_of_blockedMiddleGaugeHyp`. -/
theorem localGauge_exists (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (hLift : HasLocalGaugeLift A B hA hDim v) :
    ∃ (Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v,
              (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ :=
  localGauge_exists_of_liftData A B hA hDim v hLift

/-! ### Gauge consistency across edges -/

/-- Local gauges extracted at adjacent vertices are consistent: for an edge
`e = (u, v)`, the gauge at `u`'s side of `e` and the gauge at `v`'s side of
`e` satisfy `X_u(e) = (X_v(e)⁻¹)ᵀ` (up to the orientation convention).

This is the combinatorial heart of the PEPS FT proof. In the MPS case,
consistency is automatic because there is only one gauge matrix. For PEPS on a
graph, one must verify that the local gauges "match up" along every edge. -/
theorem gaugeConsistency (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim) :
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          gaugeVertex A X v η σ := by
  -- TODO: first derive `BlockedMiddleGaugeHyp A B hA hDim v` from `SameState`
  -- at each vertex via the blocked-middle / three-site-MPS reduction, then use
  -- `HasLocalGaugeLift_of_blockedMiddleGaugeHyp` to obtain the local gauges.
  -- The key remaining consistency step is: for each edge e = (u,v), the gauges
  -- extracted from u and v must agree as inverse-transposes, with the
  -- orientation convention in `edgeGaugeAt`.
  sorry

/-! ### Main theorem -/

/-- **Fundamental Theorem for injective PEPS** (arXiv:1804.04964, Theorem 2).

If two PEPS tensors on a simple graph are both vertex-injective and generate
the same state, then they are gauge-equivalent: there exist invertible matrices
`X_e` on each edge such that `B` is the gauge transform of `A`.

The proof proceeds in two stages:
1. **Local extraction** (`localGauge_exists`): after proving the sharper local
   hypothesis `HasLocalGaugeLift`, injectivity and the chosen left inverse
   produce a factorized local gauge relation.
2. **Global consistency** (`gaugeConsistency`): local gauges along shared
   edges are shown to be compatible, yielding a single coherent family of
   edge gauges.

In the MPS (1D chain) case, this reduces to `fundamentalTheorem_singleBlock`. -/
theorem fundamentalTheorem_PEPS (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B) :
    GaugeEquiv A B := by
  -- Step 1: Show bond dimensions must agree.
  -- TODO: derive hDim from injectivity + SameState.
  -- Missing lemma: `SameState` captures only the fully-contracted scalar,
  -- whereas the PEPS FT derivation of bond-dimension equality uses the full
  -- family of boundary insertions.  Linear independence at each vertex
  -- (`IsVertexInjective`) gives the right local data, but the global argument
  -- that different bond dimensions cannot yield the same state family still
  -- requires a boundary-insertion / blocking lemma.
  have hDim : A.bondDim = B.bondDim := by
    sorry
  -- Step 2: Extract globally consistent gauges.
  rcases gaugeConsistency A B hA hB hAB hDim with ⟨X, hX⟩
  exact ⟨hDim, X, hX⟩

/-! ### Balanced edge scalars -/

/-- The scalar contributed by an edge-scalar family at a chosen endpoint.

For an edge `(u, w)` with `u < w` and scalar `c_e`, the lower endpoint carries
`c_e` and the upper endpoint carries `c_e⁻¹`, mirroring `edgeGaugeAt`. -/
def edgeScalarAt (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) : ℂ :=
  if ie.1.1.1 = v then (c ie.1 : ℂ) else ↑((c ie.1)⁻¹)

/-- A scalar edge family is vertex-balanced if the oriented product of its
endpoint scalars is `1` at every vertex. -/
def IsVertexBalanced (c : (e : Edge G) → Units ℂ) : Prop :=
  ∀ v : V, ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie = 1

/-- Two PEPS gauge families are equivalent modulo balanced edge scalars if,
after inserting the corresponding endpoint scalars, they induce the same
oriented edge action on every incident half-edge. -/
def GaugeEquivModEdgeScalars (A : Tensor G d)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) : Prop :=
  ∃ c : (e : Edge G) → Units ℂ,
    IsVertexBalanced (G := G) c ∧
      ∀ (v : V) (ie : IncidentEdge G v),
        edgeGaugeAt A X v ie =
          edgeScalarAt (G := G) c v ie • edgeGaugeAt A Y v ie

/-- Balanced edge-scalar reweightings do not change the gauged tensor at a
vertex. -/
theorem GaugeEquivModEdgeScalars.gaugeVertex_eq
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
    (σ : Fin d) :
    gaugeVertex A X v η σ = gaugeVertex A Y v η σ := by
  rcases hXY with ⟨c, hc, hedge⟩
  unfold gaugeVertex
  refine Finset.sum_congr rfl ?_
  intro η' _
  have hprod :
      ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie) =
        ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
    calc
      ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie) =
          ∏ ie : IncidentEdge G v,
            edgeScalarAt (G := G) c v ie *
              edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            refine Finset.prod_congr rfl ?_
            intro ie _
            have hEntry := congrArg (fun M => M (η ie) (η' ie)) (hedge v ie)
            simpa [Matrix.smul_apply, smul_eq_mul] using hEntry
      _ = (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie) *
            ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
            rw [hc v, one_mul]
  rw [hprod]

/-! ### Uniqueness modulo balanced edge scalars -/

/-- **Gauge uniqueness modulo balanced edge scalars** (arXiv:1804.04964,
Theorem 2, uniqueness clause, repaired form).

If `X` and `Y` are two gauge families relating the same pair of injective PEPS,
then they represent the same gauge class modulo edge-wise nonzero
scalars whose oriented product is `1` at every vertex. This replaces the
earlier global-scalar conclusion, which is refuted by the connected-triangle,
bond-dimension-`1` counterexample discussed in issue #762. -/
theorem gauge_unique_mod_edge_scalars (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A X v η σ)
    (hY : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A Y v η σ) :
    GaugeEquivModEdgeScalars (G := G) A X Y := by
  -- TODO: compare `hX` and `hY` vertexwise and use linear independence of
  -- `A.component v` to extract scalar ratios on each incident edge.
  -- The remaining missing ingredient is the tensor-factor uniqueness lemma:
  -- if two products of oriented edge gauges act identically on an injective
  -- vertex tensor, then the factors differ by nonzero scalars whose product
  -- is `1` at that vertex. Assembling these local scalar relations into a
  -- single edge family gives the desired balanced quotient relation.
  -- This is the repaired uniqueness endpoint for PEPS gauges; the former
  -- global-scalar statement was false on the triangle counterexample.
  sorry

end PEPS
end TNLean

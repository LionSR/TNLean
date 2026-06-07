import TNLean.PEPS.Blocking
import TNLean.PEPS.InsertionAlgebra
import TNLean.PEPS.EdgeGaugeFamily
import TNLean.PEPS.LocalGauge
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

-- The contraction algebra is proved. The remaining converse ingredients are
-- separated by mathematical role in
-- `docs/paper-gaps/peps_injective_ft_section3_route.tex` and
-- `docs/paper-gaps/peps_gauge_edge_scalars.tex`. The hypothesis
-- `IsVertexInjective` is the linear-independence formulation from `PEPS.Defs`,
-- which gives the local left inverses used below.

/-!
# Fundamental Theorem for injective PEPS

**Root-only.** This module is currently not imported downstream — it
records the full statement of the PEPS Fundamental Theorem
(arXiv:1804.04964 §3, Theorem 2), with the forward bond-dimension
obligation and converse gaps documented in the paper-gap notes cited below.
The separate root-only audit is tracked by issue #1512.

This file develops the Fundamental Theorem for injective PEPS on simple graphs
(arXiv:1804.04964, Theorem 2, Section 3):

> Two injective PEPS defined on a graph (no double edges/self-loops) generate
> the same state iff the generating tensors are related by local gauges on each
> edge, with uniqueness understood modulo balanced edge scalars on the graph.

## Source proof shape

For a chosen edge \(e=(u,v)\), the source proof blocks all vertices other than
\(u\) and \(v\) into a middle tensor. The two endpoint tensors and this middle
tensor form a three-site injective MPS, so the three-site isomorphism lemma of
arXiv:1804.04964, Section 3, assigns an edge gauge. After repeating this for
every edge and absorbing the gauges into the second tensor family, the proof
obtains the edge-insertion equality of arXiv:1804.04964, Section 3: for every
edge and every matrix \(X\), inserting \(X\) on that edge in the first PEPS
gives the same state as inserting \(X\) on the same edge in the modified second
PEPS. Blocking one vertex against its complement and applying the two-injective
tensor comparison of arXiv:1804.04964, Section 3, gives
\(A_v = \lambda_v \cdot \tilde{B}_v\); the scalars \(\lambda_v\) are absorbed
into the edge gauges.

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

/-- The tensor family obtained by absorbing an oriented edge-gauge family into
the second PEPS tensor.

Source: arXiv:1804.04964, Section 3, lines 1037--1038, where the tensors
$\widetilde B_i$ are defined by absorbing into $B_i$ the edge gauges obtained
from the injective-chain isomorphism lemma; the translationally invariant
version is repeated in lines 1500--1519. This definition records only the
absorption construction. The post-absorption insertion equality labelled
eq:inj_equal_edge in the paper is a separate statement. -/
noncomputable def absorbEdgeGauges (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) : Tensor G d :=
  applyGauge B X

/-- Absorbing edge gauges does not change the bond spaces.

Source: arXiv:1804.04964, Section 3, lines 1037--1038. -/
@[simp] theorem absorbEdgeGauges_bondDim (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) :
    (absorbEdgeGauges B X).bondDim = B.bondDim := rfl

/-- The local component formula for absorbing oriented edge gauges.

Source: arXiv:1804.04964, Section 3, lines 1037--1038, and lines 1500--1519
for the normal translationally invariant absorption picture. -/
theorem absorbEdgeGauges_component (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (v : V) (η : (ie : IncidentEdge G v) → Fin (B.bondDim ie.1)) (σ : Fin d) :
    (absorbEdgeGauges B X).component v η σ = gaugeVertex B X v η σ := rfl

/-- Edge-gauge absorption produces a modified tensor family $\widetilde B$ whose local
components are obtained from $B$ by the oriented endpoint gauge action.

Source: arXiv:1804.04964, Section 3, lines 1037--1038: after applying
the injective-chain isomorphism lemma around every edge, the resulting edge
gauges are absorbed into the tensors $B_i$ to form $\widetilde B_i$. This
result constructs $\widetilde B$; it does not assert the later
equality labelled eq:inj_equal_edge in the paper. -/
theorem edge_gauge_absorption (B : Tensor G d)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ) :
    (absorbEdgeGauges B X).bondDim = B.bondDim ∧
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (B.bondDim ie.1)) (σ : Fin d),
        (absorbEdgeGauges B X).component v η σ = gaugeVertex B X v η σ := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

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

/-- Contracting a matrix with its inverse over the shared virtual index gives the
Kronecker delta on the remaining indices. -/
lemma gauge_sum_left_right_matrix_inv {n : Type*} [Fintype n] [DecidableEq n]
    (X : GL n ℂ) (a b : n) :
    (∑ j, (X : Matrix n n ℂ) j a * ((X : Matrix n n ℂ)⁻¹) b j) =
      if a = b then 1 else 0 := by
  simpa [Matrix.GeneralLinearGroup.coe_inv] using gauge_sum_left_right X a b

/-- A product over all incident half-edges factors as the product, over graph
edges, of the two endpoint contributions. -/
lemma prod_incident_eq_prod_edge (f : (v : V) → IncidentEdge G v → ℂ) :
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
    simpa only [Fintype.piFinset_univ, LocalConfig] using
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

/-! ### Open-edge gauge action

The closed-network result `applyGauge_stateCoeff` shows that internal gauges
cancel pairwise on every edge. With one edge left open and a matrix inserted on
it, the same cancellation holds on all other edges, while the two endpoint
gauges on the open edge survive and conjugate the inserted matrix. This realizes
the open-edge analog of the closed contraction, used in the post-absorption
edge-insertion identity (arXiv:1804.04964, Section 3, `eq:inj_equal_edge`). -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- An incident edge other than the distinguished left incidence is not the
distinguished edge. -/
private theorem otherLeft_edge_ne' (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.1 (edgeLeftIncident (G := G) e)) :
    ie.1.1 ≠ e := fun hie => ie.2 (Subtype.ext hie)

omit [Fintype V] [DecidableRel G.Adj] in
/-- An incident edge other than the distinguished right incidence is not the
distinguished edge. -/
private theorem otherRight_edge_ne' (e : Edge G)
    (ie : OtherIncidentEdge (G := G) e.1.2 (edgeRightIncident (G := G) e)) :
    ie.1.1 ≠ e := fun hie => ie.2 (Subtype.ext hie)

/-- Inserted-edge boundary data together with a compatible open-middle
configuration are the same finite data as the two distinguished edge indices and
a free virtual configuration on every other edge.

The two distinguished indices are the open left and right bond indices; the
complement configuration supplies all remaining edges, and the endpoint residual
families are read off it. This is the open-edge analog of
`virtualConfigEquivEdgeBoundary`. -/
noncomputable def insertedOpenConfigEquiv (A : Tensor G d) (e : Edge G) :
    (Σ β : EdgeInsertedBoundaryConfig (G := G) A e,
      EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual) ≃
      (Fin (A.bondDim e) × Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e) where
  toFun x := (x.1.leftEdgeIndex, x.1.rightEdgeIndex, x.2.1)
  invFun y :=
    ⟨{ leftEdgeIndex := y.1
       rightEdgeIndex := y.2.1
       leftResidual := fun ie => y.2.2 ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩
       rightResidual := fun ie => y.2.2 ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ },
      ⟨y.2.2, by constructor <;> intro ie <;> rfl⟩⟩
  left_inv x := by
    rcases x with ⟨β, ζ⟩
    rcases ζ with ⟨ζ, hζ⟩
    obtain ⟨hL, hR⟩ := hζ
    refine Sigma.subtype_ext ?_ ?_
    · rcases β with ⟨li, ri, lr, rr⟩
      dsimp
      congr 1
      · funext ie; exact hL ie
      · funext ie; exact hR ie
    · dsimp
  right_inv _ := rfl

/-- Global open form of the inserted-edge coefficient: a sum over the two open
edge indices, the inserted-matrix weight, and a free complement configuration on
all other edges, with the two endpoint tensors and the open middle tensor
contracted against the complement data. -/
theorem edgeInsertedCoeff_eq_sum_complement (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ N =
      ∑ x : Fin (A.bondDim e) × Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e,
          N x.1 x.2.1 *
          A.component e.1.1
            (edgeInsertedLeftLocalConfig (G := G) A e
              { leftEdgeIndex := x.1, rightEdgeIndex := x.2.1,
                leftResidual := fun ie => x.2.2 ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩,
                rightResidual := fun ie => x.2.2 ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ })
            (σ e.1.1) *
          (∏ v : {v : V // v ∈ edgeMiddleVertices e},
            A.component v.1 (fun ie => edgeComplementValue (G := G) A e x.2.2 v.2 ie) (σ v.1)) *
          A.component e.1.2
            (edgeInsertedRightLocalConfig (G := G) A e
              { leftEdgeIndex := x.1, rightEdgeIndex := x.2.1,
                leftResidual := fun ie => x.2.2 ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩,
                rightResidual := fun ie => x.2.2 ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ })
            (σ e.1.2) := by
  classical
  rw [edgeInsertedCoeff]
  set F : (Σ β : EdgeInsertedBoundaryConfig (G := G) A e,
      EdgeOpenMiddleConfig (G := G) A e β.leftResidual β.rightResidual) → ℂ := fun p =>
    N p.1.leftEdgeIndex p.1.rightEdgeIndex *
      A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e p.1) (σ e.1.1) *
      (∏ v : {v : V // v ∈ edgeMiddleVertices e},
        A.component v.1 (fun ie => edgeComplementValue (G := G) A e p.2.1 v.2 ie) (σ v.1)) *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e p.1) (σ e.1.2)
    with hF
  have hstep :
      (∑ β : EdgeInsertedBoundaryConfig (G := G) A e,
        A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
          N β.leftEdgeIndex β.rightEdgeIndex *
          edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
          A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)) =
      ∑ p, F p := by
    have hsig : (∑ p, F p) = ∑ β, ∑ ζ, F ⟨β, ζ⟩ :=
      Fintype.sum_sigma' (fun β ζ => F ⟨β, ζ⟩)
    rw [hsig]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [edgeOpenMiddleWeight]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro ζ _
    simp only [hF]
    ring
  rw [hstep]
  refine Fintype.sum_equiv (insertedOpenConfigEquiv (G := G) A e) F _ ?_
  intro p
  rcases p with ⟨β, ζ⟩
  rcases β with ⟨li, ri, lr, rr⟩
  rcases ζ with ⟨ζ, hζ⟩
  obtain ⟨hL, hR⟩ := hζ
  have hlr : lr = fun ie => ζ ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩ :=
    funext fun ie => (hL ie).symm
  have hrr : rr = fun ie => ζ ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ :=
    funext fun ie => (hR ie).symm
  subst hlr hrr
  rfl

/-- A vertex-indexed assignment of virtual indices to each incident edge, before
imposing any edge compatibility. This is the per-vertex local data summed over in
the gauged contraction; on the open edge the two endpoints may carry different
indices. -/
abbrev OpenLocalConfig (A : Tensor G d) : Type _ :=
  (v : V) → (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)

omit [DecidableRel G.Adj] in
/-- A local configuration is *consistent off `e`* when the two endpoints of every
edge other than `e` agree on its virtual index. -/
def IsConsistentOff (A : Tensor G d) (e : Edge G)
    (ξ : OpenLocalConfig (G := G) A) : Prop :=
  ∀ f : Edge G, f ≠ e →
    ξ f.1.1 (edgeLeftIncident (G := G) f) = ξ f.1.2 (edgeRightIncident (G := G) f)

omit [Fintype V] in
/-- On any edge other than `e`, a configuration consistent off `e` reads the same
index at each of its endpoints. -/
private theorem localConfig_value_eq_left (A : Tensor G d) (e : Edge G)
    (ξ : OpenLocalConfig (G := G) A) (hξ : IsConsistentOff (G := G) A e ξ)
    {v : V} (ie : IncidentEdge G v) (hne : ie.1 ≠ e) :
    ξ v ie = ξ ie.1.1.1 (edgeLeftIncident (G := G) ie.1) := by
  obtain ⟨f, hf⟩ := ie
  rcases hf with hL | hR
  · subst hL; rfl
  · subst hR; exact (hξ f hne).symm

/-- Rebuild a local configuration from the two open edge indices and a free
configuration on every other edge. -/
noncomputable def localOfDoubled (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    OpenLocalConfig (G := G) A :=
  fun v ie =>
    if h : ie.1 = e then
      if v = e.1.1 then Fin.cast (by rw [h]) i else Fin.cast (by rw [h]) k
    else ζ ⟨ie.1, h⟩

omit [Fintype V] in
/-- The rebuilt configuration reads the left open index at the left incidence of
`e`. -/
theorem localOfDoubled_left_e (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζ e.1.1 (edgeLeftIncident (G := G) e) = i := by
  unfold localOfDoubled edgeLeftIncident; simp

omit [Fintype V] in
/-- The rebuilt configuration reads the right open index at the right incidence of
`e`. -/
theorem localOfDoubled_right_e (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζ e.1.2 (edgeRightIncident (G := G) e) = k := by
  unfold localOfDoubled edgeRightIncident
  have hvne : ¬ e.1.2 = e.1.1 := (edgeLeft_ne_edgeRight e).symm
  simp [hvne]

omit [Fintype V] in
/-- On any edge other than `e`, the rebuilt configuration reads the complement
index at the left incidence. -/
theorem localOfDoubled_left_ne (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
    (g : {g : Edge G // g ≠ e}) :
    localOfDoubled (G := G) A e i k ζ g.1.1.1 (edgeLeftIncident (G := G) g.1) = ζ g := by
  unfold localOfDoubled
  simp only [edgeLeftIncident, dif_neg g.2]

omit [Fintype V] in
/-- On any edge other than `e`, the rebuilt configuration reads the complement
index at the right incidence. -/
theorem localOfDoubled_right_ne (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
    (g : {g : Edge G // g ≠ e}) :
    localOfDoubled (G := G) A e i k ζ g.1.1.2 (edgeRightIncident (G := G) g.1) = ζ g := by
  unfold localOfDoubled
  simp only [edgeRightIncident, dif_neg g.2]

/-- Local configurations consistent off `e` are the same finite data as the two
open edge indices together with a free configuration on every other edge. -/
noncomputable def consistentOffEquivDoubled (A : Tensor G d) (e : Edge G) :
    {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ} ≃
      (Fin (A.bondDim e) × Fin (A.bondDim e) × EdgeComplementConfig (G := G) A e) where
  toFun ξ := (ξ.1 e.1.1 (edgeLeftIncident (G := G) e),
              ξ.1 e.1.2 (edgeRightIncident (G := G) e),
              fun f => ξ.1 f.1.1.1 (edgeLeftIncident (G := G) f.1))
  invFun y := ⟨localOfDoubled (G := G) A e y.1 y.2.1 y.2.2, by
    intro f hf
    unfold localOfDoubled
    simp only [edgeLeftIncident, edgeRightIncident, dif_neg hf]⟩
  left_inv ξ := by
    rcases ξ with ⟨ξ, hξ⟩
    apply Subtype.ext
    funext v ie
    change localOfDoubled (G := G) A e _ _ _ v ie = ξ v ie
    unfold localOfDoubled
    by_cases hie : ie.1 = e
    · rw [dif_pos hie]
      obtain ⟨f, hf⟩ := ie
      simp only at hie ⊢
      subst hie
      rcases hf with hL | hR
      · subst hL
        rw [if_pos rfl]
        simp [edgeLeftIncident]
      · subst hR
        have hvne : ¬ f.1.2 = f.1.1 := (edgeLeft_ne_edgeRight f).symm
        rw [if_neg hvne]
        simp [edgeRightIncident]
    · rw [dif_neg hie]
      exact (localConfig_value_eq_left (G := G) A e ξ hξ ie hie).symm
  right_inv y := by
    rcases y with ⟨i, k, ζ⟩
    have hvne : ¬ e.1.2 = e.1.1 := (edgeLeft_ne_edgeRight e).symm
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change localOfDoubled (G := G) A e i k ζ e.1.1 (edgeLeftIncident (G := G) e) = i
      unfold localOfDoubled edgeLeftIncident; simp
    · change localOfDoubled (G := G) A e i k ζ e.1.2 (edgeRightIncident (G := G) e) = k
      unfold localOfDoubled edgeRightIncident; simp [hvne]
    · funext f
      change localOfDoubled (G := G) A e i k ζ f.1.1.1 (edgeLeftIncident (G := G) f.1) = ζ f
      have hf : f.1 ≠ e := f.2
      unfold localOfDoubled
      simp only [edgeLeftIncident, dif_neg hf]

/-- The per-edge consistency deltas off `e` collapse to the consistency-off-`e`
predicate. -/
theorem prod_off_delta_eq (A : Tensor G d) (e : Edge G)
    (ξ : OpenLocalConfig (G := G) A) [Decidable (IsConsistentOff (G := G) A e ξ)] :
    (∏ f : {f : Edge G // f ≠ e},
      if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
          ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) =
      if IsConsistentOff (G := G) A e ξ then 1 else 0 := by
  classical
  have hpred : (∀ f : {f : Edge G // f ≠ e},
      ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
        ξ f.1.1.2 (edgeRightIncident (G := G) f.1)) ↔ IsConsistentOff (G := G) A e ξ := by
    constructor
    · intro h f hf; exact h ⟨f, hf⟩
    · intro h f; exact h f.1 f.2
  rw [Fintype.prod_boole]
  exact if_congr hpred rfl rfl

omit [Fintype V] in
/-- The left endpoint local configuration of a complement-built boundary datum is
the rebuilt local configuration at the left endpoint. -/
private theorem edgeInsertedLeftLocalConfig_eq_localOfDoubled (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    edgeInsertedLeftLocalConfig (G := G) A e
      { leftEdgeIndex := i, rightEdgeIndex := k,
        leftResidual := fun ie => ζ ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩,
        rightResidual := fun ie => ζ ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ } =
      localOfDoubled (G := G) A e i k ζ e.1.1 := by
  funext ie
  by_cases hie : ie = edgeLeftIncident (G := G) e
  · subst hie
    rw [edgeInsertedLeftLocalConfig_edgeIndex]
    unfold localOfDoubled edgeLeftIncident
    simp
  · have hne : ie.1 ≠ e := fun h => hie (Subtype.ext h)
    rw [edgeInsertedLeftLocalConfig_residual (G := G) A e _ ⟨ie, hie⟩]
    unfold localOfDoubled
    simp [hne]

omit [Fintype V] in
/-- The right endpoint local configuration of a complement-built boundary datum is
the rebuilt local configuration at the right endpoint. -/
private theorem edgeInsertedRightLocalConfig_eq_localOfDoubled (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    edgeInsertedRightLocalConfig (G := G) A e
      { leftEdgeIndex := i, rightEdgeIndex := k,
        leftResidual := fun ie => ζ ⟨ie.1.1, otherLeft_edge_ne' (G := G) e ie⟩,
        rightResidual := fun ie => ζ ⟨ie.1.1, otherRight_edge_ne' (G := G) e ie⟩ } =
      localOfDoubled (G := G) A e i k ζ e.1.2 := by
  funext ie
  by_cases hie : ie = edgeRightIncident (G := G) e
  · subst hie
    rw [edgeInsertedRightLocalConfig_edgeIndex]
    unfold localOfDoubled edgeRightIncident
    have hvne : ¬ e.1.2 = e.1.1 := (edgeLeft_ne_edgeRight e).symm
    simp [hvne]
  · have hne : ie.1 ≠ e := fun h => hie (Subtype.ext h)
    rw [edgeInsertedRightLocalConfig_residual (G := G) A e _ ⟨ie, hie⟩]
    unfold localOfDoubled
    simp [hne]

/-- The middle complement value of a configuration agrees with the rebuilt local
configuration at any middle vertex. -/
private theorem edgeComplementValue_eq_localOfDoubled (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
    (v : {v : V // v ∈ edgeMiddleVertices e}) (ie : IncidentEdge G v.1) :
    edgeComplementValue (G := G) A e ζ v.2 ie = localOfDoubled (G := G) A e i k ζ v.1 ie := by
  unfold edgeComplementValue localOfDoubled
  have hvne : v.1 ≠ e.1.1 ∧ v.1 ≠ e.1.2 := (mem_edgeMiddleVertices_iff e v.1).mp v.2
  have hie_ne : ie.1 ≠ e := by
    intro h
    rcases ie.2 with hl | hr
    · exact hvne.1 (hl.symm.trans (congrArg (fun f : Edge G => f.1.1) h))
    · exact hvne.2 (hr.symm.trans (congrArg (fun f : Edge G => f.1.2) h))
  rw [dif_neg hie_ne]

/-- Local-configuration form of the inserted-edge coefficient: a sum over all
local configurations, with consistency deltas forcing agreement on every edge
other than `e`, the inserted-matrix weight on the two open indices of `e`, and the
per-vertex tensors contracted along the configuration.

This is the open-edge analog of `sum_local_with_edge_deltas`; the delta on every
edge other than `e` filters to configurations consistent off `e`, which are the
two open indices plus a free complement configuration. -/
theorem edgeInsertedCoeff_eq_sum_local (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ N =
      ∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ v : V, A.component v (ξ v) (σ v) := by
  classical
  rw [edgeInsertedCoeff_eq_sum_complement]
  -- Collapse the delta product to the consistency-off-`e` filter, restrict the
  -- sum to consistent configurations, and reindex them to the doubled data.
  set F : OpenLocalConfig (G := G) A → ℂ := fun ξ =>
    N (ξ e.1.1 (edgeLeftIncident (G := G) e)) (ξ e.1.2 (edgeRightIncident (G := G) e)) *
      ∏ v : V, A.component v (ξ v) (σ v) with hF
  have hcollapse :
      (∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ v : V, A.component v (ξ v) (σ v)) =
        ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, F ξ.1 := by
    calc
      (∑ ξ : OpenLocalConfig (G := G) A,
        (∏ f : {f : Edge G // f ≠ e},
          if ξ f.1.1.1 (edgeLeftIncident (G := G) f.1) =
              ξ f.1.1.2 (edgeRightIncident (G := G) f.1) then (1 : ℂ) else 0) *
          N (ξ e.1.1 (edgeLeftIncident (G := G) e))
            (ξ e.1.2 (edgeRightIncident (G := G) e)) *
          ∏ v : V, A.component v (ξ v) (σ v))
          = ∑ ξ : OpenLocalConfig (G := G) A,
              if IsConsistentOff (G := G) A e ξ then F ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) A e ξ <;> simp [h, hF]
      _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ},
            F ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (OpenLocalConfig (G := G) A)))
              (f := F) (p := IsConsistentOff (G := G) A e)]
            simp
  rw [hcollapse]
  symm
  refine Fintype.sum_equiv (consistentOffEquivDoubled (G := G) A e) (fun ξ => F ξ.1) _ ?_
  rintro ⟨ξ, hξ⟩
  set d := consistentOffEquivDoubled (G := G) A e ⟨ξ, hξ⟩ with hd
  obtain ⟨i, k, ζ⟩ := d
  have hξeq : ξ = localOfDoubled (G := G) A e i k ζ := by
    have := (consistentOffEquivDoubled (G := G) A e).symm_apply_apply ⟨ξ, hξ⟩
    rw [← hd] at this
    exact congrArg Subtype.val this.symm
  subst hξeq
  simp only [hF]
  rw [show localOfDoubled (G := G) A e i k ζ e.1.1 (edgeLeftIncident (G := G) e) = i by
        unfold localOfDoubled edgeLeftIncident; simp]
  rw [show localOfDoubled (G := G) A e i k ζ e.1.2 (edgeRightIncident (G := G) e) = k by
        unfold localOfDoubled edgeRightIncident
        have hvne : ¬ e.1.2 = e.1.1 := (edgeLeft_ne_edgeRight e).symm
        simp [hvne]]
  rw [prod_univ_splitAtEdge e
    (fun v => A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v))]
  rw [edgeInsertedLeftLocalConfig_eq_localOfDoubled,
    edgeInsertedRightLocalConfig_eq_localOfDoubled]
  have hmid :
      (∏ v ∈ edgeMiddleVertices e,
          A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v)) =
      ∏ v : {v : V // v ∈ edgeMiddleVertices e},
        A.component v.1 (fun ie => edgeComplementValue (G := G) A e ζ v.2 ie) (σ v.1) := by
    rw [← Finset.prod_coe_sort (edgeMiddleVertices e)
      (fun v => A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v))]
    refine Finset.prod_congr rfl ?_
    intro v _
    congr 1
    funext ie
    exact (edgeComplementValue_eq_localOfDoubled (G := G) A e i k ζ v ie).symm
  rw [hmid]
  ring

/-- The product over vertices of gauged local tensors, evaluated at a per-vertex
local configuration, expands into a sum over inner local configurations with one
gauge-matrix factor on each incident edge.

This is `prod_gaugeVertex_eq_sum_local` with the outer configuration allowed to
differ at the two endpoints of an edge, as needed when one edge is left open. -/
lemma prod_gaugeVertex_eq_sum_local_open (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (ω : OpenLocalConfig (G := G) A) (σ : V → Fin d) :
    (∏ v : V, gaugeVertex A X v (ω v) (σ v)) =
      ∑ ξ : OpenLocalConfig (G := G) A,
        ∏ v : V,
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ω v ie) (ξ v ie)) *
            A.component v (ξ v) (σ v) := by
  classical
  simp_rw [gaugeVertex]
  rw [show
      (∏ v : V,
        ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ω v ie) (η' ie)) *
            A.component v η' (σ v)) =
        ∑ ξ : OpenLocalConfig (G := G) A,
          ∏ v : V,
            (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ω v ie) (ξ v ie)) *
              A.component v (ξ v) (σ v) by
    simpa only [Fintype.piFinset_univ, OpenLocalConfig] using
      (Finset.prod_univ_sum (fun v : V => Finset.univ)
        (fun v η' =>
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ω v ie) (η' ie)) *
            A.component v η' (σ v)))]
end PEPS
end TNLean

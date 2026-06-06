import TNLean.PEPS.Blocking
import TNLean.PEPS.InsertionAlgebra
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

For a chosen edge `e = (u,v)`, the source proof blocks all vertices other than
`u` and `v` into a middle tensor. The two endpoint tensors and this middle tensor
form a three-site injective MPS. Lemma `inj_isomorph` then assigns an edge gauge.
After repeating this for every edge and absorbing the gauges into the second
tensor family, the proof obtains the equality labelled `eq:inj_equal_edge`:
for every edge and every matrix `X`, inserting `X` on that edge in the first
PEPS gives the same state as inserting `X` on the same edge in the modified
second PEPS. Blocking one vertex against its complement and applying
`inj_equal_tensors_2` then gives $A_v = \lambda_v \cdot \tilde{B}_v$; the
scalars $\lambda_v$ are absorbed into the edge gauges.

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
private abbrev OpenLocalConfig (A : Tensor G d) : Type _ :=
  (v : V) → (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)

omit [DecidableRel G.Adj] in
/-- A local configuration is *consistent off `e`* when the two endpoints of every
edge other than `e` agree on its virtual index. -/
private def IsConsistentOff (A : Tensor G d) (e : Edge G)
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
private noncomputable def localOfDoubled (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    OpenLocalConfig (G := G) A :=
  fun v ie =>
    if h : ie.1 = e then
      if v = e.1.1 then Fin.cast (by rw [h]) i else Fin.cast (by rw [h]) k
    else ζ ⟨ie.1, h⟩

omit [Fintype V] in
/-- The rebuilt configuration reads the left open index at the left incidence of
`e`. -/
private theorem localOfDoubled_left_e (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζ e.1.1 (edgeLeftIncident (G := G) e) = i := by
  unfold localOfDoubled edgeLeftIncident; simp

omit [Fintype V] in
/-- The rebuilt configuration reads the right open index at the right incidence of
`e`. -/
private theorem localOfDoubled_right_e (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e) :
    localOfDoubled (G := G) A e i k ζ e.1.2 (edgeRightIncident (G := G) e) = k := by
  unfold localOfDoubled edgeRightIncident
  have hvne : ¬ e.1.2 = e.1.1 := (edgeLeft_ne_edgeRight e).symm
  simp [hvne]

omit [Fintype V] in
/-- On any edge other than `e`, the rebuilt configuration reads the complement
index at the left incidence. -/
private theorem localOfDoubled_left_ne (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
    (g : {g : Edge G // g ≠ e}) :
    localOfDoubled (G := G) A e i k ζ g.1.1.1 (edgeLeftIncident (G := G) g.1) = ζ g := by
  unfold localOfDoubled
  simp only [edgeLeftIncident, dif_neg g.2]

omit [Fintype V] in
/-- On any edge other than `e`, the rebuilt configuration reads the complement
index at the right incidence. -/
private theorem localOfDoubled_right_ne (A : Tensor G d) (e : Edge G)
    (i k : Fin (A.bondDim e)) (ζ : EdgeComplementConfig (G := G) A e)
    (g : {g : Edge G // g ≠ e}) :
    localOfDoubled (G := G) A e i k ζ g.1.1.2 (edgeRightIncident (G := G) g.1) = ζ g := by
  unfold localOfDoubled
  simp only [edgeRightIncident, dif_neg g.2]

/-- Local configurations consistent off `e` are the same finite data as the two
open edge indices together with a free configuration on every other edge. -/
private noncomputable def consistentOffEquivDoubled (A : Tensor G d) (e : Edge G) :
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
    show localOfDoubled (G := G) A e _ _ _ v ie = ξ v ie
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
    · show localOfDoubled (G := G) A e i k ζ e.1.1 (edgeLeftIncident (G := G) e) = i
      unfold localOfDoubled edgeLeftIncident; simp
    · show localOfDoubled (G := G) A e i k ζ e.1.2 (edgeRightIncident (G := G) e) = k
      unfold localOfDoubled edgeRightIncident; simp [hvne]
    · funext f
      show localOfDoubled (G := G) A e i k ζ f.1.1.1 (edgeLeftIncident (G := G) f.1) = ζ f
      have hf : f.1 ≠ e := f.2
      unfold localOfDoubled
      simp only [edgeLeftIncident, dif_neg hf]

/-- The per-edge consistency deltas off `e` collapse to the consistency-off-`e`
predicate. -/
private theorem prod_off_delta_eq (A : Tensor G d) (e : Edge G)
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
          = ∑ ξ : OpenLocalConfig (G := G) A, if IsConsistentOff (G := G) A e ξ then F ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) A e ξ <;> simp [h, hF]
      _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, F ξ.1 := by
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
  rw [prod_univ_splitAtEdge e (fun v => A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v))]
  rw [edgeInsertedLeftLocalConfig_eq_localOfDoubled,
    edgeInsertedRightLocalConfig_eq_localOfDoubled]
  have hmid :
      (∏ v ∈ edgeMiddleVertices e, A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v)) =
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
private lemma prod_gaugeVertex_eq_sum_local_open (A : Tensor G d)
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
    simpa [Fintype.piFinset_univ, OpenLocalConfig] using
      (Finset.prod_univ_sum (fun v : V => Finset.univ)
        (fun v η' =>
          (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (ω v ie) (η' ie)) *
            A.component v η' (σ v)))]

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
            (ω g.1.2 (edgeRightIncident (G := G) g)) (ξ g.1.2 (edgeRightIncident (G := G) g)) := by
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
                (ω g.1.2 (edgeRightIncident (G := G) g)) (ξ g.1.2 (edgeRightIncident (G := G) g))) =
        ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, G' ξ.1 := by
    calc
      _ = ∑ ξ : OpenLocalConfig (G := G) A, if IsConsistentOff (G := G) A e ξ then G' ξ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ξ _
            rw [prod_off_delta_eq]
            by_cases h : IsConsistentOff (G := G) A e ξ <;> simp [h, hG']
      _ = ∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, G' ξ.1 := by
            rw [Finset.sum_ite]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (OpenLocalConfig (G := G) A)))
              (f := G') (p := IsConsistentOff (G := G) A e)]
            simp
  rw [hcollapse]
  -- Reindex the consistent-off-`e` outer configurations to the two open indices
  -- and a free complement configuration.
  rw [show (∑ ξ : {ξ : OpenLocalConfig (G := G) A // IsConsistentOff (G := G) A e ξ}, G' ξ.1) =
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

/-- Under the sharper local hypothesis `HasFactorizedLocalGauge`, one obtains a
factorized local gauge relation at `v`.

The local left inverse and the canonical local gauge map are defined in
`PEPS/LocalGauge`. It remains to derive `BlockedMiddleGaugeFormula` from
`SameState` by comparing the edge-blocked coefficient from `PEPS/Blocking` with
the three-site MPS reduction, then convert it to `HasFactorizedLocalGauge` by
`hasFactorizedLocalGauge_of_blockedMiddleGaugeFormula`. -/
theorem localGauge_exists (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim) (v : V)
    (hFactorized : HasFactorizedLocalGauge A B hA hDim v) :
    ∃ (Xv : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v,
              (↑(Xv ie.1) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ :=
  localGauge_exists_of_factorizedLocalGauge A B hA hDim v hFactorized

/-! ### Gauge consistency across edges -/

/-- Post-absorption edge insertion equality from arXiv:1804.04964, Section 3,
lines 1037--1065. Assuming the separately tracked bond-dimension equality
(\#874), the edge gauges obtained from the three-site comparison can be absorbed
into the second tensor family so that every edge insertion in \(A\) agrees with
the transported edge insertion in the absorbed tensor family. The remaining
proof is #1364. -/
theorem post_absorption_edge_insertion_equality (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B) (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim) :
    ∃ Z, PostAbsorptionEdgeInsertionEquality A (absorbEdgeGauges B Z) := by
  sorry

/-- Edge gauges obtained from the three-site reductions give one global gauge
family. Source: arXiv:1804.04964, Section 3, from `eq:TN_5_particle_eq` through
`eq:inj_equal_edge`.

**Proof status:** The edge-blocked route and remaining insertion-to-gauge
obligations are recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. -/
theorem gaugeConsistency (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          gaugeVertex A X v η σ := by
  -- `exists_edgeGaugeFamily` supplies the per-edge gauges. It remains to prove
  -- post-absorption insertion equality (#1364) and the one-vertex complement
  -- comparison through the two-injective theorem (#1361), then convert the
  -- resulting `BlockedMiddleGaugeFormula` to the local gauge relation.
  sorry

/-! ### Main theorem -/

/-- **Fundamental Theorem for injective PEPS, conditional on bond-dimension
equality** (arXiv:1804.04964, Theorem 2).

If the bond spaces of `A` and `B` are already identified, equality of their PEPS
states and vertex injectivity imply the gauge formula
`B_v = gaugeVertex A X v` for one invertible matrix `X_e` on each edge, under
the explicit assumption that every virtual bond of `A` has positive dimension.
Via the bond-dimension equality this is also the corresponding positivity
assumption for `B`.

**Proof status:** This theorem is proved from the conditional global-gauge
statement above. The remaining difference from the source theorem is recorded
in `docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem fundamentalTheorem_PEPS_of_bondDim (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    GaugeEquiv A B := by
  rcases gaugeConsistency A B hA hB hAB hDim hpos with ⟨X, hX⟩
  exact ⟨hDim, X, hX⟩

/-- A matrix-algebra equivalence between full matrix algebras on `Fin m` and
`Fin n` forces `m = n`, since each algebra has linear dimension equal to the
square of its index size.

Source: standard dimension count; used to discharge the bond-dimension equality
hypothesis of `fundamentalTheorem_PEPS_of_bondDim` (issue #874). -/
theorem bondDim_eq_of_matrixAlgEquiv {m n : ℕ}
    (Φ : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) : m = n := by
  have hfr : Module.finrank ℂ (Matrix (Fin m) (Fin m) ℂ) =
      Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    LinearEquiv.finrank_eq Φ.toLinearEquiv
  rw [Module.finrank_matrix, Module.finrank_matrix] at hfr
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hfr
  exact Nat.mul_self_inj.mp hfr

/-- **Fundamental Theorem for injective PEPS** (arXiv:1804.04964, Theorem 2).

For PEPS tensors on a finite simple graph, if `A` and `B` are vertex-injective
and have the same state coefficients, then there are invertible edge matrices
`X_e` such that, at every vertex, `B_v` is obtained from `A_v` by the oriented
endpoint action of the matrices `X_e` on the incident virtual legs.

**Positive-bond hypothesis (faithfulness fix).** Without the positivity conditions the
theorem is false: a zero-dimensional edge makes the virtual configuration empty,
so both state coefficients vanish and `SameState` holds vacuously without
relating the two tensors, while the gauge-equivalence conclusion stays a genuine
constraint that fails. The hypotheses (every bond dimension positive) are the
source's standing assumption that injective PEPS have nonzero virtual bond
spaces; the same defect was corrected for the edge-blocked three-site
injectivity (#1366) and the physical-to-virtual recovery (#1370), and is
recorded in `docs/paper-gaps/peps_injective_ft_section3_route.tex`.

**Proof status:** The conclusion is the source gauge-equivalence conclusion, with
positive bond dimension made explicit to exclude the zero-bond vacuous-state
case above. The bond-dimension equality is now discharged edgewise from the
edge-blocked insertion algebra equivalence (issue #874). The remaining
edge-centred gauge obligation is `gaugeConsistency`, recorded in
`docs/paper-gaps/peps_injective_ft_section3_route.tex`, Section "Remaining
mathematical obligations". -/
theorem fundamentalTheorem_PEPS (A B : Tensor G d)
    (hA : IsVertexInjective A) (hB : IsVertexInjective B)
    (hAB : SameState A B)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) :
    GaugeEquiv A B := by
  -- Bond-dimension equality follows edgewise from the edge-blocked insertion
  -- algebra isomorphism: blocking around an edge gives two injective three-site
  -- chains generating the same state, and the matched matrix insertions on that
  -- bond form an algebra equivalence between the two full bond matrix algebras.
  -- Such an equivalence forces equal matrix sizes.
  have hDim : A.bondDim = B.bondDim := by
    funext e
    exact bondDim_eq_of_matrixAlgEquiv
      (edgeTransferAlgEquiv A B e
        (hA.edgeBlockedThreeSiteInjective hposA e)
        (hB.edgeBlockedThreeSiteInjective hposB e)
        hAB hposA hposB)
  -- With matching bond dimensions, gauge consistency supplies the global gauges.
  exact fundamentalTheorem_PEPS_of_bondDim A B hA hB hAB hDim hposA

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

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalars multiply pointwise under multiplication of edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; endpoint factors are
defined by the oriented edge scalar and its inverse. -/
theorem edgeScalarAt_mul (c d : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) (fun e => c e * d e) v ie =
      edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simpa [edgeScalarAt, h] using
      (mul_comm (((d ie.1 : Units ℂ) : ℂ)⁻¹) (((c ie.1 : Units ℂ) : ℂ)⁻¹))

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalars invert pointwise under inversion of edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses nonzero edge scalars and the inverse endpoint action on the opposite end
of each oriented edge. -/
theorem edgeScalarAt_inv (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie =
      (edgeScalarAt (G := G) c v ie)⁻¹ := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simp [edgeScalarAt, h]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Endpoint scalar factors are nonzero.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; edge scalars are
nonzero and the opposite endpoint uses their inverse. -/
theorem edgeScalarAt_ne_zero (c : (e : Edge G) → Units ℂ)
    (v : V) (ie : IncidentEdge G v) :
    edgeScalarAt (G := G) c v ie ≠ 0 := by
  by_cases h : ie.1.1.1 = v
  · simp [edgeScalarAt, h]
  · simp [edgeScalarAt, h]

/-- Vertex-balanced edge scalars are closed under pointwise multiplication.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses the multiplicative group of edge scalars whose oriented product is `1` at
each vertex. -/
theorem IsVertexBalanced.mul {c d : (e : Edge G) → Units ℂ}
    (hc : IsVertexBalanced (G := G) c)
    (hd : IsVertexBalanced (G := G) d) :
    IsVertexBalanced (G := G) (fun e => c e * d e) := by
  intro v
  calc
    ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) (fun e => c e * d e) v ie =
        ∏ ie : IncidentEdge G v,
          edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie := by
          refine Finset.prod_congr rfl ?_
          intro ie _
          simp [edgeScalarAt_mul]
    _ =
        (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie) *
          ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) d v ie := by
          rw [Finset.prod_mul_distrib]
    _ = 1 := by simp [hc v, hd v]

/-- Vertex-balanced edge scalars are closed under pointwise inversion.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
uses invertible edge scalars, and the inverse family again has oriented product
`1` at every vertex. -/
theorem IsVertexBalanced.inv {c : (e : Edge G) → Units ℂ}
    (hc : IsVertexBalanced (G := G) c) :
    IsVertexBalanced (G := G) (fun e => (c e)⁻¹) := by
  intro v
  calc
    ∏ ie : IncidentEdge G v, edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie =
        ∏ ie : IncidentEdge G v, (edgeScalarAt (G := G) c v ie)⁻¹ := by
          refine Finset.prod_congr rfl ?_
          intro ie _
          simp [edgeScalarAt_inv]
    _ = (∏ ie : IncidentEdge G v, edgeScalarAt (G := G) c v ie)⁻¹ := by
          rw [Finset.prod_inv_distrib]
    _ = 1 := by simp [hc v]

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

/-- Gauge equivalence modulo balanced edge scalars is reflexive.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the identity edge-scalar
family is vertex-balanced and leaves every oriented endpoint action unchanged. -/
theorem GaugeEquivModEdgeScalars.refl (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) :
    GaugeEquivModEdgeScalars (G := G) A X X := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro v
    simp [edgeScalarAt]
  · intro v ie
    simp [edgeScalarAt]

/-- Gauge equivalence modulo balanced edge scalars is symmetric.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; reversing a balanced
edge-scalar reweighting uses the inverse edge-scalar family. -/
theorem GaugeEquivModEdgeScalars.symm {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    GaugeEquivModEdgeScalars (G := G) A Y X := by
  rcases hXY with ⟨c, hc, hXY⟩
  refine ⟨fun e => (c e)⁻¹, IsVertexBalanced.inv (G := G) hc, ?_⟩
  intro v ie
  set s : ℂ := edgeScalarAt (G := G) c v ie with hs_def
  have hs : s ≠ 0 := by
    rw [hs_def]
    exact edgeScalarAt_ne_zero (G := G) c v ie
  calc
    edgeGaugeAt A Y v ie = s⁻¹ • (s • edgeGaugeAt A Y v ie) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    _ = s⁻¹ • edgeGaugeAt A X v ie := by
      rw [← hXY v ie]
    _ =
        edgeScalarAt (G := G) (fun e => (c e)⁻¹) v ie •
          edgeGaugeAt A X v ie := by
          rw [edgeScalarAt_inv, ← hs_def]

/-- Gauge equivalence modulo balanced edge scalars is transitive.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; composing two balanced
edge-scalar reweightings multiplies their edge scalars, and the balancing
condition is multiplicatively closed at every vertex. -/
theorem GaugeEquivModEdgeScalars.trans {A : Tensor G d}
    {X Y Z : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y)
    (hYZ : GaugeEquivModEdgeScalars (G := G) A Y Z) :
    GaugeEquivModEdgeScalars (G := G) A X Z := by
  rcases hXY with ⟨c, hc, hXY⟩
  rcases hYZ with ⟨d, hd, hYZ⟩
  refine ⟨fun e => c e * d e, IsVertexBalanced.mul (G := G) hc hd, ?_⟩
  intro v ie
  calc
    edgeGaugeAt A X v ie =
        edgeScalarAt (G := G) c v ie • edgeGaugeAt A Y v ie := hXY v ie
    _ =
        edgeScalarAt (G := G) c v ie •
          (edgeScalarAt (G := G) d v ie • edgeGaugeAt A Z v ie) := by
          rw [hYZ v ie]
    _ =
        (edgeScalarAt (G := G) c v ie * edgeScalarAt (G := G) d v ie) •
          edgeGaugeAt A Z v ie := by
          rw [smul_smul]
    _ =
        edgeScalarAt (G := G) (fun e => c e * d e) v ie •
          edgeGaugeAt A Z v ie := by
          rw [edgeScalarAt_mul]

/-- Gauge equivalence modulo balanced edge scalars is an equivalence relation.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the corrected quotient
is the quotient of edge gauges by the vertex-balanced scalar action. -/
theorem GaugeEquivModEdgeScalars.equivalence (A : Tensor G d) :
    Equivalence (GaugeEquivModEdgeScalars (G := G) A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact GaugeEquivModEdgeScalars.refl (G := G) A X
  · intro X Y hXY
    exact GaugeEquivModEdgeScalars.symm (G := G) hXY
  · intro X Y Z hXY hYZ
    exact GaugeEquivModEdgeScalars.trans (G := G) hXY hYZ

/-- The quotient relation on gauge families modulo balanced edge scalars.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; this packages the
corrected balanced edge-scalar quotient as a formal equivalence relation. -/
def GaugeEquivModEdgeScalars.setoid (A : Tensor G d) :
    Setoid ((e : Edge G) → GL (Fin (A.bondDim e)) ℂ) where
  r := GaugeEquivModEdgeScalars (G := G) A
  iseqv := GaugeEquivModEdgeScalars.equivalence (G := G) A

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

/-- Balanced edge-scalar equivalent gauges define the same gauged PEPS tensor.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; balanced endpoint
scalars leave every local gauged tensor unchanged, hence the whole gauged
tensor is unchanged. -/
theorem GaugeEquivModEdgeScalars.applyGauge_eq
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    applyGauge A X = applyGauge A Y := by
  change Tensor.mk A.bondDim (fun v => gaugeVertex A X v) =
    Tensor.mk A.bondDim (fun v => gaugeVertex A Y v)
  congr
  funext v η σ
  exact GaugeEquivModEdgeScalars.gaugeVertex_eq (G := G) hXY v η σ

/-- Balanced edge-scalar equivalent gauges give the same PEPS state.

Source: `docs/paper-gaps/peps_gauge_edge_scalars.tex`; the balanced quotient
acts trivially on every local gauged tensor, and hence on the contracted state. -/
theorem GaugeEquivModEdgeScalars.applyGauge_sameState
    {A : Tensor G d}
    {X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ}
    (hXY : GaugeEquivModEdgeScalars (G := G) A X Y) :
    SameState (applyGauge A X) (applyGauge A Y) := by
  intro σ
  rw [GaugeEquivModEdgeScalars.applyGauge_eq (G := G) hXY]

/-! ### Uniqueness modulo balanced edge scalars -/

/-- If the gauged vertex tensors produced by two gauge families agree pointwise
at a vertex `v`, then, by linear independence of `A.component v`, the products
of incident edge-gauge matrix entries coincide for every pair of virtual
configurations `η, η'`.

This reduces the remaining step in `gauge_unique_mod_edge_scalars` from the
functional equality of gauged vertex tensors to an equality of scalar products
of incident edge-gauge entries, which is the proper input to the pending
tensor-factor uniqueness argument. -/
private lemma edgeGaugeProduct_eq_of_gaugeVertex_eq
    (A : Tensor G d) (hA : IsVertexInjective A) (v : V)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (h : ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1))
        (σ : Fin d),
      gaugeVertex A X v η σ = gaugeVertex A Y v η σ)
    (η η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) :
    (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie)) =
      ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) := by
  refine (hA v).eq_coords_of_eq
    (f := fun ξ => ∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (ξ ie))
    (g := fun ξ => ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (ξ ie))
    ?_ η'
  funext σ
  simpa [gaugeVertex, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h η σ

/-- **Gauge uniqueness modulo balanced edge scalars** (arXiv:1804.04964,
Theorem 2, uniqueness clause, corrected graph quotient).

If `X` and `Y` are two gauge families relating the same injective PEPS tensor
`A` to the same tensor `B`, then their oriented endpoint actions differ by
edge scalars `c_e` whose product around every vertex is `1`.

**Local fix (balanced edge scalars):** The source states that the gauges
are unique up to a multiplicative constant. On a general graph the connected
triangle with one-dimensional bonds refutes uniqueness modulo one global scalar.
The graph-correct quotient is uniqueness modulo vertex-balanced edge scalars;
see `docs/paper-gaps/peps_gauge_edge_scalars.tex`.

**Proof status:** The proof has been reduced to equality of products of
incident edge-gauge entries at each vertex. The remaining step extracts the
local scalar ratios and reconciles them into one vertex-balanced edge-scalar
family; see `docs/paper-gaps/peps_gauge_edge_scalars.tex`. -/
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
  -- Step 1: combine `hX` and `hY` to obtain vertex-wise equality of the
  -- gauged tensors `gaugeVertex A X v η σ = gaugeVertex A Y v η σ`.
  have hGauge : ∀ (v : V)
      (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      gaugeVertex A X v η σ = gaugeVertex A Y v η σ :=
    fun v η σ => (hX v η σ).symm.trans (hY v η σ)
  -- Step 2: linear independence of `A.component v` promotes this to equality
  -- of incident edge-gauge products for every configuration pair `η, η'`.
  have hProd : ∀ (v : V)
      (η η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)),
      (∏ ie : IncidentEdge G v, edgeGaugeAt A X v ie (η ie) (η' ie)) =
        ∏ ie : IncidentEdge G v, edgeGaugeAt A Y v ie (η ie) (η' ie) :=
    fun v η η' =>
      edgeGaugeProduct_eq_of_gaugeVertex_eq (G := G) A hA v X Y (hGauge v) η η'
  -- From `hProd v` at each vertex `v`, extract a nonzero scalar `c_v(ie)` on
  -- each incident edge such that `edgeGaugeAt A X v ie = c_v(ie) • edgeGaugeAt A Y v ie`
  -- with the oriented product of `c_v(ie)` over incident `ie` at `v` equal to
  -- `1`, then reconcile `c_u` and `c_w` on every shared edge `e = (u,w)` into a
  -- single global family `c : (e : Edge G) → Units ℂ` satisfying
  -- `IsVertexBalanced c`. This is the local scalar-ratio argument of
  -- arXiv:1804.04964 Section 3; it is independent of the virtual-insertion and
  -- blocking lemmas used for local gauge existence.
  -- The current status is recorded in
  -- `docs/paper-gaps/peps_gauge_edge_scalars.tex`.
  sorry

end PEPS
end TNLean

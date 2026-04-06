import TNLean.PEPS.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Fundamental Theorem for injective PEPS (scaffold)

This file scaffolds the Fundamental Theorem for injective PEPS on simple graphs
(arXiv:1804.04964, Theorem 2, Section 3):

> Two injective PEPS defined on a graph (no double edges/self-loops) generate
> the same state iff the generating tensors are related by local gauges on each
> edge, unique up to a multiplicative constant.

## Strategy

The proof (from the paper) generalises the 1D MPS Fundamental Theorem
(`TNLean.MPS.FundamentalTheorem.Basic`) to arbitrary graph geometries:

1. At each vertex `v`, injectivity gives a left inverse for the local tensor map.
2. `SameState` plus contraction over all vertices except `v` yields a local
   gauge relation at `v`.
3. Consistency across adjacent vertices forces the gauges to be compatible,
   giving a global gauge equivalence.

This parallels the MPS proof's linear-extension → multiplicativity →
Skolem–Noether pipeline, but replaces chain algebra with graph-local reasoning.

## References

* [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Gauge matrices at oriented endpoints -/

/-- The gauge matrix to apply at vertex `v` for an incident edge `ie`.

For edge `(u, v)` with `u < v` and gauge `X_e`:
* at the first endpoint (`v = u`): apply `X_e`,
* at the second endpoint (`v = v`): apply `(X_e⁻¹)ᵀ`.

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

/-- Applying a gauge to a PEPS tensor preserves the state coefficients.

The proof relies on the fact that for each edge, the gauge matrix and its
inverse-transpose cancel upon contraction of the shared virtual index:
`∑_j X(i,j) · (X⁻¹)ᵀ(j,k) = δ(i,k)`. -/
theorem applyGauge_stateCoeff (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (σ : V → Fin d) :
    stateCoeff (applyGauge A X) σ = stateCoeff A σ := by
  -- TODO: expand stateCoeff, swap sums, apply gauge cancellation per edge.
  sorry

/-- Gauge equivalence implies the same PEPS state. -/
theorem GaugeEquiv.sameState {A B : Tensor G d} (h : GaugeEquiv A B) :
    SameState A B := by
  -- TODO: transport the applyGauge_stateCoeff result through hDim.
  sorry

/-! ### Local gauge extraction -/

/-- The local tensor at vertex `v`, viewed as a linear map from the virtual
index space to the physical/coefficient space. -/
noncomputable def localTensorMap (A : Tensor G d) (v : V) :
    ((ie : IncidentEdge G v) → Fin (A.bondDim ie.1) → ℂ) →ₗ[ℂ]
    (Fin d → ℂ) where
  toFun f σ := ∑ η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
    (∏ ie : IncidentEdge G v, f ie (η ie)) * A.component v η σ
  map_add' := by intros; ext; simp; ring_nf; sorry
  map_smul' := by intros; ext; simp; ring_nf; sorry

/-- At a single vertex, `SameState` plus injectivity forces a local gauge
relation between the two tensors.

This is the PEPS analogue of the MPS linear-extension step: injectivity at `v`
provides a left inverse, and `SameState` (contracted over all other vertices)
constrains the relationship to a linear isomorphism on the virtual indices of
`v`. -/
theorem localGauge_exists (A B : Tensor G d)
    (hA : IsVertexInjective A) (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim) (v : V) :
    ∃ (Xv : (ie : IncidentEdge G v) →
        GL (Fin (A.bondDim ie.1)) ℂ),
      ∀ (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          ∑ η' : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1),
            (∏ ie : IncidentEdge G v, (↑(Xv ie) : Matrix _ _ ℂ) (η ie) (η' ie)) *
              A.component v η' σ := by
  -- TODO: use injectivity of A at v to define a left inverse,
  -- then extract the gauge matrix from the SameState condition.
  -- This requires contracting over all vertices except v and using
  -- the resulting linear relation on the virtual space of v.
  sorry

/-! ### Gauge consistency across edges -/

/-- Local gauges extracted at adjacent vertices are consistent: for an edge
`e = (u, v)`, the gauge at `u`'s side of `e` and the gauge at `v`'s side of
`e` satisfy `X_u(e) = (X_v(e)⁻¹)ᵀ` (up to the orientation convention).

This is the combinatorial heart of the PEPS FT proof. In the MPS case,
consistency is automatic because there is only one gauge matrix. For PEPS on a
graph, one must verify that the local gauges "match up" along every edge. -/
theorem gaugeConsistency (A B : Tensor G d)
    (hA : IsVertexInjective A) (hAB : SameState A B)
    (hDim : A.bondDim = B.bondDim) :
    ∃ (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ),
      ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
        B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
          gaugeVertex A X v η σ := by
  -- TODO: combine localGauge_exists at each vertex with consistency
  -- across shared edges. The key step is: for each edge e = (u,v),
  -- the gauge obtained from u's local extraction and v's local extraction
  -- must agree (because the SameState condition couples them).
  sorry

/-! ### Main theorem -/

/-- **Fundamental Theorem for injective PEPS** (arXiv:1804.04964, Theorem 2).

If two PEPS tensors on a simple graph are both vertex-injective and generate
the same state, then they are gauge-equivalent: there exist invertible matrices
`X_e` on each edge such that `B` is the gauge transform of `A`.

The proof proceeds in two stages:
1. **Local extraction** (`localGauge_exists`): at each vertex, injectivity
   provides a left inverse that converts the SameState condition into a
   local gauge relation.
2. **Global consistency** (`gaugeConsistency`): local gauges along shared
   edges are shown to be compatible, yielding a single coherent family of
   edge gauges.

In the MPS (1D chain) case, this reduces to `fundamentalTheorem_singleBlock`. -/
theorem fundamentalTheorem_PEPS (A B : Tensor G d)
    (hA : IsVertexInjective A) (hAB : SameState A B) :
    GaugeEquiv A B := by
  -- Step 1: Show bond dimensions must agree.
  -- TODO: derive hDim from injectivity + SameState.
  -- For now, assume it as a hypothesis via sorry.
  have hDim : A.bondDim = B.bondDim := by
    sorry
  -- Step 2: Extract globally consistent gauges.
  rcases gaugeConsistency A B hA hAB hDim with ⟨X, hX⟩
  exact ⟨hDim, X, hX⟩

/-! ### Uniqueness (up to scalar) -/

/-- The gauge in the Fundamental Theorem is unique up to a global multiplicative
scalar. If `X` and `Y` are two gauge families relating the same pair of
injective PEPS, then `X_e = c · Y_e` for some nonzero `c : ℂ` independent
of `e`.

This is the PEPS analogue of the MPS result that the gauge matrix is unique
up to scalar (arXiv:1804.04964, Theorem 2, uniqueness clause). -/
theorem gauge_unique_up_to_scalar (A B : Tensor G d)
    (hA : IsVertexInjective A)
    (hDim : A.bondDim = B.bondDim)
    (X Y : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ)
    (hX : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A X v η σ)
    (hY : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σ : Fin d),
      B.component v (fun ie => Fin.cast (congr_fun hDim ie.1) (η ie)) σ =
        gaugeVertex A Y v η σ) :
    ∃ (c : ℂ), c ≠ 0 ∧ ∀ (e : Edge G),
      (X e).val = c • (Y e).val := by
  -- TODO: from hX and hY, gauge(X) = gauge(Y) at every vertex.
  -- Injectivity forces X_e · Y_e⁻¹ to be scalar at each edge,
  -- and connectivity of the graph forces the scalar to be uniform.
  sorry

end PEPS
end TNLean

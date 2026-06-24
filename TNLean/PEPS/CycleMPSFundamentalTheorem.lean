import TNLean.PEPS.CycleMPSInjectivity
import TNLean.PEPS.CycleFundamentalTheorem
import TNLean.PEPS.TorusAbsorbedCovariance
import TNLean.PEPS.CycleMPSOverlapCapstone

/-!
# The Fundamental Theorem for translation-invariant normal MPS on a closed chain

This file delivers the matrix-level form of the closed-chain corollary of the
Fundamental Theorem for normal PEPS (arXiv:1804.04964, Section 3, first
corollary after the theorem labelled `normal`, lines 1585--1631 of
`Papers/1804.04964/paper_normal.tex`), specialized to one site-independent
tensor: two matrix tensors `A, B`, each `L`-block injective, generating the
same closed-chain state on `n ≥ 2L + 1` sites, are related by invertible
matrices `Z_v` (one per bond, `n + 1 ≡ 1`) with `B = Z_v⁻¹ A Z_{v+1}` at
every site (`fundamentalTheorem_normalMPS`).

The statement is the source corollary's conclusion — a family of per-bond
gauges — with the source's site-dependent families `{A_i}`, `{B_i}`
specialized to a single repeated tensor; the source's translation-invariant
corollary (lines 1624--1661: a single gauge `Z` and a constant `λ` with
`λ^n = 1`) refines this output and is not delivered here.

The existence clause carries the optimal system size `n ≥ 2L + 1` of the
source's alternative proof (line 1623 and Section `normal_alt`, the corollary
after Lemma 5): `fundamentalTheorem_normalMPS` delegates to the
overlapping-window corollary `fundamentalTheorem_normalMPS_of_overlap`.

The uniqueness clause `fundamentalTheorem_normalMPS_gauge_unique` still uses
the `n ≥ 3L` route through the cycle-graph corollary
(`fundamentalTheorem_normalMPS_cycle`).  There the cycle tensors of `A` and
`B` generate the same state since their coefficients are the matrix-product
traces, every arc of `L` consecutive sites is blocked-injective by `L`-block
injectivity of the matrix tensors, and the graph-level gauge equivalence
hands back one invertible matrix per edge.  The per-edge matrices convert to
per-bond gauges through the stored-edge orientation: away from the seam the
gauge of the bond entering site `v` is the transpose of the edge matrix,
while on the seam edge — stored with its endpoints in the opposite order — it
is the inverse (`cycleGaugeOfEdgeGauge`).  The per-vertex component identity
of the graph-level gauge equivalence is equivalent to the matrix identity
`B = Z_v⁻¹ A Z_{v+1}` (`cycleGauge_component_iff_matrix`).  The uniqueness
clause converts a per-bond family back into a per-edge family
(`edgeGaugeOfCycleGauge`), invokes the graph-level uniqueness for a constant
per edge, and merges the constants into one because the relation
`B = Z_v⁻¹ A Z_{v+1}` pins the ratio of consecutive constants against the
nonzero tensor `B`.

The matrix-level hypotheses match the source corollary: `0 < L` (implicit in
blocking `L` consecutive sites), `L`-block injectivity of both tensors, and
equality of the closed-chain coefficients at the single size `n`.  The
positivity side conditions of the graph-level corollary are discharged here,
not assumed: a vanishing bond dimension makes the conclusion trivial, and a
vanishing physical dimension contradicts block injectivity.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, first corollary after the theorem labelled `normal`, lines
  1585--1631 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped Matrix

namespace TNLean
namespace PEPS

variable {n d D : ℕ}

section GaugeVertexFormula

variable [NeZero n]

/-- The gauge matrix at an incidence whose stored first endpoint is the
vertex. -/
theorem edgeGaugeAt_of_fst {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) (v : V) (ie : IncidentEdge G v)
    (h : ie.1.1.1 = v) :
    edgeGaugeAt A X v ie = (X ie.1 : Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ) :=
  if_pos h

/-- The gauge matrix at an incidence whose stored second endpoint is the
vertex. -/
theorem edgeGaugeAt_of_snd {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (A : Tensor G d)
    (X : (e : Edge G) → GL (Fin (A.bondDim e)) ℂ) (v : V) (ie : IncidentEdge G v)
    (h : ¬ ie.1.1.1 = v) :
    edgeGaugeAt A X v ie =
      (((X ie.1)⁻¹ : GL (Fin (A.bondDim ie.1)) ℂ) :
        Matrix (Fin (A.bondDim ie.1)) (Fin (A.bondDim ie.1)) ℂ)ᵀ :=
  if_neg h

/-- The oriented gauge matrix of the bond entering a site of the closed
chain. -/
noncomputable def cycleLeftGauge (hn : 3 ≤ n) (A : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    Matrix (Fin D) (Fin D) ℂ :=
  edgeGaugeAt (cycleTensorOfMPS hn A) X v (cycleLeftIncident hn v)

/-- The oriented gauge matrix of the bond leaving a site of the closed
chain. -/
noncomputable def cycleRightGauge (hn : 3 ≤ n) (A : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    Matrix (Fin D) (Fin D) ℂ :=
  edgeGaugeAt (cycleTensorOfMPS hn A) X v (cycleRightIncident hn v)

/-- **Two-bond factorization of the gauge action on the cycle.**  At a site of
the closed chain the gauge action contracts the two incident gauge matrices
against the site matrix: the gauged component is an entry of
`M_left * A^σ * M_rightᵀ`, where `M_left`, `M_right` are the oriented gauge
matrices of the two incident bonds. -/
theorem gaugeVertex_cycleTensorOfMPS (hn : 3 ≤ n) (A : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ)
    (v : Fin n) (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D)
    (σ : Fin d) :
    gaugeVertex (cycleTensorOfMPS hn A) X v η σ =
      (cycleLeftGauge hn A X v * A σ * (cycleRightGauge hn A X v)ᵀ)
        (η (cycleLeftIncident hn v)) (η (cycleRightIncident hn v)) := by
  classical
  set Ml := cycleLeftGauge hn A X v with hMl
  set Mr := cycleRightGauge hn A X v with hMr
  simp only [gaugeVertex]
  calc (∑ η' : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) →
        Fin ((cycleTensorOfMPS hn A).bondDim ie.1),
        (∏ ie : IncidentEdge (SimpleGraph.cycleGraph n) v,
          edgeGaugeAt (cycleTensorOfMPS hn A) X v ie (η ie) (η' ie)) *
          (cycleTensorOfMPS hn A).component v η' σ)
      = ∑ p : Fin D × Fin D,
          Ml (η (cycleLeftIncident hn v)) p.1 * Mr (η (cycleRightIncident hn v)) p.2 *
            A σ p.1 p.2 := by
        refine Fintype.sum_equiv (cycleIncidentPairEquiv hn v) _ _ fun η' => ?_
        rw [show (∏ ie : IncidentEdge (SimpleGraph.cycleGraph n) v,
            edgeGaugeAt (cycleTensorOfMPS hn A) X v ie (η ie) (η' ie)) =
            Ml (η (cycleLeftIncident hn v)) (η' (cycleLeftIncident hn v)) *
              Mr (η (cycleRightIncident hn v)) (η' (cycleRightIncident hn v)) by
          rw [show (Finset.univ :
              Finset (IncidentEdge (SimpleGraph.cycleGraph n) v)) =
              {cycleLeftIncident hn v, cycleRightIncident hn v} from
            univ_incidentEdge_eq_pair hn v]
          rw [Finset.prod_pair (cycleLeftIncident_ne_cycleRightIncident hn v)]
          rfl]
        rfl
    _ = (Ml * A σ * Mrᵀ) (η (cycleLeftIncident hn v)) (η (cycleRightIncident hn v)) := by
        rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.transpose_apply]
        ring

/-- Reading a bond-pair assignment at the bond entering the site. -/
theorem cycleIncidentPairEquiv_symm_left (hn : 3 ≤ n) (v : Fin n) (p : Fin D × Fin D) :
    (cycleIncidentPairEquiv (D := D) hn v).symm p (cycleLeftIncident hn v) = p.1 :=
  if_pos rfl

/-- Reading a bond-pair assignment at the bond leaving the site. -/
theorem cycleIncidentPairEquiv_symm_right (hn : 3 ≤ n) (v : Fin n) (p : Fin D × Fin D) :
    (cycleIncidentPairEquiv (D := D) hn v).symm p (cycleRightIncident hn v) = p.2 :=
  if_neg (cycleLeftIncident_ne_cycleRightIncident hn v).symm

/-- The component of the cycle tensor at a bond-pair assignment is the matrix
entry at the pair. -/
theorem cycleTensorOfMPS_component_pair (hn : 3 ≤ n) (B : MPSTensor d D) (v : Fin n)
    (p : Fin D × Fin D) (σ : Fin d) :
    (cycleTensorOfMPS hn B).component v ((cycleIncidentPairEquiv (D := D) hn v).symm p) σ =
      B σ p.1 p.2 := by
  rw [cycleTensorOfMPS_component, cycleIncidentPairEquiv_symm_left,
    cycleIncidentPairEquiv_symm_right]

/-- **Per-site component identity in matrix form.**  At a site of the closed
chain, the gauge-equivalence component identity between the cycle tensors of
`B` and `A` holds for all bond assignments exactly when the matrix identity
`B = M_left * A * M_rightᵀ` holds, with `M_left`, `M_right` the oriented gauge
matrices of the two incident bonds. -/
theorem cycleGauge_component_iff (hn : 3 ≤ n) (A B : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    (∀ (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) (σ : Fin d),
      (cycleTensorOfMPS hn B).component v η σ =
        gaugeVertex (cycleTensorOfMPS hn A) X v η σ) ↔
    (∀ i : Fin d, B i =
      cycleLeftGauge hn A X v * A i * (cycleRightGauge hn A X v)ᵀ) := by
  constructor
  · intro hcomp i
    apply Matrix.ext
    intro a b
    have h := hcomp ((cycleIncidentPairEquiv (D := D) hn v).symm (a, b)) i
    rw [cycleTensorOfMPS_component_pair, gaugeVertex_cycleTensorOfMPS,
      cycleIncidentPairEquiv_symm_left, cycleIncidentPairEquiv_symm_right] at h
    exact h
  · intro hmat η σ
    rw [cycleTensorOfMPS_component, gaugeVertex_cycleTensorOfMPS, hmat σ]

end GaugeVertexFormula

section GaugeConversion

variable [NeZero n]

/-- The per-bond gauge of a per-edge gauge family: the gauge of the bond
entering site `v`.  Away from the seam this is the transpose of the matrix on
the stored edge; at the seam — the edge stored with its endpoints in the
opposite cyclic order — it is the inverse.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1631 of `Papers/1804.04964/paper_normal.tex`:
the corollary's gauges `Z_i` live on the bonds of the closed chain. -/
noncomputable def cycleGaugeOfEdgeGauge (hn : 3 ≤ n)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    GL (Fin D) ℂ :=
  if v = 0 then (X (cycleSuccEdge hn (v - 1)))⁻¹
  else glTranspose (X (cycleSuccEdge hn (v - 1)))

/-- The bond entering site `0` is the seam edge. -/
private theorem pred_zero_wrap (hn : 3 ≤ n) {v : Fin n} (hv0 : v = 0) :
    (v - 1).val + 1 = n := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  subst hv0
  rw [val_sub_eq_ite]
  simp only [h1, Fin.val_zero]
  split_ifs <;> omega

/-- Away from site `0`, the bond entering a site is stored away from the
seam. -/
private theorem pred_val_lt (hn : 3 ≤ n) {v : Fin n} (hv0 : ¬ v = 0) :
    (v - 1).val + 1 < n := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hv : v.val ≠ 0 := fun h => hv0 (Fin.ext h)
  have := v.isLt
  rw [val_sub_eq_ite]
  simp only [h1]
  split_ifs <;> omega

/-- No site is its own cyclic predecessor. -/
private theorem sub_one_ne_self (hn : 3 ≤ n) (v : Fin n) : ¬ v - 1 = v := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  intro h
  have hval := congrArg Fin.val h
  rw [val_sub_eq_ite, h1] at hval
  have := v.isLt
  split_ifs at hval <;> omega

/-- No site is its own cyclic successor. -/
private theorem add_one_ne_self (hn : 3 ≤ n) (v : Fin n) : ¬ v + 1 = v := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_add_eq_ite, h1] at hval
  have := v.isLt
  split_ifs at hval <;> omega

/-- The oriented gauge matrix of the bond entering a site is the inverse of
the per-bond gauge of that bond. -/
theorem cycleLeftGauge_eq (hn : 3 ≤ n) (A : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    cycleLeftGauge hn A X v =
      ((cycleGaugeOfEdgeGauge hn X v)⁻¹ : GL (Fin D) ℂ) := by
  by_cases hv0 : v = 0
  · -- The bond entering site `0` is the seam edge, stored first endpoint `0`.
    have hfst : (cycleSuccEdge hn (v - 1)).1.1 = v := by
      rw [cycleSuccEdge_val_of_eq hn (pred_zero_wrap hn hv0)]
      change v - 1 + 1 = v
      rw [sub_add_cancel]
    have hM : cycleLeftGauge hn A X v =
        (X (cycleSuccEdge hn (v - 1)) : Matrix (Fin D) (Fin D) ℂ) :=
      edgeGaugeAt_of_fst _ _ _ _ hfst
    rw [hM, cycleGaugeOfEdgeGauge, if_pos hv0, inv_inv]
  · -- Away from the seam the bond is stored with the predecessor first.
    have hfst : ¬ (cycleSuccEdge hn (v - 1)).1.1 = v := by
      rw [cycleSuccEdge_val_of_lt hn (pred_val_lt hn hv0)]
      exact sub_one_ne_self hn v
    have hM : cycleLeftGauge hn A X v =
        (((X (cycleSuccEdge hn (v - 1)))⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ)ᵀ :=
      edgeGaugeAt_of_snd _ _ _ _ hfst
    rw [hM, cycleGaugeOfEdgeGauge, if_neg hv0, glTranspose_inv_coe]

/-- The transposed oriented gauge matrix of the bond leaving a site is the
per-bond gauge of the bond entering the next site. -/
theorem cycleRightGauge_transpose_eq (hn : 3 ≤ n) (A : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    (cycleRightGauge hn A X v)ᵀ =
      (cycleGaugeOfEdgeGauge hn X (v + 1) : GL (Fin D) ℂ) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
  have hsub : v + 1 - 1 = v := add_sub_cancel_right v 1
  by_cases hvlast : v.val + 1 = n
  · -- The bond leaving the last site is the seam edge, stored second endpoint.
    have hnext0 : v + 1 = 0 := by
      apply Fin.ext
      rw [Fin.val_add_eq_ite, h1]
      simp only [Fin.val_zero]
      split_ifs <;> omega
    have hfst : ¬ (cycleSuccEdge hn v).1.1 = v := by
      rw [cycleSuccEdge_val_of_eq hn hvlast]
      exact add_one_ne_self hn v
    have hM : cycleRightGauge hn A X v =
        (((X (cycleSuccEdge hn v))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)ᵀ :=
      edgeGaugeAt_of_snd _ _ _ _ hfst
    rw [hM, Matrix.transpose_transpose, cycleGaugeOfEdgeGauge, if_pos hnext0, hsub]
  · -- Away from the seam the bond is stored with `v` first.
    have hfst : (cycleSuccEdge hn v).1.1 = v := by
      rw [cycleSuccEdge_val_of_lt hn (by omega : v.val + 1 < n)]
    have hnext0 : ¬ v + 1 = 0 := by
      intro h
      have hval := congrArg Fin.val h
      rw [Fin.val_add_eq_ite, h1] at hval
      simp only [Fin.val_zero] at hval
      have := v.isLt
      split_ifs at hval
      omega
    have hM : cycleRightGauge hn A X v =
        (X (cycleSuccEdge hn v) : Matrix (Fin D) (Fin D) ℂ) :=
      edgeGaugeAt_of_fst _ _ _ _ hfst
    rw [hM, cycleGaugeOfEdgeGauge, if_neg hnext0, hsub, glTranspose_coe]

/-- **Per-site component identity in per-bond gauge form.**  At a site `v` of
the closed chain, the gauge-equivalence component identity holds for all bond
assignments exactly when `B = Z_v⁻¹ A Z_{v+1}` for the per-bond gauges `Z` of
the edge family.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1631 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem cycleGauge_component_iff_matrix (hn : 3 ≤ n) (A B : MPSTensor d D)
    (X : (e : Edge (SimpleGraph.cycleGraph n)) → GL (Fin D) ℂ) (v : Fin n) :
    (∀ (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) (σ : Fin d),
      (cycleTensorOfMPS hn B).component v η σ =
        gaugeVertex (cycleTensorOfMPS hn A) X v η σ) ↔
    (∀ i : Fin d, B i =
      ((cycleGaugeOfEdgeGauge hn X v)⁻¹ : GL (Fin D) ℂ) * A i *
        (cycleGaugeOfEdgeGauge hn X (v + 1) : GL (Fin D) ℂ)) := by
  rw [cycleGauge_component_iff hn A B X v]
  refine forall_congr' fun i => ?_
  rw [cycleLeftGauge_eq hn A X v, cycleRightGauge_transpose_eq hn A X v]

/-- The per-edge gauge family of a per-bond gauge family, inverting
`cycleGaugeOfEdgeGauge`: the edge from a site to its cyclic successor carries
the transpose of the gauge of that bond, except the seam edge — stored with
its endpoints in the opposite cyclic order — which carries the inverse. -/
noncomputable def edgeGaugeOfCycleGauge (Z : Fin n → GL (Fin D) ℂ)
    (e : Edge (SimpleGraph.cycleGraph n)) : GL (Fin D) ℂ :=
  if e.1.1 + 1 = e.1.2 then glTranspose (Z e.1.2) else (Z e.1.1)⁻¹

/-- The per-bond gauges of the per-edge family of a per-bond family are the
original gauges. -/
theorem cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge (hn : 3 ≤ n)
    (Z : Fin n → GL (Fin D) ℂ) (v : Fin n) :
    cycleGaugeOfEdgeGauge hn (edgeGaugeOfCycleGauge Z) v = Z v := by
  rw [cycleGaugeOfEdgeGauge]
  by_cases hv0 : v = 0
  · rw [if_pos hv0]
    have hpair := cycleSuccEdge_val_of_eq hn (pred_zero_wrap hn hv0)
    have hcond : ¬ ((cycleSuccEdge hn (v - 1)).1.1 + 1 = (cycleSuccEdge hn (v - 1)).1.2) := by
      rw [hpair]
      change ¬ (v - 1 + 1) + 1 = v - 1
      rw [sub_add_cancel]
      intro h
      have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
      have hval := congrArg Fin.val h
      rw [Fin.val_add_eq_ite, h1, val_sub_eq_ite, h1] at hval
      have := v.isLt
      split_ifs at hval <;> omega
    rw [edgeGaugeOfCycleGauge, if_neg hcond, hpair]
    change ((Z (v - 1 + 1))⁻¹)⁻¹ = Z v
    rw [sub_add_cancel, inv_inv]
  · rw [if_neg hv0]
    have hpair := cycleSuccEdge_val_of_lt hn (pred_val_lt hn hv0)
    have hcond : (cycleSuccEdge hn (v - 1)).1.1 + 1 = (cycleSuccEdge hn (v - 1)).1.2 := by
      rw [hpair]
    rw [edgeGaugeOfCycleGauge, if_pos hcond, hpair]
    change glTranspose (glTranspose (Z (v - 1 + 1))) = Z v
    rw [sub_add_cancel, glTranspose_glTranspose]

end GaugeConversion

section Capstone

/-- A block-injective tensor with positive bond dimension is not the zero
family: some matrix of the family is nonzero. -/
theorem exists_ne_zero_of_isNBlkInjective {L : ℕ} (hL : 0 < L) (hD : 0 < D)
    {B : MPSTensor d D} (hB : MPSTensor.IsNBlkInjective B L) :
    ∃ i : Fin d, B i ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hB' : Submodule.span ℂ (Set.range fun σ : Fin L → Fin d =>
      MPSTensor.evalWord B (List.ofFn σ)) = ⊤ := hB
  have hran : (Set.range fun σ : Fin L → Fin d =>
      MPSTensor.evalWord B (List.ofFn σ)) ⊆ {0} := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    change MPSTensor.evalWord B (List.ofFn σ) ∈ ({0} : Set (Matrix (Fin D) (Fin D) ℂ))
    rw [Set.mem_singleton_iff, List.ofFn_succ, MPSTensor.evalWord_cons, hall (σ 0),
      Matrix.zero_mul]
  have hle : (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) ≤ ⊥ := by
    rw [← hB', ← Submodule.span_zero_singleton (R := ℂ)
      (M := Matrix (Fin D) (Fin D) ℂ)]
    exact Submodule.span_mono hran
  have h10 : (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    (Submodule.mem_bot ℂ).mp (hle Submodule.mem_top)
  have hentry := congrFun (congrFun h10 ⟨0, hD⟩) ⟨0, hD⟩
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-- A vanishing physical dimension contradicts block injectivity at positive
bond dimension. -/
theorem pos_d_of_isNBlkInjective {L : ℕ} (hL : 0 < L) (hD : 0 < D)
    {A : MPSTensor d D} (hA : MPSTensor.IsNBlkInjective A L) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · exfalso
    obtain ⟨i, _⟩ := exists_ne_zero_of_isNBlkInjective hL hD hA
    have := i.isLt
    omega
  · exact hd

/-- **Fundamental Theorem for translation-invariant normal MPS on a closed
chain** (arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, specialized to one site-independent tensor; strengthened
to the optimal system size of the alternative proof of its Section
`normal_alt`).

Two matrix tensors `A` and `B` on `n ≥ 2L + 1` sites, each `L`-block
injective — the matrix form of "blocking any `L` consecutive sites results
in an injective tensor" for a site-independent family — generating the same
closed-chain state at the single size `n`, are related by invertible matrices
`Z_v`, one per bond of the closed chain (`n + 1 ≡ 1`), with
`B = Z_v⁻¹ A Z_{v+1}` at every site.

The conclusion is the source corollary's per-bond gauge family.  The source
states the corollary for site-dependent families `{A_i}`, `{B_i}`; this
statement is its specialization to one repeated tensor, and the source's
translation-invariant corollary (lines 1624--1661, a single gauge `Z` with a
constant `λ`, `λ^n = 1`) is the follow-up refinement, not delivered here.

The system size is the optimal `n ≥ 2L + 1` of the source's alternative
proof (line 1623 and Section `normal_alt`, the corollary after Lemma 5),
rather than the `n ≥ 3L` of the Section-`normal` blocking route: the proof
delegates to the overlapping-window corollary
`fundamentalTheorem_normalMPS_of_overlap`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1631 of `Papers/1804.04964/paper_normal.tex`,
strengthened to `n ≥ 2L + 1` per line 1623 and Section `normal_alt`. -/
theorem fundamentalTheorem_normalMPS {n L d D : ℕ} [NeZero n] (hL : 0 < L)
    (hn : 2 * L + 1 ≤ n)
    (A B : MPSTensor d D) (hA : MPSTensor.IsNBlkInjective A L)
    (hB : MPSTensor.IsNBlkInjective B L)
    (hAB : ∀ σ : Fin n → Fin d, MPSTensor.mpv A σ = MPSTensor.mpv B σ) :
    ∃ Z : Fin n → GL (Fin D) ℂ, ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ) :=
  fundamentalTheorem_normalMPS_of_overlap hL hn A B hA hB hAB

/-- **Uniqueness clause of the Fundamental Theorem for translation-invariant
normal MPS on a closed chain** (arXiv:1804.04964, Section 3, first corollary
after the theorem labelled `normal`: the gauges `Z_i` are unique up to a
multiplicative constant).

Two families of per-bond gauges realizing the relation `B = Z_v⁻¹ A Z_{v+1}`
at every site of the closed chain of `n ≥ 3L` sites are proportional by a
single constant.  The per-edge constants come from the graph-level uniqueness
clause; the relation itself pins the ratio of consecutive constants against
the nonzero tensor `B`, merging them into one.

The source's uniqueness clause carries no system-size constraint, while this
proof keeps the `n ≥ 3L` of the graph-level uniqueness route it invokes; the
existence clause `fundamentalTheorem_normalMPS` already holds at the optimal
`n ≥ 2L + 1`.  The size-free single-gauge uniqueness is
`fundamentalTheorem_normalMPS_translationInvariant_gauge_unique`; lowering
this per-bond clause to `n ≥ 2L + 1` is tracked as a follow-up to
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, first corollary after the theorem
labelled `normal`, lines 1585--1631 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalMPS_gauge_unique {n L d D : ℕ} [NeZero n] (hL : 0 < L)
    (hn : 3 * L ≤ n) (A B : MPSTensor d D) (hA : MPSTensor.IsNBlkInjective A L)
    (hB : MPSTensor.IsNBlkInjective B L) (Z Z' : Fin n → GL (Fin D) ℂ)
    (hZ : ∀ (v : Fin n) (i : Fin d),
      B i = ((Z v)⁻¹ : GL (Fin D) ℂ) * A i * (Z (v + 1) : GL (Fin D) ℂ))
    (hZ' : ∀ (v : Fin n) (i : Fin d),
      B i = ((Z' v)⁻¹ : GL (Fin D) ℂ) * A i * (Z' (v + 1) : GL (Fin D) ℂ)) :
    ∃ c : ℂˣ, ∀ v : Fin n, (Z' v : Matrix (Fin D) (Fin D) ℂ) =
      (c : ℂ) • (Z v : Matrix (Fin D) (Fin D) ℂ) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    refine ⟨1, fun v => ?_⟩
    apply Matrix.ext
    intro a b
    exact a.elim0
  have hn3 : 3 ≤ n := by omega
  have hLn : L < n := by omega
  -- Convert each per-bond family back into a per-edge family.
  have hXrel : ∀ v : Fin n,
      ∀ (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) (σ : Fin d),
      (cycleTensorOfMPS hn3 B).component v η σ =
        gaugeVertex (cycleTensorOfMPS hn3 A) (edgeGaugeOfCycleGauge Z) v η σ := by
    intro v
    refine (cycleGauge_component_iff_matrix hn3 A B (edgeGaugeOfCycleGauge Z) v).mpr ?_
    intro i
    rw [cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge hn3 Z v,
      cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge hn3 Z (v + 1)]
    exact hZ v i
  have hXrel' : ∀ v : Fin n,
      ∀ (η : (ie : IncidentEdge (SimpleGraph.cycleGraph n) v) → Fin D) (σ : Fin d),
      (cycleTensorOfMPS hn3 B).component v η σ =
        gaugeVertex (cycleTensorOfMPS hn3 A) (edgeGaugeOfCycleGauge Z') v η σ := by
    intro v
    refine (cycleGauge_component_iff_matrix hn3 A B (edgeGaugeOfCycleGauge Z') v).mpr ?_
    intro i
    rw [cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge hn3 Z' v,
      cycleGaugeOfEdgeGauge_edgeGaugeOfCycleGauge hn3 Z' (v + 1)]
    exact hZ' v i
  -- The graph-level uniqueness gives a constant on every edge.
  have hedge : ∀ e : Edge (SimpleGraph.cycleGraph n), ∃ ce : ℂˣ,
      (edgeGaugeOfCycleGauge Z' e : Matrix (Fin D) (Fin D) ℂ) =
        (ce : ℂ) • (edgeGaugeOfCycleGauge Z e : Matrix (Fin D) (Fin D) ℂ) :=
    fun e => fundamentalTheorem_normalMPS_cycle_gauge_unique hL hn
      (cycleTensorOfMPS hn3 A) (cycleTensorOfMPS hn3 B)
      (fun s => regionBlockedTensorInjective_cycleTensorOfMPS hn3 hL hLn hD hA s)
      (fun s => regionBlockedTensorInjective_cycleTensorOfMPS hn3 hL hLn hD hB s)
      rfl (fun _ => hD) (fun _ => hD)
      (edgeGaugeOfCycleGauge Z) (edgeGaugeOfCycleGauge Z')
      (fun v η σ => hXrel v η σ) (fun v η σ => hXrel' v η σ) e
  -- Per-bond constants: transpose away from the seam, invert at the seam.
  have hprop : ∀ v : Fin n, ∃ μ : ℂˣ,
      (Z' v : Matrix (Fin D) (Fin D) ℂ) = (μ : ℂ) • (Z v : Matrix (Fin D) (Fin D) ℂ) := by
    intro v
    by_cases hv0 : v = 0
    · -- The bond entering site `0` is the seam edge, carrying the inverses.
      obtain ⟨ce, hce⟩ := hedge (cycleSuccEdge hn3 (v - 1))
      have hcond : ¬ ((cycleSuccEdge hn3 (v - 1)).1.1 + 1 = (cycleSuccEdge hn3 (v - 1)).1.2) := by
        have hpair := cycleSuccEdge_val_of_eq hn3 (pred_zero_wrap hn3 hv0)
        rw [hpair]
        change ¬ (v - 1 + 1) + 1 = v - 1
        rw [sub_add_cancel]
        intro h
        have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
        have hval := congrArg Fin.val h
        rw [Fin.val_add_eq_ite, h1, val_sub_eq_ite, h1] at hval
        have := v.isLt
        split_ifs at hval <;> omega
      have hZ1 : (cycleSuccEdge hn3 (v - 1)).1.1 = v := by
        rw [cycleSuccEdge_val_of_eq hn3 (pred_zero_wrap hn3 hv0)]
        change v - 1 + 1 = v
        rw [sub_add_cancel]
      rw [edgeGaugeOfCycleGauge, edgeGaugeOfCycleGauge, if_neg hcond, if_neg hcond, hZ1]
        at hce
      -- `hce`: the inverses are proportional; invert the proportionality.
      refine ⟨ce⁻¹, ?_⟩
      have hZval : ((Z v : Matrix (Fin D) (Fin D) ℂ)) =
          (ce : ℂ) • (Z' v : Matrix (Fin D) (Fin D) ℂ) := by
        calc (Z v : Matrix (Fin D) (Fin D) ℂ)
            = (Z' v : Matrix (Fin D) (Fin D) ℂ) *
                (((Z' v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
                (Z v : Matrix (Fin D) (Fin D) ℂ) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
          _ = (Z' v : Matrix (Fin D) (Fin D) ℂ) *
                ((ce : ℂ) • (((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
                (Z v : Matrix (Fin D) (Fin D) ℂ) := by rw [← hce]
          _ = (ce : ℂ) • ((Z' v : Matrix (Fin D) (Fin D) ℂ) *
                ((((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
                  (Z v : Matrix (Fin D) (Fin D) ℂ))) := by
              rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
          _ = (ce : ℂ) • (Z' v : Matrix (Fin D) (Fin D) ℂ) := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [hZval, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero ce),
        one_smul]
    · -- Away from the seam the bond carries the transposes.
      obtain ⟨ce, hce⟩ := hedge (cycleSuccEdge hn3 (v - 1))
      have hpair := cycleSuccEdge_val_of_lt hn3 (pred_val_lt hn3 hv0)
      have hcond : (cycleSuccEdge hn3 (v - 1)).1.1 + 1 = (cycleSuccEdge hn3 (v - 1)).1.2 := by
        rw [hpair]
      rw [edgeGaugeOfCycleGauge, edgeGaugeOfCycleGauge, if_pos hcond, if_pos hcond, hpair]
        at hce
      refine ⟨ce, ?_⟩
      have hce' : (glTranspose (Z' (v - 1 + 1)) : Matrix (Fin D) (Fin D) ℂ) =
          (ce : ℂ) • (glTranspose (Z (v - 1 + 1)) : Matrix (Fin D) (Fin D) ℂ) := hce
      rw [glTranspose_coe, glTranspose_coe, sub_add_cancel] at hce'
      have := congrArg Matrix.transpose hce'
      rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose]
        at this
  classical
  choose μ hμ using hprop
  -- The relation pins the ratio of consecutive constants against `B ≠ 0`.
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_of_isNBlkInjective hL hD hB
  -- The inverse of a proportional gauge is inversely proportional.
  have hinv : ∀ v : Fin n,
      (((Z' v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
        ((((μ v)⁻¹ : ℂˣ) : ℂ)) •
          (((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    intro v
    refine (left_inv_eq_right_inv
      (a := ((Z' v : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ?_ ?_).symm
    · calc ((((μ v)⁻¹ : ℂˣ) : ℂ) •
            (((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
            ((Z' v : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
          = (((((μ v)⁻¹ : ℂˣ) : ℂ)) * ((μ v : ℂˣ) : ℂ)) •
              ((((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
                ((Z v : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            rw [hμ v, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = 1 := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
              ← Units.val_mul, inv_mul_cancel, Units.val_one]
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hstep : ∀ v : Fin n, μ (v + 1) = μ v := by
    intro v
    -- The two gauge relations force the scalar around site `v` to be `1`.
    have hBi : B i₀ = ((((μ v)⁻¹ * μ (v + 1) : ℂˣ)) : ℂ) • B i₀ := by
      calc B i₀
          = (((Z' v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i₀ *
              ((Z' (v + 1) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := hZ' v i₀
        _ = (((((μ v)⁻¹ : ℂˣ) : ℂ)) •
              (((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) * A i₀ *
              (((μ (v + 1) : ℂˣ) : ℂ) •
                ((Z (v + 1) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            rw [← hinv v, ← hμ (v + 1)]
        _ = ((((μ v)⁻¹ * μ (v + 1) : ℂˣ)) : ℂ) •
              ((((Z v)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i₀ *
                ((Z (v + 1) : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
            rw [Units.val_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
              smul_smul]
        _ = ((((μ v)⁻¹ * μ (v + 1) : ℂˣ)) : ℂ) • B i₀ := by rw [← hZ v i₀]
    have hzero : (((((μ v)⁻¹ * μ (v + 1) : ℂˣ)) : ℂ) - 1) • B i₀ = 0 := by
      rw [sub_smul, one_smul, ← hBi, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact (inv_mul_eq_one.mp (Units.val_eq_one.mp (sub_eq_zero.mp h))).symm
    · exact absurd h hi₀
  -- All the constants agree around the cycle.
  have hconst : ∀ v : Fin n, μ v = μ 0 := by
    intro v
    obtain ⟨k, hk⟩ := v
    induction k with
    | zero => exact congrArg μ (Fin.ext (by simp))
    | succ k IH =>
      have hk' : k < n := by omega
      have hsucc : (⟨k, hk'⟩ : Fin n) + 1 = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        have h1 : ((1 : Fin n) : ℕ) = 1 := val_one_of_two_le (by omega)
        rw [Fin.val_add_eq_ite, h1]
        change (if n ≤ k + 1 then k + 1 - n else k + 1) = k + 1
        split_ifs <;> omega
      rw [← hsucc, hstep ⟨k, hk'⟩, IH hk']
  exact ⟨μ 0, fun v => by rw [hμ v, hconst v]⟩

end Capstone

end PEPS
end TNLean

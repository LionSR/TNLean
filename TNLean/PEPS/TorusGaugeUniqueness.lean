import TNLean.PEPS.TorusCovariantAbsorbedFamily
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.TorusFundamentalTheorem

/-!
# Uniqueness of the torus gauge family up to a multiplicative constant

This file formalizes the last clause of Theorem 3 of the normal PEPS Fundamental Theorem on the
torus: *"`X` and `Y` are unique up to a multiplicative constant"* (arXiv:1804.04964, Section 3,
Theorem 3, line 1471 of `Papers/1804.04964/paper_normal.tex`).  The source derives it from the
determinacy of the per-edge conjugator in the proof of the isomorphism lemma: the conjugating
matrix realizing the bond-algebra isomorphism *"is uniquely defined (up to a multiplicative
constant)"* (lines 560--583 of `Papers/1804.04964/paper_normal.tex`).

The route mirrors the source.  A gauge family realizing the bare-edge absorbed equality at an
edge `e` induces, at any region with `e` on its boundary, the region-insertion coefficient
identity in conjugation form, conjugated by the orientation-adapted absorbing gauge of `X e`
(`regionConjIdentity_of_edgeAbsorbed`); two families realizing the same bare-edge equality
therefore induce the same conjugation map (`gaugeConj_eq_of_coeffIdentities_target`), so their
absorbing gauges differ by a nonzero scalar (`gl_conj_unique_scalar`), and unwinding the
orientation adaptation gives the per-edge proportionality `X' e = c · X e`
(`torusAbsorbedGauge_unique_scalar`).

When both families are translation covariant, the per-edge scalar is transported from the
reference edge of each orientation class along the translations
(`torusCovariantAbsorbedGauge_unique_classScalar`).  The transported constant is *not* uniform
over the class in the stored edge convention: an edge wrapping the torus seam stores its
endpoints swapped, the covariance carries the transposed inverse of the class matrix there, and
the transpose-inverse of a proportionality inverts the constant.  The true class statement is
therefore one constant `c` on the edges stored in the natural cyclic order (the stored second
endpoint is the cyclic successor of the first) and `c⁻¹` on the seam edges.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Theorem 3 (line 1471) and the proof
  of the isomorphism lemma (lines 560--583) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/-! ### Scalar bookkeeping for invertible matrices -/

/-- A proportionality between invertible matrices inverts its constant on the inverses: if
`W' = c · W` entrywise, then `W'⁻¹ = c⁻¹ · W⁻¹` entrywise.  The candidate `c⁻¹ · W⁻¹` is a
two-sided inverse of `W'`, and the matrix inverse is unique.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3 (the scalar bookkeeping behind the
uniqueness clause, line 1471 of `Papers/1804.04964/paper_normal.tex`). -/
theorem gl_inv_coe_smul {n : ℕ} {W W' : GL (Fin n) ℂ} {c : ℂˣ}
    (h : (W' : Matrix (Fin n) (Fin n) ℂ) = (c : ℂ) • (W : Matrix (Fin n) (Fin n) ℂ)) :
    (↑W'⁻¹ : Matrix (Fin n) (Fin n) ℂ) =
      ((c⁻¹ : ℂˣ) : ℂ) • (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by
  have hWW : (W : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hprod : (W' : Matrix (Fin n) (Fin n) ℂ) *
      (((c⁻¹ : ℂˣ) : ℂ) • (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) = 1 := by
    rw [h, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, hWW]
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_eq_right_inv hprod]

/-- Reindexing across an index-size equality commutes with scalar multiplication. -/
theorem reindexAlgEquiv_smul {m n : ℕ} (h : m = n) (c : ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) (c • M) =
      c • Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) M := by
  simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_smul,
    Pi.smul_apply]

/-! ### The conjugation-form identity of an absorbing family -/

section CoeffBridge

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

omit [Fintype V] in
/-- The orientation-adapted absorbing gauge is an involution: absorbing twice returns the
original gauge.  Both branches are involutions — the packaged transpose and the group inverse.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem absorbedBoundaryGauge_absorbedBoundaryGauge (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (Z : GL (Fin (B.bondDim f.1)) ℂ) :
    absorbedBoundaryGauge (G := G) B R f (absorbedBoundaryGauge (G := G) B R f Z) = Z := by
  unfold absorbedBoundaryGauge
  split_ifs with h
  · exact glTranspose_glTranspose Z
  · exact inv_inv Z

/-- **The conjugation-form coefficient identity of an absorbing family.**

If the gauge family `X` realizes the bare-edge absorbed equality at the boundary edge `f.1` of a
region `R` — inserting `N` on `A`'s edge matches inserting the reindexed `N` on
`applyGauge B X`'s edge for every global physical configuration — then `A`'s region-insertion
coefficient at `R`, `f` matches `B`'s with the inserted matrix conjugated by the
orientation-adapted absorbing gauge of `X f.1`.

This inverts the production of the absorbed equality: the bare-edge identity lifts to the region
absorbed equality at `R` (`regionInsertedCoeff_eq_applyGauge_of_edge`), the gauge-absorption
bridge `regionInsertedCoeff_applyGauge` exposes the boundary conjugation, and the orientation
reconciliation `regionEdgeOrient_absorbedBoundaryGauge`, read through the involution of the
absorbing adaptation, rewrites it as conjugation by `absorbedBoundaryGauge B R f (X f.1)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionConjIdentity_of_edgeAbsorbed (A B : Tensor G d) (hbd : A.bondDim = B.bondDim)
    (X : (g : Edge G) → GL (Fin (B.bondDim g)) ℂ)
    (R : Finset V) (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hedge : ∀ (σ : V → Fin d) (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := G) A f.1 σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N))
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) B R f
        ((absorbedBoundaryGauge (G := G) B R f (X f.1) :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M *
          (↑(absorbedBoundaryGauge (G := G) B R f (X f.1))⁻¹ :
            Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ := by
  rw [regionInsertedCoeff_eq_applyGauge_of_edge A B hbd X f.1 hedge R f rfl M σ τ,
    regionInsertedCoeff_applyGauge B R X f
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ]
  have hkey := regionEdgeOrient_absorbedBoundaryGauge B R f
    (absorbedBoundaryGauge (G := G) B R f (X f.1))
    (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M)
  rw [absorbedBoundaryGauge_absorbedBoundaryGauge B R f (X f.1)] at hkey
  rw [hkey]

end CoeffBridge

/-! ### Per-edge uniqueness of the absorbing gauge up to a scalar -/

section TorusUniqueness

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **Per-edge uniqueness up to a scalar, from a comparison region.**

Two gauge families `X`, `X'` both realizing the bare-edge absorbed equality at the boundary edge
`f.1` of a region `R` at which `B` is region- and complement-injective have proportional gauges
at that edge: `X' f.1 = c · X f.1` for a nonzero scalar `c`.

Both families induce the conjugation-form coefficient identity at `R`, `f`, conjugated by their
orientation-adapted absorbing gauges (`regionConjIdentity_of_edgeAbsorbed`); the region-insertion
transfer map is determined by the identity (`gaugeConj_eq_of_coeffIdentities_target`), so the two
absorbing gauges induce the same conjugation and differ by a nonzero scalar
(`gl_conj_unique_scalar`).  Unwinding the orientation adaptation gives the proportionality of
the gauges themselves — with the inverse constant on the transposed-inverse branch, which the
final scalar absorbs.

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471, via the conjugator determinacy of the
isomorphism lemma, lines 560--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem torusAbsorbedGauge_unique_scalar_of_region
    {A B : Tensor (torusGraph width height) d} (hbd : A.bondDim = B.bondDim)
    (R : Finset (TorusVertex width height))
    (f : {f : Edge (torusGraph width height) //
      IsRegionBoundaryEdge (G := torusGraph width height) R f})
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B R)
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B (Finset.univ \ R))
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (X X' : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    (hedgeX : ∀ (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A f.1 σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N))
    (hedgeX' : ∀ (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A f.1 σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X') f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N)) :
    ∃ c : ℂˣ, (X' f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (c : ℂ) • (X f.1 : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := by
  -- The two absorbing gauges induce the same conjugation map.
  have hconj : ∀ N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ,
      (absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1) :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑(absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1))⁻¹ :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) =
      (absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1) :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) * N *
        (↑(absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1))⁻¹ :
          Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) := fun N =>
    gaugeConj_eq_of_coeffIdentities_target (A := A) (B := B) R f hRB hCB hposB
      (hE₁ := congr_fun hbd f.1) (hE₂ := congr_fun hbd f.1)
      (absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1))
      (absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1))
      (fun M σ τ => regionConjIdentity_of_edgeAbsorbed A B hbd X R f hedgeX M σ τ)
      (fun M σ τ => regionConjIdentity_of_edgeAbsorbed A B hbd X' R f hedgeX' M σ τ) N
  obtain ⟨c, hc⟩ := gl_conj_unique_scalar
    (absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1))
    (absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1)) hconj
  -- Unwind the orientation adaptation on each branch.
  by_cases hmem : f.1.1.1 ∈ R
  · refine ⟨c, ?_⟩
    have hZ : absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1) =
        glTranspose (X f.1) := by
      unfold absorbedBoundaryGauge; rw [if_pos hmem]
    have hZ' : absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1) =
        glTranspose (X' f.1) := by
      unfold absorbedBoundaryGauge; rw [if_pos hmem]
    rw [hZ, hZ', glTranspose_coe, glTranspose_coe] at hc
    have htr := congrArg Matrix.transpose hc
    rwa [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_transpose] at htr
  · refine ⟨c⁻¹, ?_⟩
    have hZ : absorbedBoundaryGauge (G := torusGraph width height) B R f (X f.1) =
        (X f.1)⁻¹ := by
      unfold absorbedBoundaryGauge; rw [if_neg hmem]
    have hZ' : absorbedBoundaryGauge (G := torusGraph width height) B R f (X' f.1) =
        (X' f.1)⁻¹ := by
      unfold absorbedBoundaryGauge; rw [if_neg hmem]
    rw [hZ, hZ'] at hc
    have hinv := gl_inv_coe_smul (W := (X f.1)⁻¹) (W' := (X' f.1)⁻¹) hc
    rwa [inv_inv, inv_inv] at hinv

/-- **Per-edge uniqueness of the absorbing gauge family, Theorem 3 uniqueness clause.**

For a translation-invariant pair `A`, `B` on the torus with the hypotheses of the torus
Fundamental Theorem (rectangular injectivity for both tensors, matched positive bond dimensions,
the same state), two gauge families `X`, `X'` both realizing the bare-edge absorbed equality at
an edge `e` are proportional at `e`: `X' e = c · X e` for a nonzero scalar `c`.

The comparison region with `e` on its boundary, together with `B`'s region and complement
injectivity, is the one produced by the witness family of `e`'s orientation class
(`exists_edgeCoeffIdentityWitness_horizontalFamily` and its vertical counterpart); the
proportionality at `e` is `torusAbsorbedGauge_unique_scalar_of_region` there.

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471 of
`Papers/1804.04964/paper_normal.tex` (*"X and Y are unique up to a multiplicative constant"*),
via the conjugator determinacy of the isomorphism lemma, lines 560--583. -/
theorem torusAbsorbedGauge_unique_scalar
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hw : 7 ≤ width) (hh : 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (X X' : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    (e : Edge (torusGraph width height))
    (hedgeX : ∀ (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A e σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (hedgeX' : ∀ (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A e σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X') e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N)) :
    ∃ c : ℂˣ, (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
      (c : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  have hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A) :=
    regionInjectivityUnionClosure_of_overlap A hposA
  have hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  rcases torusEdge_horizontal_or_vertical e with he | he
  · obtain ⟨Z, Zref, hE, ⟨w⟩⟩ := exists_edgeCoeffIdentityWitness_horizontalFamily
      (xStart := width - 5) (yStart := height - 5) hA hB hAr hBr hUA hUB (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) hbond hAB hd hposA hposB e he
    exact torusAbsorbedGauge_unique_scalar_of_region hbond w.region ⟨e, w.isBoundary⟩
      w.hRB w.hCB hposB X X' hedgeX hedgeX'
  · obtain ⟨Z, Zref, hE, ⟨w⟩⟩ := exists_edgeCoeffIdentityWitness_verticalFamily
      (xStart := width - 5) (yStart := height - 5) hA hB hAr hBr hUA hUB (by omega) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega)) hbond hAB hd hposA hposB e he
    exact torusAbsorbedGauge_unique_scalar_of_region hbond w.region ⟨e, w.isBoundary⟩
      w.hRB w.hCB hposB X X' hedgeX hedgeX'

end TorusUniqueness

/-! ### The stored-order marker of a torus edge

In the ordered edge convention a horizontal (vertical) edge is stored either in the natural
cyclic order — the stored second endpoint is the cyclic successor of the first — or, on the
edges wrapping the torus seam, with its endpoints swapped.  The marker `e.1.1.1 + 1 = e.1.2.1`
(respectively `e.1.1.2 + 1 = e.1.2.2`) reads the branch off the stored endpoints, and at a right
(up) edge it coincides with the covariance branch condition "the stored first endpoint is the
translated left (lower) endpoint". -/

section StoredOrder

variable {width height : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- At a right edge, the stored first endpoint is the left endpoint exactly when the stored
second endpoint is the cyclic right successor of the first.  For `2 < width` the two readings
agree on both storage branches.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex` (the edge convention of the torus seam). -/
theorem torusRightEdge_fst_eq_iff (hw : 2 < width) (q : TorusVertex width height) :
    (torusRightEdge q).1.1 = q ↔
      (torusRightEdge q).1.1.1 + 1 = (torusRightEdge q).1.2.1 := by
  have h20 : ((2 : ℕ) : ZMod width) ≠ 0 := by
    intro hcon
    rw [ZMod.natCast_eq_zero_iff] at hcon
    have := Nat.le_of_dvd (by norm_num) hcon
    omega
  have hends := Edge.ofAdj_endpoints (torusGraph_adj_right q.1 q.2)
  simp only [Prod.mk.eta] at hends
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Stored in the natural cyclic order.
    have h1' : (torusRightEdge q).1.1 = q := h1
    have h2' : (torusRightEdge q).1.2 = (q.1 + 1, q.2) := h2
    refine iff_of_true h1' ?_
    rw [h1', h2']
  · -- Stored with the endpoints swapped (the seam).
    have h1' : (torusRightEdge q).1.1 = (q.1 + 1, q.2) := h1
    have h2' : (torusRightEdge q).1.2 = q := h2
    refine iff_of_false ?_ ?_
    · intro hcon
      rw [h1'] at hcon
      have hx : q.1 + 1 = q.1 := congrArg Prod.fst hcon
      exact one_ne_zero (α := ZMod width)
        (add_left_cancel (a := q.1) (b := (1 : ZMod width)) (c := 0) (by rw [add_zero]; exact hx))
    · intro hcon
      rw [h1', h2'] at hcon
      have hx : q.1 + 1 + 1 = q.1 := hcon
      refine h20 (add_left_cancel (a := q.1) (b := ((2 : ℕ) : ZMod width)) (c := 0) ?_)
      push_cast
      linear_combination hx

/-- At an up edge, the stored first endpoint is the lower endpoint exactly when the stored second
endpoint is the cyclic upper successor of the first.  The vertical counterpart of
`torusRightEdge_fst_eq_iff`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem torusUpEdge_fst_eq_iff (hh : 2 < height) (q : TorusVertex width height) :
    (torusUpEdge q).1.1 = q ↔
      (torusUpEdge q).1.1.2 + 1 = (torusUpEdge q).1.2.2 := by
  have h20 : ((2 : ℕ) : ZMod height) ≠ 0 := by
    intro hcon
    rw [ZMod.natCast_eq_zero_iff] at hcon
    have := Nat.le_of_dvd (by norm_num) hcon
    omega
  have hends := Edge.ofAdj_endpoints (torusGraph_adj_up q.1 q.2)
  simp only [Prod.mk.eta] at hends
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (torusUpEdge q).1.1 = q := h1
    have h2' : (torusUpEdge q).1.2 = (q.1, q.2 + 1) := h2
    refine iff_of_true h1' ?_
    rw [h1', h2']
  · have h1' : (torusUpEdge q).1.1 = (q.1, q.2 + 1) := h1
    have h2' : (torusUpEdge q).1.2 = q := h2
    refine iff_of_false ?_ ?_
    · intro hcon
      rw [h1'] at hcon
      have hy : q.2 + 1 = q.2 := congrArg Prod.snd hcon
      exact one_ne_zero (α := ZMod height)
        (add_left_cancel (a := q.2) (b := (1 : ZMod height)) (c := 0) (by rw [add_zero]; exact hy))
    · intro hcon
      rw [h1', h2'] at hcon
      have hy : q.2 + 1 + 1 = q.2 := hcon
      refine h20 (add_left_cancel (a := q.2) (b := ((2 : ℕ) : ZMod height)) (c := 0) ?_)
      push_cast
      linear_combination hy

end StoredOrder

/-! ### Class constancy of the per-edge scalar for covariant families -/

section ClassScalar

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **Class constancy of the per-edge scalar for translation-covariant families.**

Two translation-covariant gauge families `X`, `X'` both realizing the bare-edge absorbed
equality at every torus edge are related by one constant per orientation class, transported
along the translations: there are nonzero scalars `c_h`, `c_v` such that on every horizontal
edge stored in the natural cyclic order `X' e = c_h · X e`, on every horizontal edge wrapping
the seam (stored with swapped endpoints) `X' e = c_h⁻¹ · X e`, and likewise for the vertical
class with `c_v`.

The constants are the per-edge scalars at the two reference edges
(`torusAbsorbedGauge_unique_scalar`); the covariance transports the reference proportionality to
every translate.  On a translate preserving the stored endpoint order the covariance is a
reindexing, which commutes with the scalar; on a translate swapping the order it is a
reindexed transposed inverse, and the transpose-inverse of a proportionality inverts the
constant (`gl_inv_coe_smul`).  The inversion on the seam is forced: a single constant on the
whole class is *not* the true statement in the ordered edge convention.

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471 of
`Papers/1804.04964/paper_normal.tex` (*"X and Y are unique up to a multiplicative constant"*,
with `X`, `Y` the class matrices), via the conjugator determinacy of the isomorphism lemma,
lines 560--583. -/
theorem torusCovariantAbsorbedGauge_unique_classScalar
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hw : 7 ≤ width) (hh : 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (X X' : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    (hXcov : IsTranslationCovariantGaugeFamily B X)
    (hX'cov : IsTranslationCovariantGaugeFamily B X')
    (hedgeX : ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A e σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (hedgeX' : ∀ (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
      (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := torusGraph width height) A e σ N =
        edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X') e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N)) :
    ∃ ch cv : ℂˣ,
      (∀ e : Edge (torusGraph width height), IsHorizontalTorusEdge e →
        (e.1.1.1 + 1 = e.1.2.1 →
          (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
            (ch : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) ∧
        (e.1.1.1 + 1 ≠ e.1.2.1 →
          (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
            ((ch⁻¹ : ℂˣ) : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))) ∧
      (∀ e : Edge (torusGraph width height), IsVerticalTorusEdge e →
        (e.1.1.2 + 1 = e.1.2.2 →
          (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
            (cv : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)) ∧
        (e.1.1.2 + 1 ≠ e.1.2.2 →
          (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
            ((cv⁻¹ : ℂˣ) : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ))) := by
  have hw2 : 2 < width := by omega
  have hh2 : 2 < height := by omega
  -- The seam-touching reference anchors of the two orientation classes.
  set xhStart := width - 5 with hxhdef
  set yhStart := height - 5 with hyhdef
  -- The reference-edge scalars of the two orientation classes.
  obtain ⟨ch, hch⟩ := torusAbsorbedGauge_unique_scalar hA hB hAr hBr hw hh
    hbond hAB hd hposA hposB X X'
    (torusHorizontalReferenceEdge xhStart yhStart) (hedgeX _) (hedgeX' _)
  obtain ⟨cv, hcv⟩ := torusAbsorbedGauge_unique_scalar hA hB hAr hBr hw hh
    hbond hAB hd hposA hposB X X'
    (torusVerticalReferenceEdge xhStart yhStart) (hedgeX _) (hedgeX' _)
  refine ⟨ch, cv, ?_, ?_⟩
  · -- The horizontal class.
    intro e he
    obtain ⟨⟨a, b⟩, rfl⟩ := translate_horizontalReferenceEdge (xStart := xhStart)
      (yStart := yhStart) he
    -- The stored first endpoint of the (non-wrapping) reference edge is its left endpoint.
    have hfst : (torusHorizontalReferenceEdge (width := width) (height := height)
        xhStart yhStart).1.1 =
        (((xhStart + 1 : ℕ) : ZMod width), ((yhStart + 2 : ℕ) : ZMod height)) :=
      (torusRightEdge_endpoints_of_lt
        (p := (((xhStart + 1 : ℕ) : ZMod width), ((yhStart + 2 : ℕ) : ZMod height)))
        (by show ((xhStart + 1 : ℕ) : ZMod width).val + 1 < width
            rw [ZMod.val_cast_of_lt (by omega : xhStart + 1 < width)]
            omega)).1
    -- The translated reference edge is the right edge at the translated left endpoint.
    have hEeq : Edge.map (translate a b)
        (torusHorizontalReferenceEdge (width := width) (height := height) xhStart yhStart) =
        torusRightEdge ((((xhStart + 1 : ℕ) : ZMod width) + a),
          (((yhStart + 2 : ℕ) : ZMod height) + b)) := by
      rw [← translateEdge_eq_map, torusHorizontalReferenceEdge, translateEdge_torusRightEdge]
    have hq : translate a b (torusHorizontalReferenceEdge (width := width) (height := height)
        xhStart yhStart).1.1 =
        ((((xhStart + 1 : ℕ) : ZMod width) + a), (((yhStart + 2 : ℕ) : ZMod height) + b)) := by
      rw [hfst, translate_apply]
    -- The covariance branch condition is the stored-order marker of the translated edge.
    have hiff : ((Edge.map (translate a b) (torusHorizontalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1 =
        translate a b (torusHorizontalReferenceEdge (width := width) (height := height)
          xhStart yhStart).1.1) ↔
        ((Edge.map (translate a b) (torusHorizontalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1.1 + 1 =
        (Edge.map (translate a b) (torusHorizontalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.2.1) := by
      rw [hq, hEeq]
      exact torusRightEdge_fst_eq_iff hw2 _
    -- The two covariance equations at the translated edge.
    have hbde : B.bondDim (Edge.map (translate a b) (torusHorizontalReferenceEdge
        (width := width) (height := height) xhStart yhStart)) =
        B.bondDim (torusHorizontalReferenceEdge (width := width) (height := height)
          xhStart yhStart) := by
      rw [← translateEdge_eq_map]
      exact bondDim_translateEdge_of_translationInvariant hB a b _
    have hXe := hXcov a b (torusHorizontalReferenceEdge xhStart yhStart) hbde.symm
    have hX'e := hX'cov a b (torusHorizontalReferenceEdge xhStart yhStart) hbde.symm
    constructor
    · intro hintr
      rw [hX'e, hXe, if_pos (hiff.mpr hintr), if_pos (hiff.mpr hintr), glReindex_coe,
        glReindex_coe, hch, reindexAlgEquiv_smul]
    · intro hintr
      have hcond : ¬((Edge.map (translate a b) (torusHorizontalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1 =
          translate a b (torusHorizontalReferenceEdge (width := width) (height := height)
            xhStart yhStart).1.1) := fun hcon => hintr (hiff.mp hcon)
      rw [hX'e, hXe, if_neg hcond, if_neg hcond, glReindex_coe, glReindex_coe]
      have htr : (glTranspose (X' (torusHorizontalReferenceEdge xhStart yhStart)) :
          Matrix (Fin (B.bondDim (torusHorizontalReferenceEdge xhStart yhStart)))
            (Fin (B.bondDim (torusHorizontalReferenceEdge xhStart yhStart))) ℂ) =
          (ch : ℂ) • (glTranspose (X (torusHorizontalReferenceEdge xhStart yhStart)) :
          Matrix (Fin (B.bondDim (torusHorizontalReferenceEdge xhStart yhStart)))
            (Fin (B.bondDim (torusHorizontalReferenceEdge xhStart yhStart))) ℂ) := by
        rw [glTranspose_coe, glTranspose_coe, hch, Matrix.transpose_smul]
      rw [gl_inv_coe_smul htr, reindexAlgEquiv_smul]
  · -- The vertical class.
    intro e he
    obtain ⟨⟨a, b⟩, rfl⟩ := translate_verticalReferenceEdge (xStart := xhStart)
      (yStart := yhStart) he
    have hfst : (torusVerticalReferenceEdge (width := width) (height := height)
        xhStart yhStart).1.1 =
        (((xhStart + 2 : ℕ) : ZMod width), ((yhStart + 1 : ℕ) : ZMod height)) :=
      (torusUpEdge_endpoints_of_lt
        (p := (((xhStart + 2 : ℕ) : ZMod width), ((yhStart + 1 : ℕ) : ZMod height)))
        (by show ((yhStart + 1 : ℕ) : ZMod height).val + 1 < height
            rw [ZMod.val_cast_of_lt (by omega : yhStart + 1 < height)]
            omega)).1
    have hEeq : Edge.map (translate a b)
        (torusVerticalReferenceEdge (width := width) (height := height) xhStart yhStart) =
        torusUpEdge ((((xhStart + 2 : ℕ) : ZMod width) + a),
          (((yhStart + 1 : ℕ) : ZMod height) + b)) := by
      rw [← translateEdge_eq_map, torusVerticalReferenceEdge, translateEdge_torusUpEdge]
    have hq : translate a b (torusVerticalReferenceEdge (width := width) (height := height)
        xhStart yhStart).1.1 =
        ((((xhStart + 2 : ℕ) : ZMod width) + a), (((yhStart + 1 : ℕ) : ZMod height) + b)) := by
      rw [hfst, translate_apply]
    have hiff : ((Edge.map (translate a b) (torusVerticalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1 =
        translate a b (torusVerticalReferenceEdge (width := width) (height := height)
          xhStart yhStart).1.1) ↔
        ((Edge.map (translate a b) (torusVerticalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1.2 + 1 =
        (Edge.map (translate a b) (torusVerticalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.2.2) := by
      rw [hq, hEeq]
      exact torusUpEdge_fst_eq_iff hh2 _
    have hbde : B.bondDim (Edge.map (translate a b) (torusVerticalReferenceEdge
        (width := width) (height := height) xhStart yhStart)) =
        B.bondDim (torusVerticalReferenceEdge (width := width) (height := height)
          xhStart yhStart) := by
      rw [← translateEdge_eq_map]
      exact bondDim_translateEdge_of_translationInvariant hB a b _
    have hXe := hXcov a b (torusVerticalReferenceEdge xhStart yhStart) hbde.symm
    have hX'e := hX'cov a b (torusVerticalReferenceEdge xhStart yhStart) hbde.symm
    constructor
    · intro hintr
      rw [hX'e, hXe, if_pos (hiff.mpr hintr), if_pos (hiff.mpr hintr), glReindex_coe,
        glReindex_coe, hcv, reindexAlgEquiv_smul]
    · intro hintr
      have hcond : ¬((Edge.map (translate a b) (torusVerticalReferenceEdge (width := width)
          (height := height) xhStart yhStart)).1.1 =
          translate a b (torusVerticalReferenceEdge (width := width) (height := height)
            xhStart yhStart).1.1) := fun hcon => hintr (hiff.mp hcon)
      rw [hX'e, hXe, if_neg hcond, if_neg hcond, glReindex_coe, glReindex_coe]
      have htr : (glTranspose (X' (torusVerticalReferenceEdge xhStart yhStart)) :
          Matrix (Fin (B.bondDim (torusVerticalReferenceEdge xhStart yhStart)))
            (Fin (B.bondDim (torusVerticalReferenceEdge xhStart yhStart))) ℂ) =
          (cv : ℂ) • (glTranspose (X (torusVerticalReferenceEdge xhStart yhStart)) :
          Matrix (Fin (B.bondDim (torusVerticalReferenceEdge xhStart yhStart)))
            (Fin (B.bondDim (torusVerticalReferenceEdge xhStart yhStart))) ℂ) := by
        rw [glTranspose_coe, glTranspose_coe, hcv, Matrix.transpose_smul]
      rw [gl_inv_coe_smul htr, reindexAlgEquiv_smul]

end ClassScalar

/-! ### The bare-edge absorbed equality from the per-vertex relation

The torus Fundamental Theorem's per-vertex relation `A_v = λ · (gauge action of B)_v` with
`λ^{nm} = 1` already implies the bare-edge absorbed equality at every edge: the edge-inserted
coefficient is multilinear in the vertex tensors, so scaling every vertex by `λ` scales the
coefficient by `λ^{nm} = 1`.  The uniqueness of the gauge family therefore holds against the
per-vertex relation itself, the literal display `B = λ · (X, Y)A` of the source. -/

section PerVertex

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

open scoped Classical in
/-- **Multilinearity of the edge-inserted coefficient in the vertex tensors.**

If every component of `A` is `λ` times the corresponding component of `C` (carried across the
bond-dimension equality), then every edge-inserted coefficient of `A` is `λ^{|V|}` times that of
the reindexed `C`: the coefficient is a sum of products with one component factor per vertex.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex` (the per-vertex relation scales the closed contraction by
one factor of `λ` per site). -/
theorem edgeInsertedCoeff_eq_pow_card_mul_reindexTensor (A C : Tensor G d)
    (hbd : A.bondDim = C.bondDim) (lam : ℂ)
    (hcomp : ∀ (v : V) (η : (ie : IncidentEdge G v) → Fin (A.bondDim ie.1)) (σp : Fin d),
      A.component v η σp =
        lam * C.component v (fun ie => Fin.cast (congr_fun hbd ie.1) (η ie)) σp)
    (e : Edge G) (σ : V → Fin d) (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := G) A e σ N =
      lam ^ (Fintype.card V) *
        edgeInsertedCoeff (G := G) (reindexTensor (G := G) C hbd) e σ N := by
  classical
  rw [edgeInsertedCoeff_eq_doubled, edgeInsertedCoeff_eq_doubled, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ (fun x => ?_)
  simp only [Equiv.refl_apply]
  obtain ⟨i, k, ζ⟩ := x
  have hterm : (∏ v : V, A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v)) =
      lam ^ (Fintype.card V) *
        ∏ v : V, (reindexTensor (G := G) C hbd).component v
          (localOfDoubled (G := G) (reindexTensor (G := G) C hbd) e i k ζ v) (σ v) :=
    calc (∏ v : V, A.component v (localOfDoubled (G := G) A e i k ζ v) (σ v))
        = ∏ v : V, lam * (reindexTensor (G := G) C hbd).component v
            (localOfDoubled (G := G) (reindexTensor (G := G) C hbd) e i k ζ v) (σ v) :=
          Finset.prod_congr rfl
            (fun v _ => hcomp v (localOfDoubled (G := G) A e i k ζ v) (σ v))
      _ = (∏ _v : V, lam) * ∏ v : V, (reindexTensor (G := G) C hbd).component v
            (localOfDoubled (G := G) (reindexTensor (G := G) C hbd) e i k ζ v) (σ v) :=
          Finset.prod_mul_distrib
      _ = lam ^ (Fintype.card V) *
            ∏ v : V, (reindexTensor (G := G) C hbd).component v
              (localOfDoubled (G := G) (reindexTensor (G := G) C hbd) e i k ζ v) (σ v) := by
          rw [Finset.prod_const, Finset.card_univ]
  rw [hterm]
  ring

end PerVertex

section TorusPerVertex

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The bare-edge absorbed equality from the per-vertex relation.**

If `A` satisfies the per-vertex relation `A_v = λ · (gauge action of B at v)` at every torus
vertex with `λ^{nm} = 1`, then the bare-edge absorbed equality holds at every edge: inserting
`N` on `A`'s edge matches inserting the reindexed `N` on `applyGauge B X`'s edge.  The
edge-inserted coefficient picks up one factor of `λ` per site
(`edgeInsertedCoeff_eq_pow_card_mul_reindexTensor`), and `λ^{nm} = 1`.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1471 of
`Papers/1804.04964/paper_normal.tex` (the displayed relation `B = λ · (X, Y)A` with
`λ^{n·m} = 1`). -/
theorem edgeAbsorbed_of_perVertex
    {A B : Tensor (torusGraph width height) d} (hbond : A.bondDim = B.bondDim)
    (X : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ) {lam : ℂ}
    (hPV : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam : lam ^ (width * height) = 1)
    (e : Edge (torusGraph width height)) (σ : TorusVertex width height → Fin d)
    (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    edgeInsertedCoeff (G := torusGraph width height) A e σ N =
      edgeInsertedCoeff (G := torusGraph width height) (applyGauge B X) e σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  have hscale := edgeInsertedCoeff_eq_pow_card_mul_reindexTensor A (applyGauge B X) hbond lam
    hPV e σ N
  rw [hscale, edgeInsertedCoeff_reindexTensor (applyGauge B X) hbond e σ N,
    card_torusVertex width height, hlam, one_mul]
  rfl

/-- **Uniqueness of the gauge family against the per-vertex relation.**

If two gauge families `X`, `X'` each realize the per-vertex relation of the torus Fundamental
Theorem — `A_v = λ · (gauge action of B at v)` with `λ^{nm} = 1`, the source's display
`B = λ · (X, Y)A` — then they are proportional at every edge: `X' e = c · X e` for a nonzero
scalar `c`.  Each per-vertex relation yields the bare-edge absorbed equality
(`edgeAbsorbed_of_perVertex`), and the absorbed equalities determine the gauge up to a scalar
(`torusAbsorbedGauge_unique_scalar`).

Source: arXiv:1804.04964, Section 3, Theorem 3, line 1471 of
`Papers/1804.04964/paper_normal.tex` (*"X and Y are unique up to a multiplicative constant"*). -/
theorem torusGauge_unique_scalar_of_perVertex
    {A B : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (hB : IsTorusTranslationInvariant B)
    (hAr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hBr : NormalTorusRectangleInjectivityHypotheses
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hw : 7 ≤ width) (hh : 7 ≤ height)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (X X' : (g : Edge (torusGraph width height)) → GL (Fin (B.bondDim g)) ℂ)
    {lam lam' : ℂ}
    (hPV : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam : lam ^ (width * height) = 1)
    (hPV' : ∀ (v : TorusVertex width height)
      (η : (ie : IncidentEdge (torusGraph width height) v) → Fin (A.bondDim ie.1))
      (σ : Fin d),
      A.component v η σ =
        lam' * gaugeVertex B X' v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ)
    (hlam' : lam' ^ (width * height) = 1)
    (e : Edge (torusGraph width height)) :
    ∃ c : ℂˣ, (X' e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) =
      (c : ℂ) • (X e : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) :=
  torusAbsorbedGauge_unique_scalar hA hB hAr hBr hw hh hbond hAB hd hposA hposB X X' e
    (edgeAbsorbed_of_perVertex hbond X hPV hlam e)
    (edgeAbsorbed_of_perVertex hbond X' hPV' hlam' e)

end TorusPerVertex

end PEPS
end TNLean

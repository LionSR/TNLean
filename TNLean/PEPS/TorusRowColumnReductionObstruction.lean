import TNLean.MPS.Defs

/-!
# The row-and-column reduction cannot factor the row-cut gauge

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) concludes a per-edge gauge
`B^i = λ · (X ⊗ Y) A^i (X⁻¹ ⊗ Y⁻¹)`, with `X` on the horizontal virtual legs
and `Y` on the vertical ones.  A natural route reduces this corollary to the
formalized one-dimensional matrix product state corollary applied row-wise and
column-wise: contract each torus row over its horizontal bonds into a single
super-site, obtaining a matrix product state tensor on the super-physical space
`(Fin d)^width` with super-bond space the collected vertical bonds, and apply
the one-dimensional Fundamental Theorem to the resulting closed chain of `m`
super-sites.

That application delivers **one** conjugating matrix `Z` on the whole collected
vertical-bond space together with a root of unity, with `B`-super-tensor equal
to the `Z`-conjugate of the `A`-super-tensor.  To reach the per-edge conclusion
the matrix `Z` would have to factor as a tensor product `⨂ Y_x` of one gauge per
vertical edge.  This file records, with a machine-checked refutation, that the
one-dimensional reduction does **not** force that factorization: the
super-tensor relation produced by the row reduction is invariant under
conjugation by an arbitrary invertible matrix of the collected bond space, and
an arbitrary invertible matrix of a tensor-product space is not a tensor
product even up to a scalar.

## The conjugation-invariance obstruction

The one-dimensional reduction reads the row super-tensor only as an abstract
family of matrices on the collected vertical-bond space, together with the
closed-chain trace coefficients (the torus state).  Both of these inputs are
*conjugation invariant*: if `A` is a normal matrix product state tensor and `G`
is any invertible matrix of the bond space, the conjugate family
`B^i = G⁻¹ A^i G` has the same closed-chain coefficients (the trace is invariant
under conjugation) and the same block injectivity (conjugation by an invertible
matrix preserves the span of any family).  So the row reduction cannot
distinguish a per-edge-gauged `B` from a `B` produced by an arbitrary,
non-product conjugation `G`; only the former has the per-edge conclusion.

Because the `A`-super-tensor here is injective, its only self-conjugations are
the scalars, so the conjugating matrix of the reduction is `G` up to a nonzero
scalar.  When `G` is not a tensor product even after rescaling, no per-edge
factorization of the reduction's gauge exists.  The witness below makes this
concrete on the smallest collected-bond space carrying two vertical edges,
`Fin 2 × Fin 2`: the matrix-unit family `A` is injective at block length one,
and the conjugator `G` is a "controlled" invertible matrix whose four
`Fin 2 × Fin 2` blocks are not mutually proportional, hence not a scalar times
any tensor product.

The companion route through a column-wise application does not repair this: a
single column cut crosses the horizontal edges of one column boundary, an
entirely disjoint set of bonds from the vertical edges crossed by a row cut, so
the row-cut gauge on the vertical-bond space and the column-cut gauge on the
horizontal-bond space share no bond and impose no consistency equation on each
other.  The factorization the per-edge conclusion needs is therefore not forced
by either application, nor by the two together.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and
  proof sketch at lines 2296--2445 of `Papers/1804.04964/paper_normal.tex`,
  whose one-dimensional engine is the overlapping-window corollary
  `fundamentalTheorem_normalMPSChain_of_overlap`](https://arxiv.org/abs/1804.04964);
  the row-and-column reduction and the absence of a coherence question are
  discussed in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the section "No
  coherence question between rows".
-/

open scoped Matrix

namespace TNLean
namespace PEPS
namespace RowColumnReductionObstruction

open MPSTensor

/-! ### The collected-bond space and its tensor-product reading

The smallest collected vertical-bond space carrying two vertical edges is
`Fin 4`, read as `Fin 2 × Fin 2` through the pairing `(r, s) ↦ 2 * r + s`.  A
*per-edge gauge* on this space is a tensor product `Y₀ ⊗ Y₁` of one `Fin 2`
gauge per edge; in entry form `(Y₀ ⊗ Y₁)_{(r,s),(r',s')} = (Y₀)_{r r'} (Y₁)_{s s'}`.
We do not need the general Kronecker product: the obstruction is a property of the
four `2 × 2` blocks `M_{r r'}` of a `4 × 4` matrix `M`, `(M_{r r'})_{s s'} =
M_{(2r+s),(2r'+s')}`, namely that a product has all four blocks proportional to
the single factor `Y₁`. -/

/-- The `(r, s)` index of `Fin 4` under the pairing `(r, s) ↦ 2 * r + s`. -/
def pair (r s : Fin 2) : Fin 4 := ⟨2 * r.val + s.val, by omega⟩

/-- The `(s', s)` entry of the `(r', r)` block of a `4 × 4` matrix under the
pairing.  A matrix is a per-edge product `Y₀ ⊗ Y₁` exactly when every block
`blockEntry M r r'` equals `(Y₀)_{r r'} • Y₁` for fixed gauges `Y₀, Y₁`. -/
def blockEntry (M : Matrix (Fin 4) (Fin 4) ℂ) (r r' : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun s s' => M (pair r s) (pair r' s')

/-- `M` is a *per-edge product matrix* when it factors as a tensor product of one
`Fin 2`-gauge per vertical edge: there are matrices `Y₀, Y₁` with every entry
`M_{(r,s),(r',s')} = (Y₀)_{r r'} (Y₁)_{s s'}`. -/
def IsPerEdgeProduct (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ Y₀ Y₁ : Matrix (Fin 2) (Fin 2) ℂ,
    ∀ r s r' s' : Fin 2, M (pair r s) (pair r' s') = Y₀ r r' * Y₁ s s'

/-- In a per-edge product matrix the two diagonal blocks `(0,0)` and `(0,1)` are
proportional: `(Y₀)_{0 1} • blockEntry M 0 0 = (Y₀)_{0 0} • blockEntry M 0 1`,
since each block is a scalar multiple of the common factor `Y₁`. -/
theorem blocks_proportional_of_isPerEdgeProduct {M : Matrix (Fin 4) (Fin 4) ℂ}
    (h : IsPerEdgeProduct M) (s s' : Fin 2) :
    blockEntry M 0 0 s s' * blockEntry M 0 1 1 1 =
      blockEntry M 0 1 s s' * blockEntry M 0 0 1 1 := by
  obtain ⟨Y₀, Y₁, hY⟩ := h
  simp only [blockEntry, hY]
  ring

/-! ### The non-product conjugator

The witness conjugator is the "controlled" invertible matrix `Gmat`: the identity
with one extra entry coupling the two edges.  Read as a block matrix under the
pairing, its `(0,0)` block is the identity and its `(0,1)` block is the single
matrix `single 0 0 1`; these two blocks are not proportional, so `Gmat` is not a
per-edge product even after rescaling. -/

/-- The controlled invertible conjugator: the `4 × 4` identity with one coupling
entry `Gmat (pair 0 0) (pair 1 0) = 1`, i.e. row `0`, column `2`. -/
def Gmat : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The inverse of `Gmat`: the identity with the coupling entry negated. -/
def Ginv : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, -1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem Gmat_mul_Ginv : Gmat * Ginv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Gmat, Ginv, Matrix.mul_apply, Fin.sum_univ_four]

theorem Ginv_mul_Gmat : Ginv * Gmat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Gmat, Ginv, Matrix.mul_apply, Fin.sum_univ_four]

/-- The conjugator as an element of the general linear group of the bond space. -/
def Gunit : GL (Fin 4) ℂ where
  val := Gmat
  inv := Ginv
  val_inv := Gmat_mul_Ginv
  inv_val := Ginv_mul_Gmat

@[simp] theorem Gunit_val : (Gunit : Matrix (Fin 4) (Fin 4) ℂ) = Gmat := rfl

@[simp] theorem Gunit_inv_val :
    ((Gunit⁻¹ : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = Ginv := rfl

/-- The two diagonal blocks of `Gmat` are not proportional: at `(s, s') = (0, 0)`
the block-proportionality identity reads `0 = 1`.  No per-edge product matrix can
satisfy it, and rescaling `Gmat` by any nonzero scalar leaves it unsatisfied. -/
theorem Gmat_blocks_not_proportional :
    blockEntry Gmat 0 0 0 0 * blockEntry Gmat 0 1 1 1 ≠
      blockEntry Gmat 0 1 0 0 * blockEntry Gmat 0 0 1 1 := by
  simp only [blockEntry, Gmat, pair]
  norm_num

/-! ### The injective row super-tensor and its non-product conjugate

The injective `A`-super-tensor of the refutation is the matrix-unit family on the
bond space `Fin 4`, indexed by the physical super-index `Fin 16 ≃ Fin 4 × Fin 4`.
Its range is all single matrices, which span the whole matrix algebra, so it is
injective at block length one (`Aunits_isNBlkInjective`).  The conjugate
`Bunits i = Ginv (Aunits i) Gmat` has the same closed-chain coefficients
(`sameMPV`) and the same block injectivity, but the conjugator is `Gunit`, not a
per-edge product. -/


/-- The physical super-index `Fin 16` read as a pair `Fin 4 × Fin 4`. -/
def physEquiv : Fin 16 ≃ Fin 4 × Fin 4 := (finProdFinEquiv (m := 4) (n := 4)).symm

/-- The matrix-unit super-tensor: the physical index `k : Fin 16` decodes to a pair
`(a, b) : Fin 4 × Fin 4`, and `Aunits k = single a b 1`.  Its range is the set of
all matrix units. -/
noncomputable def Aunits : MPSTensor 16 4 :=
  fun k => Matrix.single (physEquiv k).1 (physEquiv k).2 1

/-- The conjugate super-tensor `Bunits i = Gunit⁻¹ (Aunits i) Gunit`. -/
noncomputable def Bunits : MPSTensor 16 4 :=
  fun i => (Gunit⁻¹ : GL (Fin 4) ℂ) * Aunits i * (Gunit : GL (Fin 4) ℂ)

/-- Every matrix unit `single a b 1` is a value of `Aunits`, at the encoded physical
index `finProdFinEquiv (a, b)`. -/
theorem Aunits_finProd (a b : Fin 4) :
    Aunits (finProdFinEquiv (a, b)) = Matrix.single a b 1 := by
  simp [Aunits, physEquiv]

/-- Every matrix unit lies in the span of the range of `Aunits`, since it is a value
of `Aunits`. -/
theorem single_mem_span_Aunits (a b : Fin 4) :
    Matrix.single a b (1 : ℂ) ∈ Submodule.span ℂ (Set.range Aunits) :=
  Aunits_finProd a b ▸ Submodule.subset_span ⟨finProdFinEquiv (a, b), rfl⟩

/-- `Aunits` is injective: its range spans the whole matrix algebra, since it
contains every matrix unit. -/
theorem Aunits_isInjective : IsInjective Aunits := by
  rw [IsInjective, eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ => ?_))
  rw [show Matrix.single a b (M a b) = M a b • Matrix.single a b (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (single_mem_span_Aunits a b)

/-- `Aunits` is injective at block length one. -/
theorem Aunits_isNBlkInjective : IsNBlkInjective Aunits 1 :=
  isNBlkInjective_one_of_isInjective Aunits_isInjective

/-- `Bunits` is the `Gunit⁻¹`-gauge of `Aunits`. -/
theorem gaugeEquiv_Aunits_Bunits : GaugeEquiv Aunits Bunits :=
  ⟨Gunit⁻¹, fun i => by rw [Bunits, inv_inv]⟩

/-- `Aunits` and `Bunits` generate the same matrix product vector family: gauge
equivalence preserves every closed-chain coefficient. -/
theorem sameMPV_Aunits_Bunits : SameMPV Aunits Bunits :=
  gaugeEquiv_Aunits_Bunits.sameMPV

/-- `Bunits` is injective at block length one: gauge equivalence preserves
injectivity, since conjugation by an invertible matrix maps a spanning family to a
spanning family. -/
theorem Bunits_isNBlkInjective : IsNBlkInjective Bunits 1 :=
  isNBlkInjective_one_of_isInjective
    (isInjective_of_gaugeEquiv Aunits_isInjective gaugeEquiv_Aunits_Bunits)

/-! ### The route's required principle and its refutation

The one-dimensional row reduction delivers a conjugating matrix `Z` and a root of
unity `lam` with `B^i = lam • (Z⁻¹ A^i Z)`; this is the conclusion of the
formalized translation-invariant corollary
(`fundamentalTheorem_normalMPS_translationInvariant`).  To reach the per-edge
two-dimensional conclusion the route additionally needs that conjugator `Z` to be
a per-edge product matrix.  The principle below packages exactly that requirement;
the refutation shows it is false. -/

/-- The strengthening the row-and-column reduction would need: for every injective
super-tensor `A` and every same-state injective super-tensor `B`, the conjugator of
the one-dimensional reduction can be taken to be a per-edge product matrix.  This is
the one-dimensional corollary's conclusion with the extra demand that the gauge
factor over the vertical edges. -/
def RowCutGaugeFactorizes : Prop :=
  ∀ A B : MPSTensor 16 4, IsNBlkInjective A 1 → IsNBlkInjective B 1 → SameMPV A B →
    ∃ (Z : GL (Fin 4) ℂ) (lam : ℂ),
      IsPerEdgeProduct (Z : Matrix (Fin 4) (Fin 4) ℂ) ∧
        ∀ i : Fin 16, B i =
          lam • (((Z⁻¹ : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) * A i *
            (Z : Matrix (Fin 4) (Fin 4) ℂ))

/-- **The row-cut gauge does not factor into per-edge gauges.**

The principle the row-and-column reduction needs is false.  For the matrix-unit
super-tensor `Aunits` and its non-product conjugate `Bunits` — both injective, with
the same closed-chain coefficients — any conjugator `Z` realizing the relation
`Bunits i = lam • (Z⁻¹ Aunits i Z)` is, because `Aunits` is injective, the
controlled matrix `Gmat` up to a nonzero scalar.  No scalar multiple of `Gmat` is a
per-edge product, since the `(0,0)` and `(0,1)` blocks of `Gmat` are not
proportional.  Hence no per-edge product conjugator exists, and the row reduction
cannot deliver the two-dimensional per-edge conclusion.

This is the precise, machine-checked verdict that the row-and-column reduction is
*not* a route to the two-dimensional overlapping-window corollary of
arXiv:1804.04964.  Documented in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
the section "No coherence question between rows". -/
theorem rowCutGaugeFactorizes_false : ¬ RowCutGaugeFactorizes := by
  intro hRoute
  obtain ⟨Z, lam, hprod, hrel⟩ :=
    hRoute Aunits Bunits Aunits_isNBlkInjective Bunits_isNBlkInjective sameMPV_Aunits_Bunits
  -- Specialize the relation to the matrix units and clear the inverse on the left.
  -- `Z * (Ginv (single a b 1) Gmat) = lam • (single a b 1 * Z)`.
  have hZrel : ∀ a b : Fin 4,
      (Z : Matrix (Fin 4) (Fin 4) ℂ) *
        (Ginv * Matrix.single a b 1 * Gmat) =
      lam • (Matrix.single a b (1 : ℂ) * (Z : Matrix (Fin 4) (Fin 4) ℂ)) := by
    intro a b
    have h := hrel (finProdFinEquiv (a, b))
    rw [Bunits, Aunits_finProd] at h
    simp only [Gunit_inv_val, Gunit_val] at h
    -- `h : Ginv (single a b 1) Gmat = lam • (Z⁻¹ (single a b 1) Z)`.
    rw [h, Matrix.mul_smul]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  -- Set `W = Z * Ginv`.  Then `W (single a b 1) = lam • (single a b 1 * W)`.
  set W : Matrix (Fin 4) (Fin 4) ℂ := (Z : Matrix (Fin 4) (Fin 4) ℂ) * Ginv with hW
  have hWcomm : ∀ a b : Fin 4,
      W * Matrix.single a b 1 = lam • (Matrix.single a b (1 : ℂ) * W) := by
    intro a b
    have h := hZrel a b
    -- Right-multiply `h` by `Ginv` and cancel `Gmat * Ginv = 1`.
    have h2 := congrArg (· * Ginv) h
    simp only at h2
    -- `h2 : Z * (Ginv (single) Gmat) * Ginv = lam • (single * Z) * Ginv`.
    rw [Matrix.mul_assoc (Z : Matrix (Fin 4) (Fin 4) ℂ), Matrix.mul_assoc,
      Gmat_mul_Ginv, Matrix.mul_one, Matrix.smul_mul] at h2
    rw [hW, Matrix.mul_assoc, h2, Matrix.mul_assoc]
  -- `W = Z * Ginv` is invertible, hence nonzero.
  have hWunit : IsUnit W := by
    rw [hW]
    exact (Z.isUnit).mul ⟨Gunit⁻¹, by rw [Gunit_inv_val]⟩
  -- The matrix units pin `W` to be a scalar and `lam = 1`: read entries of `hWcomm`.
  -- Diagonal entries: `W a a = lam * W b b` for every `a, b`.
  have hdiag : ∀ a b : Fin 4, W a a = lam * W b b := by
    intro a b
    have h := congrFun (congrFun (hWcomm a b) a) b
    rw [Matrix.mul_single_apply_same, Matrix.smul_apply, Matrix.single_mul_apply_same,
      one_mul, mul_one, smul_eq_mul] at h
    exact h
  -- Off-diagonal entries vanish: `W a' a = 0` for `a' ≠ a`.
  have hoff : ∀ a' a : Fin 4, a' ≠ a → W a' a = 0 := by
    intro a' a ha
    have h := congrFun (congrFun (hWcomm a a) a') a
    rw [Matrix.mul_single_apply_same, mul_one, Matrix.smul_apply,
      Matrix.single_mul_apply_of_ne (c := (1 : ℂ)) (h := ha) (M := W), smul_zero] at h
    exact h
  -- All diagonal entries equal `lam * W 0 0`.
  have hdiag0 : ∀ a : Fin 4, W a a = lam * W 0 0 := fun a => hdiag a 0
  -- `W 0 0 ≠ 0`: otherwise all entries vanish and `W = 0`, contradicting invertibility.
  have hc0 : W 0 0 ≠ 0 := by
    intro hzero
    apply hWunit.ne_zero
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [hdiag0 x, hzero, mul_zero, Matrix.zero_apply]
    · rw [hoff x y (fun h => hxy (by rw [h])), Matrix.zero_apply]
  -- Name the common diagonal value `c = W 0 0`.
  set c : ℂ := W 0 0 with hc_def
  -- `lam = 1` from `W 0 0 = lam * W 0 0` and `W 0 0 ≠ 0`.
  have hlam : lam = 1 := by
    have h := hdiag 0 0
    rw [← hc_def] at h
    refine mul_right_cancel₀ hc0 ?_
    rw [one_mul, ← h]
  -- Hence `W` is the scalar matrix `c • 1`.
  have hWscalar : W = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext x y
    rcases eq_or_ne x y with rfl | hxy
    · rw [hdiag0 x, hlam, one_mul, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
    · rw [hoff x y (fun h => hxy (by rw [h])), Matrix.smul_apply,
        Matrix.one_apply_ne hxy, smul_zero]
  -- Therefore `Z = c • Gmat`, since `Z = W * Gmat`.
  have hZscalar : (Z : Matrix (Fin 4) (Fin 4) ℂ) = c • Gmat := by
    have hZW : (Z : Matrix (Fin 4) (Fin 4) ℂ) = W * Gmat := by
      rw [hW, Matrix.mul_assoc, Ginv_mul_Gmat, Matrix.mul_one]
    rw [hZW, hWscalar, Matrix.smul_mul, Matrix.one_mul]
  -- `Z` is a per-edge product, so its `(0,0)` and `(0,1)` blocks are proportional;
  -- but `Z = c • Gmat` and the blocks of `Gmat` are not proportional.
  have hprodBlocks := blocks_proportional_of_isPerEdgeProduct hprod 0 0
  rw [hZscalar] at hprodBlocks
  simp only [blockEntry, Matrix.smul_apply, smul_eq_mul] at hprodBlocks
  apply Gmat_blocks_not_proportional
  -- Cancel the common factor `c ^ 2`, nonzero, from both sides.
  have hsq : c * c ≠ 0 := mul_ne_zero hc0 hc0
  refine mul_left_cancel₀ hsq ?_
  simp only [blockEntry]
  -- Both sides of `hprodBlocks` are `c * c` times a product of `Gmat` block entries,
  -- so cancelling the nonzero `c * c` yields the `Gmat` block identity.
  calc c * c * (Gmat (pair 0 0) (pair 0 0) * Gmat (pair 0 1) (pair 1 1))
      = c * Gmat (pair 0 0) (pair 0 0) * (c * Gmat (pair 0 1) (pair 1 1)) := by ring
    _ = c * Gmat (pair 0 0) (pair 1 0) * (c * Gmat (pair 0 1) (pair 0 1)) := hprodBlocks
    _ = c * c * (Gmat (pair 0 0) (pair 1 0) * Gmat (pair 0 1) (pair 0 1)) := by ring

end RowColumnReductionObstruction
end PEPS
end TNLean

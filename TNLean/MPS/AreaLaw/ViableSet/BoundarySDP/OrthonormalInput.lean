/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.InputEncoding
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SupportCoordinates

/-!
# Structured rational input from orthonormal support coordinates

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q k : ℕ}

/-- A support isometry over a finite MPS family may be transported to an orthonormal
family spanning the same subspace.  The replacement has no larger cardinality and each
of its vectors has the finite-span bond budget `|S| max(1,b)`. -/
theorem exists_orthonormalBoundarySupport_isLeftOpenMPS
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧ Orthonormal ℂ (fun t : T ↦ t.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      Z * Zᴴ = (reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (T : Set (LeftBlockVector L q k)))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ) := by
  obtain ⟨T, hcard, horth, hspan, hmps⟩ :=
    exists_orthonormal_isLeftOpenMPS_span_finset S hS
  have hproj : spanProjection (T : Set (LeftBlockVector L q k)) =
      spanProjection (S : Set (LeftBlockVector L q k)) := by
    simp only [spanProjection, hspan]
  exact ⟨T, hcard, horth, hspan, hmps, by simpa only [hproj] using hZZ⟩

/-- The auxiliary dimension of a support isometry is at most the dimension of the
retained left space times the bond dimension. -/
theorem boundarySupport_isometry_order_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    n ≤ S.card * m := by
  calc
    n = (1 : Matrix (Fin n) (Fin n) ℂ).rank := by simp
    _ = (Zᴴ * Z).rank := congrArg Matrix.rank hZ.symm
    _ ≤ Z.rank := Matrix.rank_mul_le_right _ _
    _ = (Z * Zᴴ).rank := (Matrix.rank_self_mul_conjTranspose Z).symm
    _ = ((reindex
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
        (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
          (1 : Matrix (Fin m) (Fin m) ℂ)).rank := congrArg Matrix.rank hZZ
    _ ≤ S.card * m := rank_boundarySupportProjection_le S m

/-- Every entry of an isometric compression is bounded by the operator norm of the
uncompressed observable. -/
theorem norm_isometricCompression_apply_le
    {a : Type*} [Fintype a] [DecidableEq a] {n : ℕ}
    (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1) (H : Matrix a a ℂ) (i j : Fin n) :
    ‖(Zᴴ * H * Z) i j‖ ≤ ‖H‖ :=
  (Matrix.norm_apply_le_l2_opNorm (Zᴴ * H * Z) i j).trans
    (l2_opNorm_isometricCompression_le Z hZ H)

/-- The physical LVV objective and a trace-norm-one boundary center have the common
dyadic entry bound `4L ≤ 2^(L+2)`.  Thus the bounded structured-input theorem may use
`R = 4L` and `u = L+2`, with no matrix-dependent radius. -/
theorem bounded_compressedObjective_and_boundaryCenter
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n L : ℕ} (hL : 1 ≤ L) (Z : Matrix a (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (H : Matrix a a ℂ) (hH : ‖H‖ ≤ 4 * L) (X : Matrix b b ℂ)
    (hX : rectangularTraceNorm X ≤ 1) :
    0 ≤ (4 * L : ℝ) ∧
      (4 * L : ℝ) ≤ ((2 ^ (L + 2) : ℕ) : ℝ) ∧
      (∀ i j, ‖(Zᴴ * H * Z) i j‖ ≤ (4 * L : ℝ)) ∧
      ∀ i j, ‖X i j‖ ≤ (4 * L : ℝ) := by
  have hpowNat : 4 * L ≤ (2 : ℕ) ^ (L + 2) := by
    have hself' : ∀ r : ℕ, r ≤ (2 : ℕ) ^ r := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [pow_succ]
          have hp : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_pow r 2 (by omega)
          omega
    have hself := hself' L
    rw [pow_add]
    norm_num
    simpa [mul_comm] using Nat.mul_le_mul_left 4 hself
  refine ⟨by positivity, by exact_mod_cast hpowNat, ?_, ?_⟩
  · intro i j
    exact (norm_isometricCompression_apply_le Z hZ H i j).trans hH
  · intro i j
    exact (Matrix.norm_apply_le_rectangularTraceNorm X i j).trans <|
      hX.trans (by exact_mod_cast (show 1 ≤ 4 * L by omega))

/-- If the retained support family is orthonormal, the support-isometry coefficients
may be chosen with modulus at most one.  They are the inner products of the retained
vectors with the corresponding bond slice. -/
theorem exists_boundarySupportOrthonormalCoordinateCoefficients
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ c : Fin n → Fin m → S → ℂ,
      (∀ j a, ∑ s : S, c j a s • s.1 =
        WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) ∧
      ∀ j a s, ‖c j a s‖ ≤ 1 := by
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  refine ⟨c, hc, ?_⟩
  intro j a s
  let u := gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j))
  let v : LeftBlockVector L q k := WithLp.toLp 2 (fun x ↦ u (x, a))
  have hv : ‖v‖ ≤ 1 := by
    calc
      ‖v‖ ≤ ‖u‖ := norm_euclidean_prod_slice_le u a
      _ = ‖(WithLp.toLp 2 (Z.col j) :
          EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))‖ :=
        (gluingLeftCoordinates L q k m).norm_map _
      _ = 1 := by
        change ‖(WithLp.toLp 2 (fun i ↦ Z i j) :
          EuclideanSpace ℂ ((CutLeft L q k × CutSite L q k) × Fin m))‖ = 1
        rw [Matrix.norm_column_eq_sqrt_gram, hZ, Matrix.one_apply, ite_eq_left rfl]
        norm_num
  have hcoeff : ⟪s.1, v⟫_ℂ = c j a s := by
    change ⟪s.1, WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))⟫_ℂ = c j a s
    rw [← hc j a]
    exact hS.inner_right_fintype (c j a) s
  rw [← hcoeff]
  exact (norm_inner_le_norm s.1 v).trans <| by
    rw [hS.norm_eq_one s, one_mul]
    exact hv

/-- For an orthonormal retained support family, every support isometry has rational
support coordinates of the universal grid height at radius one.  At mesh `δ`, every
reconstructed bond slice has error at most `|S| δ`; no condition-number parameter is
needed. -/
theorem exists_rational_boundarySupportOrthonormalCoordinates
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a s, HasRationalComplexCoordinatesOfHeight
        (rationalBoundedMatrixGridHeight 1 δ) (qc j a s)) ∧
      ∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ := by
  obtain ⟨c, hc, hcbound⟩ :=
    exists_boundarySupportOrthonormalCoordinateCoefficients S m Z hS hZ hZZ
  have hSbound : ∀ s : S, ‖s.1‖ ≤ 1 := fun s ↦ (hS.norm_eq_one s).le
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinateApproximation S c zero_le_one hδ
      hcbound hSbound
  refine ⟨qc, hqc, ?_⟩
  intro j a
  rw [← hc j a]
  simpa only [mul_one] using hclose j a

/-- If `n ≤ |S|m ≤ M` and the boundary order is at most `M`, the structured input has
at most `2(3M²+2)` rational scalar coordinates. -/
theorem structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r M : ℕ}
    (hn : n ≤ S.card * m) (hSm : S.card * m ≤ M) (hr : r ≤ M) :
    structuredCompressedSDPInputRationalCoordinateCount S m n r ≤
      2 * (3 * M ^ 2 + 2) := by
  have hc := boundarySupportCoordinateCoefficientCount_le_sq S m n hn
  have hSm2 : (S.card * m) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hSm 2
  have hnM : n ≤ M := hn.trans hSm
  have hn2 : n ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hnM 2
  have hr2 : r ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hr 2
  unfold structuredCompressedSDPInputRationalCoordinateCount
  omega

/-- Exponentially bounded structured-coordinate height and polynomially bounded support
and boundary orders give an explicit polynomial structured-input bit-size bound. -/
theorem structuredCompressedSDPInputBitSizeBound_le_of_order_and_height_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r H M p : ℕ}
    (hn : n ≤ S.card * m) (hSm : S.card * m ≤ M) (hr : r ≤ M)
    (hH : H ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r H ≤
      2 * (3 * M ^ 2 + 2) * (p + 1) := by
  unfold structuredCompressedSDPInputBitSizeBound
  apply Nat.mul_le_mul
  · exact structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds
      S hn hSm hr
  · apply Nat.add_le_add_right
    rw [Nat.log2_eq_log_two]
    calc
      Nat.log 2 H ≤ Nat.log 2 (2 ^ p) := Nat.log_mono_right hH
      _ = p := Nat.log_pow (by omega) p

/-- Canonical structured-coordinate bound, using the larger of the support order
`|S|m` and the boundary order `r`. -/
theorem structuredCompressedSDPInputRationalCoordinateCount_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r : ℕ}
    (hn : n ≤ S.card * m) :
    structuredCompressedSDPInputRationalCoordinateCount S m n r ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) :=
  structuredCompressedSDPInputRationalCoordinateCount_le_of_order_bounds S hn
    (le_max_left _ _) (le_max_right _ _)

/-- Canonical structured bit-size bound at logarithmic height exponent `p`. -/
theorem structuredCompressedSDPInputBitSizeBound_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r H p : ℕ}
    (hn : n ≤ S.card * m) (hH : H ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r H ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_of_order_and_height_bounds S hn
    (le_max_left _ _) (le_max_right _ _) hH

/-- Separate exponential bounds for the support coefficients, objective, boundary
center, and shifts imply the canonical quadratic bit-size estimate for their common
structured encoding. -/
theorem structuredCompressedSDPInputBitSizeBound_le_of_component_height_bounds
    (S : Finset (LeftBlockVector L q k)) {m n r Hc HK HX Hε Hεb p : ℕ}
    (hn : n ≤ S.card * m) (hc : Hc ≤ 2 ^ p) (hK : HK ≤ 2 ^ p)
    (hX : HX ≤ 2 ^ p) (hε : Hε ≤ 2 ^ p) (hεb : Hεb ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r
        (rationalStructuredCompressedSDPInputHeight Hc HK HX Hε Hεb) ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_max_order S hn
    (rationalStructuredCompressedSDPInputHeight_le_two_pow hc hK hX hε hεb)

/-- A structured rational encoding of height at most `2^p` has the canonical quadratic
bit-size bound. -/
theorem RationalStructuredCompressedSDPInputEncoding.bitSizeBound_le_max_order
    (S : Finset (LeftBlockVector L q k)) {m n r p : ℕ}
    {c : Fin n → Fin m → S → ℂ} {K : Matrix (Fin n) (Fin n) ℂ}
    {X : Matrix (Fin r) (Fin r) ℂ} {ε εb : ℝ}
    (h : RationalStructuredCompressedSDPInputEncoding S m n r c K X ε εb)
    (hn : n ≤ S.card * m) (hheight : h.height ≤ 2 ^ p) :
    structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) :=
  structuredCompressedSDPInputBitSizeBound_le_max_order S hn hheight

/-- The orthonormal-support rational coordinates assemble with separately rational
objective, boundary, and shift data into a complete structured LVV input.  If all five
component heights are at most `2^p`, the resulting input has the canonical quadratic
bit-size bound. -/
theorem exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb p : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hcHeight : rationalBoundedMatrixGridHeight 1 δ ≤ 2 ^ p)
    (hKHeight : HK ≤ 2 ^ p) (hXHeight : HX ≤ 2 ^ p)
    (hεHeight : Hε ≤ 2 ^ p) (hεbHeight : Hεb ≤ 2 ^ p) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * δ) ∧
      ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb,
        structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
          2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) := by
  obtain ⟨qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportOrthonormalCoordinates S m Z hS hZ hZZ hδ
  let h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb :=
    rationalStructuredCompressedSDPInputEncodingOfHeightBounds S qc K X ε εb
      hqc hK hX hε hεb
  refine ⟨qc, hclose, h, ?_⟩
  apply h.bitSizeBound_le_max_order S hn
  exact rationalStructuredCompressedSDPInputHeight_le_two_pow hcHeight hKHeight
    hXHeight hεHeight hεbHeight

/-- Dyadic specialization of the orthonormal structured-input construction.  Precision
`2⁻ᵗ` gives coefficient height at most `2^(2t+5)` and hence an explicit bit-size bound
linear in `2t+6` per rational scalar coordinate. -/
theorem exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {HK HX Hε Hεb : ℕ} (t : ℕ)
    (hK : Matrix.HasRationalEntriesOfHeight HK K)
    (hX : Matrix.HasRationalEntriesOfHeight HX X)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hKHeight : HK ≤ 2 ^ (2 * t + 5)) (hXHeight : HX ≤ 2 ^ (2 * t + 5))
    (hεHeight : Hε ≤ 2 ^ (2 * t + 5))
    (hεbHeight : Hεb ≤ 2 ^ (2 * t + 5)) :
    ∃ qc : Fin n → Fin m → S → ℂ,
      (∀ j a,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
          ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
      ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc K X ε εb,
        structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
          2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (2 * t + 6) := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
      S m Z hS hZ hZZ K X ε εb (inv_pos.mpr (by positivity)) hK hX hε hεb hn
      (rationalBoundedMatrixGridHeight_one_inv_two_pow_le t)
      hKHeight hXHeight hεHeight hεbHeight

/-- Bounded objective and boundary-center matrices can be rounded together with the
orthonormal support coordinates.  Radius `2^u` and mesh `2⁻ᵗ` give a common height
exponent `2u+2t+5`, entrywise matrix errors `2⁻ᵗ`, slice error `|S|2⁻ᵗ`, and the
displayed quadratic structured-input bit bound. -/
theorem exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_bounded_orthonormal
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (ε εb : ℝ) {R : ℝ} (u t : ℕ) {Hε Hεb : ℕ}
    (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R)
    (hε : HasRationalComplexCoordinatesOfHeight Hε (ε : ℂ))
    (hεb : HasRationalComplexCoordinatesOfHeight Hεb (εb : ℂ))
    (hn : n ≤ S.card * m)
    (hεHeight : Hε ≤ 2 ^ (2 * u + 2 * t + 5))
    (hεbHeight : Hεb ≤ 2 ^ (2 * u + 2 * t + 5)) :
    ∃ QK : Matrix (Fin n) (Fin n) ℂ,
      ∃ QX : Matrix (Fin r) (Fin r) ℂ,
        (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        ∃ qc : Fin n → Fin m → S → ℂ,
          (∀ j a,
            ‖WithLp.toLp 2 (fun x ↦
                gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
              ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
          ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc QK QX ε εb,
            structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
              2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                (2 * u + 2 * t + 6) := by
  obtain ⟨QK, hQK, hQKclose⟩ :=
    exists_dyadic_rational_rectangular_approximation hR0 hR K hKbound
  obtain ⟨QX, hQX, hQXclose⟩ :=
    exists_dyadic_rational_rectangular_approximation hR0 hR X hXbound
  have hcHeight : rationalBoundedMatrixGridHeight 1 ((2 ^ t : ℝ)⁻¹) ≤
      2 ^ (2 * u + 2 * t + 5) := by
    exact (rationalBoundedMatrixGridHeight_one_inv_two_pow_le t).trans <|
      Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  obtain ⟨qc, hqcclose, h⟩ :=
    exists_rationalStructuredCompressedSDPInputEncoding_of_orthonormal
      S m Z hS hZ hZZ QK QX ε εb (inv_pos.mpr (by positivity)) hQK hQX hε hεb hn
      hcHeight le_rfl le_rfl hεHeight hεbHeight
  exact ⟨QK, QX, hQKclose, hQXclose, qc, hqcclose, h⟩

/-- Fully constructed dyadic structured input for the bounded orthonormal branch.  The
two cone shifts are the canonical positive rational tolerances below `2⁻ᵗ`, so no
external rational-height assumptions remain. -/
theorem exists_dyadicStructuredInput_of_bounded_orthonormal_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hS : Orthonormal ℂ (fun s : S ↦ s.1))
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    {R : ℝ} (u t : ℕ) (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R)
    (hn : n ≤ S.card * m) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ QK : Matrix (Fin n) (Fin n) ℂ,
      ∃ QX : Matrix (Fin r) (Fin r) ℂ,
        (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
        ∃ qc : Fin n → Fin m → S → ℂ,
          (∀ j a,
            ‖WithLp.toLp 2 (fun x ↦
                gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
              ∑ s : S, qc j a s • s.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
          ∃ h : RationalStructuredCompressedSDPInputEncoding S m n r qc QK QX ε ε,
            structuredCompressedSDPInputBitSizeBound S m n r h.height ≤
              2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                (2 * u + 2 * t + 6) := by
  dsimp only
  have hshift := rationalPositiveTolerance_inv_two_pow_hasRationalCoordinatesOfHeight t
  have hshiftHeight : 2 ^ (t + 2) ≤ 2 ^ (2 * u + 2 * t + 5) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact exists_dyadicRationalStructuredCompressedSDPInputEncoding_of_bounded_orthonormal
    S m Z hS hZ hZZ K X _ _ u t hR0 hR hKbound hXbound hshift hshift hn
    hshiftHeight hshiftHeight

/-- Fully constructed dyadic structured input for an arbitrary finite retained MPS
family.  The family is first replaced by a no-larger orthonormal family with the same
span; its vectors remain left-open matrix product states with bond dimension at most
`|S| max(1,b)`. -/
theorem exists_dyadicStructuredInput_of_bounded_isLeftOpenMPS_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n r : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (K : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    {R : ℝ} (u t : ℕ) (hR0 : 0 ≤ R) (hR : R ≤ (2 ^ u : ℕ))
    (hKbound : ∀ i j, ‖K i j‖ ≤ R) (hXbound : ∀ i j, ‖X i j‖ ≤ R) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧
      Orthonormal ℂ (fun v : T ↦ v.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∃ QK : Matrix (Fin n) (Fin n) ℂ,
        ∃ QX : Matrix (Fin r) (Fin r) ℂ,
          (∀ i j, ‖(K - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          ∃ qc : Fin n → Fin m → T → ℂ,
            (∀ j a,
              ‖WithLp.toLp 2 (fun x ↦
                  gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
                ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
            (∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates T m qc) p j‖ ≤
              S.card * (2 ^ t : ℝ)⁻¹) ∧
            ∃ h : RationalStructuredCompressedSDPInputEncoding T m n r qc QK QX ε ε,
              structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
                2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                  (2 * u + 2 * t + 6) := by
  dsimp only
  obtain ⟨T, hcard, horth, hspan, hmps, hZZT⟩ :=
    exists_orthonormalBoundarySupport_isLeftOpenMPS S m b hS Z hZZ
  have hn : n ≤ T.card * m := boundarySupport_isometry_order_le T m Z hZ hZZT
  obtain ⟨QK, QX, hQK, hQX, qc, hqc, henc⟩ :=
    exists_dyadicStructuredInput_of_bounded_orthonormal_withCanonicalShifts
      T m Z horth hZ hZZT K X u t hR0 hR hKbound hXbound hn
  obtain ⟨h, henc⟩ := henc
  have hqcS : ∀ j a,
      ‖WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
        ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹ := by
    intro j a
    exact (hqc j a).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity))
  have hencS : structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
      2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (2 * u + 2 * t + 6) := by
    refine henc.trans ?_
    gcongr
  have hQZS := norm_boundarySupportMatrixOfCoordinates_sub_apply_le T m Z qc hqcS
  exact ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqcS, hQZS, h, hencS⟩

/-- Dyadic structured input for the physical LVV bounds.  If the uncompressed left
observable has norm at most `4L` and the boundary center has trace norm at most one,
then the common dyadic exponent is canonically `L+2`; no entrywise bounds or auxiliary
radius remain as hypotheses. -/
theorem exists_dyadicStructuredInput_of_physical_isLeftOpenMPS_withCanonicalShifts
    (S : Finset (LeftBlockVector L q k)) (m b : ℕ)
    (hS : ∀ w ∈ S, IsLeftOpenMPS b w) {n r : ℕ}
    (hL : 1 ≤ L)
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    (H : Matrix ((CutLeft L q k × CutSite L q k) × Fin m)
      ((CutLeft L q k × CutSite L q k) × Fin m) ℂ)
    (hH : ‖H‖ ≤ 4 * L) (X : Matrix (Fin r) (Fin r) ℂ)
    (hX : rectangularTraceNorm X ≤ 1) (t : ℕ) :
    let ε := rationalPositiveTolerance ((2 ^ t : ℝ)⁻¹)
    ∃ T : Finset (LeftBlockVector L q k),
      T.card ≤ S.card ∧
      Orthonormal ℂ (fun v : T ↦ v.1) ∧
      Submodule.span ℂ (T : Set (LeftBlockVector L q k)) =
        Submodule.span ℂ (S : Set (LeftBlockVector L q k)) ∧
      (∀ v ∈ T, IsLeftOpenMPS (S.card * max 1 b) v) ∧
      ∃ QK : Matrix (Fin n) (Fin n) ℂ,
        ∃ QX : Matrix (Fin r) (Fin r) ℂ,
          (∀ i j, ‖(Zᴴ * H * Z - QK) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          (∀ i j, ‖(X - QX) i j‖ ≤ (2 ^ t : ℝ)⁻¹) ∧
          ∃ qc : Fin n → Fin m → T → ℂ,
            (∀ j a,
              ‖WithLp.toLp 2 (fun x ↦
                  gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) -
                ∑ v : T, qc j a v • v.1‖ ≤ S.card * (2 ^ t : ℝ)⁻¹) ∧
            (∀ p j, ‖(Z - boundarySupportMatrixOfCoordinates T m qc) p j‖ ≤
              S.card * (2 ^ t : ℝ)⁻¹) ∧
            ∃ h : RationalStructuredCompressedSDPInputEncoding T m n r qc QK QX ε ε,
              structuredCompressedSDPInputBitSizeBound T m n r h.height ≤
                2 * (3 * (max (S.card * m) r) ^ 2 + 2) *
                  (2 * (L + 2) + 2 * t + 6) := by
  obtain ⟨hR0, hR, hKbound, hXbound⟩ :=
    bounded_compressedObjective_and_boundaryCenter hL Z hZ H hH X hX
  obtain ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqc, hQZ, henc⟩ :=
    exists_dyadicStructuredInput_of_bounded_isLeftOpenMPS_withCanonicalShifts
      S m b hS Z hZ hZZ (Zᴴ * H * Z) X (L + 2) t hR0 hR hKbound hXbound
  exact ⟨T, hcard, horth, hspan, hmps, QK, QX, hQK, hQX, qc, hqc, hQZ, henc⟩

/-- A support isometry admits structured coefficients together with the canonical
quadratic input-size bound.  This combines the geometric coordinate construction with
the structured rational-input accounting. -/
theorem exists_boundarySupportCoordinateCoefficients_with_bitSizeBound
    (S : Finset (LeftBlockVector L q k)) (m r H p : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hn : n ≤ S.card * m) (hH : H ≤ 2 ^ p)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ)) :
    ∃ c : Fin n → Fin m → S → ℂ,
      (∀ j a, ∑ s : S, c j a s • s.1 =
        WithLp.toLp 2 (fun x ↦
          gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) ∧
      structuredCompressedSDPInputBitSizeBound S m n r H ≤
        2 * (3 * (max (S.card * m) r) ^ 2 + 2) * (p + 1) := by
  obtain ⟨c, hc⟩ := exists_boundarySupportCoordinateCoefficients S m Z hZ hZZ
  exact ⟨c, hc, structuredCompressedSDPInputBitSizeBound_le_max_order S hn hH⟩

end TNLean.MPS.AreaLaw

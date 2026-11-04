/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.SupportCoordinates
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalViableFamilies

/-!
# Rational representations of finite spans

This is part of the finite-precision analysis of the boundary optimization in
Landau, Vazirani and Vidick, arXiv:1307.5143v1, equation `eq:conv`.
-/

open Matrix
open scoped Kronecker ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw
/-- A compact rational description of one finite output family in the span of a retained
MPS family.  It stores the linear-combination coefficients rather than expanding the
vectors into exponentially many physical coordinates.

This is the data required by the size-trimming step of LVV13, `algo53.tex`, lines
472--478 and 520--527. -/
structure RationalSpanFamilyEncodingOfHeight
    (H : ℕ) (S : Finset (LeftBlockVector L q k))
    (T : Finset (LeftBlockVector L q k)) where
  coefficient : T → S → ℂ
  coefficient_height : ∀ t s,
    HasRationalComplexCoordinatesOfHeight H (coefficient t s)
  linearCombination_eq : ∀ t : T,
    t.1 = ∑ s : S, coefficient t s • s.1

/-- The finite family of all left columns decoded from a structured coefficient array. -/
noncomputable def spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) : Finset (LeftBlockVector L q k) :=
  Finset.image₂ (fun j a ↦ ∑ s : S, c j a s • s.1) Finset.univ Finset.univ

/-- A decoded span-column family contains at most `n m` vectors. -/
theorem spanColumnFamily_card_le
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) :
    (spanColumnFamily S m c).card ≤ n * m := by
  unfold spanColumnFamily
  simpa using Finset.card_image₂_le
    (fun j : Fin n ↦ fun a : Fin m ↦ ∑ s : S, c j a s • s.1)
      Finset.univ Finset.univ

/-- Every coefficient slice is represented by its decoded vector in the finite column
family. -/
theorem sum_mem_spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (j : Fin n) (a : Fin m) :
    (∑ s : S, c j a s • s.1) ∈ spanColumnFamily S m c := by
  unfold spanColumnFamily
  exact Finset.mem_image₂.mpr
    ⟨j, Finset.mem_univ j, a, Finset.mem_univ a, rfl⟩

/-- A uniform approximation of coefficient slices becomes an approximation by explicit
members of the decoded finite column family. -/
theorem exists_mem_spanColumnFamily_close
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (v : Fin n → Fin m → LeftBlockVector L q k)
    {θ : ℝ} (hclose : ∀ j a, ‖v j a - ∑ s : S, c j a s • s.1‖ ≤ θ) :
    ∀ j a, ∃ w ∈ spanColumnFamily S m c, ‖v j a - w‖ ≤ θ := by
  intro j a
  exact ⟨∑ s : S, c j a s • s.1, sum_mem_spanColumnFamily S m c j a,
    hclose j a⟩

/-- Every member of the decoded column family has a coefficient-index preimage. -/
theorem exists_spanColumnFamily_index
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (c : Fin n → Fin m → S → ℂ) (t : spanColumnFamily S m c) :
    ∃ p : Fin n × Fin m, ∑ s : S, c p.1 p.2 s • s.1 = t.1 := by
  obtain ⟨j, _hj, a, _ha, hja⟩ := Finset.mem_image₂.mp t.2
  exact ⟨(j, a), hja⟩

/-- Rational structured coefficients canonically equip their decoded column family
with a compact rational span encoding.  A preimage is selected only to resolve duplicate
columns in the finite image. -/
noncomputable def rationalSpanFamilyEncodingOfCoefficients
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n H : ℕ}
    (c : Fin n → Fin m → S → ℂ)
    (hc : ∀ j a s, HasRationalComplexCoordinatesOfHeight H (c j a s)) :
    RationalSpanFamilyEncodingOfHeight H S (spanColumnFamily S m c) where
  coefficient t s :=
    let p := Classical.choose (exists_spanColumnFamily_index S m c t)
    c p.1 p.2 s
  coefficient_height t s := by
    dsimp only
    exact hc _ _ s
  linearCombination_eq t := by
    dsimp only
    exact (Classical.choose_spec (exists_spanColumnFamily_index S m c t)).symm

namespace RationalSpanFamilyEncodingOfHeight

/-- Uniform physical-coordinate height for a rational linear combination of at most
`s` inputs whose physical coordinates have height at most `Hv`. -/
def linearCombinationCoordinateHeight (H Hv s : ℕ) : ℕ :=
  let HM := 2 * (H * Hv) * (H * Hv)
  (2 * HM) ^ s

/-- If coefficient and input-coordinate heights have binary exponents `p` and `v`,
then the physical-coordinate height of a linear combination of at most `s` inputs has
the displayed explicit binary exponent.  This is the one-step height recurrence for a
fully expanded coordinate representation. -/
theorem linearCombinationCoordinateHeight_le_two_pow
    {H Hv p v : ℕ} (hH : H ≤ 2 ^ p) (hHv : Hv ≤ 2 ^ v) (s : ℕ) :
    linearCombinationCoordinateHeight H Hv s ≤
      2 ^ ((2 * p + 2 * v + 2) * s) := by
  unfold linearCombinationCoordinateHeight
  have hprod : H * Hv ≤ (2 ^ p) * (2 ^ v) := Nat.mul_le_mul hH hHv
  have hbase : 2 * (2 * (H * Hv) * (H * Hv)) ≤ 2 ^ (2 * p + 2 * v + 2) := by
    calc
      2 * (2 * (H * Hv) * (H * Hv)) = 4 * (H * Hv) ^ 2 := by ring
      _ ≤ 4 * ((2 ^ p) * (2 ^ v)) ^ 2 := by gcongr
      _ = 2 ^ (2 * p + 2 * v + 2) := by
        rw [← pow_add]
        ring_nf
  calc
    (2 * (2 * (H * Hv) * (H * Hv))) ^ s ≤
        (2 ^ (2 * p + 2 * v + 2)) ^ s := Nat.pow_le_pow_left hbase s
    _ = 2 ^ ((2 * p + 2 * v + 2) * s) := by rw [pow_mul]

/-- Uniform physical-coordinate height of a rational linear combination of a retained
height-bounded MPS family.  This bound is used only when a physical coordinate is
queried; the stored representation remains the compact coefficient array. -/
def outputCoordinateHeight (H Hv b k s : ℕ) : ℕ :=
  linearCombinationCoordinateHeight H
    (RationalLeftOpenMPSRepresentationOfHeight.coordinateHeightBound Hv b k) s

/-- Number of rational scalar coordinates stored by a compact span-family encoding. -/
def rationalCoordinateCount (S T : Finset (LeftBlockVector L q k)) : ℕ :=
  2 * T.card * S.card

/-- Bit-size bound for the stored rational coefficient array. -/
def coefficientBitSizeBound (H : ℕ)
    (S T : Finset (LeftBlockVector L q k)) : ℕ :=
  rationalCoordinateCount S T * (Nat.log2 H + 1)

/-- Each stored complex coefficient is represented by two rationals of bit length at
most `log₂ H + 1`. -/
theorem coefficient_exists_bitLength_le
    {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (t : T) (s : S) :
    ∃ x y : ℚ, E.coefficient t s = ⟨(x : ℝ), (y : ℝ)⟩ ∧
      rationalBitLength x ≤ Nat.log2 H + 1 ∧
      rationalBitLength y ≤ Nat.log2 H + 1 :=
  (E.coefficient_height t s).exists_bitLength_le

/-- Polynomial cardinality bounds on the input and output families give the expected
quadratic bound on the number of stored rational coordinates. -/
theorem rationalCoordinateCount_le {H s t : ℕ}
    {S T : Finset (LeftBlockVector L q k)}
    (_E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : S.card ≤ s) (hT : T.card ≤ t) :
    rationalCoordinateCount S T ≤ 2 * t * s := by
  unfold rationalCoordinateCount
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hT) hS

/-- The same family-cardinality bounds control the complete coefficient bit-size. -/
theorem coefficientBitSizeBound_le {H s t : ℕ}
    {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : S.card ≤ s) (hT : T.card ≤ t) :
    coefficientBitSizeBound H S T ≤ 2 * t * s * (Nat.log2 H + 1) := by
  unfold coefficientBitSizeBound
  exact Nat.mul_le_mul_right _ (E.rationalCoordinateCount_le hS hT)

/-- Every encoded output vector belongs to the span of the retained input family. -/
theorem mem_span {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (t : T) :
    t.1 ∈ Submodule.span ℂ (S : Set (LeftBlockVector L q k)) := by
  rw [E.linearCombination_eq t]
  apply Submodule.sum_mem
  intro s _hs
  exact Submodule.smul_mem _ _ (Submodule.subset_span s.2)

/-- The compact span encoding carries the usual finite-span MPS bond bound. -/
theorem isLeftOpenMPS {H b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : ∀ s ∈ S, IsLeftOpenMPS b s) (t : T) :
    IsLeftOpenMPS (S.card * max 1 b) t.1 :=
  isLeftOpenMPS_of_mem_span S hS (E.mem_span t)

/-- Querying any physical coordinate of an encoded output vector gives a rational
number with a uniform explicit height bound. -/
theorem coordinate_height_of_input
    {H Hv : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (hS : ∀ s : S,
      ∀ x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k),
        HasRationalComplexCoordinatesOfHeight Hv (s.1 x))
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (linearCombinationCoordinateHeight H Hv S.card) (t.1 x) := by
  rw [E.linearCombination_eq t]
  unfold linearCombinationCoordinateHeight
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun s _hs ↦ (E.coefficient_height t s).mul (hS s x))

/-- Querying any physical coordinate of an encoded output vector gives a rational
number with a uniform explicit height bound. -/
theorem coordinate_height {H Hv b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1)
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (outputCoordinateHeight H Hv b k S.card) (t.1 x) := by
  exact E.coordinate_height_of_input
    (fun s x ↦ (hS s).coordinate_height_le hHv hk x) t x

/-- In particular, every physical coordinate of the compactly encoded output family is
Gaussian rational. -/
theorem coordinate_rational {H Hv b : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) (hHv : 0 < Hv) (hk : k ≤ L)
    (hS : ∀ s : S, RationalLeftOpenMPSRepresentationOfHeight Hv b s.1)
    (t : T) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinates (t.1 x) :=
  (E.coordinate_height hHv hk hS t x).forget

/-- A compact rational span encoding transports the coordinate-rational viable-MPS
invariant from its input family to any viable decoded output family. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s₀ s b : ℕ} {δ δ' : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ S)
    (hcard : T.card ≤ s) (hviable : IsViable Γ δ' (T : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (linearCombinationCoordinateHeight H Hv S.card)
      Γ s (S.card * max 1 b) δ' T where
  card_le := hcard
  isLeftOpenMPS t := E.isLeftOpenMPS
    (fun u hu ↦ D.isLeftOpenMPS ⟨u, hu⟩) t
  coordinate_height t x := E.coordinate_height_of_input D.coordinate_height t x
  viable := hviable

/-- Dyadic-exponent form of the preceding transport theorem.  It records the exact
one-step bit-height recurrence for a fully expanded output coordinate. -/
theorem coordinateViableMPSData_twoPow
    {H Hv p v : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s₀ s b : ℕ}
    {δ δ' : ℝ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T)
    (D : RationalCoordinateViableMPSDataOfHeight Hv Γ s₀ b δ S)
    (hH : H ≤ 2 ^ p) (hHv : Hv ≤ 2 ^ v)
    (hcard : T.card ≤ s) (hviable : IsViable Γ δ' (T : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (2 ^ ((2 * p + 2 * v + 2) * S.card))
      Γ s (S.card * max 1 b) δ' T :=
  (E.coordinateViableMPSData D hcard hviable).mono_height
    (linearCombinationCoordinateHeight_le_two_pow hH hHv S.card)

end RationalSpanFamilyEncodingOfHeight

/-- A shared multi-layer rational span representation at one cut.  The zeroth family
is the stored input family, and every later family is represented by rational linear
combinations of the preceding one.  Keeping the intermediate families shared gives a
directed acyclic representation: its storage is the sum of the coefficient arrays,
without expanding any physical coordinate through all preceding layers.

This is the fixed-cut arithmetic representation required when successive LVV size
selection steps are composed; see LVV13, `algo53.tex`, lines 472--527. -/
structure RationalSpanEncodingDAGOfHeight
    (depth : ℕ) (height : Fin depth → ℕ)
    (family : Fin (depth + 1) → Finset (LeftBlockVector L q k)) where
  layer : ∀ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight (height i)
      (family i.castSucc) (family i.succ)

namespace RationalSpanEncodingDAGOfHeight

/-- The number of rational scalar coordinates stored by all coefficient arrays in a
shared span DAG. -/
def rationalCoordinateCount
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (_D : RationalSpanEncodingDAGOfHeight depth height family) : ℕ :=
  ∑ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
      (family i.castSucc) (family i.succ)

/-- The coefficient bit-size bound of a shared span DAG is the sum of the bounds for
its layers.  In particular, no flattened physical-coordinate height occurs here. -/
def coefficientBitSizeBound
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (_D : RationalSpanEncodingDAGOfHeight depth height family) : ℕ :=
  ∑ i : Fin depth,
    RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
      (height i) (family i.castSucc) (family i.succ)

/-- Every vector in a noninitial layer belongs to the span of the immediately
preceding family. -/
theorem mem_span_previous
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (i : Fin depth) (t : family i.succ) :
    t.1 ∈ Submodule.span ℂ
      (family i.castSucc : Set (LeftBlockVector L q k)) :=
  (D.layer i).mem_span t

/-- The span of each noninitial layer is contained in the span of its immediate
predecessor. -/
theorem span_le_previous
    {depth : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family) (i : Fin depth) :
    Submodule.span ℂ (family i.succ : Set (LeftBlockVector L q k)) ≤
      Submodule.span ℂ (family i.castSucc : Set (LeftBlockVector L q k)) := by
  apply Submodule.span_le.mpr
  intro v hv
  exact D.mem_span_previous i ⟨v, hv⟩

/-- If every intermediate family has cardinality at most `s`, then the complete
shared coefficient representation has at most `depth · 2s²` rational scalar
coordinates.  Thus composition is additive in the number of layers. -/
theorem rationalCoordinateCount_le
    {depth s : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (hcard : ∀ i, (family i).card ≤ s) :
    D.rationalCoordinateCount ≤ depth * (2 * s * s) := by
  unfold rationalCoordinateCount
  calc
    (∑ i : Fin depth,
        RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
          (family i.castSucc) (family i.succ)) ≤
        ∑ _i : Fin depth, 2 * s * s := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hcard i.succ)) (hcard i.castSucc)
    _ = depth * (2 * s * s) := by simp

/-- If every layer has cardinality at most `s` and coefficient height at most
`2^p`, then the complete shared representation has bit size at most
`depth · 2s²(p+1)`.  The dependence on the number of composed layers is additive. -/
theorem coefficientBitSizeBound_le
    {depth s p : ℕ} {height : Fin depth → ℕ}
    {family : Fin (depth + 1) → Finset (LeftBlockVector L q k)}
    (D : RationalSpanEncodingDAGOfHeight depth height family)
    (hcard : ∀ i, (family i).card ≤ s) (hheight : ∀ i, height i ≤ 2 ^ p) :
    D.coefficientBitSizeBound ≤ depth * (2 * s * s * (p + 1)) := by
  unfold coefficientBitSizeBound
  calc
    (∑ i : Fin depth,
        RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
          (height i) (family i.castSucc) (family i.succ)) ≤
        ∑ _i : Fin depth, 2 * s * s * (p + 1) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold RationalSpanFamilyEncodingOfHeight.coefficientBitSizeBound
      apply Nat.mul_le_mul
      · unfold RationalSpanFamilyEncodingOfHeight.rationalCoordinateCount
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hcard i.succ)) (hcard i.castSucc)
      · apply Nat.add_le_add_right
        rw [Nat.log2_eq_log_two]
        calc
          Nat.log 2 (height i) ≤ Nat.log 2 (2 ^ p) :=
            Nat.log_mono_right (hheight i)
          _ = p := Nat.log_pow (by omega) p
    _ = depth * (2 * s * s * (p + 1)) := by simp

end RationalSpanEncodingDAGOfHeight

/-- A rational span encoding with explicit finite indices.  Unlike a `Finset` image,
the index types retain multiplicities.  This makes one-site extension functorial:
each node is paired with its computational-basis label, even when two decoded vectors
coincide. -/
structure RationalIndexedSpanEncodingOfHeight
    (H : ℕ) (I J : Type*) [Fintype I] [Fintype J]
    (input : I → LeftBlockVector L q k) (output : J → LeftBlockVector L q k) where
  coefficient : J → I → ℂ
  coefficient_height : ∀ j a,
    HasRationalComplexCoordinatesOfHeight H (coefficient j a)
  linearCombination_eq : ∀ j,
    output j = ∑ a : I, coefficient j a • input a

namespace RationalIndexedSpanEncodingOfHeight

/-- The finite family decoded from an explicitly indexed collection of vectors. -/
noncomputable def decodedFamily {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) : Finset (LeftBlockVector L q k) :=
  Finset.univ.image output

/-- The decoded family has at most as many elements as its finite index type. -/
theorem decodedFamily_card_le {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) :
    (decodedFamily output).card ≤ Fintype.card J := by
  classical
  exact Finset.card_image_le

/-- Every decoded vector has an index preimage. -/
theorem exists_decodedFamily_index {J : Type*} [Fintype J]
    (output : J → LeftBlockVector L q k) (t : decodedFamily output) :
    ∃ j : J, output j = t.1 := by
  classical
  obtain ⟨j, _hj, hjo⟩ := Finset.mem_image.mp t.2
  exact ⟨j, hjo⟩

/-- A finite-family span encoding is canonically an indexed encoding, using the
subtypes of its input and output finsets as node sets. -/
def ofFinset
    {H : ℕ} {S T : Finset (LeftBlockVector L q k)}
    (E : RationalSpanFamilyEncodingOfHeight H S T) :
    RationalIndexedSpanEncodingOfHeight H S T
      (fun s ↦ s.1) (fun t ↦ t.1) where
  coefficient := E.coefficient
  coefficient_height := E.coefficient_height
  linearCombination_eq := E.linearCombination_eq

/-- Every decoded output vector belongs to the span of the decoded input family. -/
theorem mem_span_decodedFamily
    {H : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (t : decodedFamily output) :
    t.1 ∈ Submodule.span ℂ
      (decodedFamily input : Set (LeftBlockVector L q k)) := by
  classical
  obtain ⟨j, hj⟩ := exists_decodedFamily_index output t
  rw [← hj, E.linearCombination_eq j]
  apply Submodule.sum_mem
  intro a _ha
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

/-- An indexed rational span encoding transports rational physical-coordinate bounds
without first quotienting coincident decoded nodes. -/
theorem coordinate_height
    {H Hv : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (hinput : ∀ a x,
      HasRationalComplexCoordinatesOfHeight Hv (input a x))
    (j : J) (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
        H Hv (Fintype.card I)) (output j x) := by
  rw [E.linearCombination_eq j]
  unfold RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
  simpa using HasRationalComplexCoordinatesOfHeight.finset_sum
    (s := Finset.univ) (fun a _ha ↦ (E.coefficient_height j a).mul (hinput a x))

/-- Decoding an indexed rational span layer gives the coordinate-rational viable-MPS
data expected by the finite-family search interface. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {b : ℕ} {δ : ℝ}
    {input : I → LeftBlockVector L q k} {output : J → LeftBlockVector L q k}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output)
    (hinputMPS : ∀ a, IsLeftOpenMPS b (input a))
    (hinputHeight : ∀ a x,
      HasRationalComplexCoordinatesOfHeight Hv (input a x))
    (hviable : IsViable Γ δ
      (decodedFamily output : Set (LeftBlockVector L q k))) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalSpanFamilyEncodingOfHeight.linearCombinationCoordinateHeight
        H Hv (Fintype.card I))
      Γ (Fintype.card J) ((decodedFamily input).card * max 1 b) δ
      (decodedFamily output) where
  card_le := decodedFamily_card_le output
  isLeftOpenMPS t := isLeftOpenMPS_of_mem_span (decodedFamily input)
    (by
      intro v hv
      obtain ⟨a, _ha, hav⟩ := Finset.mem_image.mp hv
      rw [← hav]
      exact hinputMPS a)
    (E.mem_span_decodedFamily t)
  coordinate_height t x := by
    obtain ⟨j, hj⟩ := exists_decodedFamily_index output t
    rw [← hj]
    exact E.coordinate_height hinputHeight j x
  viable := hviable

/-- One-site extension preserves an indexed rational span encoding and its coefficient
height.  The new coefficient is the old coefficient when the computational-basis
labels agree, and zero otherwise.  Retaining the product indices avoids any expansion
of physical coordinates or quotienting of coincident decoded vectors. -/
noncomputable def extend
    {H : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {input : I → LeftBlockVector L q (i - 1)}
    {output : J → LeftBlockVector L q (i - 1)}
    (E : RationalIndexedSpanEncodingOfHeight H I J input output) (hH : 1 ≤ H) :
    RationalIndexedSpanEncodingOfHeight H (I × Fin q) (J × Fin q)
      (fun a ↦ AreaLaw.extendSite i a.2 (input a.1))
      (fun j ↦ AreaLaw.extendSite i j.2 (output j.1)) where
  coefficient j a := if j.2 = a.2 then E.coefficient j.1 a.1 else 0
  coefficient_height j a := by
    split_ifs
    · exact E.coefficient_height j.1 a.1
    · exact HasRationalComplexCoordinatesOfHeight.zero.mono hH
  linearCombination_eq j := by
    rw [E.linearCombination_eq j.1]
    simp only [map_sum, map_smul]
    rw [Fintype.sum_prod_type]
    simp

end RationalIndexedSpanEncodingOfHeight

/-- A multi-layer rational span DAG with explicit finite node indices.  The decoded
vectors may coincide, but their nodes remain distinct; hence shared arithmetic data
can be transported functorially through one-site extension. -/
structure RationalIndexedSpanEncodingDAGOfHeight
    (depth : ℕ) (height : Fin depth → ℕ)
    (node : Fin (depth + 1) → Type*)
    [nodeFintype : ∀ r, Fintype (node r)]
    (value : ∀ r, node r → LeftBlockVector L q k) where
  layer : ∀ j : Fin depth,
    RationalIndexedSpanEncodingOfHeight (height j)
      (node j.castSucc) (node j.succ) (value j.castSucc) (value j.succ)

namespace RationalIndexedSpanEncodingDAGOfHeight

/-- One-site extension transports every layer of an indexed span DAG simultaneously.
The node set at each layer is multiplied by the `q` computational-basis labels, while
all old coefficient heights are preserved. -/
noncomputable def extend
    {depth : ℕ} {height : Fin depth → ℕ}
    {node : Fin (depth + 1) → Type*}
    [nodeFintype : ∀ r, Fintype (node r)]
    {value : ∀ r, node r → LeftBlockVector L q (i - 1)}
    (D : RationalIndexedSpanEncodingDAGOfHeight depth height node value)
    (hheight : ∀ j, 1 ≤ height j) :
    RationalIndexedSpanEncodingDAGOfHeight depth height
      (fun r ↦ node r × Fin q)
      (fun r a ↦ AreaLaw.extendSite i a.2 (value r a.1)) where
  layer j := (D.layer j).extend (hheight j)

end RationalIndexedSpanEncodingDAGOfHeight

/-- The unconditional rational support-coordinate construction produces an explicit
finite family of compactly encoded rational columns over the original retained family.
Its cardinality is at most `n m`, and every exact support-isometry slice is close to a
member of this family.  The height and error retain the conditioning radius `R`; a
polynomial runtime corollary therefore requires a polynomial bound on `R`. -/
theorem exists_rational_spanColumnFamily
    (S : Finset (LeftBlockVector L q k)) (m : ℕ) {n : ℕ}
    (Z : Matrix ((CutLeft L q k × CutSite L q k) × Fin m) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = (reindex
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (Entropy.subsetSplitEquiv (fun _ : Fin L ↦ q) (leftBlock_mono (Nat.sub_le k 1)))
      (spanProjection (S : Set (LeftBlockVector L q k)))) ⊗ₖ
        (1 : Matrix (Fin m) (Fin m) ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ qc : Fin n → Fin m → S → ℂ,
      let H := rationalBoundedMatrixGridHeight R δ
      let T := spanColumnFamily S m qc
      (∀ j a s, HasRationalComplexCoordinatesOfHeight H (qc j a s)) ∧
      T.card ≤ n * m ∧
      Nonempty (RationalSpanFamilyEncodingOfHeight H S T) ∧
      ∀ j a, ∃ w ∈ T,
        ‖WithLp.toLp 2 (fun x ↦
            gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a)) - w‖ ≤
          S.card * δ * R := by
  obtain ⟨R, hR, qc, hqc, hclose⟩ :=
    exists_rational_boundarySupportCoordinates S m Z hZ hZZ hδ
  refine ⟨R, hR, qc, hqc, spanColumnFamily_card_le S m qc,
    ⟨rationalSpanFamilyEncodingOfCoefficients S m qc hqc⟩, ?_⟩
  exact exists_mem_spanColumnFamily_close S m qc
    (fun j a ↦ WithLp.toLp 2 (fun x ↦
      gluingLeftCoordinates L q k m (WithLp.toLp 2 (Z.col j)) (x, a))) hclose

/-- Data-bearing invariant for a viable output family stored as rational linear
combinations of a height-bounded rational MPS input family.  This is the compact form
appropriate after LVV size trimming. -/
structure RationalSpanViableMPSDataOfHeight
    (H Hv : ℕ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)) (s b : ℕ) (δ : ℝ)
    (S T : Finset (LeftBlockVector L q k)) where
  input_representation : ∀ u : S,
    RationalLeftOpenMPSRepresentationOfHeight Hv b u.1
  encoding : RationalSpanFamilyEncodingOfHeight H S T
  card_le : T.card ≤ s
  viable : IsViable Γ δ (T : Set (LeftBlockVector L q k))

namespace RationalSpanViableMPSDataOfHeight

/-- Forgetting the compact rational encoding gives the ordinary viable-MPS predicate,
with the finite-span bond budget. -/
theorem isViableMPS
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T) :
    IsViableMPS Γ s (S.card * max 1 b) δ T :=
  ⟨D.card_le,
    fun v hv ↦ D.encoding.isLeftOpenMPS
      (fun u hu ↦ (D.input_representation ⟨u, hu⟩).data.isLeftOpenMPS) ⟨v, hv⟩,
    D.viable⟩

/-- Every queried coordinate of the compact viable output has the uniform rational
height bound inherited from its coefficients and input tensors. -/
theorem coordinate_height
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hHv : 0 < Hv) (hk : k ≤ L) (t : T)
    (x : Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) :
    HasRationalComplexCoordinatesOfHeight
      (RationalSpanFamilyEncodingOfHeight.outputCoordinateHeight H Hv b k S.card)
      (t.1 x) :=
  D.encoding.coordinate_height hHv hk D.input_representation t x

/-- A compact span-encoded output supplies exactly the coordinate-rational viable-MPS
invariant required by the next LVV iteration.  No direct-sum tensor expansion is
performed: the bond bound follows from finite-span closure, while rationality is
queried through the stored coefficient array. -/
theorem coordinateViableMPSData
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hHv : 0 < Hv) (hk : k ≤ L) :
    RationalCoordinateViableMPSDataOfHeight
      (RationalSpanFamilyEncodingOfHeight.outputCoordinateHeight H Hv b k S.card)
      Γ s (S.card * max 1 b) δ T where
  card_le := D.card_le
  isLeftOpenMPS t := D.encoding.isLeftOpenMPS
    (fun u hu ↦ (D.input_representation ⟨u, hu⟩).data.isLeftOpenMPS) t
  coordinate_height t x := D.coordinate_height hHv hk t x
  viable := D.viable

/-- Enlarging the permitted overlap error leaves all rational encoding, cardinality,
and bond data unchanged. -/
noncomputable def mono_error
    {H Hv : ℕ} {Γ : EuclideanSpace ℂ (Fin L → Fin q)} {s b : ℕ} {δ δ' : ℝ}
    {S T : Finset (LeftBlockVector L q k)}
    (D : RationalSpanViableMPSDataOfHeight H Hv Γ s b δ S T)
    (hδ : δ ≤ δ') :
    RationalSpanViableMPSDataOfHeight H Hv Γ s b δ' S T where
  input_representation := D.input_representation
  encoding := D.encoding
  card_le := D.card_le
  viable := by
    obtain ⟨φ, hφ, hoverlap, hsupport⟩ := D.viable
    exact ⟨φ, hφ, hoverlap.trans' (by linarith), hsupport⟩

end RationalSpanViableMPSDataOfHeight

end TNLean.MPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SplitSupportSize

/-!
# Physical logarithmic dimensions for actual transport

For local physical dimension `q ≥ 1`, a region of at most `(2r₀+1)²`
sites has logarithmic dimension at most `1 + (2r₀+1)² log q`. This is a
concrete choice of the transport parameter, derived from the actual fill,
charge, and splitting-support cardinalities. Arbitrary auxiliary dimensions
do not occur. Unsplit designated supports are deliberately left unbounded.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 331–352, and `08-scanner.tex`, lines 225–233,
at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The geometric physical-dimension bound for the transport parameter. -/
noncomputable def transportLogDimBound (q r : ℕ) : ℝ :=
  1 + (((2 * r + 1) ^ 2 : ℕ) : ℝ) * Real.log q

/-- The physical dimension cap satisfies the source requirement `ℓ ≥ 1`. -/
theorem one_le_transportLogDimBound {q : ℕ} (hq : 1 ≤ q) (r : ℕ) :
    1 ≤ transportLogDimBound q r := by
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast hq)))

variable {V : Type*}

/-- The tensor product over physical sites has dimension `q^|B|`. Including the
factor `e` gives exactly `1 + |B| log q`, also for the empty region and `q = 1`. -/
theorem log_physicalDimension_eq (B : Finset V) {q : ℕ} (hq : 1 ≤ q) :
    Real.log (Real.exp 1 * (q : ℝ) ^ B.card) = 1 + (B.card : ℝ) * Real.log q := by
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))),
    Real.log_exp, Real.log_pow]

/-- A physical site count controls the logarithmic tensor-product dimension. -/
theorem log_physicalDimension_le_of_card_le (B : Finset V) {q N : ℕ}
    (hq : 1 ≤ q) (hB : B.card ≤ N) :
    Real.log (Real.exp 1 * (q : ℝ) ^ B.card) ≤ 1 + (N : ℝ) * Real.log q := by
  rw [log_physicalDimension_eq B hq]
  exact add_le_add_right (mul_le_mul_of_nonneg_right (show (B.card : ℝ) ≤ N by exact_mod_cast hB)
    (Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq))) 1

/-- Physical-only regions in the augmented factor set have dimension `q^|B|`.
The dimensions at both auxiliary factors are completely unrestricted. -/
theorem prod_physical_subsystem_dimension (B : Finset V) (n : V ⊕ Bool → ℕ)
    (q : ℕ) (hphysical : ∀ x, n (Sum.inl x) = q) :
    (∏ v ∈ B.map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ Bool), (n v : ℝ)) =
      (q : ℝ) ^ B.card := by
  simp [Finset.prod_map, hphysical]

variable [Fintype V] [DecidableEq V]

/-- Every actual fill has logarithmic dimension at most `1 + log q`, even if
its scheduled site is absent or already assigned. -/
theorem log_fill_moved_dimension_le (A : Finset V) (depth : V → ℤ) (n : ℕ)
    (lo hi : ℤ) (k : ℕ) (σ : PhysicalPartition V) {q : ℕ} (hq : 1 ≤ q) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (middle σ \ middle (fill A depth n lo hi k σ)).card) ≤ 1 + Real.log q := by
  simpa using log_physicalDimension_le_of_card_le _ hq
    (card_fill_moved_le_one A depth n lo hi k σ)

namespace CollarScan

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- Every actual charge satisfies the explicit logarithmic dimension cap. No
history regularity, positive radius, or positive charge capacity is assumed. -/
theorem log_chargeStep_moved_dimension_le_domainGraph {Λ : Finset (ℤ × ℤ)}
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (g r k : ℕ) (c : Bool × Fin S.M) (σ : PhysicalPartition (Site Λ))
    {q : ℕ} (hq : 1 ≤ q) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (middle σ \ middle (S.chargeStep g r k c σ)).card) ≤
        transportLogDimBound q S.r₀ :=
  log_physicalDimension_le_of_card_le _ hq
    (S.card_chargeStep_moved_le_domainGraph hgraph g r k c σ)

/-- A designated support has the explicit physical logarithmic dimension cap
when it splits some completed status. Large supports that never split incur no cap. -/
theorem log_designatedSupport_dimension_le_of_state_split_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hq : 1 ≤ q) (hL : 8 * S.K * S.m ≤ L)
    (hs : S.designatedSplitIncidence (S.state h g) L i side) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card) ≤
        transportLogDimBound q S.r₀ :=
  log_physicalDimension_le_of_card_le _ hq
    (S.card_designatedSupport_le_of_state_split_domainGraph hgraph h g side i hL hs)

/-- The same physical cap applies when the support splits a pre-charge status. -/
theorem log_designatedSupport_dimension_le_of_old_split_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hq : 1 ≤ q) (hL : 8 * S.K * S.m ≤ L)
    (hs : S.designatedSplitIncidence (S.oldChargeState h g) L i side) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card) ≤
        transportLogDimBound q S.r₀ :=
  log_physicalDimension_le_of_card_le _ hq
    (S.card_designatedSupport_le_of_old_split_domainGraph hgraph h g side i hL hs)

/-- Every non-contained designated support in a completed status has the cap,
without any separate support-compatibility or terminal-classification assumption. -/
theorem log_designatedSupport_dimension_le_of_state_not_constant_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (i : I)
    (hq : 1 ≤ q) (hL : 8 * S.K * S.m ≤ L)
    (hnc : ¬ ∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i), S.state h g x = part) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card) ≤
        transportLogDimBound q S.r₀ := by
  rw [S.designatedSupport_eq_ball_of_state_not_constant h g i hL hnc]
  exact log_physicalDimension_le_of_card_le _ hq (S.card_ball_le_domainGraph hgraph i)

/-- Every non-contained designated support in a pre-charge status has the same cap. -/
theorem log_designatedSupport_dimension_le_of_old_not_constant_domainGraph
    {Λ : Finset (ℤ × ℤ)} (S : CollarScan (Site Λ) I)
    (hgraph : S.graph = domainGraph Λ) {k L q : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (i : I)
    (hq : 1 ≤ q) (hL : 8 * S.K * S.m ≤ L)
    (hnc : ¬ ∃ part : Option Bool, ∀ x ∈
      designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i),
        S.oldChargeState h g x = part) :
    Real.log (Real.exp 1 * (q : ℝ) ^
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).card) ≤
        transportLogDimBound q S.r₀ := by
  rw [S.designatedSupport_eq_ball_of_old_not_constant h g i hL hnc]
  exact log_physicalDimension_le_of_card_le _ hq (S.card_ball_le_domainGraph hgraph i)

end CollarScan
end TNLean.PEPS.AreaLaw.Scan

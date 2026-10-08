/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelSchedule

/-!
# Guides read after a small displacement

A guide of the source is specified by its open polygonal chambers. On a boundary it is read by one
consistent tie convention: the sampled point is moved by an arbitrarily small generic vector `v`
into an incident chamber, and the label found there is taken. The formal guides of the schedule
instead fix the label on a boundary by a rule of their own: on an interface curve `x = t` of a band
the word takes the label for `x ≥ t`. The normal coordinate `d` points into the square and the
curves have slopes at most `8/1000` in edge coordinates, so a displacement `v` whose two components
are not small relative to each other crosses to the side `x > t` on two edges of a square and to
the side `x < t` on the other two: the two conventions differ on the interface curves.

This file proves that the estimates of Lemma 7.2 do not depend on that difference. A labelling
`f'` *reads* a labelling `f` after the displacement `v` if, at every point `p`, `f' p = f (p + ε v)`
for all small `ε > 0`. When `f` agrees with the open chambers of the source off finitely many
segments and `v` is parallel to none of them, the ray `p + ε v` leaves those segments at once, so
the source's sampled guide reads `f` after `v`. We prove:

* readings of two labellings along one displacement differ only in the closure of the set where
  the labellings differ, and a reading takes a value other than `c` only in the closure of the set
  where the labelling does;
* consequently every estimate stated, as in the source, for closures of changed regions,
  obstructing sets and noncommon sets passes from the labellings to their readings;
* Lemma 7.2 on every block of the hierarchy (`blockRepainting_central`, `blockRepainting_auxStep`,
  `blockRepainting_mainStep`, `blockRepainting_exchange`) holds for the readings of the schedule's
  guides after any displacement `v`, so for the source's sampled guides on all four edges.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: guides and the tie convention
  (lines 69–80), the edge construction (lines 142–241), and Lemma 7.2 `lem:geometry-angular`
  (lines 243–319).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Readings after a displacement -/

/-- The labelling `f'` reads `f` after a small displacement along `v`: at every point `p`, the
label `f' p` equals `f (p + ε • v)` for all sufficiently small `ε > 0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:71–77`: "move a sampled point
by an arbitrarily small generic vector into an incident chamber, consistently across all
descriptions, and take the resulting label". -/
def IsDisplacedReading {X ι : Type*} [AddCommGroup X] [Module ℝ X] (f' f : X → ι) (v : X) :
    Prop :=
  ∀ p, ∀ᶠ ε in 𝓝[>] (0 : ℝ), f' p = f (p + ε • v)

/-- A constant labelling reads itself. -/
theorem isDisplacedReading_const {X ι : Type*} [AddCommGroup X] [Module ℝ X] (c : ι) (v : X) :
    IsDisplacedReading (fun _ : X => c) (fun _ => c) v :=
  fun _ => Eventually.of_forall fun _ => rfl

section Readings

variable {X ι : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [ContinuousAdd X]
  [ContinuousSMul ℝ X] {v : X}

/-- A small displacement of `p` along `v` stays in every neighborhood of `p`. -/
theorem tendsto_add_smul_nhdsGT (p v : X) :
    Tendsto (fun ε : ℝ => p + ε • v) (𝓝[>] 0) (𝓝 p) := by
  have h : Tendsto (fun ε : ℝ => p + ε • v) (𝓝 0) (𝓝 (p + (0 : ℝ) • v)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Readings along one displacement of two labellings that agree near `p` agree at `p`. -/
theorem IsDisplacedReading.eq_of_eventuallyEq {f₁ f₂ f₁' f₂' : X → ι}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v) {p : X}
    (h : f₁ =ᶠ[𝓝 p] f₂) : f₁' p = f₂' p := by
  have hε := (tendsto_add_smul_nhdsGT p v).eventually h
  obtain ⟨ε, e₁, e₂, e⟩ := ((h₁ p).and ((h₂ p).and hε)).exists
  rw [e₁, e₂, e]

/-- **Changed sets of readings.** Readings along one displacement differ only in the closure of
the set where the labellings differ.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:76–80`: separation estimates
are stated for closures and remain valid for the sampled labels. -/
theorem IsDisplacedReading.ne_subset_closure {f₁ f₂ f₁' f₂' : X → ι}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v) :
    {p | f₁' p ≠ f₂' p} ⊆ closure {p | f₁ p ≠ f₂ p} := by
  intro p hp
  by_contra hc
  refine hp (h₁.eq_of_eventuallyEq h₂ ?_)
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with q hq
  by_contra hne
  exact hq (subset_closure hne)

theorem IsDisplacedReading.closure_ne_subset {f₁ f₂ f₁' f₂' : X → ι}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v) :
    closure {p | f₁' p ≠ f₂' p} ⊆ closure {p | f₁ p ≠ f₂ p} :=
  closure_minimal (h₁.ne_subset_closure h₂) isClosed_closure

/-- A reading takes a value other than `c` only in the closure of the set where the labelling
does. -/
theorem IsDisplacedReading.closure_ne_const_subset {f f' : X → ι}
    (h : IsDisplacedReading f' f v) (c : ι) :
    closure {p | f' p ≠ c} ⊆ closure {p | f p ≠ c} :=
  h.closure_ne_subset (isDisplacedReading_const c v)

/-- The positions that are not common `C` on two readings lie in the closure of those of the two
labellings. -/
theorem IsDisplacedReading.closure_noncommon_subset {f₁ f₂ f₁' f₂' : X → ι}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v) (C : ι) :
    closure {p | f₁' p ≠ C ∨ f₂' p ≠ C} ⊆ closure {p | f₁ p ≠ C ∨ f₂ p ≠ C} := by
  refine closure_minimal (fun p hp => ?_) isClosed_closure
  rcases hp with hp | hp
  · exact closure_mono (fun q hq => Or.inl hq)
      (h₁.closure_ne_const_subset C (subset_closure hp))
  · exact closure_mono (fun q hq => Or.inr hq)
      (h₂.closure_ne_const_subset C (subset_closure hp))

/-- The same inside an open set `Y`: the positions of `Y` that are not common `C` on two readings
lie in the closure of those of the two labellings. -/
theorem IsDisplacedReading.closure_noncommon_inter_subset {f₁ f₂ f₁' f₂' : X → ι}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v) (C : ι) {Y : Set X}
    (hY : IsOpen Y) :
    closure {p | p ∈ Y ∧ (f₁' p ≠ C ∨ f₂' p ≠ C)} ⊆
      closure {p | p ∈ Y ∧ (f₁ p ≠ C ∨ f₂ p ≠ C)} := by
  refine closure_minimal (fun p ⟨hpY, hp⟩ => ?_) isClosed_closure
  have := (h₁.closure_noncommon_subset h₂ C) (subset_closure hp)
  exact hY.inter_closure ⟨hpY, this⟩

end Readings

/-! ### Transfer of the estimates -/

section Transfer

variable {X ι : Type*} [AddCommGroup X] [Module ℝ X] [PseudoMetricSpace X] [ContinuousAdd X]
  [ContinuousSMul ℝ X] {v : X}

/-- **Transfer of a clearance estimate to readings.** If every point of the closure of the set
where `f₁`, `f₂` differ is at distance at least `Φ y` from the closure of the positions where `g`
is not `P`, the same holds for readings of the three labellings along one displacement.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:76–80`. -/
theorem IsDisplacedReading.clearance {f₁ f₂ g f₁' f₂' g' : X → ι} {P : ι} {Φ : X → ℝ}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v)
    (hg : IsDisplacedReading g' g v)
    (H : ∀ y ∈ closure {p | f₁ p ≠ f₂ p}, ∀ z ∈ closure {p | g p ≠ P}, Φ y ≤ dist y z) :
    ∀ y ∈ closure {p | f₁' p ≠ f₂' p}, ∀ z ∈ closure {p | g' p ≠ P}, Φ y ≤ dist y z :=
  fun y hy z hz => H y (h₁.closure_ne_subset h₂ hy) z (hg.closure_ne_const_subset P hz)

/-- **Transfer of a diameter bound to readings.** -/
theorem IsDisplacedReading.dist_le {f₁ f₂ f₁' f₂' : X → ι} {c : ℝ}
    (h₁ : IsDisplacedReading f₁' f₁ v) (h₂ : IsDisplacedReading f₂' f₂ v)
    (H : ∀ y ∈ closure {p | f₁ p ≠ f₂ p}, ∀ z ∈ closure {p | f₁ p ≠ f₂ p}, dist y z ≤ c) :
    ∀ y ∈ closure {p | f₁' p ≠ f₂' p}, ∀ z ∈ closure {p | f₁' p ≠ f₂' p}, dist y z ≤ c :=
  fun y hy z hz => H y (h₁.closure_ne_subset h₂ hy) z (h₁.closure_ne_subset h₂ hz)

end Transfer

/-! ### Lemma 7.2 for the sampled guides -/

section Lemma72

variable {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι) (S : ℤ × ℤ) (B : ι) {v : ℝ × ℝ}

local notation "R" => blockBaseline hn lab S B
local notation "o" => blockCorner n S

/-- **Lemma 7.2 for the sampled guides, central birth.** For readings `g₀`, `g₁`, along one
displacement `v`, of the block guide and of the guide after the central birth of the block `S`,
the changed region has closure of diameter at most `n`, and each of its points `y` lies at sup
distance at least `a₀ min(n, d_V(y))` from the closure of the positions where `g₀` is not the old
label.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:71–80, 254–264, 276–281`. -/
theorem blockRepainting_central_of_reading {g₀ g₁ : ℝ × ℝ → ι}
    (h₀ : IsDisplacedReading g₀ (blockGuide n lab) v)
    (h₁ : IsDisplacedReading g₁ (shiftGuide o (R).centralGuide) v) :
    (∀ y ∈ closure {p | g₀ p ≠ g₁ p}, ∀ z ∈ closure {p | g₀ p ≠ g₁ p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | g₀ p ≠ g₁ p}, ∀ z ∈ closure {p | g₀ p ≠ lab S},
      angularConstant * min n (cornerMarkDist n (y - o)) ≤ dist y z :=
  ⟨h₀.dist_le h₁ (blockRepainting_central hn lab S B).1,
    h₀.clearance h₁ h₀ (blockRepainting_central hn lab S B).2⟩

/-- **Lemma 7.2 for the sampled guides, auxiliary births.** For readings along one displacement of
the auxiliary guides before, after and surrounding an elementary birth on the auxiliary sheet of
the edge `e`, the estimates of `blockRepainting_auxStep` hold.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:71–80, 254–264, 283–286`. -/
theorem blockRepainting_auxStep_of_reading (e : SquareEdge) {op : BandOperation ι}
    (hop : op ∈ auxSteps (lab S) B (lab (e.nbrBlock S))) {gb ga gs : ℝ × ℝ → ι}
    (hb : IsDisplacedReading gb (shiftGuide o ((R).auxGuide e op.before)) v)
    (ha : IsDisplacedReading ga (shiftGuide o ((R).auxGuide e op.after)) v)
    (hs : IsDisplacedReading gs (shiftGuide o ((R).auxGuide e op.surrounding)) v) :
    (∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gb p ≠ ga p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gs p ≠ op.label},
      angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  ⟨hb.dist_le ha (blockRepainting_auxStep hn lab S B e hop).1,
    hb.clearance ha hs (blockRepainting_auxStep hn lab S B e hop).2⟩

/-- **Lemma 7.2 for the sampled guides, main births and deaths.** For readings along one
displacement of the main guides before, after and surrounding an elementary birth or death on the
main sheet along the edge `e`, after the edges of `E`, the estimates of `blockRepainting_mainStep`
hold.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-birth-clearance`, `06-geometry.tex:71–80, 254–264, 286–293`. -/
theorem blockRepainting_mainStep_of_reading (E : List SquareEdge) (e : SquareEdge)
    {op : BandOperation ι} (hop : op ∈ mainSteps (lab S) B (lab (e.nbrBlock S)))
    {gb ga gs : ℝ × ℝ → ι}
    (hb : IsDisplacedReading gb (shiftGuide o ((R).mainGuide E e op.before)) v)
    (ha : IsDisplacedReading ga (shiftGuide o ((R).mainGuide E e op.after)) v)
    (hs : IsDisplacedReading gs (shiftGuide o ((R).mainGuide E e op.surrounding)) v) :
    (∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gb p ≠ ga p}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gb p ≠ ga p}, ∀ z ∈ closure {p | gs p ≠ op.label},
      angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z :=
  ⟨hb.dist_le ha (blockRepainting_mainStep hn lab S B E e hop).1,
    hb.clearance ha hs (blockRepainting_mainStep hn lab S B E e hop).2⟩

/-- **Lemma 7.2 for the sampled guides, lens exchange.** For readings `gm`, `gx`, along one
displacement, of the main guide with the starting word and of the auxiliary guide with the
auxiliary word along the edge `e`, every point `y` in the closure of the positions that are not
common `C_e` on `gm` and `gx` lies at sup distance at least `a₀ min(n, d_V(y))` from the boundary
of the translated lens, and the closure of those positions inside the translated lens has
diameter at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`, equation
`eq:geometry-exchange-clearance`, `06-geometry.tex:71–80, 265–272, 295–299`, and the diameter of
the exchange, `06-geometry.tex:421–424`. -/
theorem blockRepainting_exchange_of_reading (E : List SquareEdge) (e : SquareEdge)
    {gm gx : ℝ × ℝ → ι}
    (hm : IsDisplacedReading gm
      (shiftGuide o ((R).mainGuide E e (edgeStartWord (lab S) B (lab (e.nbrBlock S))))) v)
    (hx : IsDisplacedReading gx
      (shiftGuide o ((R).auxGuide e (auxWord (lab S) B (lab (e.nbrBlock S))))) v) :
    (∀ y ∈ closure {p | p - o ∈ edgeLens n e ∧ (gm p ≠ lab (e.nbrBlock S) ∨
        gx p ≠ lab (e.nbrBlock S))},
      ∀ z ∈ closure {p | p - o ∈ edgeLens n e ∧ (gm p ≠ lab (e.nbrBlock S) ∨
        gx p ≠ lab (e.nbrBlock S))}, dist y z ≤ n) ∧
    ∀ y ∈ closure {p | gm p ≠ lab (e.nbrBlock S) ∨ gx p ≠ lab (e.nbrBlock S)},
      ∀ z ∈ frontier ((fun p => p - o) ⁻¹' edgeLens n e),
        angularConstant * min n (edgeMarkDist n e (y - o)) ≤ dist y z := by
  have hY : IsOpen ((fun p : ℝ × ℝ => p - o) ⁻¹' edgeLens n e) :=
    (isOpen_edgeBand n e _ _).preimage (continuous_id.sub continuous_const)
  have H := blockRepainting_exchange hn lab S B E e
  exact ⟨fun y hy z hz => H.2.1 y (hm.closure_noncommon_inter_subset hx _ hY hy) z
      (hm.closure_noncommon_inter_subset hx _ hY hz),
    fun y hy z hz => H.2.2 y (hm.closure_noncommon_subset hx _ hy) z hz⟩

end Lemma72

end TNLean.PEPS.Approximation

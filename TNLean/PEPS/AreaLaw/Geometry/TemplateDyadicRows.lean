/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers
import TNLean.PEPS.AreaLaw.Geometry.MixedDyadicSquares

/-!
# Mixed dyadic squares of an integer-dilated template piece

An occupied horizontal row of an actual sampled polygon can be reached from
any other occupied row with at most the same horizontal displacement. This
property survives exact integer sup-norm dilation. In every interior dyadic
row block, a mixed square therefore lies near one of the two row endpoints.
The two extreme row blocks are counted using the piece diameter.

Original proofs from `scanner:mixed-piece`, lines 622–649 of `08-scanner.tex`,
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The four integer supporting strips give a nearby sampled point on any
occupied row, with no positivity or width assumption on the sampled piece. -/
theorem Template.exists_sample_in_row_within {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {x y z d : ℤ}
    (hp : (x, y) ∈ T.sample i) (hyz : y - d ≤ z ∧ z ≤ y + d)
    (hz : (latticeRow (T.sample i) z).Nonempty) :
    ∃ w : ℤ, (w, z) ∈ T.sample i ∧ x - d ≤ w ∧ w ≤ x + d := by
  obtain ⟨lx, ux, ly, uy, ls, us, ld, ud, h⟩ := T.exists_sample_four_strip_bounds i
  have hp' := (h x y).mp hp
  obtain ⟨w, hw⟩ := hz
  have hw' := (h w z).mp (mem_latticeRow.mp hw)
  let L := max lx (max (ls - z) (ld + z))
  let U := min ux (min (us - z) (ud + z))
  have hLU : L ≤ U := by dsimp [L, U]; omega
  have hL : L ≤ x + d := by dsimp [L]; omega
  have hU : x - d ≤ U := by dsimp [U]; omega
  refine ⟨max L (min x U), ?_, ?_, ?_⟩
  · apply (h _ z).mpr
    dsimp [L, U] at *
    omega
  · omega
  · omega

/-- Exact integer dilation preserves the occupied-row displacement bound.
The proof clamps an actual source row and then an actual integer coordinate. -/
theorem Template.exists_dilation_in_row_within {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r : ℕ) {x y z d : ℤ}
    (hp : (x, y) ∈ ambientDilation (T.sample i) r)
    (hyz : y - d ≤ z ∧ z ≤ y + d)
    (hz : (latticeRow (ambientDilation (T.sample i) r) z).Nonempty) :
    ∃ w : ℤ, (w, z) ∈ ambientDilation (T.sample i) r ∧ x - d ≤ w ∧ w ≤ x + d := by
  obtain ⟨p, hp, hpx⟩ := mem_ambientDilation_iff.mp hp
  obtain ⟨v, hv⟩ := hz
  obtain ⟨q, hq, hqv⟩ := mem_ambientDilation_iff.mp (mem_latticeRow.mp hv)
  let t := max (z - r) (min p.2 (z + r))
  have ht : z - r ≤ t ∧ t ≤ z + r := by dsimp [t]; omega
  have hnear : p.2 - d ≤ t ∧ t ≤ p.2 + d := by dsimp [t]; omega
  have hbetween : (p.2 ≤ t ∧ t ≤ q.2) ∨ (q.2 ≤ t ∧ t ≤ p.2) := by
    dsimp [t]
    omega
  have hrow : (latticeRow (T.sample i) t).Nonempty := by
    rcases hbetween with h | h
    · exact T.latticeRow_nonempty_between i ⟨p.1, mem_latticeRow.mpr hp⟩
        ⟨q.1, mem_latticeRow.mpr hq⟩ h.1 h.2
    · exact T.latticeRow_nonempty_between i ⟨q.1, mem_latticeRow.mpr hq⟩
        ⟨p.1, mem_latticeRow.mpr hp⟩ h.1 h.2
  obtain ⟨a, ha, hpa⟩ := T.exists_sample_in_row_within i hp hnear hrow
  let w := max (a - r) (min x (a + r))
  refine ⟨w, mem_ambientDilation_iff.mpr ⟨(a, t), ha, ?_⟩, ?_, ?_⟩
  · dsimp [w]
    omega
  · dsimp [w]
    omega
  · dsimp [w]
    omega

private theorem quotient_interval_card (a b u : ℤ) (hu : 0 < u) (hab : a ≤ b) :
    u * ((Finset.Icc (a / u) (b / u)).card : ℤ) ≤ b - a + 2 * u := by
  have hdiv := Int.ediv_le_ediv hu hab
  rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
  have ha := Int.lt_ediv_add_one_mul_self a hu
  have hb := Int.ediv_mul_le b (ne_of_gt hu)
  nlinarith

private theorem quotient_near (x y a u z : ℤ) (hu : 0 < u)
    (hx : z * u ≤ x ∧ x < z * u + u)
    (hy : z * u ≤ y ∧ y < z * u + u)
    (h : a - u ≤ x ∧ y < a + u) :
    z ∈ Finset.Icc (a / u - 2) (a / u + 2) := by
  have hlo := Int.ediv_mul_le a (ne_of_gt hu)
  have hhi := Int.lt_ediv_add_one_mul_self a hu
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hz
    have : z ≤ a / u - 3 := by omega
    nlinarith
  · by_contra hz
    have : a / u + 3 ≤ z := by omega
    nlinarith

private theorem quotient_near_right (x y a u z : ℤ) (hu : 0 < u)
    (hx : z * u ≤ x ∧ x < z * u + u)
    (hy : z * u ≤ y ∧ y < z * u + u)
    (h : x ≤ a + u ∧ a - u < y) :
    z ∈ Finset.Icc (a / u - 2) (a / u + 2) := by
  have hlo := Int.ediv_mul_le a (ne_of_gt hu)
  have hhi := Int.lt_ediv_add_one_mul_self a hu
  apply Finset.mem_Icc.mpr
  constructor
  · by_contra hz
    have : z ≤ a / u - 3 := by omega
    nlinarith
  · by_contra hz
    have : a / u + 3 ≤ z := by omega
    nlinarith

private theorem mixed_interior_columns {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r k : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ mixedDyadicIndices (ambientDilation (T.sample i) r) k)
    (hrows : ∀ y : ℤ, z.2 * 2 ^ k ≤ y → y < z.2 * 2 ^ k + 2 ^ k →
      (latticeRow (ambientDilation (T.sample i) r) y).Nonempty)
    (hbase : (latticeRow (ambientDilation (T.sample i) r) (z.2 * 2 ^ k)).Nonempty) :
    let l := (latticeRow (ambientDilation (T.sample i) r) (z.2 * 2 ^ k)).min' hbase
    let v := (latticeRow (ambientDilation (T.sample i) r) (z.2 * 2 ^ k)).max' hbase
    z.1 ∈ Finset.Icc (l / 2 ^ k - 2) (l / 2 ^ k + 2) ∪
      Finset.Icc (v / 2 ^ k - 2) (v / 2 ^ k + 2) := by
  dsimp only
  let R := latticeRow (ambientDilation (T.sample i) r) (z.2 * 2 ^ k)
  let l := R.min' hbase
  let v := R.max' hbase
  have hl : (l, z.2 * 2 ^ k) ∈ ambientDilation (T.sample i) r :=
    mem_latticeRow.mp (Finset.min'_mem _ hbase)
  have hv : (v, z.2 * 2 ^ k) ∈ ambientDilation (T.sample i) r :=
    mem_latticeRow.mp (Finset.max'_mem _ hbase)
  have hu : (0 : ℤ) < 2 ^ k := by positivity
  obtain ⟨⟨p, hp, hpS⟩, q, hq, hqS⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
  have hpB := (mem_latticeDyadicCell_iff_bounds k z p).mp hp
  have hqB := (mem_latticeDyadicCell_iff_bounds k z q).mp hq
  obtain ⟨w, hw, hwp⟩ := T.exists_dilation_in_row_within i r hpS
    (show p.2 - 2 ^ k ≤ z.2 * 2 ^ k ∧ z.2 * 2 ^ k ≤ p.2 + 2 ^ k by omega) hbase
  have hwl : l ≤ w := Finset.min'_le _ _ (mem_latticeRow.mpr hw)
  have hwv : w ≤ v := Finset.le_max' _ _ (mem_latticeRow.mpr hw)
  have hqrow := hrows q.2 hqB.2.2.1 hqB.2.2.2
  obtain ⟨lq, hlq, hlqnear⟩ := T.exists_dilation_in_row_within i r hl
    (show z.2 * 2 ^ k - 2 ^ k ≤ q.2 ∧ q.2 ≤ z.2 * 2 ^ k + 2 ^ k by omega) hqrow
  obtain ⟨vq, hvq, hvqnear⟩ := T.exists_dilation_in_row_within i r hv
    (show z.2 * 2 ^ k - 2 ^ k ≤ q.2 ∧ q.2 ≤ z.2 * 2 ^ k + 2 ^ k by omega) hqrow
  have hout : q.1 < lq ∨ vq < q.1 := by
    by_contra h
    have hbetween : lq ≤ q.1 ∧ q.1 ≤ vq := by omega
    exact hqS (mem_latticeRow.mp (T.mem_latticeRow_dilation_of_between i r
      (mem_latticeRow.mpr hlq) (mem_latticeRow.mpr hvq) hbetween.1 hbetween.2))
  rcases hout with hout | hout
  · apply Finset.mem_union_left
    exact quotient_near p.1 q.1 l (2 ^ k) z.1 hu ⟨hpB.1, hpB.2.1⟩
      ⟨hqB.1, hqB.2.1⟩ (by omega)
  · apply Finset.mem_union_right
    exact quotient_near_right p.1 q.1 v (2 ^ k) z.1 hu ⟨hpB.1, hpB.2.1⟩
      ⟨hqB.1, hqB.2.1⟩ (by omega)

/-- At side `2^k`, the mixed squares of one actual integer-dilated polygon
have total side length at most `24 * (s₀ + r + 2^k)`. Empty and thin samples
are included. The bound is derived from sampling and allowed slopes. -/
theorem Template.card_mixedDyadicIndices_sample_dilation_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (r k : ℕ) :
    2 ^ k * (mixedDyadicIndices (ambientDilation (T.sample i) r) k).card ≤
      24 * (s₀ + r + 2 ^ k) := by
  classical
  by_cases hne : (T.sample i).Nonempty
  · obtain ⟨p, hp⟩ := hne
    obtain ⟨a, b, hab, hheight, hdomain⟩ := T.exists_dilation_row_domain i ⟨p, hp⟩
    let u : ℤ := 2 ^ k
    have hu : 0 < u := by dsimp [u]; positivity
    let lo := a - (r : ℤ)
    let hi := b + (r : ℤ)
    let X := Finset.Icc ((p.1 - s₀ - r) / u) ((p.1 + s₀ + r) / u)
    let Y := Finset.Icc (lo / u) (hi / u)
    let cols (y : ℤ) : Finset ℤ :=
      if h : (latticeRow (ambientDilation (T.sample i) r) (y * u)).Nonempty then
        let l := (latticeRow (ambientDilation (T.sample i) r) (y * u)).min' h
        let v := (latticeRow (ambientDilation (T.sample i) r) (y * u)).max' h
        Finset.Icc (l / u - 2) (l / u + 2) ∪ Finset.Icc (v / u - 2) (v / u + 2)
      else ∅
    have hcols (y : ℤ) : (cols y).card ≤ 10 := by
      dsimp only [cols]
      split_ifs with h
      · calc
          _ ≤ (Finset.Icc (_ / u - 2) (_ / u + 2)).card +
              (Finset.Icc (_ / u - 2) (_ / u + 2)).card := Finset.card_union_le _ _
          _ = 10 := by simp only [Int.card_Icc]; omega
      · simp
    let bands := Y.biUnion fun y ↦ (cols y).product {y}
    have hcover : mixedDyadicIndices (ambientDilation (T.sample i) r) k ⊆
        X.product {lo / u, hi / u} ∪ bands := by
      intro z hz
      obtain ⟨⟨x, hxcell, hxS⟩, _⟩ := (mem_mixedDyadicIndices _ _ _).mp hz
      have hxidx : x.1 / u = z.1 ∧ x.2 / u = z.2 := by
        have h := (mem_latticeDyadicCell k z x).mp hxcell
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      obtain ⟨q, hq, hqx⟩ := mem_ambientDilation_iff.mp hxS
      have hqbox := T.sample_subset_box i hp hq
      simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hqbox
      have hxX : z.1 ∈ X := by
        apply Finset.mem_Icc.mpr
        constructor
        · rw [← hxidx.1]
          exact Int.ediv_le_ediv hu (by omega)
        · rw [← hxidx.1]
          exact Int.ediv_le_ediv hu (by omega)
      have hxrow := (hdomain r x.2).mp ⟨x.1, mem_latticeRow.mpr hxS⟩
      have hzY : z.2 ∈ Y := by
        apply Finset.mem_Icc.mpr
        constructor
        · rw [← hxidx.2]
          exact Int.ediv_le_ediv hu hxrow.1
        · rw [← hxidx.2]
          exact Int.ediv_le_ediv hu hxrow.2
      by_cases hedge : z.2 = lo / u ∨ z.2 = hi / u
      · apply Finset.mem_union_left
        exact Finset.mem_product.mpr ⟨hxX, by simpa only [Finset.mem_insert,
          Finset.mem_singleton] using hedge⟩
      · have hzstrict : lo / u < z.2 ∧ z.2 < hi / u := by
          have h := Finset.mem_Icc.mp hzY
          omega
        have hrows (y : ℤ) (hy₀ : z.2 * 2 ^ k ≤ y)
            (hy₁ : y < z.2 * 2 ^ k + 2 ^ k) :
            (latticeRow (ambientDilation (T.sample i) r) y).Nonempty := by
          apply (hdomain r y).mpr
          have hlo := Int.lt_ediv_add_one_mul_self lo hu
          have hhi := Int.ediv_mul_le hi (ne_of_gt hu)
          have hzlo : lo / u + 1 ≤ z.2 := by omega
          have hzhi : z.2 + 1 ≤ hi / u := by omega
          change z.2 * u ≤ y at hy₀
          change y < z.2 * u + u at hy₁
          change lo ≤ y ∧ y ≤ hi
          constructor <;> nlinarith
        have hbase := hrows (z.2 * 2 ^ k) le_rfl (by
          change z.2 * u < z.2 * u + u
          omega)
        have hzcols : z.1 ∈ cols z.2 := by
          dsimp only [cols]
          rw [dite_eq_left hbase]
          exact mixed_interior_columns T i r k z hz hrows hbase
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨z.2, hzY, Finset.mem_product.mpr
          ⟨hzcols, Finset.mem_singleton_self _⟩⟩
    have hend : ({lo / u, hi / u} : Finset ℤ).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le (lo / u) {hi / u}
    have hcount : (mixedDyadicIndices (ambientDilation (T.sample i) r) k).card ≤
        2 * X.card + 10 * Y.card := by
      calc
        _ ≤ (X.product {lo / u, hi / u} ∪ bands).card := Finset.card_le_card hcover
        _ ≤ (X.product {lo / u, hi / u}).card + bands.card := Finset.card_union_le _ _
        _ ≤ X.card * 2 + ∑ y ∈ Y, 10 := by
          apply Nat.add_le_add
          · simpa only [Finset.product_eq_sprod, Finset.card_product] using
              Nat.mul_le_mul_left X.card hend
          · exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ ↦ by
              simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton,
                Nat.mul_one] using hcols y)
        _ = _ := by simp [Nat.mul_comm]
    have hX : u * (X.card : ℤ) ≤ 2 * s₀ + 2 * r + 2 * u := by
      have h := quotient_interval_card (p.1 - s₀ - r) (p.1 + s₀ + r) u hu (by omega)
      dsimp only [X]
      convert h using 1 <;> ring
    have hY : u * (Y.card : ℤ) ≤ 2 * s₀ + 2 * r + 2 * u := by
      calc
        _ ≤ hi - lo + 2 * u :=
          quotient_interval_card lo hi u hu (by dsimp [lo, hi]; omega)
        _ ≤ _ := by dsimp only [lo, hi]; omega
    have hcountZ : ((mixedDyadicIndices (ambientDilation (T.sample i) r) k).card : ℤ) ≤
        2 * (X.card : ℤ) + 10 * (Y.card : ℤ) := by exact_mod_cast hcount
    have hfinal : u * ((mixedDyadicIndices (ambientDilation (T.sample i) r) k).card : ℤ) ≤
        24 * ((s₀ : ℤ) + r + u) := by
      have hm := mul_le_mul_of_nonneg_left hcountZ (le_of_lt hu)
      nlinarith
    dsimp only [u] at hfinal
    exact_mod_cast hfinal
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he, ambientDilation]

end TNLean.PEPS.AreaLaw.Geometry

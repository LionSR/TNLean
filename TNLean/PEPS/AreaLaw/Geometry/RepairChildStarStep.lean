/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairChildStars
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# One repair step preserves isolated stars at the children

Suppose a parent at `v` with scale `S` has a local radial model, with wedge
assignment `σ`, in an open square of radius `r ≥ 3 d / 2` about `v`, where
`d = d(S)`. Consider any labelled family which, near a child `c = v + d e`,
consists of the old regions with the closed removal square deleted, keeping
their labels, and of the replacement runs of `σ` with the opposite labels.
Then `c` has an isolated star of every radius `ρ < d / 2`.

This is the local assertion of the repair induction: after normalization the
new boundaries lie on the parent's radial rays and on the sides of the
removal square, and the same finite configuration recurs at every
generation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417, and
`geometry:repair-induction`, lines 497–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable {ι : Type*}

theorem repairFanRunExteriorColor_runOf (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (s : RepairFanSlot) :
    repairFanRunExteriorColor ξ σ (repairFanRunOf ξ σ s) = ξ (σ s) :=
  rfl

theorem mem_supp_iff_repairFanRunOf {ξ : ι → Fin 2} {σ : RepairFanSlot → ι}
    (H : RepairFanRun ξ σ) (s : RepairFanSlot) : s ∈ H.supp ↔ repairFanRunOf ξ σ s = H :=
  SimpleGraph.ConnectedComponent.mem_supp_iff H s

/-- A wedge and its successor lie in one replacement run exactly when their
exterior labels agree.
Source: area-law Section 11, lines 404–417. -/
theorem repairFanRunOf_next_eq_iff (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (s : RepairFanSlot) :
    repairFanRunOf ξ σ s = repairFanRunOf ξ σ (cellFanNext s) ↔
      ξ (σ s) = ξ (σ (cellFanNext s)) := by
  constructor
  · intro h
    exact cellFanRun_color_eq (-1, -1) 1 (0, 0) repairFanSplit (repairExteriorColor ξ σ) _ _ h
  · intro h
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    exact ⟨(cellFanNext_ne_self s).symm,
      Or.inl (cellFanEnd_eq_cellFanStart_next (-1, -1) 1 (0, 0) s), h⟩

/-- Membership in the closed birth of a replacement run.
Source: area-law Section 11, lines 404–417. -/
theorem mem_repairReplacementBirthRegion_iff {ξ : ι → Fin 2} {σ : RepairFanSlot → ι}
    {v w : ℝ × ℝ} {S : ℝ} (H : RepairFanRun ξ σ) :
    w ∈ repairReplacementBirthRegion v S ξ σ H ↔
      ∃ s, repairFanRunOf ξ σ s = H ∧ w - v ∈ repairFanCone s ∧
        ‖w - v‖ ≤ repairHalfSide S := by
  have hd := repairHalfSide_pos S
  simp only [repairReplacementBirthRegion, repairAffineMap, cellFanRunRegion, Set.mem_image,
    Set.mem_iUnion, exists_prop, mem_normalizedTriangle_iff]
  constructor
  · rintro ⟨u, ⟨s, hs, hu, hun⟩, rfl⟩
    refine ⟨s, (mem_supp_iff_repairFanRunOf H s).mp hs, ?_, ?_⟩
    · rw [add_sub_cancel_left]
      exact smul_mem_repairFanCone hd.le hu
    · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hd.le]
      exact mul_le_of_le_one_right hd.le hun
  · rintro ⟨s, hs, hw, hwn⟩
    refine ⟨(repairHalfSide S)⁻¹ • (w - v), ⟨s, (mem_supp_iff_repairFanRunOf H s).mpr hs,
      smul_mem_repairFanCone (inv_pos.mpr hd).le hw, ?_⟩, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hd).le]
      exact inv_mul_le_one_of_le₀ hwn hd.le
    · rw [smul_smul, mul_inv_cancel₀ hd.ne', one_smul, add_sub_cancel]

/-- A binary label differs from its reversal.
Auxiliary to area-law Section 11, lines 404–407. -/
theorem fin_two_ne_one_sub_self (x : Fin 2) : x ≠ 1 - x := by
  fin_cases x <;> decide

/-- **Isolated stars at the children of one repair.**
Source: area-law Section 11, `geometry:repair-induction`, lines 497–514. -/
theorem isIsolatedStar_repairChild {κ : Type*} {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2}
    {σ : RepairFanSlot → ι} {v : ℝ × ℝ} {S r : ℝ}
    (hr : 3 / 2 * repairHalfSide S ≤ r)
    (hcl : ∀ i, closure (R i) ∩ Metric.ball v r = repairSectorSet σ v i ∩ Metric.ball v r)
    (hint : ∀ i, (repairSectorSet σ v i \ repairActiveRaySet σ v) ∩ Metric.ball v r ⊆
      interior (R i))
    (hcol : ∀ s, ξ (σ s) = ξ (σ (cellFanNext s)) ↔ σ s = σ (cellFanNext s))
    (R' : κ → Set (ℝ × ℝ)) (ξ' : κ → Fin 2) (old : ι → κ) (fresh : RepairFanRun ξ σ → κ)
    (hold : Function.Injective old) (hfresh : Function.Injective fresh)
    (hdisj : ∀ i H, old i ≠ fresh H) (e : Fin 3 × Fin 3)
    (hR'old : ∀ i, R' (old i) ∩
        Metric.ball (v + repairHalfSide S • repairChildOffset e) (repairHalfSide S / 2) =
      (R i \ Metric.closedBall v (repairHalfSide S)) ∩
        Metric.ball (v + repairHalfSide S • repairChildOffset e) (repairHalfSide S / 2))
    (hR'fresh : ∀ H, R' (fresh H) ∩
        Metric.ball (v + repairHalfSide S • repairChildOffset e) (repairHalfSide S / 2) =
      repairReplacementOpenRegion v S ξ σ H ∩
        Metric.ball (v + repairHalfSide S • repairChildOffset e) (repairHalfSide S / 2))
    (hR'other : ∀ x, (∀ i, x ≠ old i) → (∀ H, x ≠ fresh H) → closure (R' x) ∩
        Metric.ball (v + repairHalfSide S • repairChildOffset e) (repairHalfSide S / 2) = ∅)
    (hξold : ∀ i, ξ' (old i) = ξ i)
    (hξfresh : ∀ H, ξ' (fresh H) = repairReplacementColor ξ σ H)
    {ρ : ℝ} (hρ : 0 < ρ) (hρd : ρ < repairHalfSide S / 2) :
    IsIsolatedStar R' ξ' (v + repairHalfSide S • repairChildOffset e) ρ := by
  set d := repairHalfSide S with hd_def
  have hd : 0 < d := repairHalfSide_pos S
  set c := v + d • repairChildOffset e with hc
  set N := Metric.ball c (d / 2) with hN_def
  set τ := repairChildAssignment ξ σ old fresh e with hτ_def
  have hNv : ∀ x ∈ N, x ∈ Metric.ball v r := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have h1 : dist c v ≤ d := by
      rw [hc, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hd.le]
      exact mul_le_of_le_one_right hd.le (norm_repairChildOffset_le e)
    linarith [dist_triangle x c v]
  -- Values of the child assignment.
  have hτold : ∀ t i, τ t = old i ↔
      repairChildSlotInside e t = false ∧ σ (repairChildSlotParent e t) = i := by
    intro t i
    simp only [hτ_def, repairChildAssignment]
    split_ifs with h
    · simp only [h, Bool.true_eq_false, false_and, iff_false]
      exact fun h' ↦ hdisj i _ h'.symm
    · simp only [Bool.not_eq_true] at h
      simp only [h, true_and]
      exact hold.eq_iff
  have hτfresh : ∀ t H, τ t = fresh H ↔
      repairChildSlotInside e t = true ∧ repairFanRunOf ξ σ (repairChildSlotParent e t) = H := by
    intro t H
    simp only [hτ_def, repairChildAssignment]
    split_ifs with h
    · simp only [h, true_and]
      exact hfresh.eq_iff
    · simp only [Bool.not_eq_true] at h
      simp only [h, Bool.false_eq_true, false_and, iff_false]
      exact hdisj _ H
  have hτrange : ∀ t, (∃ i, τ t = old i) ∨ ∃ H, τ t = fresh H := by
    intro t
    simp only [hτ_def, repairChildAssignment]
    split_ifs
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  have hfacts := fun x (hx : x ∈ N) t ↦ repairChild_facts (v := v) hd e hx t
  -- The closed birth of a run contains the clipped cones of its wedges.
  have hbirth : ∀ (H : RepairFanRun ξ σ) (s : RepairFanSlot) (w : ℝ × ℝ),
      repairFanRunOf ξ σ s = H → w - v ∈ repairFanCone s → ‖w - v‖ ≤ d →
      w ∈ repairReplacementBirthRegion v S ξ σ H :=
    fun H s w hs hw hwn ↦ (mem_repairReplacementBirthRegion_iff H).mpr ⟨s, hs, hw, hwn⟩
  apply isIsolatedStar_of_model hρ hρd τ
  · -- Closures in the child square.
    intro x
    by_cases hxo : ∃ i, x = old i
    · obtain ⟨i, rfl⟩ := hxo
      rw [closure_inter_eq_of_inter_eq Metric.isOpen_ball (hR'old i)]
      ext z
      constructor
      · rintro ⟨hz, hzN⟩
        refine ⟨?_, hzN⟩
        have hz' := Metric.isOpen_ball.closure_inter ⟨hz, hzN⟩
        refine (isClosed_repairSectorSet τ c (old i)).closure_subset_iff.mpr ?_ hz'
        rintro w ⟨⟨hwR, hwQ⟩, hwN⟩
        obtain ⟨⟨s, hs, hws⟩, -⟩ := (hcl i).subset ⟨subset_closure hwR, hNv w hwN⟩
        have hwd : d < ‖w - v‖ := by simpa [dist_eq_norm] using hwQ
        obtain ⟨t, hin, hp, ht⟩ := exists_outer_child_cone hd hwN hwd hws
        exact ⟨t, (hτold t i).mpr ⟨hin, hp ▸ hs⟩, ht⟩
      · rintro ⟨⟨t, ht, hzt⟩, hzN⟩
        obtain ⟨hin, hσ⟩ := (hτold t i).mp ht
        refine ⟨closure_mono ?_ (mem_closure_openCone_inter Metric.isOpen_ball hzN hzt), hzN⟩
        rintro w ⟨hwt, hwN⟩
        have hf := hfacts w hwN t
        have hwo := hf.2.1 hwt
        refine ⟨?_, fun hwQ ↦ hf.2.2.2.2.2 hin hwt (by simpa [dist_eq_norm] using hwQ)⟩
        refine interior_subset (hint i ⟨⟨⟨_, hσ, repairFanOpenCone_subset _ hwo⟩, ?_⟩,
          hNv w hwN⟩)
        rintro ⟨u, -, hu⟩
        exact not_sameRay_of_mem_repairFanOpenCone hwo hu
    by_cases hxf : ∃ H, x = fresh H
    · obtain ⟨H, rfl⟩ := hxf
      rw [closure_inter_eq_of_inter_eq Metric.isOpen_ball (hR'fresh H)]
      ext z
      constructor
      · rintro ⟨hz, hzN⟩
        refine ⟨?_, hzN⟩
        have hz' := Metric.isOpen_ball.closure_inter ⟨hz, hzN⟩
        refine (isClosed_repairSectorSet τ c (fresh H)).closure_subset_iff.mpr ?_ hz'
        rintro w ⟨hwR, hwN⟩
        obtain ⟨s, hs, hws, hwn⟩ := (mem_repairReplacementBirthRegion_iff H).mp
          (interior_subset hwR)
        obtain ⟨t, hin, hp, ht⟩ := exists_inner_child_cone hd hwN hwn hws
        exact ⟨t, (hτfresh t H).mpr ⟨hin, hp ▸ hs⟩, ht⟩
      · rintro ⟨⟨t, ht, hzt⟩, hzN⟩
        obtain ⟨hin, hrun⟩ := (hτfresh t H).mp ht
        refine ⟨closure_mono ?_ (mem_closure_openCone_inter Metric.isOpen_ball hzN hzt), hzN⟩
        rintro w ⟨hwt, hwN⟩
        have hf := hfacts w hwN t
        have hwo := hf.2.1 hwt
        have hwd := hf.2.2.2.1 hin hwt
        have hsub : repairCurrentFanTriangle v d (repairChildSlotParent e t) ⊆
            repairReplacementBirthRegion v S ξ σ H := by
          intro u hu
          rw [mem_repairCurrentFanTriangle_iff hd] at hu
          exact hbirth H _ u hrun hu.1 hu.2
        apply interior_mono hsub
        rw [interior_repairCurrentFanTriangle hd]
        exact ⟨hwo, hwd⟩
    · push Not at hxo hxf
      rw [hR'other x (fun i h ↦ hxo i h) (fun H h ↦ hxf H h)]
      symm
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨⟨t, ht, -⟩, -⟩
      rcases hτrange t with ⟨i, hi⟩ | ⟨H, hH⟩
      · exact hxo i (ht ▸ hi)
      · exact hxf H (ht ▸ hH)
  · -- Membership away from the active rays.
    intro x z ⟨⟨⟨t, ht, hzt⟩, hzA⟩, hzN⟩
    have hf := hfacts z hzN t
    rcases hτrange t with ⟨i, hi⟩ | ⟨H, hH⟩
    · rw [hi] at ht
      subst ht
      obtain ⟨hin, hσ⟩ := (hτold t i).mp hi
      have hmem : z ∈ (R i \ Metric.closedBall v d) ∩ N := by
        refine ⟨⟨?_, ?_⟩, hzN⟩
        · refine interior_subset (hint i ⟨⟨⟨_, hσ, hf.1 hzt⟩, ?_⟩, hNv z hzN⟩)
          rintro ⟨s₀, hs₀, hray⟩
          have hboth := (mem_repairFanCone_inter_next_iff s₀ _).mpr hray
          have hzd : d < ‖z - v‖ := by
            by_contra hle
            push Not at hle
            obtain ⟨s, hs⟩ := exists_mem_repairFanCone (z - v)
            obtain ⟨u, hu, -, hzu⟩ := exists_inner_child_cone hd hzN hle hs
            obtain ⟨H, hH⟩ : ∃ H, τ u = fresh H := ⟨_, (hτfresh u _).mpr ⟨hu, rfl⟩⟩
            exact hzA (mem_repairActiveRaySet_of_mem_two hzt hzu (by
              rw [hi, hH]; exact hdisj i H))
          obtain ⟨u, hu, hpu, hzu⟩ := exists_outer_child_cone hd hzN hzd hboth.1
          obtain ⟨u', hu', hpu', hzu'⟩ := exists_outer_child_cone hd hzN hzd hboth.2
          apply hzA (mem_repairActiveRaySet_of_mem_two hzu hzu' _)
          rw [(hτold u _).mpr ⟨hu, rfl⟩, (hτold u' _).mpr ⟨hu', rfl⟩, hpu, hpu']
          exact fun h ↦ hs₀ (hold h)
        · intro hzQ
          have hle : ‖z - v‖ ≤ d := by simpa [dist_eq_norm] using hzQ
          obtain ⟨s, hs⟩ := exists_mem_repairFanCone (z - v)
          obtain ⟨u, hu, -, hzu⟩ := exists_inner_child_cone hd hzN hle hs
          obtain ⟨H, hH⟩ : ∃ H, τ u = fresh H := ⟨_, (hτfresh u _).mpr ⟨hu, rfl⟩⟩
          exact hzA (mem_repairActiveRaySet_of_mem_two hzt hzu (by
            rw [hi, hH]; exact hdisj i H))
      rw [← hR'old i] at hmem
      exact hmem.1
    · rw [hH] at ht
      subst ht
      obtain ⟨hin, hrun⟩ := (hτfresh t H).mp hH
      suffices hz : z ∈ repairReplacementOpenRegion v S ξ σ H by
        have hz' : z ∈ repairReplacementOpenRegion v S ξ σ H ∩ N := ⟨hz, hzN⟩
        rw [← hR'fresh H] at hz'
        exact hz'.1
      have hzd : ‖z - v‖ < d := by
        by_contra hle
        push Not at hle
        obtain ⟨u, hu, hzu⟩ := exists_outer_child_cone_of_le hd hzN hle
        obtain ⟨i, hi⟩ : ∃ i, τ u = old i := ⟨_, (hτold u _).mpr ⟨hu, rfl⟩⟩
        exact hzA (mem_repairActiveRaySet_of_mem_two hzt hzu (by
          rw [hH, hi]; exact (hdisj i H).symm))
      set κf := repairFanRunOf ξ σ
      have hO : IsOpen ((repairSectorSet κf v H \ repairActiveRaySet κf v) ∩
          Metric.ball v d) :=
        (isOpen_repairSectorSet_diff κf v H).inter Metric.isOpen_ball
      refine interior_maximal ?_ hO ⟨⟨⟨_, hrun, hf.1 hzt⟩, ?_⟩, by
        simpa [dist_eq_norm] using hzd⟩
      · rintro w ⟨⟨⟨s, hs, hws⟩, -⟩, hwd⟩
        exact hbirth H s w hs hws (by simpa [dist_eq_norm] using (Metric.mem_ball.mp hwd).le)
      · rintro ⟨s₀, hs₀, hray⟩
        have hboth := (mem_repairFanCone_inter_next_iff s₀ _).mpr hray
        obtain ⟨u, hu, hpu, hzu⟩ := exists_inner_child_cone hd hzN hzd.le hboth.1
        obtain ⟨u', hu', hpu', hzu'⟩ := exists_inner_child_cone hd hzN hzd.le hboth.2
        apply hzA (mem_repairActiveRaySet_of_mem_two hzu hzu' _)
        rw [(hτfresh u _).mpr ⟨hu, rfl⟩, (hτfresh u' _).mpr ⟨hu', rfl⟩, hpu, hpu']
        exact fun h ↦ hs₀ (hfresh h)
  · -- Labels.
    intro t
    have hcode := repairSlotCode_next t
    set m : Fin 8 := ⟨repairSlotCode t, repairSlotCode_lt t⟩
    have hin_next : repairChildSlotInside e (cellFanNext t) =
        repairChildInside e ((m.val + 1) % 8) := by
      simp only [repairChildSlotInside, hcode, m]
    have hps_next : repairChildSlotParent e (cellFanNext t) =
        repairSlotOfCode (repairChildParentCode e ((m.val + 1) % 8)) := by
      simp only [repairChildSlotParent, hcode, m]
    have hps : repairChildSlotParent e t = repairSlotOfCode (repairChildParentCode e m.val) := rfl
    have hin : repairChildSlotInside e t = repairChildInside e m.val := rfl
    -- Rewriting slot positions modulo eight.
    have hslot : ∀ a b : ℕ, a % 8 = b % 8 → repairSlotOfCode a = repairSlotOfCode b := by
      intro a b h
      rw [← repairSlotOfCode_mod a, h, repairSlotOfCode_mod]
    have hslot_succ : ∀ a b : ℕ, a % 8 = (b + 1) % 8 →
        repairSlotOfCode a = cellFanNext (repairSlotOfCode b) := by
      intro a b h
      rw [cellFanNext_repairSlotOfCode]
      exact hslot a (b + 1) h
    by_cases hkind : repairChildInside e ((m.val + 1) % 8) = repairChildInside e m.val
    · rcases repairChildParentCode_succ_of_inside_eq e m hkind with h | h | h
      · -- Same parent wedge.
        have hp : repairChildSlotParent e (cellFanNext t) = repairChildSlotParent e t := by
          rw [hps_next, hps]
          exact hslot _ _ h
        cases hk : repairChildInside e m.val
        · have h1 : τ t = old (σ (repairChildSlotParent e t)) :=
            (hτold t _).mpr ⟨hin.trans hk, rfl⟩
          have h2 : τ (cellFanNext t) = old (σ (repairChildSlotParent e t)) :=
            (hτold _ _).mpr ⟨hin_next.trans (hkind.trans hk), by rw [hp]⟩
          rw [h1, h2]
          simp
        · have h1 : τ t = fresh (repairFanRunOf ξ σ (repairChildSlotParent e t)) :=
            (hτfresh t _).mpr ⟨hin.trans hk, rfl⟩
          have h2 : τ (cellFanNext t) = fresh (repairFanRunOf ξ σ (repairChildSlotParent e t)) :=
            (hτfresh _ _).mpr ⟨hin_next.trans (hkind.trans hk), by rw [hp]⟩
          rw [h1, h2]
          simp
      all_goals
        -- Adjacent parent wedges `a` and `b`, in either order.
        obtain ⟨a, b, hab, hta, htb⟩ : ∃ a b : RepairFanSlot, b = cellFanNext a ∧
            ((repairChildSlotParent e t = a ∧ repairChildSlotParent e (cellFanNext t) = b) ∨
              (repairChildSlotParent e t = b ∧ repairChildSlotParent e (cellFanNext t) = a)) ∧
            True := by
          first
          | exact ⟨repairChildSlotParent e t, repairChildSlotParent e (cellFanNext t),
              by rw [hps_next, hps]; exact hslot_succ _ _ h, Or.inl ⟨rfl, rfl⟩, trivial⟩
          | exact ⟨repairChildSlotParent e (cellFanNext t), repairChildSlotParent e t,
              by rw [hps_next, hps]; exact hslot_succ _ _ h, Or.inr ⟨rfl, rfl⟩, trivial⟩
        subst hab
        cases hk : repairChildInside e m.val
        · have h1 : τ t = old (σ (repairChildSlotParent e t)) :=
            (hτold t _).mpr ⟨hin.trans hk, rfl⟩
          have h2 : τ (cellFanNext t) = old (σ (repairChildSlotParent e (cellFanNext t))) :=
            (hτold _ _).mpr ⟨hin_next.trans (hkind.trans hk), rfl⟩
          rw [h1, h2, hξold, hξold, hold.eq_iff]
          rcases hta with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
          · exact hcol a
          · have key := hcol a
            exact ⟨fun h ↦ (key.mp h.symm).symm, fun h ↦ (key.mpr h.symm).symm⟩
        · have h1 : τ t = fresh (repairFanRunOf ξ σ (repairChildSlotParent e t)) :=
            (hτfresh t _).mpr ⟨hin.trans hk, rfl⟩
          have h2 : τ (cellFanNext t) =
              fresh (repairFanRunOf ξ σ (repairChildSlotParent e (cellFanNext t))) :=
            (hτfresh _ _).mpr ⟨hin_next.trans (hkind.trans hk), rfl⟩
          rw [h1, h2, hξfresh, hξfresh, hfresh.eq_iff]
          simp only [repairReplacementColor, repairFanRunExteriorColor_runOf, sub_right_inj]
          rcases hta with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
          · exact (repairFanRunOf_next_eq_iff ξ σ a).symm
          · have key := repairFanRunOf_next_eq_iff ξ σ a
            exact ⟨fun h ↦ (key.mpr h.symm).symm, fun h ↦ (key.mp h.symm).symm⟩
    · -- A change of kind: the parent wedge is the same and the labels are opposite.
      have hp : repairChildSlotParent e (cellFanNext t) = repairChildSlotParent e t := by
        rw [hps_next, hps]
        exact hslot _ _ (repairChildParentCode_succ_of_inside_ne e m hkind)
      cases hk : repairChildInside e m.val
      · have hk' : repairChildInside e ((m.val + 1) % 8) = true := by
          cases h : repairChildInside e ((m.val + 1) % 8)
          · exact absurd (h.trans hk.symm) hkind
          · rfl
        have h1 : τ t = old (σ (repairChildSlotParent e t)) :=
          (hτold t _).mpr ⟨hin.trans hk, rfl⟩
        have h2 : τ (cellFanNext t) = fresh (repairFanRunOf ξ σ (repairChildSlotParent e t)) :=
          (hτfresh _ _).mpr ⟨hin_next.trans hk', by rw [hp]⟩
        rw [h1, h2, hξold, hξfresh]
        simp only [repairReplacementColor, repairFanRunExteriorColor_runOf]
        exact iff_of_false (fin_two_ne_one_sub_self _) (hdisj _ _)
      · have hk' : repairChildInside e ((m.val + 1) % 8) = false := by
          cases h : repairChildInside e ((m.val + 1) % 8)
          · rfl
          · exact absurd (h.trans hk.symm) hkind
        have h1 : τ t = fresh (repairFanRunOf ξ σ (repairChildSlotParent e t)) :=
          (hτfresh t _).mpr ⟨hin.trans hk, rfl⟩
        have h2 : τ (cellFanNext t) = old (σ (repairChildSlotParent e t)) :=
          (hτold _ _).mpr ⟨hin_next.trans hk', by rw [hp]⟩
        rw [h1, h2, hξold, hξfresh]
        simp only [repairReplacementColor, repairFanRunExteriorColor_runOf]
        exact iff_of_false (fun h ↦ fin_two_ne_one_sub_self _ h.symm) (fun h ↦ hdisj _ _ h.symm)

end TNLean.PEPS.AreaLaw.Geometry

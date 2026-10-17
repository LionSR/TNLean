/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.UniformAreaLaw
import TNLean.PEPS.AreaLaw.InitialBufferReal
import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary

/-!
# Linear entropy bounds for safe rectangles

A rectangle disjoint from the endpoints of the cut has at most forty-eight
times its size many physical boundary edges. The uniform area law therefore
gives a linear entropy bound under any nonnegative real clearance.

The same padding and error constants can be chosen for the real-clearance
buffer estimate and the printed safe-box entropy recurrence. The latter is
deduced from the area law, with a uniformly enlarged additive constant. It is
a subsequent consequence of the area law, rather than an ingredient in its
proof. The supremum in the recurrence retains its fixed real clearance.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Theorem 1.1; `02-initial.tex`, safe rectangles at
lines 223–228, Lemma 3.2 (`lem:initial-buffer`) at lines 240–256,
the safe-box entropy at lines 590–594, and the recurrence
`eq:initial-box-recursion` in the proof of Proposition 3.3 at lines 606–646.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- A rectangle avoiding cut endpoints has a linear physical edge-boundary
bound. Empty physical intersections and disconnected domains are allowed.
Source: the safe rectangles of `02-initial.tex`, lines 223–228, together with
the physical-to-ambient boundary comparison in Lemma 9.4. -/
theorem card_edgeBoundary_rectRegion_le_of_disjoint
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (Q : IntRect)
    (hdisj : Disjoint Q.toFinset (Geometry.boundaryEndpoints Λ A)) :
    (edgeBoundary Λ (rectRegion A Q)).card ≤ 48 * Q.size := by
  classical
  have hboundary : (edgeBoundary Λ (rectRegion A Q)).card ≤
      (ambientBoundary Q.toFinset).card :=
    Geometry.card_edgeBoundary_filter_le_ambientBoundary Λ A Q.toFinset hdisj
  have houter := card_ambientBoundary_le_outer_layer Q.toFinset
  have hlayer : (ambientDilation Q.toFinset 1 \ Q.toFinset).card ≤ 4 * (Q.size + 2) := by
    simpa only [Nat.sub_self, IntRect.dilate_zero, IntRect.toFinset_dilate,
      Nat.mul_one] using (card_dilate_sdiff_le Q (d := 1) (k := 1) le_rfl)
  have hsize := Q.one_le_size
  omega

/-- The area law gives a linear entropy bound with one constant chosen before
the nonnegative real clearance and every physical instance.
Source: Theorem 1.1 and the safe rectangles of `02-initial.tex`, lines 223–228. -/
theorem exists_regionalEntropy_safe_rect_le_linear
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 ≤ d →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (A : Finset (Site Λ)) (Q : IntRect),
          (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
            d * (Q.size : ℝ) < (supDist t z : ℝ)) →
          regionalEntropy Λ q Ω (rectRegion A Q) ≤ K * (Q.size : ℝ) := by
  classical
  obtain ⟨C, hC, harea⟩ := uniformAreaLaw q hq R (J + 1) Δ (by linarith) hΔ
  refine ⟨48 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro d hd Λ h E₀ Ω hgs A Q hclear
  let h' : LocalHamiltonian Λ q R (J + 1) :=
    { term := h.term
      supported := h.supported
      hermitian := h.hermitian
      norm_le := fun X ↦ (h.norm_le X).trans (by linarith) }
  have hgs' : IsGappedGroundState Λ q h'.operator E₀ Ω Δ := hgs
  have hdisj : Disjoint Q.toFinset (Geometry.boundaryEndpoints Λ A) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzcut
    have hbad : d * (Q.size : ℝ) < 0 := by
      simpa [supDist] using hclear z hz z hzcut
    exact (not_lt_of_ge (mul_nonneg hd (Nat.cast_nonneg Q.size))) hbad
  calc
    regionalEntropy Λ q Ω (rectRegion A Q) ≤
        C * (edgeBoundary Λ (rectRegion A Q)).card := harea Λ h' E₀ Ω hgs' _
    _ ≤ C * (48 * (Q.size : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by exact_mod_cast card_edgeBoundary_rectRegion_le_of_disjoint Λ A Q hdisj) hC
    _ = (48 * C) * (Q.size : ℝ) := by ring

/-- One padding constant and one error constant satisfy both the real-clearance
buffer estimate and the printed recurrence for the supremum at that same
clearance. The constants precede the clearance and all physical instances.
The recurrence follows here from the area law after enlarging the additive
constant uniformly; the multiplicative coefficient remains the printed one.
Source: `02-initial.tex`, Lemma 3.2 (`lem:initial-buffer`), lines 240–256;
the safe-box supremum, lines 590–594; and `eq:initial-box-recursion`,
lines 638–641, in the proof of Proposition 3.3. -/
theorem exists_initialBuffer_and_real_boxEntropy_recurrence
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ b : ℝ, 0 ≤ b ∧
      (∀ d : ℝ, 2 * (R : ℝ) + 10 < d →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (Q : IntRect),
            (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
              d * (Q.size : ℝ) < (supDist t z : ℝ)) →
            ∀ r : ℕ, 1 ≤ r → ∀ Q₀ : IntRect, Q₀.size ≤ r →
              (Q₀.dilate (c * r)).toFinset ⊆ Q.toFinset →
              regionalEntropy Λ q Ω (rectRegion A Q₀ ∪
                  (rectRegion A (Q₀.dilate (c * r)) \ rectRegion A Q₀)) -
                regionalEntropy Λ q Ω (rectRegion A (Q₀.dilate (c * r)) \ rectRegion A Q₀) ≤
              regionalEntropy Λ q Ω (rectRegion A Q₀) / 2 + b * r) ∧
      (∀ d : ℝ, 2 * (R : ℝ) + 10 < d →
        let F : ℕ → ℝ := fun r ↦ sSup
          {s : ℝ | ∃ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
            (E₀ : ℝ) (Ω : StateSpace Λ q) (A : Finset (Site Λ)) (Q : IntRect),
            IsGappedGroundState Λ q h.operator E₀ Ω Δ ∧
              (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                d * (Q.size : ℝ) < (supDist t z : ℝ)) ∧
              Q.size ≤ r ∧ s = regionalEntropy Λ q Ω (rectRegion A Q)}
        let p₀ : ℝ := 1 / (2 * (c : ℝ) + 5) ^ 2
        ∀ M r : ℕ, 1 ≤ M → 1 ≤ r →
          F (M * r) ≤
            ((1 - p₀ / 2) * (M : ℝ) ^ 2 +
                (p₀ / 2) * (4 * ((c : ℝ) + 2) * (M : ℝ))) * F r +
              b * (M : ℝ) ^ 2 * (r : ℝ)) := by
  classical
  obtain ⟨c, hc, b₀, hb₀, hbuffer⟩ :=
    exists_condEntropy_le_initialBuffer_real q R hq hJ hΔ
  obtain ⟨K, hK, hlinear⟩ := exists_regionalEntropy_safe_rect_le_linear q R hq hJ hΔ
  have hb : 0 ≤ max b₀ K := hb₀.trans (le_max_left _ _)
  refine ⟨c, hc, max b₀ K, hb, ?_, ?_⟩
  · intro d hd Λ h E₀ Ω hgs A Q hclear r hr Q₀ hQ₀ hpad
    exact (hbuffer d hd Λ h E₀ Ω hgs A Q hclear r hr Q₀ hQ₀ hpad).trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_left b₀ K) (Nat.cast_nonneg r)))
  · intro d hd F p₀ M r hM _hr
    have hd0 : 0 ≤ d := by linarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]
    have hF0 (t : ℕ) : 0 ≤ F t := by
      apply Real.sSup_nonneg
      rintro s ⟨Λ, h, E₀, Ω, A, Q, hgs, _, _, rfl⟩
      exact regionalEntropy_nonneg Λ q Ω hgs.1 _
    have hFle (t : ℕ) : F t ≤ K * (t : ℝ) := by
      refine Real.sSup_le (fun s hs ↦ ?_) (mul_nonneg hK (Nat.cast_nonneg t))
      obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, hclear, hQ, rfl⟩ := hs
      exact (hlinear d hd0 Λ h E₀ Ω hgs A Q hclear).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) hK)
    have hden : 1 ≤ (2 * (c : ℝ) + 5) ^ 2 := by
      nlinarith [sq_nonneg (c : ℝ), show (0 : ℝ) ≤ c from Nat.cast_nonneg c]
    have hp0 : 0 ≤ p₀ := by dsimp [p₀]; positivity
    have hp1 : p₀ ≤ 1 := by
      change 1 / (2 * (c : ℝ) + 5) ^ 2 ≤ 1
      apply (div_le_iff₀ (by linarith : 0 < (2 * (c : ℝ) + 5) ^ 2)).2
      simpa using hden
    have hα : 0 ≤ (1 - p₀ / 2) * (M : ℝ) ^ 2 +
        (p₀ / 2) * (4 * ((c : ℝ) + 2) * (M : ℝ)) :=
      add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
        (mul_nonneg (div_nonneg hp0 (by norm_num)) (by positivity))
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hMsq : (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
    calc
      F (M * r) ≤ K * (↑(M * r) : ℝ) := hFle _
      _ = K * (M : ℝ) * (r : ℝ) := by push_cast; ring
      _ ≤ max b₀ K * (M : ℝ) ^ 2 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (le_max_right b₀ K) hMsq (Nat.cast_nonneg M) hb)
          (Nat.cast_nonneg r)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hα (hF0 r))

end TNLean.PEPS.AreaLaw

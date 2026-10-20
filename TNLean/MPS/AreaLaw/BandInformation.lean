/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BandDissolution
import TNLean.MPS.AreaLaw.LogarithmicSeparation
import Mathlib.Data.Nat.Dist

/-!
# Original-state information bounds for one band

All eight estimates concern the same original ground-state vector, not an evolving vector.

**Scope restriction (contiguous chains):** The sites are `Fin L`; the broader finite-domain
reading remains recorded in `docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`.

**Local fix (half-open lattice bands):** Integer-ended moves include their left endpoints,
restoring the site `a - 3*w` to C. The real exchange window remains open, and the retired
auxiliary retains its actual A and B owners. See
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.

Sources: the one-dimensional note, `part2b_mps_protocol.tex`, Construction con:band,
lines 248–276, and Lemma lem:band, lines 287–318; `part2a_mps_information.tex`,
Lemma lem:logsep, lines 472–488.
The information exponent is 24, as in the source's logarithmic width choice.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.MPS.AreaLaw.OneBand

section Geometry

variable {L : ℕ} {Party : Type}

/-- An interval is separated from the exterior of any sufficiently enlarged interval. -/
private theorem interval_separation_of_notMem {b c u v w : ℕ}
    (hleft : u + w ≤ b) (hright : c + w ≤ v)
    (x y : Fin L) (hx : x ∈ interval L b c) (hy : y ∉ interval L u v) :
    w ≤ Nat.dist x.val y.val := by
  simp only [mem_interval] at hx hy
  unfold Nat.dist
  omega

/-- Constant ownership on an enlarged interval separates the actual birth environment. -/
private theorem separation_of_owner_window (F : Sheet (Fin L) Party) (P : Party)
    {b c u v w : ℕ}
    (howner : ∀ y ∈ interval L u v, F.owner y = P)
    (hleft : u + w ≤ b) (hright : c + w ≤ v) :
    ∀ x ∈ interval L b c, ∀ y ∈ F.birthEnv P, w ≤ Nat.dist x.val y.val := by
  intro x hx y hy
  apply interval_separation_of_notMem hleft hright x y hx
  intro hywindow
  exact (Sheet.mem_birthEnv F).mp hy (howner y hywindow)

/-- The actual after-death owner windows. No exterior owner is prescribed.
Source: Part II, Lemma lem:band, the after-exchange ownership calculation. -/
private theorem after_death_owner_windows
    (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a)
    (hA : ∀ x ∈ interval L a (a + w), own x = A)
    (hB : ∀ x ∈ interval L (a + w) (a + 2 * w), own x = B) :
    (∀ x ∈ interval L (a - 5 * w) (a + w),
      (main₅ own A B C a w).owner x = A) ∧
    (∀ x ∈ interval L (a - 6 * w) (a + 2 * w),
      (main₆ own A B C a w).owner x = B) := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have h6 : 6 * w ≤ a := by omega
  have h4 : 4 * w ≤ a := by omega
  have hc6 : ((a - 6 * w : ℕ) : ℝ) = (a : ℝ) - 6 * w := by
    simp only [Nat.cast_sub h6, Nat.cast_mul, Nat.cast_ofNat]
  have hc4 : ((a - 4 * w : ℕ) : ℝ) = (a : ℝ) - 4 * w := by
    simp only [Nat.cast_sub h4, Nat.cast_mul, Nat.cast_ofNat]
  have hin (x : Fin L) (hlo : a - 6 * w ≤ x.val) (hhi : x.val < a - 4 * w) :
      x ∈ exchangeRegion L a w := by
    have hloR : ((a - 6 * w : ℕ) : ℝ) ≤ x.val := by exact_mod_cast hlo
    have hhiR : (x.val : ℝ) < ((a - 4 * w : ℕ) : ℝ) := by exact_mod_cast hhi
    rw [hc6] at hloR
    rw [hc4] at hhiR
    simp only [exchangeRegion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> linarith
  have hout (x : Fin L) (hx : a ≤ x.val) : x ∉ exchangeRegion L a w := by
    intro hy
    simp only [exchangeRegion, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hxR : (a : ℝ) ≤ x.val := by exact_mod_cast hx
    linarith [hy.2]
  constructor
  · intro x hx
    have hx' : a - 5 * w ≤ x.val ∧ x.val < a + w := by
      simpa only [mem_interval] using hx
    by_cases hdeath : x ∈ interval L (a - 4 * w) a
    · simp only [main₅, Sheet.changeOwner, ite_eq_left hdeath]
    · by_cases hxa : x.val < a
      · have hxhi : x.val < a - 4 * w := by
          simp only [mem_interval] at hdeath
          omega
        have hY : x ∈ exchangeRegion L a w := hin x (by omega) hxhi
        have h₂ : x ∈ interval L (a - 5 * w) (a - 2 * w) := by
          simp only [mem_interval]
          omega
        have h₃ : x ∉ interval L (a - 4 * w) (a - 3 * w) := by
          simp only [mem_interval]
          omega
        have haux : (aux₃ A B C a w).owner x = A := by
          simp only [aux₃, aux₂, Sheet.changeOwner, ite_eq_right h₃, ite_eq_left h₂]
        change (if x ∈ interval L (a - 4 * w) a then A else
          if x ∈ exchangeRegion L a w then
            (aux₃ A B C a w).owner x else own x) = A
        simpa only [hdeath, hY, ite_false, ite_true] using haux
      · have hxA : x ∈ interval L a (a + w) := by
          simp only [mem_interval]
          omega
        have hY : x ∉ exchangeRegion L a w := hout x (by omega)
        change (if x ∈ interval L (a - 4 * w) a then A else
          if x ∈ exchangeRegion L a w then
            (aux₃ A B C a w).owner x else own x) = A
        simpa only [hdeath, hY, ite_false] using hA x hxA
  · intro x hx
    have hx' : a - 6 * w ≤ x.val ∧ x.val < a + 2 * w := by
      simpa only [mem_interval] using hx
    by_cases hdeath : x ∈ interval L (a - 5 * w) (a + w)
    · simp only [main₆, Sheet.changeOwner, ite_eq_left hdeath]
    · by_cases hxa : x.val < a
      · have hxhi : x.val < a - 5 * w := by
          simp only [mem_interval] at hdeath
          omega
        have hY : x ∈ exchangeRegion L a w := hin x hx'.1 (by omega)
        have h₁ : x ∈ interval L (a - 6 * w) (a - w) := by
          simp only [mem_interval]
          omega
        have h₂ : x ∉ interval L (a - 5 * w) (a - 2 * w) := by
          simp only [mem_interval]
          omega
        have h₃ : x ∉ interval L (a - 4 * w) (a - 3 * w) := by
          simp only [mem_interval]
          omega
        have h₄ : x ∉ interval L (a - 4 * w) a := by
          simp only [mem_interval]
          omega
        have haux : (aux₃ A B C a w).owner x = B := by
          simp only [aux₃, aux₂, aux₁, Sheet.changeOwner, ite_eq_right h₃,
            ite_eq_right h₂, ite_eq_left h₁]
        change (if x ∈ interval L (a - 5 * w) (a + w) then B else
          if x ∈ interval L (a - 4 * w) a then A else
          if x ∈ exchangeRegion L a w then
            (aux₃ A B C a w).owner x else own x) = B
        simpa only [hdeath, h₄, hY, ite_false, ite_true] using haux
      · have hxB : x ∈ interval L (a + w) (a + 2 * w) := by
          simp only [mem_interval] at hdeath ⊢
          omega
        have h₄ : x ∉ interval L (a - 4 * w) a := by
          simp only [mem_interval]
          omega
        have hY : x ∉ exchangeRegion L a w := hout x (by omega)
        change (if x ∈ interval L (a - 5 * w) (a + w) then B else
          if x ∈ interval L (a - 4 * w) a then A else
          if x ∈ exchangeRegion L a w then
            (aux₃ A B C a w).owner x else own x) = B
        simpa only [hdeath, h₄, hY, ite_false] using hB x hxB

/-- The eight exact geometric margins for the existing primitive information sets.
The exchange environment is Z minus Y, rather than the complement of Y.
Source: Part II, Lemma lem:band, lines 300–318. -/
theorem primitive_separation
    (own : Fin L → Party) (A B C : Party) (a w : ℕ)
    (hAC : A ≠ C) (hBC : B ≠ C)
    (hw : 1 ≤ w) (hleft : 8 * w ≤ a) (hright : a + 2 * w ≤ L)
    (hC : ∀ x ∈ interval L (a - 8 * w) a, own x = C)
    (hA : ∀ x ∈ interval L a (a + w), own x = A)
    (hB : ∀ x ∈ interval L (a + w) (a + 2 * w), own x = B) :
    (∀ x ∈ interval L (a - 6 * w) (a - w),
      ∀ y ∈ (aux₀ (L := L) C).birthEnv C, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 5 * w) (a - 2 * w),
      ∀ y ∈ (aux₁ (L := L) B C a w).birthEnv B, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 4 * w) (a - 3 * w),
      ∀ y ∈ (aux₂ (L := L) A B C a w).birthEnv A, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ exchangeTSet own A B C a w,
      ∀ y ∈ exchangeESet own A B C a w, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 4 * w) a,
      ∀ y ∈ (main₅ own A B C a w).birthEnv A, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 5 * w) (a + w),
      ∀ y ∈ (main₆ own A B C a w).birthEnv B, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 3 * w) a,
      ∀ y ∈ (main₆ own A B C a w).birthEnv B, w ≤ Nat.dist x.val y.val) ∧
    (∀ x ∈ interval L (a - 6 * w) (a - 3 * w),
      ∀ y ∈ (main₈ own A B C a w).birthEnv C, w ≤ Nat.dist x.val y.val) := by
  classical
  obtain ⟨hownerA, hownerB⟩ :=
    after_death_owner_windows own A B C a w hw hleft hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact ((Sheet.mem_birthEnv (aux₀ C)).mp hy rfl).elim
  · apply separation_of_owner_window (aux₁ B C a w) B
      (u := a - 6 * w) (v := a - w)
    · intro y hy
      simp only [aux₁, Sheet.changeOwner, ite_eq_left hy]
    · omega
    · omega
  · apply separation_of_owner_window (aux₂ A B C a w) A
      (u := a - 5 * w) (v := a - 2 * w)
    · intro y hy
      simp only [aux₂, Sheet.changeOwner, ite_eq_left hy]
    · omega
    · omega
  · obtain ⟨hT, hE⟩ :=
      exchange_regions own A B C a w hAC hBC hw hleft hC
    intro x hx y hy
    rw [hT] at hx
    rw [hE] at hy
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [mem_interval] at hx hy
      unfold Nat.dist
      omega
    · have hne := (Sheet.mem_birthEnv (main₀ own)).mp hy
      have hout : y ∉ interval L (a - 8 * w) a := by
        intro hyC
        exact hne (hC y hyC)
      exact interval_separation_of_notMem (by omega) (by omega) x y hx hout
  · exact separation_of_owner_window (main₅ own A B C a w) A
      hownerA (by omega) (by omega)
  · exact separation_of_owner_window (main₆ own A B C a w) B
      hownerB (by omega) (by omega)
  · exact separation_of_owner_window (main₆ own A B C a w) B
      hownerB (by omega) (by omega)
  · have hownerC : ∀ y ∈ interval L (a - 8 * w) a,
        (main₈ own A B C a w).owner y = C := by
      rw [main₈_eq_changeOwner own A B C a w hw hleft hC]
      intro y hy
      have hout : y ∉ interval L a (a + w) := by
        simp only [mem_interval] at hy ⊢
        omega
      simpa only [main₀, Sheet.changeOwner, hout, ite_false] using hC y hy
    exact separation_of_owner_window (main₈ own A B C a w) C
      hownerC (by omega) (by omega)

end Geometry

/-- The actual eight primitive information estimates follow from the existing physical
logarithmic-separation theorem. Constants precede the chain, ground state and ownership data.
Source: Lemma lem:band, `part2b_mps_protocol.tex`, and Lemma lem:logsep,
`part2a_mps_information.tex`. -/
theorem primitive_information_of_logarithmic_separation
    (q : ℕ) (hq : 1 ≤ q) (R : ℕ) (J Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ (D₂₄ : ℝ) (L₀ : ℕ), 0 < D₂₄ ∧ 1 ≤ L₀ ∧
      ∀ (L : ℕ), L₀ ≤ L →
      ∀ (h : ChainHamiltonian L q R J)
        (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (E₀ : ℝ),
        Matrix.IsGappedGroundState h.operator E₀ Ω Δ →
      ∀ (Party : Type)
        (own : Fin L → Party) (A B C : Party) (a w : ℕ),
        A ≠ C → B ≠ C → 1 ≤ w → 8 * w ≤ a → a + 2 * w ≤ L →
        (∀ x ∈ interval L (a - 8 * w) a, own x = C) →
        (∀ x ∈ interval L a (a + w), own x = A) →
        (∀ x ∈ interval L (a + w) (a + 2 * w), own x = B) →
        D₂₄ * Real.log (L : ℝ) ≤ (w : ℝ) →
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 6 * w) (a - w))
          ((aux₀ (L := L) C).birthEnv C) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 5 * w) (a - 2 * w))
          ((aux₁ (L := L) B C a w).birthEnv B) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 4 * w) (a - 3 * w))
          ((aux₂ (L := L) A B C a w).birthEnv A) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (exchangeTSet own A B C a w) (exchangeESet own A B C a w) ≤
            (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 4 * w) a)
          ((main₅ own A B C a w).birthEnv A) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 5 * w) (a + w))
          ((main₆ own A B C a w).birthEnv B) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 3 * w) a)
          ((main₆ own A B C a w).birthEnv B) ≤ (L : ℝ) ^ (-24 : ℤ)) ∧
        (FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
          (interval L (a - 6 * w) (a - 3 * w))
          ((main₈ own A B C a w).birthEnv C) ≤ (L : ℝ) ^ (-24 : ℤ)) := by
  classical
  obtain ⟨D₂₄, L₀, hD, hL₀, hlogsep⟩ :=
    ChainHamiltonian.mutualInformation_le_of_logarithmic_separation
      q hq R J Δ hΔ 24 (by norm_num) 1 le_rfl
  refine ⟨D₂₄, L₀, hD, hL₀, ?_⟩
  intro L hL h Ω E₀ hgs Party own A B C a w hAC hBC hw hleft hright hC hA hB hwidth
  obtain ⟨hd₀, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆, hd₇⟩ :=
    primitive_separation own A B C a w
      hAC hBC hw hleft hright hC hA hB
  have hinterval (b c : ℕ) (E : Finset (Fin L))
      (hd : ∀ x ∈ interval L b c, ∀ y ∈ E, w ≤ Nat.dist x.val y.val) :
      FiniteProduct.mutualInformation (fun _ : Fin L ↦ Fin q) Ω
        (interval L b c) E ≤ (L : ℝ) ^ (-24 : ℤ) := by
    have hT : ∃ (n : ℕ) (a z : Fin n → ℕ), n ≤ 1 ∧
        interval L b c = Finset.univ.biUnion (fun i ↦ interval L (a i) (z i)) :=
      ⟨1, fun _ ↦ b, fun _ ↦ c, le_rfl, by simp⟩
    have hi := hlogsep L hL h Ω E₀ hgs (interval L b c) E hT
      (fun x hx y hy ↦ hwidth.trans (by exact_mod_cast hd x hx y hy))
    have hexponent : -(24 : ℝ) = ((-24 : ℤ) : ℝ) := by norm_num
    rw [hexponent, Real.rpow_intCast] at hi
    exact hi
  refine ⟨hinterval _ _ _ hd₀, hinterval _ _ _ hd₁, hinterval _ _ _ hd₂,
    ?_, hinterval _ _ _ hd₄, hinterval _ _ _ hd₅, hinterval _ _ _ hd₆,
    hinterval _ _ _ hd₇⟩
  have hT := (exchange_regions own A B C a w
    hAC hBC hw hleft hC).1
  rw [hT]
  apply hinterval
  intro x hx y hy
  apply hd₃ x _ y hy
  rwa [hT]

end TNLean.MPS.AreaLaw.OneBand

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledErrorReduction
import TNLean.MPS.AreaLaw.ViableSet.SampledProjectorPolynomial
import TNLean.MPS.AreaLaw.ViableSet.SizeBondTrimming
import TNLean.MPS.AreaLaw.ViableSet.BondTrimmingBound
import TNLean.MPS.AreaLaw.ViableSet.FinalMPS

/-!
# The sampled viable-set induction with fixed polynomial bounds

The four operations are extension, size trimming, independent bond trimming and
sampled error reduction. For each fixed target accuracy, every positive cut has size
and individual bond bounds chosen before the chain length. The degree may depend on
a fixed upper bound for the ground-energy-to-gap ratio, as required by the power
normalization.

**Local fix (trimming and normalization):** The independent trimmings use the
quadratic radius documented at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The error-reduction correction is recorded in
`docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

**Scope restriction (quantitative constants):** The library constant-cut bond and
net exponent are those recorded in `docs/paper-gaps/lvv13_constant_bond.tex`.
Ground-energy dependence is retained as in `docs/paper-gaps/lvv13_runtime_ground_energy.tex`.
These are existence statements; they assert neither a running time nor the sharper
printed dependence of the polynomial degree on the gap.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claims `c:ext`, `c:2`, `c:trim`, `c:errorreduction`, lines 379–592, and
induction, lines 652–678.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The error constant for the successive construction, capped at one and the target accuracy.
LVV13, `algo53.tex`, the precision in Claim `c:2`, lines 520–527. -/
noncomputable def lvvViabilityPrecision (Δ η : ℝ) : ℝ := min (min 1 η) ((Δ / 169) ^ 2)

private theorem lvvViabilityPrecision_pos {Δ η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    0 < lvvViabilityPrecision Δ η :=
  lt_min (lt_min zero_lt_one hη) (sq_pos_of_pos (div_pos hΔ (by norm_num)))

/-- One complete LVV step has polynomial size and bond bounds independent of the
input size and bond. All constants precede the length and ground energy.
LVV13, `algo53.tex`, the four steps, lines 379–592. -/
theorem exists_sampled_viable_successor_polynomial {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2))) →
      (∀ j, (h j).PosSemidef) → (∀ j, h j ≤ 1) →
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∀ (i b : ℕ), 0 < i → i ≤ L → ∀ S : Finset (LeftBlockVector L q (i - 1)),
      (∀ v ∈ S, IsLeftOpenMPS b v) →
      IsViable Γ (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S : Set (LeftBlockVector L q (i - 1))) →
      ∃ T : Finset (LeftBlockVector L q i),
        IsViableMPS Γ (C * L ^ p) (D * L ^ r) (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) T := by
  classical
  let α := lvvViabilityPrecision Δ η
  have hα : 0 < α := lvvViabilityPrecision_pos hΔ hη
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (min_le_left 1 η)
  obtain ⟨P, t, hP, hsample⟩ := exists_sampledProjector_uniform_polynomial (B := B)
    (show 1 ≤ q by omega) a (div_pos hα (by norm_num))
    (show α / 8 ≤ 1 by linarith) hΔ
  obtain ⟨M, u, hM, hradius⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Δ
  let c := (Δ / 169) ^ 2
  let d := constantCutBond q 1 1 Δ c
  let k := 2 * (q * d) ^ 2
  let netRadius := ⌈2 * ((q * d : ℕ) : ℝ) ^ 2 / c⌉₊
  let F := (d + 1) * d * (2 * netRadius + 1) ^ k
  refine ⟨max 1 (P * F), t + k, P * max 1 ⌈M⌉₊, t + u, le_max_left _ _, ?_, ?_⟩
  · simpa only [one_mul] using Nat.mul_le_mul hP (le_max_left 1 ⌈M⌉₊)
  · intro L hL h hs h0 h1 E₀ Γ hgs hEB i b hi0 hiL S hS hviable
    let : NeZero L := ⟨by omega⟩
    have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hδ : 0 < α / (L : ℝ) ^ a := div_pos hα (pow_pos hLp a)
    have hδ1 : α / (L : ℝ) ^ a ≤ 1 := (div_le_one (pow_pos hLp a)).mpr
      (hα1.trans (one_le_pow₀ (by exact_mod_cast hL)))
    let chain := ChainHamiltonian.ofBonds h hs h0 h1
    have hgs' : IsGappedGroundState chain.operator E₀ Γ Δ := by
      simpa only [chain, ChainHamiltonian.ofBonds_operator] using hgs
    have hExt : ∀ v ∈ AreaLaw.extend i S, IsLeftOpenMPS b v := by
      intro v hv
      obtain ⟨w, hw, z, _, rfl⟩ := Finset.mem_image₂.mp hv
      exact (hS w hw).extendSite hi0 hiL z
    obtain ⟨T₀, hcard, hbond, hhalf⟩ := chain.exists_size_bond_trimmed_family_polynomial
      (ChainHamiltonian.posSemidef_ofBonds_term h hs h0 h1) (by omega) hq hiL hΔ
      (AreaLaw.extend i S) b hExt
    have hsmall : IsViable Γ (c / L)
        (AreaLaw.extend i S : Set (LeftBlockVector L q i)) := by
      obtain ⟨v, hv, hoverlap, hsupport⟩ := hviable.extend hi0 hiL
      refine ⟨v, hv, ?_, hsupport⟩
      have hLpow : (L : ℝ) ≤ (L : ℝ) ^ a := le_self_pow₀ (by exact_mod_cast hL) (by omega)
      have hprec : α / (L : ℝ) ^ a ≤ c / L := by
        calc
          _ ≤ c / (L : ℝ) ^ a := div_le_div_of_nonneg_right
            (min_le_right (min 1 η) c) (pow_nonneg hLp.le a)
          _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hLp hLpow
      linarith only [hoverlap, hprec]
    have hT₀ : IsViableMPS Γ (F * L ^ k)
        (bondTrimmingRadius L (lvvReferenceBond q Δ L)) (1 / 2) T₀ :=
      ⟨hcard, hbond, hhalf E₀ Γ hgs' hsmall⟩
    obtain ⟨I, _, hcuts⟩ := exists_sampled_errorReduction (show 1 ≤ q by omega)
      h hs h0 h1 hgs hΔ hδ hδ1
    obtain ⟨N, A, _, _, _, _, hgood⟩ := hcuts i hiL
    have hout := hgood _ _ T₀ hT₀
    obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
    have hbudgets := hsample L E₀ hL hE₀ hE₀L hEB
    have hηeq : α / (L : ℝ) ^ a / 8 = (α / 8) / (L : ℝ) ^ a := by ring
    simp only [hηeq] at hout
    have hradiusNat : bondTrimmingRadius L (lvvReferenceBond q Δ L) ≤ ⌈M⌉₊ * L ^ u := by
      have hreal := (hradius L hL).trans
        (mul_le_mul_of_nonneg_right (Nat.le_ceil M) (pow_nonneg (Nat.cast_nonneg L) u))
      exact_mod_cast hreal
    have hmax : max 1 (bondTrimmingRadius L (lvvReferenceBond q Δ L)) ≤
        max 1 ⌈M⌉₊ * L ^ u := max_le
      (by simpa only [one_mul] using Nat.mul_le_mul (le_max_left 1 ⌈M⌉₊) (one_le_pow₀ hL))
      (hradiusNat.trans (Nat.mul_le_mul_right _ (le_max_right 1 ⌈M⌉₊)))
    refine ⟨_, hout.1.trans ?_, ?_, hout.2.2⟩
    · calc
        _ ≤ (P * L ^ t) * (F * L ^ k) := Nat.mul_le_mul_right _ hbudgets.1
        _ = (P * F) * L ^ (t + k) := by rw [pow_add]; ring
        _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right 1 (P * F))
    · intro v hv
      apply isOpenMPS_of_internal_cutMatrix_rank_le
        (WithLp.toLp 2 fun x ↦ v (leftConfigOfFin x))
      intro j hj0 hji
      exact ((hout.2.1 v hv).rank_cutMatrix_le
        (ψ := WithLp.toLp 2 fun x ↦ v (leftConfigOfFin x)) hj0 hji).trans
        (max_le_max_left 1 (by
          calc
            _ ≤ (P * L ^ t) * (max 1 ⌈M⌉₊ * L ^ u) := Nat.mul_le_mul hbudgets.2 hmax
            _ = _ := by rw [pow_add]; ring))


/-- Starting from the scalar singleton, the four successive operations construct
viable families at every cut with fixed polynomial size and bond bounds.
LVV13, `algo53.tex`, induction, lines 652–678, in the documented quantitative scope. -/
theorem exists_sampled_successive_viable_sets_polynomial {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2))) →
      (∀ j, (h j).PosSemidef) → (∀ j, h j ≤ 1) →
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i), S 0 = {emptyLeftVector L q} ∧
        ∀ i : ℕ, i ≤ L →
          IsViableMPS Γ (C * L ^ p) (D * L ^ r)
            (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S i) := by
  classical
  obtain ⟨C, p, D, r, hC, hD, hstep⟩ :=
    exists_sampled_viable_successor_polynomial (B := B) hq a ha hΔ hη
  refine ⟨C, p, D, r, hC, hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB
  let P := fun i (S : Finset (LeftBlockVector L q i)) ↦
    IsViableMPS Γ (C * L ^ p) (D * L ^ r) (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) S
  have hbase : P 0 {emptyLeftVector L q} := by
    obtain ⟨hcard, hbond, v, hv, hoverlap, hsupport⟩ := isViableMPS_emptyLeftVector hgs.1
    refine ⟨hcard.trans ?_, ?_, v, hv, ?_, hsupport⟩
    · simpa only [one_mul] using Nat.mul_le_mul hC (one_le_pow₀ hL)
    · intro w hw
      exact isOpenMPS_of_internal_cutMatrix_rank_le
        (WithLp.toLp 2 fun x ↦ w (leftConfigOfFin x)) (fun j hj0 hjL ↦ by omega)
    · have hδ : 0 ≤ lvvViabilityPrecision Δ η / (L : ℝ) ^ a :=
        div_nonneg (lvvViabilityPrecision_pos hΔ hη).le (pow_nonneg (Nat.cast_nonneg L) a)
      linarith only [hoverlap, hδ]
  let State := fun i : ℕ ↦ {S : Finset (LeftBlockVector L q i) // i ≤ L → P i S}
  let initial : State 0 := ⟨{emptyLeftVector L q}, fun _ ↦ hbase⟩
  let advance : (i : ℕ) → State i → State (i + 1) := fun i previous ↦
    if hi : i + 1 ≤ L then
      let hprevious := previous.property (by omega)
      let step := hstep L hL h hs h0 h1 E₀ Γ hgs hEB (i + 1) (D * L ^ r)
        (by omega) hi previous.val hprevious.2.1 hprevious.2.2
      ⟨Classical.choose step, fun _ ↦ Classical.choose_spec step⟩
    else ⟨∅, fun hi' ↦ False.elim (hi hi')⟩
  let run : (i : ℕ) → State i := Nat.rec initial advance
  exact ⟨fun i ↦ (run i).val, rfl, fun i hi ↦ (run i).property hi⟩

/-- The final viable span contains a normalized matrix product state with a fixed
polynomial bond bound at any prescribed positive overlap error. The polynomial constants
precede the length, Hamiltonian and ground energy.
LVV13, `algo53.tex`, final induction, lines 652–678. -/
theorem exists_sampled_groundState_openMPS_polynomial {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p : ℕ, 1 ≤ C ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2))) →
      (∀ j, (h j).PosSemidef) → (∀ j, h j ≤ 1) →
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
        1 - η / (L : ℝ) ^ a ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧
        IsOpenMPS L q (C * L ^ p) (fun x ↦ ψ x) := by
  obtain ⟨C, p, D, r, hC, hD, hsets⟩ :=
    exists_sampled_successive_viable_sets_polynomial (B := B) hq a ha hΔ hη
  refine ⟨C * D, p + r, by simpa only [one_mul] using Nat.mul_le_mul hC hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB
  obtain ⟨S, _, hS⟩ := hsets L hL h hs h0 h1 E₀ Γ hgs hEB
  obtain ⟨ψ, hψ, hoverlap, hMPS⟩ := (hS L le_rfl).exists_openMPS
  refine ⟨ψ, hψ, ?_, ?_⟩
  · have hprec : lvvViabilityPrecision Δ η ≤ η :=
      (min_le_left _ _).trans (min_le_right 1 η)
    have hdiv : lvvViabilityPrecision Δ η / (L : ℝ) ^ a ≤ η / (L : ℝ) ^ a :=
      div_le_div_of_nonneg_right hprec (pow_nonneg (Nat.cast_nonneg L) a)
    linarith only [hoverlap, hdiv]
  · have hbond : 1 ≤ D * L ^ r := by simpa only [one_mul] using Nat.mul_le_mul hD (one_le_pow₀ hL)
    have heq : C * L ^ p * max 1 (D * L ^ r) = (C * D) * L ^ (p + r) := by
      rw [max_eq_right hbond, pow_add]
      ring
    rwa [heq] at hMPS

end TNLean.MPS.AreaLaw

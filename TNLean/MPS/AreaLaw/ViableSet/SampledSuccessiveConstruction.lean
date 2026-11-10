/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledErrorReduction
import TNLean.MPS.AreaLaw.ViableSet.SampledProjectorPolynomial
import TNLean.MPS.AreaLaw.ViableSet.SuccessiveStep
import TNLean.MPS.AreaLaw.ViableSet.BondTrimmingBound
import TNLean.MPS.AreaLaw.ViableSet.FinalMPS
import TNLean.Algebra.DependentSequence

/-!
# The sampled viable-set induction with fixed polynomial bounds

The four operations are extension, size trimming, independent bond trimming and
sampled error reduction. Each family is the named step `successiveStep` applied to the
size-trimming selection of the extended previous family, trimmed independently through
its bonds, then multiplied by the left factors of the cut decomposition of the sampled
projector. For each fixed target accuracy, every positive
cut has size and individual bond bounds chosen before the chain length. The degree may depend on
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
open scoped InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker

namespace TNLean.MPS.AreaLaw

/-- The error constant for the successive construction, capped at one and the target accuracy.
LVV13, `algo53.tex`, the precision in Claim `c:2`, lines 520–527. -/
noncomputable def lvvViabilityPrecision (Δ η : ℝ) : ℝ := min (min 1 η) ((Δ / 169) ^ 2)

private theorem lvvViabilityPrecision_pos {Δ η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    0 < lvvViabilityPrecision Δ η :=
  lt_min (lt_min zero_lt_one hη) (sq_pos_of_pos (div_pos hΔ (by norm_num)))

/-- **One complete sampled step with its selections named.** The output is the step
`successiveStep hiL m Finset.univ A` applied to the size-trimming selection of the
extension of the input family, where `A` are the left factors of the cut decomposition of
a sampled projector within `δ / 4` of the ground projection. The output has polynomial
size and bond bounds independent of the input size and bond, with all constants preceding
the length and the ground energy. LVV13, `algo53.tex`, the four steps, lines 379–592. -/
theorem exists_sampled_viable_successor_polynomial_explicit_energy_degree
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p₀ D r₀ : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
      (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∀ (i : ℕ), 0 < i → ∀ (hiL : i ≤ L), ∀ S : Finset (LeftBlockVector L q (i - 1)),
      IsViable Γ (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S : Set (LeftBlockVector L q (i - 1))) →
      ∃ (ℓ n N : ℕ) (I : Fin ℓ → Fin n → Fin L)
        (A : Fin N → LeftBlockMatrix L q i) (B' : Fin N → RightBlockMatrix L q i),
        ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ <
          lvvViabilityPrecision Δ η / (L : ℝ) ^ a / 4 ∧
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
        IsViableMPS Γ (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀))
          (D * L ^ (sampledProjectorTotalDegree q a Δ B + r₀))
          (lvvViabilityPrecision Δ η / (L : ℝ) ^ a)
          (successiveStep hiL (bondTrimmingRadius L (lvvReferenceBond q Δ L)) Finset.univ A
            (ChainHamiltonian.sizeTrimmingSelection (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ
              (AreaLaw.extend i S))) := by
  classical
  let α := lvvViabilityPrecision Δ η
  have hα : 0 < α := lvvViabilityPrecision_pos hΔ hη
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (min_le_left 1 η)
  obtain ⟨P, hP, hsample⟩ := exists_sampledProjector_uniform_polynomial_explicit_degree (B := B)
    (show 1 ≤ q by omega) a (div_pos hα (by norm_num))
    (show α / 8 ≤ 1 by linarith) hΔ
  let t := sampledProjectorTotalDegree q a Δ B
  obtain ⟨M, u, hM, hradius⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Δ
  let c := (Δ / 169) ^ 2
  let d := constantCutBond q 1 1 Δ c
  let k := 2 * (q * d) ^ 2
  let netRadius := ⌈2 * ((q * d : ℕ) : ℝ) ^ 2 / c⌉₊
  let F := (d + 1) * d * (2 * netRadius + 1) ^ k
  refine ⟨max 1 (P * F), k, P * max 1 ⌈M⌉₊, u, le_max_left _ _, ?_, ?_⟩
  · simpa only [one_mul] using Nat.mul_le_mul hP (le_max_left 1 ⌈M⌉₊)
  · intro L hL h hs h0 h1 E₀ Γ hgs hEB i hi0 hiL S hviable
    let : NeZero L := ⟨by omega⟩
    have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hδ : 0 < α / (L : ℝ) ^ a := div_pos hα (pow_pos hLp a)
    have hδ1 : α / (L : ℝ) ^ a ≤ 1 := (div_le_one (pow_pos hLp a)).mpr
      (hα1.trans (one_le_pow₀ (by exact_mod_cast hL)))
    let chain := ChainHamiltonian.ofBonds h hs h0 h1
    have hgs' : IsGappedGroundState chain.operator E₀ Γ Δ := by
      simpa only [chain, ChainHamiltonian.ofBonds_operator] using hgs
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
    let m := bondTrimmingRadius L (lvvReferenceBond q Δ L)
    let T₀ := chain.sizeTrimmingSelection hq Δ (AreaLaw.extend i S)
    have hT₁ : IsViableMPS Γ (F * L ^ k) m (1 / 2) (bondTrimSet hiL m T₀) :=
      ⟨(card_bondTrimSet_le hiL m T₀).trans
        (chain.card_sizeTrimmingSelection_le_polynomial (by omega) hq hΔ _),
        fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hiL m T₀ hv,
        chain.isViable_bondTrimSet_sizeTrimmingSelection
          (ChainHamiltonian.posSemidef_ofBonds_term h hs h0 h1) (by omega) hq hiL hΔ
          (AreaLaw.extend i S) E₀ Γ hgs' hsmall⟩
    obtain ⟨I, hproj, hcuts⟩ := exists_sampled_errorReduction (show 1 ≤ q by omega)
      h hs h0 h1 hgs hΔ hδ hδ1
    obtain ⟨N, A, B', _, hdec, _, hgood⟩ := hcuts i hiL
    have hout := hgood _ _ (bondTrimSet hiL m T₀) hT₁
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
    refine ⟨_, _, N, I, A, B', hproj, hdec, hout.1.trans ?_, ?_, hout.2.2⟩
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

/-- **One complete sampled step with its selections named.** The output is the step
`successiveStep hiL m Finset.univ A` applied to the size-trimming selection of the
extension of the input family, where `A` are the left factors of the cut decomposition of
a sampled projector within `δ / 4` of the ground projection. The output has polynomial
size and bond bounds independent of the input size and bond, with all constants preceding
the length and the ground energy. LVV13, `algo53.tex`, the four steps, lines 379–592. -/
theorem exists_sampled_viable_successor_polynomial {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
      (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∀ (i : ℕ), 0 < i → ∀ (hiL : i ≤ L), ∀ S : Finset (LeftBlockVector L q (i - 1)),
      IsViable Γ (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S : Set (LeftBlockVector L q (i - 1))) →
      ∃ (ℓ n N : ℕ) (I : Fin ℓ → Fin n → Fin L)
        (A : Fin N → LeftBlockMatrix L q i) (B' : Fin N → RightBlockMatrix L q i),
        ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ <
          lvvViabilityPrecision Δ η / (L : ℝ) ^ a / 4 ∧
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L i)
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
        IsViableMPS Γ (C * L ^ p) (D * L ^ r) (lvvViabilityPrecision Δ η / (L : ℝ) ^ a)
          (successiveStep hiL (bondTrimmingRadius L (lvvReferenceBond q Δ L)) Finset.univ A
            (ChainHamiltonian.sizeTrimmingSelection (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ
              (AreaLaw.extend i S))) := by
  obtain ⟨C, p₀, D, r₀, hC, hD, hstep⟩ :=
    exists_sampled_viable_successor_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  exact ⟨C, sampledProjectorTotalDegree q a Δ B + p₀,
    D, sampledProjectorTotalDegree q a Δ B + r₀, hC, hD, hstep⟩

/-- **The sampled induction with each family obtained from the previous one.** Starting
from the scalar singleton, the family at the cut after `i + 1` sites is the step
`successiveStep _ m Finset.univ A` applied to the size-trimming selection of the extension
of the previous family, with `A` the left factors of the cut decomposition of a sampled
projector within `δ / 4` of the ground projection. Every family has fixed polynomial size
and bond bounds. LVV13, `algo53.tex`, induction, lines 652–678, in the documented
quantitative scope. -/
theorem exists_sampled_successive_viable_sets_polynomial_explicit_energy_degree
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p₀ D r₀ : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
      (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
        S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, (hi : i + 1 ≤ L) →
          ∃ (ℓ n N : ℕ) (I : Fin ℓ → Fin n → Fin L)
            (A : Fin N → LeftBlockMatrix L q (i + 1))
            (B' : Fin N → RightBlockMatrix L q (i + 1)),
            ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ <
              lvvViabilityPrecision Δ η / (L : ℝ) ^ a / 4 ∧
            Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (i + 1))
              (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
            S (i + 1) = successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
              Finset.univ A (ChainHamiltonian.sizeTrimmingSelection
                (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ (AreaLaw.extend (i + 1) (S i)))) ∧
        ∀ i : ℕ, i ≤ L →
          IsViableMPS Γ (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀))
            (D * L ^ (sampledProjectorTotalDegree q a Δ B + r₀))
            (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S i) := by
  classical
  obtain ⟨C, p₀, D, r₀, hC, hD, hstep⟩ :=
    exists_sampled_viable_successor_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  let p := sampledProjectorTotalDegree q a Δ B + p₀
  let r := sampledProjectorTotalDegree q a Δ B + r₀
  refine ⟨C, p₀, D, r₀, hC, hD, ?_⟩
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
  let Step := fun (i : ℕ) (S : Finset (LeftBlockVector L q i))
      (T : Finset (LeftBlockVector L q (i + 1))) ↦
    ∀ hi : i + 1 ≤ L,
      ∃ (ℓ n N : ℕ) (I : Fin ℓ → Fin n → Fin L)
        (A : Fin N → LeftBlockMatrix L q (i + 1))
        (B' : Fin N → RightBlockMatrix L q (i + 1)),
        ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ <
          lvvViabilityPrecision Δ η / (L : ℝ) ^ a / 4 ∧
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (i + 1))
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
        T = successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L)) Finset.univ A
          (ChainHamiltonian.sizeTrimmingSelection (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ
            (AreaLaw.extend (i + 1) S))
  have hadvance : ∀ (i : ℕ) (S : Finset (LeftBlockVector L q i)), (i ≤ L → P i S) →
      ∃ T : Finset (LeftBlockVector L q (i + 1)), (i + 1 ≤ L → P (i + 1) T) ∧ Step i S T := by
    intro i S hS
    by_cases hi : i + 1 ≤ L
    · obtain ⟨-, -, hviable⟩ := hS (by omega)
      obtain ⟨ℓ, n, N, I, A, B', hproj, hdec, hT⟩ :=
        hstep L hL h hs h0 h1 E₀ Γ hgs hEB (i + 1) (by omega) hi S hviable
      exact ⟨_, fun _ ↦ hT, fun _ ↦ ⟨ℓ, n, N, I, A, B', hproj, hdec, rfl⟩⟩
    · exact ⟨∅, fun hi' ↦ absurd hi' hi, fun hi' ↦ absurd hi' hi⟩
  let State := fun i : ℕ ↦ {S : Finset (LeftBlockVector L q i) // i ≤ L → P i S}
  let initial : State 0 := ⟨{emptyLeftVector L q}, fun _ ↦ hbase⟩
  have htransition (i : ℕ) (previous : State i) :
      ∃ next : State (i + 1), Step i previous.val next.val := by
    obtain ⟨T, hT, hStep⟩ := hadvance i previous.val previous.property
    exact ⟨⟨T, hT⟩, hStep⟩
  obtain ⟨run, hrun0, hrunStep⟩ := Nat.exists_dependent_sequence
    (fun i (S : State i) (T : State (i + 1)) ↦ Step i S.val T.val) initial htransition
  exact ⟨fun i ↦ (run i).val, congrArg Subtype.val hrun0, fun i hi ↦ hrunStep i hi,
    fun i hi ↦ (run i).property hi⟩

/-- The total number of candidate vectors retained during the whole sampled
LVV sweep is polynomial with one degree more than the bound for a single
viable family. This counts the candidates at all cuts, but makes no assertion
about the arithmetic cost of the convex optimization or spectral
computations. LVV13, `algo53.tex`, lines 652–678. -/
theorem exists_sampled_successive_viable_sets_polynomial_total_cardinality
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p₀ D r₀ : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2))) →
      (∀ j, (h j).PosSemidef) → (∀ j, h j ≤ 1) →
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i), S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, i ≤ L →
          IsViableMPS Γ
            (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀))
            (D * L ^ (sampledProjectorTotalDegree q a Δ B + r₀))
            (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S i)) ∧
        (∑ i ∈ Finset.range (L + 1), (S i).card) ≤
          C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀ + 1) := by
  classical
  obtain ⟨C, p₀, D, r₀, hC, hD, hsets⟩ :=
    exists_sampled_successive_viable_sets_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  refine ⟨2 * C, p₀, D, r₀, by omega, hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB
  obtain ⟨S, hS0, _, hS⟩ := hsets L hL h hs h0 h1 E₀ Γ hgs hEB
  refine ⟨S, hS0, ?_, ?_⟩
  · intro i hi
    obtain ⟨hcard, hbond, hviable⟩ := hS i hi
    exact ⟨hcard.trans (Nat.mul_le_mul_right _ (by omega)), hbond, hviable⟩
  · have hsum : (∑ i ∈ Finset.range (L + 1), (S i).card) ≤
        (L + 1) * (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀)) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (L + 1),
            C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀) := by
          apply Finset.sum_le_sum
          intro i hi
          exact (hS i (by have := Finset.mem_range.mp hi; omega)).1
        _ = _ := by simp
    calc
      _ ≤ (L + 1) * (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀)) := hsum
      _ ≤ (2 * L) * (C * L ^ (sampledProjectorTotalDegree q a Δ B + p₀)) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (2 * C) * L ^ (sampledProjectorTotalDegree q a Δ B + p₀ + 1) := by
        rw [pow_succ]
        ring

/-- **The sampled induction with each family obtained from the previous one.** Starting
from the scalar singleton, the family at the cut after `i + 1` sites is the step
`successiveStep _ m Finset.univ A` applied to the size-trimming selection of the extension
of the previous family, with `A` the left factors of the cut decomposition of a sampled
projector within `δ / 4` of the ground projection. Every family has fixed polynomial size
and bond bounds. LVV13, `algo53.tex`, induction, lines 652–678, in the documented
quantitative scope. -/
theorem exists_sampled_successive_viable_sets_polynomial {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2)))
      (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
      (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
        S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, (hi : i + 1 ≤ L) →
          ∃ (ℓ n N : ℕ) (I : Fin ℓ → Fin n → Fin L)
            (A : Fin N → LeftBlockMatrix L q (i + 1))
            (B' : Fin N → RightBlockMatrix L q (i + 1)),
            ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ <
              lvvViabilityPrecision Δ η / (L : ℝ) ^ a / 4 ∧
            Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (i + 1))
              (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
            S (i + 1) = successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
              Finset.univ A (ChainHamiltonian.sizeTrimmingSelection
                (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ (AreaLaw.extend (i + 1) (S i)))) ∧
        ∀ i : ℕ, i ≤ L →
          IsViableMPS Γ (C * L ^ p) (D * L ^ r)
            (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S i) := by
  obtain ⟨C, p₀, D, r₀, hC, hD, hsets⟩ :=
    exists_sampled_successive_viable_sets_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  exact ⟨C, sampledProjectorTotalDegree q a Δ B + p₀,
    D, sampledProjectorTotalDegree q a Δ B + r₀, hC, hD, hsets⟩

/-- The final viable span contains a normalized matrix product state whose bond
degree is twice the explicit sampled-projector degree plus an
energy-independent offset. LVV13, `algo53.tex`, final induction,
lines 652–678. -/
theorem exists_sampled_groundState_openMPS_polynomial_explicit_energy_degree
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p₀ : ℕ, 1 ≤ C ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
        (interval L j (j + 2))) →
      (∀ j, (h j).PosSemidef) → (∀ j, h j ≤ 1) →
      ∀ (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ ψ : EuclideanSpace ℂ (Fin L → Fin q), ‖ψ‖ = 1 ∧
        1 - η / (L : ℝ) ^ a ≤ ‖⟪ψ, Γ⟫_ℂ‖ ∧
        IsOpenMPS L q
          (C * L ^ (2 * sampledProjectorTotalDegree q a Δ B + p₀))
          (fun x ↦ ψ x) := by
  obtain ⟨C, p₀, D, r₀, hC, hD, hsets⟩ :=
    exists_sampled_successive_viable_sets_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  let t := sampledProjectorTotalDegree q a Δ B
  let p := t + p₀
  let r := t + r₀
  refine ⟨C * D, p₀ + r₀, by simpa only [one_mul] using Nat.mul_le_mul hC hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB
  obtain ⟨S, _, _, hS⟩ := hsets L hL h hs h0 h1 E₀ Γ hgs hEB
  obtain ⟨ψ, hψ, hoverlap, hMPS⟩ := (hS L le_rfl).exists_openMPS
  refine ⟨ψ, hψ, ?_, ?_⟩
  · have hprec : lvvViabilityPrecision Δ η ≤ η :=
      (min_le_left _ _).trans (min_le_right 1 η)
    have hdiv : lvvViabilityPrecision Δ η / (L : ℝ) ^ a ≤ η / (L : ℝ) ^ a :=
      div_le_div_of_nonneg_right hprec (pow_nonneg (Nat.cast_nonneg L) a)
    linarith only [hoverlap, hdiv]
  · have hbond : 1 ≤ D * L ^ r := by simpa only [one_mul] using Nat.mul_le_mul hD (one_le_pow₀ hL)
    have heq : C * L ^ p * max 1 (D * L ^ r) =
        (C * D) * L ^ (2 * t + (p₀ + r₀)) := by
      rw [max_eq_right hbond, pow_add]
      dsimp only [p, r]
      rw [pow_add, pow_add]
      ring
    rwa [heq] at hMPS

/-- Existential-degree form of
`exists_sampled_groundState_openMPS_polynomial_explicit_energy_degree`. -/
theorem exists_sampled_groundState_openMPS_polynomial {q : ℕ} (hq : 2 ≤ q)
    (a : ℕ) (ha : 1 ≤ a) {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
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
  obtain ⟨C, p₀, hC, hMPS⟩ :=
    exists_sampled_groundState_openMPS_polynomial_explicit_energy_degree
      (B := B) hq a ha hΔ hη
  exact ⟨C, 2 * sampledProjectorTotalDegree q a Δ B + p₀, hC, hMPS⟩

end TNLean.MPS.AreaLaw

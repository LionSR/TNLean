/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SampledSuccessiveConstruction
import TNLean.MPS.AreaLaw.ViableSet.RationalOrthonormalFamily
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.RationalRepresentationBounds
import TNLean.MPS.AreaLaw.ViableSet.BoundarySDP.PolynomialPrecision
import TNLean.Algebra.DependentSequence

/-!
# Uniform rational data for a sampled viable-set step

Extend the input family by one site, take the Hamiltonian's size-trimming
selection, independently trim its bonds, and apply the left factors of a
sampled projector. Approximate an orthonormal basis of the resulting span
by rational open-chain tensors. The final approximation has polynomial
cardinality and bond bounds and a common parameter height whose binary
exponent is bounded by a fixed quadratic in the chain length.

The constants precede the length, Hamiltonian, cut and input family. Their
dependence on a fixed ground-energy-to-gap bound is retained explicitly.
The result is an existence theorem with finite-precision data; it asserts
no arithmetic running time.

Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`,
Claims `c:ext`, `c:2`, `c:trim`, `c:errorreduction`, lines 379–592.

**Local fix (trimming and normalization):** The quadratic trimming radius
is documented at <https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.
The sampled normalization correction is recorded in
`docs/paper-gaps/lvv13_error_reduction_witness_norm.tex`.

**Scope restriction (quantitative constants):** The library constant-cut
bond and corrected net exponent are those of `docs/paper-gaps/lvv13_constant_bond.tex`.
The ground-energy dependence is recorded in
`docs/paper-gaps/lvv13_runtime_ground_energy.tex`.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- One complete positive-cut step has uniform rational tensor data. The exact
family is the named successive step of the extended input. Its rational
replacement transfers viability for every normalized target, with loss at
most half the target error. Source: LVV13, `algo53.tex`, lines 379–592,
with the quantitative qualifications stated in the module docstring. -/
theorem exists_rational_sampled_viable_successor_polynomial
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r E : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ L : ℕ, 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j (j + 2)))
        (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
        (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∀ n : ℕ, ∀ (hi : n + 1 ≤ L) (S : Finset (LeftBlockVector L q n)),
      IsViable Γ (lvvViabilityPrecision Δ η / (L : ℝ) ^ a)
        (S : Set (LeftBlockVector L q n)) →
      ∃ (ℓ m N : ℕ) (I : Fin ℓ → Fin m → Fin L)
        (A : Fin N → LeftBlockMatrix L q (n + 1))
        (B' : Fin N → RightBlockMatrix L q (n + 1))
        (T : Finset (LeftBlockVector L q (n + 1))),
        let δ := lvvViabilityPrecision Δ η / (L : ℝ) ^ a
        let V := successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
          Finset.univ A (ChainHamiltonian.sizeTrimmingSelection
            (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ (AreaLaw.extend (n + 1) S))
        ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 8 ∧
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (n + 1))
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
        T.card ≤ V.card ∧
        (∀ v ∈ T, Nonempty (RationalLeftOpenMPSRepresentationOfHeight
          (2 ^ (E * (L + 1) ^ 2)) (D * L ^ r) v)) ∧
        (∀ (Γ' : EuclideanSpace ℂ (Fin L → Fin q)) (ε : ℝ),
          ‖Γ'‖ = 1 → IsViable Γ' ε (V : Set (LeftBlockVector L q (n + 1))) →
          IsViable Γ' (ε + δ / 2) (T : Set (LeftBlockVector L q (n + 1)))) ∧
        IsViableMPS Γ (C * L ^ p) (D * L ^ r) δ T := by
  classical
  let α := lvvViabilityPrecision Δ η
  have hα : 0 < α :=
    lt_min (lt_min zero_lt_one hη) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
  have hα1 : α ≤ 1 := (min_le_left _ _).trans (min_le_left 1 η)
  obtain ⟨P, t, hP, hsample⟩ := exists_sampledProjector_uniform_polynomial (B := B)
    (by omega : 1 ≤ q) a (div_pos hα (by norm_num))
    (show α / 16 ≤ 1 by linarith) hΔ
  obtain ⟨M, u, _, hradius⟩ := exists_bondTrimmingRadius_lvvReferenceBond_polynomial q Δ
  let c := (Δ / 169) ^ 2
  let d := constantCutBond q 1 1 Δ c
  let k := 2 * (q * d) ^ 2
  let F := (d + 1) * d * (2 * ⌈2 * ((q * d : ℕ) : ℝ) ^ 2 / c⌉₊ + 1) ^ k
  let C := P * max 1 F
  let p := t + k
  let M' := max 1 ⌈M⌉₊
  let D := C * P * M'
  let r := p + t + u
  obtain ⟨E, hprecision⟩ := exists_tensor_dyadic_precision_quadratic_bound
    q C p D r a (show 0 < α / 2 by positivity)
  have hC : 1 ≤ C := by
    simpa only [one_mul] using Nat.mul_le_mul hP (le_max_left 1 F)
  have hD : 1 ≤ D := by
    simpa only [one_mul] using Nat.mul_le_mul
      (show 1 ≤ C * P by simpa only [one_mul] using Nat.mul_le_mul hC hP)
      (le_max_left 1 ⌈M⌉₊)
  refine ⟨C, p, D, r, 2 * E + 5, hC, hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB n hi S hviable
  let : NeZero L := ⟨by omega⟩
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  let δ := α / (L : ℝ) ^ a
  have hδ : 0 < δ := div_pos hα (pow_pos hLp a)
  have hδ1 : δ ≤ 1 := (div_le_one (pow_pos hLp a)).mpr
    (hα1.trans (one_le_pow₀ (by exact_mod_cast hL)))
  let chain := ChainHamiltonian.ofBonds h hs h0 h1
  have hgs' : IsGappedGroundState chain.operator E₀ Γ Δ := by
    simpa only [chain, ChainHamiltonian.ofBonds_operator] using hgs
  have hsmall : IsViable Γ (c / L)
      (AreaLaw.extend (n + 1) S : Set (LeftBlockVector L q (n + 1))) := by
    obtain ⟨v, hv, hoverlap, hsupport⟩ := hviable.extend (by omega) hi
    refine ⟨v, hv, ?_, hsupport⟩
    have hLpow : (L : ℝ) ≤ (L : ℝ) ^ a := le_self_pow₀ (by exact_mod_cast hL) (by omega)
    have hprec : δ ≤ c / L := by
      calc
        _ ≤ c / (L : ℝ) ^ a := div_le_div_of_nonneg_right
          (min_le_right (min 1 η) c) (pow_nonneg hLp.le a)
        _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hLp hLpow
    linarith only [hoverlap, hprec]
  let m := bondTrimmingRadius L (lvvReferenceBond q Δ L)
  let T₀ := chain.sizeTrimmingSelection hq Δ (AreaLaw.extend (n + 1) S)
  have htrim : IsViableMPS Γ (F * L ^ k) m (1 / 2) (bondTrimSet hi m T₀) :=
    ⟨(card_bondTrimSet_le hi m T₀).trans
      (chain.card_sizeTrimmingSelection_le_polynomial (by omega) hq hΔ _),
      fun v hv ↦ isLeftOpenMPS_of_mem_bondTrimSet hi m T₀ hv,
      chain.isViable_bondTrimSet_sizeTrimmingSelection
        (ChainHamiltonian.posSemidef_ofBonds_term h hs h0 h1) (by omega) hq hi hΔ
        (AreaLaw.extend (n + 1) S) E₀ Γ hgs' hsmall⟩
  have hexact := exists_sampled_errorReduction (by omega : 1 ≤ q) h hs h0 h1 hgs hΔ
    (δ := δ / 2) (by positivity) (by linarith)
  dsimp only at hexact
  rw [show δ / 2 / 8 = (α / 16) / (L : ℝ) ^ a by dsimp only [δ]; ring] at hexact
  obtain ⟨I, hproj, hcuts⟩ := hexact
  obtain ⟨N, A, B', _, hdec, _, hgood⟩ := hcuts (n + 1) hi
  let V := successiveStep hi m Finset.univ A T₀
  have hV := hgood (F * L ^ k) m (bondTrimSet hi m T₀) htrim
  obtain ⟨hE₀, hE₀L⟩ := groundEnergy_nonneg_and_le h h0 h1 hgs
  have hbudgets := hsample L E₀ hL hE₀ hE₀L hEB
  have hVcard : V.card ≤ C * L ^ p := by
    calc
      _ ≤ (P * L ^ t) * (F * L ^ k) :=
        hV.1.trans (Nat.mul_le_mul_right _ hbudgets.1)
      _ = (P * F) * L ^ p := by dsimp only [p]; rw [pow_add]; ring
      _ ≤ C * L ^ p := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left P (le_max_right 1 F))
  have hm : max 1 m ≤ M' * L ^ u := by
    apply max_le
    · simpa only [one_mul] using Nat.mul_le_mul (le_max_left 1 ⌈M⌉₊) (one_le_pow₀ hL)
    · have hreal := (hradius L hL).trans
        (mul_le_mul_of_nonneg_right (Nat.le_ceil M) (pow_nonneg (Nat.cast_nonneg L) u))
      have hnat : m ≤ ⌈M⌉₊ * L ^ u := by exact_mod_cast hreal
      exact hnat.trans (Nat.mul_le_mul_right _ (le_max_right 1 ⌈M⌉₊))
  let sampleError := (α / 16) / (L : ℝ) ^ a
  let wordLength := ⌈((L - E₀) / Δ) * Real.log (1 / sampleError)⌉₊
  let wordCount := sampledProjectorWordCount q L E₀ sampleError wordLength
  let Dsample := q ^ (2 * sampledProjectorLetterBound L wordCount wordLength)
  have hDbound : max 1 (Dsample * max 1 m) ≤ (P * M') * L ^ (t + u) := by
    apply max_le
    · simpa only [one_mul] using Nat.mul_le_mul
        (show 1 ≤ P * M' by simpa only [one_mul] using Nat.mul_le_mul hP (le_max_left 1 ⌈M⌉₊))
        (one_le_pow₀ hL)
    · calc
        _ ≤ (P * L ^ t) * (M' * L ^ u) := Nat.mul_le_mul hbudgets.2 hm
        _ = _ := by rw [pow_add]; ring
  let b' := V.card * max 1 (Dsample * max 1 m)
  have hb' : b' ≤ D * L ^ r := by
    calc
      _ ≤ (C * L ^ p) * ((P * M') * L ^ (t + u)) := Nat.mul_le_mul hVcard hDbound
      _ = _ := by dsimp only [D, r]; rw [pow_add, pow_add]; ring
  obtain ⟨T, hcard, hdata, htransfer⟩ :=
    exists_rational_leftFamily_approximation_of_orthonormalization V hi hV.2.1
      (ε := δ / 2) (by positivity) (by linarith)
  have hmeshEq : (α / 2) / (2 * (L : ℝ) ^ a * (V.card + 1)) =
      (δ / 2) / (2 * (V.card + 1)) := by
    have hcardne : (V.card : ℝ) + 1 ≠ 0 := by positivity
    dsimp only [δ]
    field_simp [hLp.ne', hcardne]
  have hheight := (hprecision L (n + 1) V.card b' hL hi hVcard hb').2
  rw [hmeshEq] at hheight
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] at hheight
  refine ⟨_, _, N, I, A, B', T, ?_, hdec, hcard, ?_, htransfer, ?_⟩
  · simpa only [show δ / 2 / 4 = δ / 8 by ring] using hproj
  · intro v hv
    obtain ⟨R⟩ := hdata v hv
    exact ⟨R.mono hheight hb'⟩
  · refine ⟨hcard.trans hVcard, ?_, ?_⟩
    · intro v hv
      obtain ⟨R⟩ := hdata v hv
      exact IsOpenMPS.mono R.data.isLeftOpenMPS (max_le_max_left 1 hb')
    · simpa only [show δ / 2 + δ / 2 = δ by ring] using htransfer Γ (δ / 2) hgs.1 hV.2.2

/-- Starting from the scalar basis vector at the empty cut, the named sampled
steps and rational span approximations give viable families at every cut.
One polynomial bounds their cardinalities and another their individual bonds;
one quadratic exponent bounds their common rational parameter height.
Source: LVV13, `algo53.tex`, induction, lines 652–678, with the finite-precision
and quantitative qualifications stated in the module docstring. -/
theorem exists_rational_sampled_successive_viable_sets_polynomial
    {q : ℕ} (hq : 2 ≤ q) (a : ℕ) (ha : 1 ≤ a)
    {Δ B η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    ∃ C p D r E : ℕ, 1 ≤ C ∧ 1 ≤ D ∧ ∀ L : ℕ, 1 ≤ L →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j (j + 2)))
        (h0 : ∀ j, (h j).PosSemidef) (h1 : ∀ j, h j ≤ 1)
        (E₀ : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
      IsGappedGroundState (∑ j, h j) E₀ Γ Δ → E₀ / Δ ≤ B →
      ∃ S : (i : ℕ) → Finset (LeftBlockVector L q i),
        S 0 = {emptyLeftVector L q} ∧
        (∀ i : ℕ, i ≤ L →
          IsViableMPS Γ (C * L ^ p) (D * L ^ r)
            (lvvViabilityPrecision Δ η / (L : ℝ) ^ a) (S i)) ∧
        (∀ i : ℕ, i ≤ L → ∀ v ∈ S i, Nonempty
          (RationalLeftOpenMPSRepresentationOfHeight
            (2 ^ (E * (L + 1) ^ 2)) (D * L ^ r) v)) ∧
        ∀ i : ℕ, ∀ hi : i + 1 ≤ L,
          ∃ (ℓ m N : ℕ) (I : Fin ℓ → Fin m → Fin L)
            (A : Fin N → LeftBlockMatrix L q (i + 1))
            (B' : Fin N → RightBlockMatrix L q (i + 1)),
            let δ := lvvViabilityPrecision Δ η / (L : ℝ) ^ a
            let V := successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
              Finset.univ A (ChainHamiltonian.sizeTrimmingSelection
                (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ (AreaLaw.extend (i + 1) (S i)))
            ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 8 ∧
            Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (i + 1))
              (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
            (S (i + 1)).card ≤ V.card ∧
            ∀ (Γ' : EuclideanSpace ℂ (Fin L → Fin q)) (ε : ℝ),
              ‖Γ'‖ = 1 → IsViable Γ' ε (V : Set (LeftBlockVector L q (i + 1))) →
              IsViable Γ' (ε + δ / 2) (S (i + 1) : Set (LeftBlockVector L q (i + 1))) := by
  classical
  obtain ⟨C, p, D, r, E, hC, hD, hstep⟩ :=
    exists_rational_sampled_viable_successor_polynomial (B := B) hq a ha hΔ hη
  refine ⟨C, p, D, r, E, hC, hD, ?_⟩
  intro L hL h hs h0 h1 E₀ Γ hgs hEB
  let H := 2 ^ (E * (L + 1) ^ 2)
  let δ := lvvViabilityPrecision Δ η / (L : ℝ) ^ a
  let P := fun i (S : Finset (LeftBlockVector L q i)) ↦
    IsViableMPS Γ (C * L ^ p) (D * L ^ r) δ S ∧
      ∀ v ∈ S, Nonempty (RationalLeftOpenMPSRepresentationOfHeight H (D * L ^ r) v)
  have hbaseData : ∀ v ∈ ({emptyLeftVector L q} : Finset (LeftBlockVector L q 0)),
      Nonempty (RationalLeftOpenMPSRepresentationOfHeight H (D * L ^ r) v) := by
    intro v hv
    obtain rfl := Finset.mem_singleton.mp hv
    exact ⟨(RationalLeftOpenMPSRepresentationOfHeight.emptyLeftVector L q).mono
      (by dsimp only [H]; exact Nat.one_le_pow _ _ (by norm_num))
      (by simpa only [one_mul] using Nat.mul_le_mul hD (one_le_pow₀ hL))⟩
  have hbase : P 0 {emptyLeftVector L q} := by
    have hempty := isViableMPS_emptyLeftVector hgs.1
    refine ⟨⟨hempty.1.trans ?_, ?_, hempty.2.2.mono_error ?_⟩, hbaseData⟩
    · simpa only [one_mul] using Nat.mul_le_mul hC (one_le_pow₀ hL)
    · intro v hv
      obtain ⟨R⟩ := hbaseData v hv
      exact R.data.isLeftOpenMPS
    · have hprec : 0 < lvvViabilityPrecision Δ η :=
        lt_min (lt_min zero_lt_one hη) (sq_pos_of_pos (div_pos hΔ (by norm_num)))
      exact div_nonneg hprec.le (pow_nonneg (Nat.cast_nonneg L) a)
  let Step := fun (i : ℕ) (S : Finset (LeftBlockVector L q i))
      (T : Finset (LeftBlockVector L q (i + 1))) ↦
    ∀ hi : i + 1 ≤ L,
      ∃ (ℓ m N : ℕ) (I : Fin ℓ → Fin m → Fin L)
        (A : Fin N → LeftBlockMatrix L q (i + 1))
        (B' : Fin N → RightBlockMatrix L q (i + 1)),
        let V := successiveStep hi (bondTrimmingRadius L (lvvReferenceBond q Δ L))
          Finset.univ A (ChainHamiltonian.sizeTrimmingSelection
            (ChainHamiltonian.ofBonds h hs h0 h1) hq Δ (AreaLaw.extend (i + 1) S))
        ‖sampledProjector h E₀ I - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ))‖ < δ / 8 ∧
        Entropy.cutOperator (n := fun _ : Fin L ↦ q) (leftBlock L (i + 1))
          (sampledProjector h E₀ I) = ∑ j, A j ⊗ₖ B' j ∧
        T.card ≤ V.card ∧
        ∀ (Γ' : EuclideanSpace ℂ (Fin L → Fin q)) (ε : ℝ),
          ‖Γ'‖ = 1 → IsViable Γ' ε (V : Set (LeftBlockVector L q (i + 1))) →
          IsViable Γ' (ε + δ / 2) (T : Set (LeftBlockVector L q (i + 1)))
  have hadvance : ∀ (i : ℕ) (S : Finset (LeftBlockVector L q i)), (i ≤ L → P i S) →
      ∃ T : Finset (LeftBlockVector L q (i + 1)), (i + 1 ≤ L → P (i + 1) T) ∧ Step i S T := by
    intro i S hS
    by_cases hi : i + 1 ≤ L
    · have hprevious := hS (by omega)
      obtain ⟨ℓ, m, N, I, A, B', T, hproj, hdec, hcard, hdata, htransfer, hviable⟩ :=
        hstep L hL h hs h0 h1 E₀ Γ hgs hEB i hi S hprevious.1.2.2
      exact ⟨T, fun _ ↦ ⟨hviable, hdata⟩,
        fun _ ↦ ⟨ℓ, m, N, I, A, B', hproj, hdec, hcard, htransfer⟩⟩
    · exact ⟨∅, fun hi' ↦ absurd hi' hi, fun hi' ↦ absurd hi' hi⟩
  let State := fun i : ℕ ↦ {S : Finset (LeftBlockVector L q i) // i ≤ L → P i S}
  let initial : State 0 := ⟨{emptyLeftVector L q}, fun _ ↦ hbase⟩
  have htransition (i : ℕ) (previous : State i) :
      ∃ next : State (i + 1), Step i previous.val next.val := by
    obtain ⟨T, hT, hStep⟩ := hadvance i previous.val previous.property
    exact ⟨⟨T, hT⟩, hStep⟩
  obtain ⟨run, hrun0, hrunStep⟩ := Nat.exists_dependent_sequence
    (fun i (S : State i) (T : State (i + 1)) ↦ Step i S.val T.val) initial htransition
  exact ⟨fun i ↦ (run i).val, congrArg Subtype.val hrun0, fun i hi ↦ ((run i).property hi).1,
    fun i hi ↦ ((run i).property hi).2,
    fun i hi ↦ hrunStep i hi⟩

end TNLean.MPS.AreaLaw

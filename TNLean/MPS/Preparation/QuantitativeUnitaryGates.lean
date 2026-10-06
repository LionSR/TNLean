/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.TwoSiteUniversality
import TNLean.Algebra.IsometryUnitaryExtension

/-!
# Quantitative synthesis by neighboring two-qudit gates

The synthesis in `TNLean.Circuit.Gates.TwoSiteUniversality` can be counted explicitly. A controlled
single-site two-level operation with at most `k` controls costs at most
`4 * n * 3 ^ k` neighboring two-qudit gates. Combining this estimate with
Givens elimination gives a polynomial bound in the Hilbert-space dimension.
The decomposition is an exact matrix equality, including the global phase,
and uses no auxiliary sites.

This is a quantitative refinement of the synthesis used in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; it is a derived result,
not a theorem quoted from arXiv:2508.08160.
-/

open Matrix MPSTensor
open QuantumCircuit
open scoped BigOperators ComplexConjugate

namespace MPSPreparation

variable {d n : ℕ}

/-- A two-level single-site rotation or phase with at most `k` controls is
an exact product of at most `4 * n * 3 ^ k` neighboring two-qudit gates.
Derived synthesis estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_ctrlOp_le_exponential (hd : 0 < d) (hn : 2 ≤ n) (k : ℕ) :
    ∀ S : Finset (Fin n), S.card ≤ k → ∀ t, t ∉ S → ∀ (c : Cfg d n) (α β : Fin d),
      α ≠ β → ∀ g, IsSpecialTwo g →
        IsPairProduct d n (4 * n * 3 ^ k) (ctrlOp S c t (twoLevel α β g)) := by
  induction k with
  | zero =>
    refine fun S hS t _ c α β hαβ g hg => ?_
    rw [Nat.le_zero, Finset.card_eq_zero] at hS
    subst hS
    rw [ctrlOp_empty]
    exact isPairProduct_of_mem_supportedOperators_card_le_two hd hn
      (T := {t}) (by simp) (siteOp_mem_unitary t (twoLevel_mem_unitary hαβ hg.mem_unitary))
      (by simpa using siteOp_mem_supportedOperators t _) |>.mono (by simp; omega)
  | succ k ih =>
    let K := 4 * n * 3 ^ k
    have hK := ih
    intro S hS t ht c α β hαβ g hg
    rcases Nat.lt_or_ge k S.card with hk | hk
    swap
    · exact (hK S hk t ht c α β hαβ g hg).mono (by
        have hp := Nat.one_le_pow k 3 (by norm_num)
        rw [pow_succ]
        nlinarith)
    obtain ⟨s, hs⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    set S' := S.erase s
    have hS' : S'.card ≤ k := by rw [Finset.card_erase_of_mem hs]; omega
    have hsS' : s ∉ S' := Finset.notMem_erase s S
    have htS' : t ∉ S' := fun h => ht (Finset.mem_of_mem_erase h)
    have hst : s ≠ t := fun h => ht (h ▸ hs)
    obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := hg.exists_commutator
    have hV := twoLevel_mem_unitary hαβ hg₁.mem_unitary
    have hW := twoLevel_mem_unitary (ι := Fin d) hαβ hg₂
    have heq : twoLevel α β (g₁ * g₂ * star g₁ * star g₂) =
        twoLevel α β g₁ * twoLevel α β g₂ * star (twoLevel α β g₁) *
          star (twoLevel α β g₂) := by
      rw [star_eq_conjTranspose (twoLevel α β g₁), star_eq_conjTranspose (twoLevel α β g₂),
        twoLevel_conjTranspose, twoLevel_conjTranspose, twoLevel_mul hαβ, twoLevel_mul hαβ,
        twoLevel_mul hαβ]; rfl
    rw [heq, ← Finset.insert_erase hs, ctrlOp_insert_commutator htS' hst c hV hW]
    have hsingle : ∀ u : Matrix (Fin d) (Fin d) ℂ, u ∈ unitary (Matrix (Fin d) (Fin d) ℂ) →
        IsPairProduct d n (2 * n) (ctrlOp {s} c t u) := fun u hu =>
      isPairProduct_of_mem_supportedOperators_card_le_two hd hn (T := {t, s})
        (Finset.card_le_two) (ctrlOp_mem_unitary (by simpa using Ne.symm hst) c hu)
        (by simpa using ctrlOp_mem_supportedOperators {s} c t u)
    have h1 := hK S' hS' t htS' c α β hαβ g₁ hg₁
    have h2 : IsPairProduct d n K (ctrlOp S' c t (star (twoLevel α β g₁))) := by
      rw [star_eq_conjTranspose, twoLevel_conjTranspose]
      exact hK S' hS' t htS' c α β hαβ _ hg₁.conjTranspose
    have := ((h1.mul (hsingle _ hW)).mul h2).mul (hsingle _ (Unitary.star_mem hW))
    exact this.mono (by
      have hp := Nat.one_le_pow k 3 (by norm_num)
      dsimp [K]
      rw [pow_succ]
      nlinarith)

/-- Every two-level rotation or phase on `n` sites has an exact
neighboring-pair decomposition of length at most
`(2 * n + 1) * (4 * n * 3 ^ n)`. No auxiliary sites are added.
Derived synthesis estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_twoLevel_le_exponential (hd : 0 < d) (hn : 2 ≤ n) :
    ∀ a b : Cfg d n, a ≠ b → ∀ g, IsSpecialTwo g →
      IsPairProduct d n ((2 * n + 1) * (4 * n * 3 ^ n)) (twoLevel a b g) := by
  let K₁ := 4 * n * 3 ^ n
  have hK₁ := isPairProduct_ctrlOp_le_exponential hd hn n
  -- configurations differing at exactly one site
  have hone : ∀ (a : Cfg d n) (t : Fin n) (β : Fin d), β ≠ a t → ∀ g, IsSpecialTwo g →
      IsPairProduct d n K₁ (twoLevel a (Function.update a t β) g) := by
    intro a t β hβ g hg
    rw [twoLevel_update_eq_ctrlOp a t hβ g]
    exact hK₁ _ ((Finset.card_le_univ _).trans (by simp)) t (by simp) a (a t) β
      (Ne.symm hβ) g hg
  have key : ∀ h : ℕ, ∀ a b : Cfg d n, hammingDist a b = h + 1 → ∀ g, IsSpecialTwo g →
      IsPairProduct d n ((2 * h + 1) * K₁) (twoLevel a b g) := by
    intro h
    induction h with
    | zero =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hab
      have hb : b = Function.update a t (b t) := by
        funext i
        by_cases hi : i = t
        · subst hi; simp
        · rw [Function.update_of_ne hi]
          by_contra h'
          have : i ∈ Finset.univ.filter fun i => a i ≠ b i := by simp [Ne.symm h']
          rw [ht] at this
          exact hi (Finset.mem_singleton.mp this)
      have hbt : b t ≠ a t := by
        have : t ∈ Finset.univ.filter fun i => a i ≠ b i := by rw [ht]; simp
        simpa [eq_comm] using this
      rw [hb]
      simpa using hone a t (b t) hbt g hg
    | succ h ih =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ : (Finset.univ.filter fun i => a i ≠ b i).Nonempty :=
        Finset.card_pos.mp (by unfold hammingDist at hab; omega)
      have hat : a t ≠ b t := (Finset.mem_filter.mp ht).2
      set c := Function.update b t (a t) with hc
      have hfilter : (Finset.univ.filter fun i => a i ≠ c i) =
          (Finset.univ.filter fun i => a i ≠ b i).erase t := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hc]
        by_cases hi : i = t
        · subst hi; simp
        · simp [hi]
      have hac' : hammingDist a c = h + 1 := by
        unfold hammingDist
        rw [hfilter, Finset.card_erase_of_mem ht]
        unfold hammingDist at hab
        omega
      have hac : a ≠ c := hammingDist_pos.mp (by omega)
      have hbc : b ≠ c := fun h' => by
        have := congrFun h' t
        rw [hc, Function.update_self] at this
        exact hat this.symm
      have hab' : a ≠ b := fun h' => by rw [h'] at hat; exact hat rfl
      have hcb : b = Function.update c t (b t) := by
        rw [hc, Function.update_idem, Function.update_eq_self]
      have hT : IsPairProduct d n K₁ (twoLevel c b quarterTwo) := by
        have hbt : b t ≠ c t := by rw [hc, Function.update_self]; exact Ne.symm hat
        rw [hcb]
        simpa using hone c t (b t) hbt _ quarterTwo_isSpecialTwo
      rw [twoLevel_conj_quarterTwo hab' hac hbc g]
      have := (hT.star.mul (ih a c hac' g hg)).mul hT
      refine this.mono (le_of_eq ?_)
      ring
  intro a b hab g hg
  obtain ⟨h, hh⟩ : ∃ h, hammingDist a b = h + 1 :=
    ⟨hammingDist a b - 1, by have := hammingDist_pos.mpr hab; omega⟩
  refine (key h a b hh g hg).mono (Nat.mul_le_mul_right _ ?_)
  have := (hammingDist_le_card_fintype (x := a) (y := b)).trans_eq (Fintype.card_fin n)
  omega

/-- Explicit neighboring-pair gate count obtained from controlled rotations
and Givens elimination. Derived synthesis estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def unitaryGateCount (d n : ℕ) : ℕ :=
  2 * n + 3 * (d ^ n) * (d ^ n) * ((2 * n + 1) * (4 * n * 3 ^ n))

/-- Every unitary on `n ≥ 2` sites admits a neighboring two-qudit circuit
with the explicit gate count `unitaryGateCount d n`. The circuit agrees
with the unitary as a matrix, including its global phase, on all inputs,
and adds no auxiliary sites. Derived synthesis theorem for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_unitaryGateCount (hd : 0 < d) (hn : 2 ≤ n) :
    ∀ X : Matrix (Cfg d n) (Cfg d n) ℂ,
      X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) →
        IsPairProduct d n (unitaryGateCount d n) X := by
  let K₂ := (2 * n + 1) * (4 * n * 3 ^ n)
  have hK₂ := isPairProduct_twoLevel_le_exponential hd hn
  set m := Fintype.card (Cfg d n)
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨fun _ => ⟨0, hd⟩⟩
  have hcost : unitaryGateCount d n = 2 * n + 3 * m * m * K₂ := by
    simp only [unitaryGateCount, m, K₂, Fintype.card_fun, Fintype.card_fin]
  rw [hcost]
  intro X hX
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq X.det hm
  have hdetn : ‖X.det‖ = 1 := by
    have h := congrArg det (Unitary.star_mul_self_of_mem hX)
    rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose, Complex.star_def,
      Complex.conj_mul'] at h
    exact_mod_cast (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (by exact_mod_cast h)
  have hμn : ‖μ‖ = 1 := by
    have h : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hμ, hdetn]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hμ0 : μ ≠ 0 := fun h => by simp [h] at hμn
  set X' := μ⁻¹ • X with hX'
  have hX'u : X' ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ) := by
    have hu := isPairProduct_smul_one (d := d) hd hn (μ := μ⁻¹) (by simp [hμn])
    have : X' = (μ⁻¹ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ)) * X := by
      rw [hX', smul_mul_assoc, Matrix.one_mul]
    rw [this]
    exact Submonoid.mul_mem _ hu.mem_unitary hX
  have hX'det : X'.det = 1 := by
    rw [hX', det_smul, inv_pow, hμ, inv_mul_cancel₀]
    intro h; rw [h] at hdetn; simp at hdetn
  obtain ⟨l, hl, hlg, hlX⟩ := isTwoLevelWord_of_det_eq_one hX'u hX'det
  have hprod : IsPairProduct d n (l.length * K₂)
      (l.map fun p => twoLevel p.1 p.2.1 p.2.2).prod := by
    have := IsPairProduct.list_prod (K := K₂) (l.map fun p => twoLevel p.1 p.2.1 p.2.2)
      (fun Y hY => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hY
        exact hK₂ _ _ (hlg p hp).1 _ (hlg p hp).2)
    simpa using this
  have hXeq : X = (μ • (1 : Matrix (Cfg d n) (Cfg d n) ℂ)) * X' := by
    rw [hX', smul_mul_assoc, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  rw [hXeq, hlX]
  refine ((isPairProduct_smul_one hd hn hμn).mul hprod).mono ?_
  have : l.length * K₂ ≤ 3 * m * m * K₂ := Nat.mul_le_mul_right _ hl
  omega


/-- The explicit neighboring-pair synthesis count is at most
`38 * (d ^ n) ^ 6` for `d ≥ 2`. Thus its cost is polynomial in the
Hilbert-space dimension. Derived estimate for Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem unitaryGateCount_le_hilbertDimension_pow (hd : 2 ≤ d) :
    unitaryGateCount d n ≤ 38 * (d ^ n) ^ 6 := by
  let m := d ^ n
  have hm : 1 ≤ m := Nat.one_le_pow n d (by omega)
  have hnm : n ≤ m := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hd n)
  have hthree : 3 ^ n ≤ m ^ 2 := by
    have hbase : 3 ≤ d ^ 2 := by nlinarith
    simpa only [m, ← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hbase n
  have hpower : m ≤ m ^ 6 := by
    simpa using Nat.pow_le_pow_right (show 0 < m by omega) (show 1 ≤ 6 by norm_num)
  calc
    unitaryGateCount d n ≤
        2 * m + 3 * m * m * ((3 * m) * (4 * m * m ^ 2)) := by
      dsimp only [unitaryGateCount]
      change 2 * n + 3 * m * m * ((2 * n + 1) * (4 * n * 3 ^ n)) ≤ _
      gcongr
      omega
    _ = 2 * m + 36 * m ^ 6 := by ring
    _ ≤ 38 * m ^ 6 := by nlinarith

/-- Every unitary on `n ≥ 2` sites of local dimension `d ≥ 2` is an exact
product of at most `38 * (d ^ n) ^ 6` neighboring two-qudit gates, with no
auxiliary sites, retaining the exact global phase. Derived synthesis theorem
for Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isPairProduct_le_hilbertDimension_pow (hd : 2 ≤ d) (hn : 2 ≤ n)
    {X : Matrix (Cfg d n) (Cfg d n) ℂ}
    (hX : X ∈ unitary (Matrix (Cfg d n) (Cfg d n) ℂ)) :
    IsPairProduct d n (38 * (d ^ n) ^ 6) X := by
  exact (isPairProduct_unitaryGateCount (by omega) hn X hX).mono
    (unitaryGateCount_le_hilbertDimension_pow hd)

/-- An isometry placed on selected input basis states extends to a full
unitary admitting an exact neighboring-pair circuit with at most
`38 * (d ^ n) ^ 6` gates. This derives both the circuit and its prescribed
columns; no synthesis witness is assumed. Derived leaf-construction theorem
for Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isPairProduct_apply_embedding_eq {κ : Type*} [DecidableEq κ]
    (hd : 2 ≤ d) (hn : 2 ≤ n) {V : Matrix (Cfg d n) κ ℂ}
    (hV : V.IsIsometry) (e : κ ↪ Cfg d n) :
    ∃ U : Matrix (Cfg d n) (Cfg d n) ℂ,
      IsPairProduct d n (38 * (d ^ n) ^ 6) U ∧
      ∀ u k, U u (e k) = V u k := by
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV e
  exact ⟨U, isPairProduct_le_hilbertDimension_pow hd hn hU, hUV⟩

end MPSPreparation

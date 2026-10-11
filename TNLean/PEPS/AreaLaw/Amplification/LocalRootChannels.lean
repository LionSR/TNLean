/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SiteExpectationOrder
import QICLean.Analysis.RootChannel

/-!
# Local root channels and their shells, with spectators

For a positive contraction `k`, the local channel on `K` has Kraus operators
`sqrt (1 - siteExpectation q K k)` and `sqrt (siteExpectation q K k)`. Each is tensored
with the identity on an arbitrary finite auxiliary system. The actual expectation error
controls the difference from the full channel, uniformly in the auxiliary dimension.

For a sequence of regions, the zeroth shell is the local channel minus the identity and
the successor shell is the difference of consecutive local channels. Their norm bounds
follow from contractivity and the expectation errors. For nested regions each shell
vanishes on the commutant of the physical algebra on its region, including operators that
also act on the auxiliary system. No ground vector or Hermiticity of the input is needed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `eq:amplification-channel-shells` and the following commutant argument,
  `09-amplification.tex`, lines 101–120; the root-channel estimate is Lemma 4.4,
  `03-quasilocal.tex`, lines 336–389. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently formalized from
  the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit Matrix

variable {q : ℕ} {ι Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

/-- The channel of the actual roots `sqrt (1 - k)` and `sqrt k`, extended by the
identity on a finite spectator system (`03-quasilocal.tex`, lines 352–368). -/
noncomputable def spectatorRootChannel (k : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  rootChannel (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix Aux Aux ℂ))
    (CFC.sqrt k ⊗ₖ (1 : Matrix Aux Aux ℂ)) B

/-- The actual local root channel obtained by replacing `k` with `E_K(k)`, with a
spectator identity (`09-amplification.tex`, lines 101–110). -/
noncomputable def localRootChannel (K : Finset ι)
    (k : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  spectatorRootChannel (siteExpectation q K k) B

/-- The root channel is linear under subtraction, for arbitrary spectator observables. -/
theorem spectatorRootChannel_sub (k : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannel k (B - C) = spectatorRootChannel k B - spectatorRootChannel k C := by
  simp only [spectatorRootChannel, rootChannel, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The local root channel is linear under subtraction. -/
theorem localRootChannel_sub (K : Finset ι) (k : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (B C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannel K k (B - C) = localRootChannel K k B - localRootChannel K k C :=
  spectatorRootChannel_sub _ B C

/-- The full root channel is contractive for every finite spectator system
(`03-quasilocal.tex`, lines 355–357). -/
theorem norm_spectatorRootChannel_le {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B‖ ≤ ‖B‖ :=
  norm_rootChannel_kronecker_le (CFC.sqrt_nonneg (1 - k)).isSelfAdjoint
    (CFC.sqrt_nonneg k).isSelfAdjoint (sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁) B

/-- The actual local root channel is contractive, uniformly in the spectator dimension
(`09-amplification.tex`, lines 101–107). -/
theorem norm_localRootChannel_le [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannel K k B‖ ≤ ‖B‖ :=
  norm_spectatorRootChannel_le (siteExpectation_nonneg K hk₀) (siteExpectation_le_one K hk₁) B

/-- The actual error `‖k - E_K(k)‖ ≤ ε` gives the completely bounded root-channel
estimate `4 sqrt ε`, expressed for every spectator system and every observable
(`03-quasilocal.tex`, `eq:quasilocal-channel-tail`, lines 365–368). -/
theorem norm_spectatorRootChannel_sub_localRootChannel_le [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {ε : ℝ}
    (hε : ‖k - siteExpectation q K k‖ ≤ ε)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖spectatorRootChannel k B - localRootChannel K k B‖ ≤ 4 * Real.sqrt ε * ‖B‖ := by
  have hl₀ := siteExpectation_nonneg K hk₀
  have hl₁ := siteExpectation_le_one K hk₁
  have hG : ‖CFC.sqrt (1 - k)‖ ≤ 1 :=
    norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one (sub_le_self _ hk₀))
  have hKr : ‖CFC.sqrt k‖ ≤ 1 :=
    norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one hk₁)
  have hGl : ‖CFC.sqrt (1 - siteExpectation q K k)‖ ≤ 1 :=
    norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one (sub_le_self _ hl₀))
  have hKl : ‖CFC.sqrt (siteExpectation q K k)‖ ≤ 1 :=
    norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one hl₁)
  have htG : ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - siteExpectation q K k)‖ ≤ Real.sqrt ε :=
    (norm_sqrt_one_sub_sub_le hk₁ hl₁).trans (Real.sqrt_le_sqrt hε)
  have htK : ‖CFC.sqrt k - CFC.sqrt (siteExpectation q K k)‖ ≤ Real.sqrt ε :=
    (norm_sqrt_sub_le hk₀ hl₀).trans (Real.sqrt_le_sqrt hε)
  refine (norm_rootChannel_kronecker_sub_le _ _ _ _ B).trans ?_
  have h₁ : (‖CFC.sqrt (1 - k)‖ + ‖CFC.sqrt (1 - siteExpectation q K k)‖) *
      ‖CFC.sqrt (1 - k) - CFC.sqrt (1 - siteExpectation q K k)‖ ≤ 2 * Real.sqrt ε :=
    mul_le_mul (by linarith) htG (norm_nonneg _) (by norm_num)
  have h₂ : (‖CFC.sqrt k‖ + ‖CFC.sqrt (siteExpectation q K k)‖) *
      ‖CFC.sqrt k - CFC.sqrt (siteExpectation q K k)‖ ≤ 2 * Real.sqrt ε :=
    mul_le_mul (by linarith) htK (norm_nonneg _) (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg B)

/-- The local channel fixes the commutant of all physical operators on `K`, also for
observables acting on spectators (`09-amplification.tex`, lines 107–110 and 120). -/
theorem localRootChannel_eq_self_of_forall_commute [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ}
    (hB : ∀ A ∈ supportedOperators q (K : Set ι),
      Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B) : localRootChannel K k B = B := by
  have hl₀ := siteExpectation_nonneg K hk₀
  have hl₁ := siteExpectation_le_one K hk₁
  have hlK := siteExpectation_mem_supportedOperators K k
  refine rootChannel_eq_self_of_commute
    (rootChannel_kronecker_hyp (sqrt_one_sub_mul_add_sqrt_mul hl₀ hl₁)) ?_ ?_
  · exact hB _ (sqrt_mem_supportedOperators K (sub_nonneg.mpr hl₁)
      ((supportedOperators q (K : Set ι)).sub_mem (one_mem_supportedOperators _) hlK))
  · exact hB _ (sqrt_mem_supportedOperators K hl₀ hlK)

/-- The local channel intertwines commutators with any operator in the physical
regional commutant, with spectators (`09-amplification.tex`, lines 122–127). -/
theorem localRootChannel_commutator_of_forall_commute [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {A : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ}
    (hA : ∀ C ∈ supportedOperators q (K : Set ι),
      Commute (C ⊗ₖ (1 : Matrix Aux Aux ℂ)) A)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    A * localRootChannel K k B - localRootChannel K k B * A =
      localRootChannel K k (A * B - B * A) := by
  have hl₀ := siteExpectation_nonneg K hk₀
  have hl₁ := siteExpectation_le_one K hk₁
  have hlK := siteExpectation_mem_supportedOperators K k
  have hG := hA _ (sqrt_mem_supportedOperators K (sub_nonneg.mpr hl₁)
    ((supportedOperators q (K : Set ι)).sub_mem (one_mem_supportedOperators _) hlK))
  have hKr := hA _ (sqrt_mem_supportedOperators K hl₀ hlK)
  have hleft (R : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
      (hR : Commute R A) : R * (A * B) * R = A * (R * B * R) := by
    rw [hR.left_comm, mul_assoc]
  have hright (R : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
      (hR : Commute R A) : R * (B * A) * R = R * B * R * A := by
    rw [← mul_assoc, hR.symm.right_comm]
  simp only [localRootChannel, spectatorRootChannel, rootChannel, mul_sub, sub_mul,
    hleft _ hG, hleft _ hKr, hright _ hG, hright _ hKr, mul_add, add_mul]
  abel

/-- An operator supported outside `K` has its commutator intertwined by the actual
local channel. In particular this applies to every on-site unitary outside `K`
(`09-amplification.tex`, lines 122–127). -/
theorem localRootChannel_commutator [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    {U : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hU : U ∈ supportedOperators q ((K : Set ι)ᶜ))
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    (U ⊗ₖ (1 : Matrix Aux Aux ℂ)) * localRootChannel K k B -
        localRootChannel K k B * (U ⊗ₖ 1) =
      localRootChannel K k ((U ⊗ₖ 1) * B - B * (U ⊗ₖ 1)) := by
  apply localRootChannel_commutator_of_forall_commute K hk₀ hk₁
  intro C hC
  change (C ⊗ₖ 1) * (U ⊗ₖ 1) = (U ⊗ₖ 1) * (C ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    (commute_of_mem_supportedOperators disjoint_compl_right hC hU).eq]

/-- The zeroth shell has norm at most two, including with spectators
(`09-amplification.tex`, lines 101–106, the case `l = 0`). -/
theorem norm_localRootChannel_sub_self_le [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannel K k B - B‖ ≤ 2 * ‖B‖ := by
  have h := norm_localRootChannel_le (q := q) K hk₀ hk₁ B
  calc
    ‖localRootChannel K k B - B‖ ≤ ‖localRootChannel K k B‖ + ‖B‖ := norm_sub_le _ _
    _ ≤ ‖B‖ + ‖B‖ := add_le_add h le_rfl
    _ = 2 * ‖B‖ := (two_mul _).symm

/-- Two local channels are close by their actual expectation errors from the same `k`.
The estimate holds without nesting the regions (`09-amplification.tex`, lines 101–106). -/
theorem norm_localRootChannel_sub_localRootChannel_le [NeZero q] (K L : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {εK εL : ℝ}
    (hK : ‖k - siteExpectation q K k‖ ≤ εK) (hL : ‖k - siteExpectation q L k‖ ≤ εL)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannel K k B - localRootChannel L k B‖ ≤
      4 * (Real.sqrt εK + Real.sqrt εL) * ‖B‖ := by
  calc
    ‖localRootChannel K k B - localRootChannel L k B‖ ≤
        ‖localRootChannel K k B - spectatorRootChannel k B‖ +
          ‖spectatorRootChannel k B - localRootChannel L k B‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖spectatorRootChannel k B - localRootChannel K k B‖ +
          ‖spectatorRootChannel k B - localRootChannel L k B‖ := by rw [norm_sub_rev]
    _ ≤ 4 * Real.sqrt εK * ‖B‖ + 4 * Real.sqrt εL * ‖B‖ :=
      add_le_add (norm_spectatorRootChannel_sub_localRootChannel_le K hk₀ hk₁ hK B)
        (norm_spectatorRootChannel_sub_localRootChannel_le L hk₀ hk₁ hL B)
    _ = 4 * (Real.sqrt εK + Real.sqrt εL) * ‖B‖ := by ring

/-- The actual shell `Δ₀ = ℰ₀ - id`, `Δₗ₊₁ = ℰₗ₊₁ - ℰₗ`, on arbitrary spectator
observables (`09-amplification.tex`, lines 101–102). -/
noncomputable def localRootChannelShell (regions : ℕ → Finset ι)
    (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) (l : ℕ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ :=
  match l with
  | 0 => localRootChannel (regions 0) k B - B
  | l + 1 => localRootChannel (regions (l + 1)) k B - localRootChannel (regions l) k B

/-- The actual channel shell is linear under subtraction. -/
theorem localRootChannelShell_sub (regions : ℕ → Finset ι)
    (k : Matrix (ι → Fin q) (ι → Fin q) ℂ) (l : ℕ)
    (B C : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell regions k l (B - C) =
      localRootChannelShell regions k l B - localRootChannelShell regions k l C := by
  cases l <;> simp only [localRootChannelShell, localRootChannel_sub] <;> abel

/-- The zeroth actual channel shell has completely bounded norm at most two
(`09-amplification.tex`, lines 101–106). -/
theorem norm_localRootChannelShell_zero_le [NeZero q] (regions : ℕ → Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k 0 B‖ ≤ 2 * ‖B‖ :=
  norm_localRootChannel_sub_self_le (regions 0) hk₀ hk₁ B

/-- A successor shell is bounded by the two actual localization errors, uniformly in
the spectator dimension (`09-amplification.tex`, `eq:amplification-channel-shells`). -/
theorem norm_localRootChannelShell_succ_le [NeZero q] (regions : ℕ → Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (l : ℕ) {εNext εPrev : ℝ}
    (hNext : ‖k - siteExpectation q (regions (l + 1)) k‖ ≤ εNext)
    (hPrev : ‖k - siteExpectation q (regions l) k‖ ≤ εPrev)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    ‖localRootChannelShell regions k (l + 1) B‖ ≤
      4 * (Real.sqrt εNext + Real.sqrt εPrev) * ‖B‖ :=
  norm_localRootChannel_sub_localRootChannel_le _ _ hk₀ hk₁ hNext hPrev B

/-- For nested regions the actual shell vanishes on the physical regional commutant,
with arbitrary spectators (`09-amplification.tex`, lines 107–110 and 120). -/
theorem localRootChannelShell_eq_zero_of_forall_commute [NeZero q]
    (regions : ℕ → Finset ι) (hregions : Monotone regions)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) (l : ℕ)
    {B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ}
    (hB : ∀ A ∈ supportedOperators q (regions l : Set ι),
      Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B) :
    localRootChannelShell regions k l B = 0 := by
  cases l with
  | zero =>
    exact sub_eq_zero.mpr (localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hB)
  | succ l =>
    have hPrev : ∀ A ∈ supportedOperators q (regions l : Set ι),
        Commute (A ⊗ₖ (1 : Matrix Aux Aux ℂ)) B := by
      intro A hA
      exact hB A (supportedOperators_mono (by exact hregions (Nat.le_succ l)) hA)
    simp only [localRootChannelShell,
      localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hB,
      localRootChannel_eq_self_of_forall_commute _ hk₀ hk₁ hPrev, sub_self]

end TNLean.PEPS.AreaLaw

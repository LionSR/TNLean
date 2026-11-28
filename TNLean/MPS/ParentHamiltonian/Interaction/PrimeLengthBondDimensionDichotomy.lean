/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTPresentation.PrimeLengthNormalBlocks
import TNLean.MPS.ParentHamiltonian.Interaction.FiniteVolumeConstraintPropagation
import TNLean.MPS.Tensor.GroundSpace.Nonvanishing
import TNLean.MPS.Operator.DensityOperator.PeriodicFiniteRepresentation
import TNLean.MPS.Tensor.VaryingBond.PeriodicBondPadding

/-!
# A quantitative prime-length bond-dimension dichotomy

For one fixed positive local interaction with a one-dimensional zero-energy
space at every permitted volume, one sufficiently small prime-length MPS
representation supplies a single fixed tensor generating the ground space
at every sufficiently large volume. Otherwise every nonzero prime-length
representation obeys the explicit fifth-degree obstruction.

All periodic/canonical reduction, phase grouping, block injectivity, local
annihilation, future-volume equations and eventual nonvanishing are derived.
**Scope restriction (eventual uniform branch):** the fixed tensor generates
all sufficiently large ground spaces. The finite-prefix representation step
for a literal all-volume uniform-dimension formulation is separate. See
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, lines 850–880 of
`Papers/0909.5347/main.tex`.

## The finite-prefix step for uniform periodic MPS bond bounds

An eventual fixed tensor gives one common bond bound for every exactly
cyclic-invariant ground vector, including all short positive volumes.
The short representations are constructed from actual OBC existence and
cyclic averaging, rather than assumed. Padding then gives one common
matrix size, while the tensors themselves may depend on the volume.

The exact condition for a nonzero ground vector to have a periodic trace
representation is that its cyclic momentum is zero. Uniqueness gives an
invariant ground line, which does not by itself state this condition.

**Scope restriction (zero-momentum finite prefix):** the uniform ground
family is proved precisely when every permitted short positive volume has
a nonzero zero-momentum ground vector. This condition is characterized,
not derived from the source's unique frustration-free ground-space
hypothesis. See
`docs/paper-gaps/spwc10_ground_state_dichotomy_quantifiers.tex`.

Source: SPWC10, arXiv:0909.5347, Theorem 5 and proof, lines 850--880.
-/

section

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}

/-- A small prime-length ground-state representation yields a single fixed
normal MPS tensor, its actual local-kernel inclusion, and its generation
of the ground space at all sufficiently large volumes. The explicit threshold
uses the general Wielandt length \((D^2+1)^2\).
Source: SPWC10, Theorem 5 proof, lines 858–880. -/
theorem exists_normal_eventual_ground_data_of_prime_length_bound
    (h : Matrix (Fin L → α) (Fin L → α) ℂ) (hh : h.PosSemidef)
    (hUnique : ∀ M [NeZero M], L ≤ M →
      Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian)) = 1)
    {D N : ℕ} (A : MPTensor α (Fin D)) (hPrime : N.Prime)
    (hBound : L + max ((D ^ 2 + 1) ^ 2)
      (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) ≤ N)
    (hA : mpvState A N ≠ 0)
    (hzero : haveI : NeZero N := ⟨hPrime.ne_zero⟩;
      Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N h).hamiltonian (mpvState A N) = 0) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ D₀ ≤ D ∧ ∃ B : MPTensor α (Fin D₀),
      Kraus.IsNormal B ∧ ((groundSpace B L).map (WithLp.linearEquiv 2 ℂ
          _).symm.toLinearMap) ≤ LinearMap.ker (Matrix.toEuclideanLin h) ∧ ∃ M₀ : ℕ,
      ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M := by
  classical
  have : NeZero N := ⟨hPrime.ne_zero⟩
  let q : ℕ := (D ^ 2 + 1) ^ 2
  change L + max q (3 * (D - 1) * (q + 1)) ≤ N at hBound
  have hq : 0 < q := by dsimp [q]; positivity
  have hDq : D < q := by
    have h₁ := Nat.le_self_pow (by decide : 2 ≠ 0) D
    have h₂ := Nat.le_self_pow (by decide : 2 ≠ 0) (D ^ 2 + 1)
    dsimp [q]
    omega
  have hDN : D < N := by
    have := le_max_left q (3 * (D - 1) * (q + 1))
    omega
  obtain ⟨r, dim, B, c, hdim, hdimD, hrD, hunital, hDual, hIrr,
      hC1, hDistinct, hc, hdecomp⟩ :=
    exists_normal_blocks_of_no_small_divisor A hPrime.two_le
      (fun m hm2 hmD hdiv =>
        (hPrime.eq_one_or_self_of_dvd m hdiv).elim (by omega) (by omega))
  have hsum : mpvState A N = ∑ j, c j • mpvState (B j) N := by
    apply PiLp.ext
    intro σ
    simpa only [mpvState_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul] using hdecomp σ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Fin.sum_univ_zero] at hsum
    exact (hA hsum).elim
  · have hSep : 3 * (r - 1) * (q + 1) ≤ 3 * (D - 1) * (q + 1) :=
      Nat.mul_le_mul_right (q + 1) (Nat.mul_le_mul_left 3 (Nat.sub_le_sub_right hrD 1))
    have hqNL : q ≤ N - L := by
      have := le_max_left q (3 * (D - 1) * (q + 1))
      omega
    have hSepNL : 3 * (r - 1) * (q + 1) ≤ N - L := by
      have := le_max_right q (3 * (D - 1) * (q + 1))
      omega
    have hSpan : WordTupleSpanTop B (N - L) :=
      wordTupleSpanTop_of_ge_of_isNBlkInjective (L₀ := q) B hdim hunital hDual hIrr hq
        hC1 hDistinct (max_le hqNL hSepNL)
    have hker := map_groundSpace_le_ker_of_toEuclideanLin_hamiltonian_translationInvariant_eq_zero
      B c hc h hh hPrime.pos (by omega) hSpan (by rwa [← hsum])
    let j : Fin r := ⟨0, hr⟩
    let : NeZero (dim j) := ⟨(hdim j).ne'⟩
    refine ⟨dim j, hdim j, hdimD j, B j, ⟨q, hq, hC1 j⟩, hker j,
      max L (q + 1), ?_⟩
    intro M _ hM
    have hLM : L ≤ M := (le_max_left _ _).trans hM
    have hqM : q + 1 ≤ M := (le_max_right _ _).trans hM
    have hnonzero : mpvState (B j) M ≠ 0 := by
      intro hMzero
      apply mpv_ne_zero_of_isNBlkInjective (hC1 j) hq hqM
      funext σ
      simpa only [mpvState_apply, PiLp.zero_apply, Pi.zero_apply] using
        congrArg (fun v : MPVSpace α M => v σ) hMzero
    have hGround :=
      toEuclideanLin_hamiltonian_translationInvariant_mpvState_eq_zero_of_map_groundSpace_le_ker
        (B j) h (hker j) hLM
    exact ⟨hnonzero, eq_span_singleton_of_mem_of_finrank_eq_one
      (hUnique M hLM) hGround hnonzero⟩

/-- A small prime-length ground-state representation yields a single fixed
MPS tensor generating the ground space at all sufficiently large volumes.
The explicit threshold uses the general Wielandt length \((D^2+1)^2\).
Source: SPWC10, Theorem 5 proof, lines 858–880. -/
theorem exists_eventually_fixed_mps_of_prime_length_bound
    (h : Matrix (Fin L → α) (Fin L → α) ℂ) (hh : h.PosSemidef)
    (hUnique : ∀ M [NeZero M], L ≤ M →
      Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian)) = 1)
    {D N : ℕ} (A : MPTensor α (Fin D)) (hPrime : N.Prime)
    (hBound : L + max ((D ^ 2 + 1) ^ 2)
      (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1)) ≤ N)
    (hA : mpvState A N ≠ 0)
    (hzero : haveI : NeZero N := ⟨hPrime.ne_zero⟩;
      Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant N h).hamiltonian (mpvState A N) = 0) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ D₀ ≤ D ∧ ∃ B : MPTensor α (Fin D₀), ∃ M₀ : ℕ,
      ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M := by
  obtain ⟨D₀, hD₀, hD, B, _, _, M₀, hB⟩ :=
    exists_normal_eventual_ground_data_of_prime_length_bound h hh hUnique A hPrime hBound hA hzero
  exact ⟨D₀, hD₀, hD, B, M₀, hB⟩

/-- Either one fixed tensor generates the eventual ground spaces, or every
prime-length nonzero MPS ground-state representation obeys the explicit
fifth-degree bound \(N<L+\max\{(D^2+1)^2,3(D-1)((D^2+1)^2+1)\}\).
The local interaction and all constants are fixed independently of the prime
and of the representing tensor. Source: SPWC10, Theorem 5, lines 850–880. -/
theorem eventually_fixed_mps_or_prime_length_bound
    (h : Matrix (Fin L → α) (Fin L → α) ℂ) (hh : h.PosSemidef)
    (hUnique : ∀ M [NeZero M], L ≤ M →
      Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian)) = 1) :
    (∃ (D₀ : ℕ) (B : MPTensor α (Fin D₀)) (M₀ : ℕ),
      ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M) ∨
    (∀ (N : ℕ) (hPrime : N.Prime) (D : ℕ) (A : MPTensor α (Fin D)),
      mpvState A N ≠ 0 →
      (haveI : NeZero N := ⟨hPrime.ne_zero⟩;
        Matrix.toEuclideanLin (ManyBody.Interaction.translationInvariant N h).hamiltonian
          (mpvState A N) = 0) →
        N < L + max ((D ^ 2 + 1) ^ 2)
          (3 * (D - 1) * ((D ^ 2 + 1) ^ 2 + 1))) := by
  classical
  by_cases hFixed : ∃ (D₀ : ℕ) (B : MPTensor α (Fin D₀)) (M₀ : ℕ),
      ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
        LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M
  · exact Or.inl hFixed
  · right
    intro N hPrime D A hA hzero
    by_contra hBound
    obtain ⟨D₀, _, _, B, M₀, hB⟩ :=
      exists_eventually_fixed_mps_of_prime_length_bound h hh hUnique A hPrime
        (Nat.le_of_not_gt hBound) hA hzero
    exact hFixed ⟨D₀, B, M₀, hB⟩

end MPSTensor

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ}

/-- An actual eventual fixed ground tensor supplies a uniform common
bond dimension for all exactly cyclic-invariant nonzero ground vectors
at all permitted positive volumes. Short representations are constructed,
with no supplied finite-volume MPS premise.
Source: the finite-prefix completion of SPWC10, Theorem 5, lines 850--880. -/
theorem exists_uniform_bond_on_cyclic_ground_sector
    (h : Matrix (Fin L → α) (Fin L → α) ℂ)
    (hUnique : ∀ M [NeZero M], L ≤ M →
      Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian)) = 1)
    {D : ℕ} (B : MPTensor α (Fin D)) (M₀ : ℕ)
    (hB : ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M) :
    ∃ K : ℕ, 0 < K ∧
      ∀ M (hM : 0 < M), L ≤ M → haveI : NeZero M := ⟨by omega⟩; ∀ ψ : MPVSpace α M,
        ψ ≠ 0 → Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian ψ = 0 →
        (∀ (s : Fin M) (σ : Fin M → α), ψ (fun k ↦ σ (k + s)) = ψ σ) →
        ∃ C : MPTensor α (Fin K), mpvState C M ≠ 0 ∧
          LinearMap.ker (Matrix.toEuclideanLin
            (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState C M := by
  classical
  let K := D + M₀ * Fintype.card α ^ M₀ + 1
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro M hM hLM ψ hψ hzero hTI
  have : NeZero M := ⟨by omega⟩
  by_cases hlong : M₀ ≤ M
  · let C := padBond B K
    have hDK : D ≤ K := by dsimp [K]; omega
    have hC : mpvState C M = mpvState B M := mpvState_padBond B hDK hM
    exact ⟨C, by rw [hC]; exact (hB M hlong).1, by rw [hC]; exact (hB M hlong).2⟩
  · have hd : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      subst d
      apply hψ
      apply PiLp.ext
      intro σ
      exact Fin.elim0 (σ ⟨0, hM⟩)
    obtain ⟨C, hC⟩ := exists_mpvState_eq_of_cyclic_invariant hM ψ hψ hTI
    have hCK : M * Fintype.card α ^ (M / 2) ≤ K := by
      have hpow : Fintype.card α ^ (M / 2) ≤ Fintype.card α ^ M₀ := Nat.pow_le_pow_right hd (by omega)
      have hmul := Nat.mul_le_mul (show M ≤ M₀ by omega) hpow
      dsimp [K]
      omega
    let C' := padBond C K
    have hC' : mpvState C' M = ψ := (mpvState_padBond C hCK hM).trans hC
    refine ⟨C', by rwa [hC'], ?_⟩
    rw [hC']
    exact eq_span_singleton_of_mem_of_finrank_eq_one (hUnique M hLM) hzero hψ

/-- The literal all-positive-volume common-bond family is equivalent to
zero cyclic momentum at the finitely many permitted volumes preceding
the eventual fixed tensor. This makes the remaining source quantifier
explicit without assuming short periodic representations.
Source: SPWC10, Theorem 5, lines 850--880, finite-prefix boundary. -/
theorem uniform_bond_family_iff_short_cyclic_ground
    (h : Matrix (Fin L → α) (Fin L → α) ℂ)
    (hUnique : ∀ M [NeZero M], L ≤ M →
      Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian)) = 1)
    {D : ℕ} (B : MPTensor α (Fin D)) (M₀ : ℕ)
    (hB : ∀ M [NeZero M], M₀ ≤ M → mpvState B M ≠ 0 ∧
      LinearMap.ker (Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState B M) :
    (∃ K : ℕ, 0 < K ∧ ∀ M (hM : 0 < M), L ≤ M → haveI : NeZero M := ⟨by omega⟩;
      ∃ C : MPTensor α (Fin K), mpvState C M ≠ 0 ∧
        LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian) = ℂ ∙ mpvState C M) ↔
    (∀ M (hM : 0 < M), L ≤ M → haveI : NeZero M := ⟨by omega⟩; M < M₀ →
      ∃ ψ : MPVSpace α M, ψ ≠ 0 ∧ Matrix.toEuclideanLin
        (ManyBody.Interaction.translationInvariant M h).hamiltonian ψ = 0 ∧
        ∀ (s : Fin M) (σ : Fin M → α), ψ (fun k ↦ σ (k + s)) = ψ σ) := by
  classical
  constructor
  · rintro ⟨K, _, hK⟩ M hM hLM _
    have : NeZero M := ⟨by omega⟩
    obtain ⟨C, hC, hker⟩ := hK M hM hLM
    refine ⟨mpvState C M, hC, ?_, mpvState_cyclic_invariant C⟩
    change mpvState C M ∈ LinearMap.ker (Matrix.toEuclideanLin
      (ManyBody.Interaction.translationInvariant M h).hamiltonian)
    rw [hker]
    exact Submodule.mem_span_singleton_self _
  · intro hshort
    obtain ⟨K, hK, hsector⟩ := exists_uniform_bond_on_cyclic_ground_sector h hUnique B M₀ hB
    refine ⟨K, hK, ?_⟩
    intro M hM hLM
    have : NeZero M := ⟨by omega⟩
    by_cases hlong : M₀ ≤ M
    · have hzero : Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian (mpvState B M) = 0 := by
        change mpvState B M ∈ LinearMap.ker (Matrix.toEuclideanLin
          (ManyBody.Interaction.translationInvariant M h).hamiltonian)
        rw [(hB M hlong).2]
        exact Submodule.mem_span_singleton_self _
      exact hsector M hM hLM (mpvState B M) (hB M hlong).1 hzero
        (mpvState_cyclic_invariant B)
    · obtain ⟨ψ, hψ, hzero, hTI⟩ := hshort M hM hLM (Nat.lt_of_not_ge hlong)
      exact hsector M hM hLM ψ hψ hzero hTI

end MPSTensor

end

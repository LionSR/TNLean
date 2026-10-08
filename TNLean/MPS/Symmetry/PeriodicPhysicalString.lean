/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinKronecker
import TNLean.MPS.Preparation.WindowCorrelator
import TNLean.MPS.Symmetry.PhysicalStringAsymptotics

/-!
# Fixed-support thermodynamic limits of periodic MPS expectations

For a fixed physical block observable, the normalized expectation on a periodic
ring tends to its stationary transfer expression as the complementary part of
the ring grows. The normalization tends to one, so the periodic vector is
nonzero for all sufficiently long rings.

Source: arXiv:0802.0447, the thermodynamic-limit paragraph after `MPS`, lines
137–162, and `SOPMP`, lines 176–181. A string length must be fixed before this
ambient-ring limit is taken. The full-ring quantity `RL`, lines 381–387, has
growing support and is a separate problem.

## References

* Pérez-García, Wolf, Sanz, Verstraete, Cirac, arXiv:0802.0447,
  the thermodynamic-limit paragraph after `MPS` and display `SOPMP`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace InnerProductSpace
open Filter

namespace MPSTensor

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A single canonical transfer rate controls the periodic closure of every
fixed insertion. The prefactor may depend on the insertion. No bound is
assumed: the rate follows from the faithful canonical spectral gap.
Source: arXiv:0802.0447, `MPS`, `SOPMP`, and lines 241–255. -/
theorem canonical_trace_mul_transfer_pow_le_geometric
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ F : Module.End ℂ Mat,
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
        ‖LinearMap.trace ℂ Mat (F * Kraus.transferMap A ^ N) -
          Matrix.trace (Λ * F 1)‖ ≤ C * r ^ N := by
  let : TopologicalSpace Mat :=
    (inferInstance : NormedAddCommGroup Mat).toUniformSpace.toTopologicalSpace
  obtain ⟨C, r, hC, hr, hr1, hpow⟩ :=
    canonical_transfer_pow_sub_stationary_le_geometric
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  refine ⟨r, hr, hr1, fun F => ?_⟩
  let ℓ : (Mat →L[ℂ] Mat) →L[ℂ] ℂ :=
    ((LinearMap.trace ℂ Mat).comp
      ((LinearMap.mulLeft ℂ F).comp (ContinuousLinearMap.coeLM ℂ))).toContinuousLinearMap
  obtain ⟨M, hM, hℓ⟩ := ℓ.bound
  let P := fnwLimitMap Λ (by simp [hΛtr])
  have htrace : LinearMap.trace ℂ Mat (F * P) = Matrix.trace (Λ * F 1) := by
    let φ : Mat →ₗ[ℂ] ℂ := (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
      (LinearMap.mulLeft ℂ Λ)
    have hFP : F * P = φ.smulRight (F 1) := by
      apply LinearMap.ext
      intro X
      simp only [Module.End.mul_apply, P, fnwLimitMap_apply_of_trace_eq_one Λ X hΛtr,
        map_smul, φ, LinearMap.smulRight_apply, LinearMap.comp_apply,
        Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply]
    rw [hFP, LinearMap.trace_smulRight]
    rfl
  refine ⟨M * C, mul_pos hM hC, fun N hN => ?_⟩
  have hid : LinearMap.trace ℂ Mat (F * Kraus.transferMap A ^ N) -
      Matrix.trace (Λ * F 1) =
        ℓ (Module.End.toContinuousLinearMap Mat (Kraus.transferMap A ^ N - P)) := by
    change _ = LinearMap.trace ℂ Mat (F * (Kraus.transferMap A ^ N - P))
    rw [mul_sub, map_sub, htrace]
  rw [hid]
  exact (hℓ _).trans (by
    simpa only [P, mul_assoc] using mul_le_mul_of_nonneg_left (hpow N hN) hM.le)

/-- The operator trace of a fixed insertion followed by a long canonical
transfer segment converges to its stationary boundary value. Source:
arXiv:0802.0447, `SOPMP`, lines 176–181. -/
private theorem canonical_trace_mul_transfer_pow_tendsto
    [NeZero D] (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (Kraus.transferMap A))
    (hPrim : IsPrimitive (Kraus.transferMap A))
    (Λ : Mat) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
    (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
    (hNorm : Kraus.transferMap A 1 = 1) (F : Module.End ℂ Mat) :
    Tendsto (fun n => LinearMap.trace ℂ Mat (F * Kraus.transferMap A ^ n)) atTop
      (nhds (Matrix.trace (Λ * F 1))) := by
  obtain ⟨r, hr, hr1, hbound⟩ := canonical_trace_mul_transfer_pow_le_geometric
    A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm
  obtain ⟨C, hC, hCF⟩ := hbound F
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)))
  filter_upwards [eventually_ge_atTop 1] with n hn using hCF n hn

/-- The one-site physical insertion is the source twisted transfer map, with
matrix coefficient `u n' n`. Source: arXiv:0802.0447, `EU`, lines 168–173. -/
theorem physicalObservableTransfer_singleton (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    physicalObservableTransfer A 1
      (Matrix.of fun τ σ : Fin 1 → Fin d => u (τ 0) (σ 0)) = twistedTransferMap A u := by
  classical
  apply LinearMap.ext
  intro X
  rw [physicalObservableTransfer_apply, twistedTransferMap_apply]
  rw [← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  change u j i • (Kraus.evalWord A (List.ofFn fun _ : Fin 1 => i) * X *
    (Kraus.evalWord A (List.ofFn fun _ : Fin 1 => j))ᴴ) =
      u j i • (A i * X * (A j)ᴴ)
  simp [Kraus.evalWord_cons, Kraus.evalWord_nil]

/-- The physical tensor power of the on-site twist inserts exactly the
corresponding transfer power. Source: arXiv:0802.0447, `EU` and `SOPMP`,
lines 168–181. This identity is finite and includes zero middle length. -/
theorem physicalObservableTransfer_finKronecker_const (A : MPSTensor d D)
    (u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    physicalObservableTransfer A N (Matrix.finKronecker fun _ : Fin N => u) =
      twistedTransferIter A u N := by
  classical
  induction N with
  | zero =>
      apply LinearMap.ext
      intro X
      simp [physicalObservableTransfer_apply, Matrix.finKronecker_apply,
        twistedTransferIter]
  | succ N ih =>
      have htensor : Matrix.finKronecker (fun _ : Fin (N + 1) => u) =
          appendObservable (Matrix.finKronecker fun _ : Fin N => u)
            (Matrix.of fun τ σ : Fin 1 → Fin d => u (τ 0) (σ 0)) := by
        ext τ σ
        simp only [Matrix.finKronecker_apply, Fin.prod_univ_castSucc]
        rfl
      rw [htensor, physicalObservableTransfer_appendObservable,
        physicalObservableTransfer_singleton, ih]
      simp only [twistedTransferIter, pow_succ]

section PureCanonical

variable [NeZero D] (A : MPSTensor d D)
  (Λ : Matrix (Fin D) (Fin D) ℂ) (hΛpos : Λ.PosDef) (hΛtr : Matrix.trace Λ = 1)
  (hΛfix : Kraus.transferMap (fun i => (A i)ᴴ) Λ = Λ)
  (hNorm : Kraus.transferMap A 1 = 1)
  (hPure : ∀ (ev : ℂ) (X : Matrix (Fin D) (Fin D) ℂ),
    X ≠ 0 → ‖ev‖ = 1 → Kraus.transferMap A X = ev • X →
    ev = 1 ∧ ∃ c : ℂ, X = c • 1)

include Λ hΛpos hΛtr hΛfix hNorm hPure

/-- The squared norm of the periodic vector tends to one in the faithful
canonical pure regime. This establishes the normalization used before the
thermodynamic limit of arXiv:0802.0447, lines 137–162. The peripheral hypothesis
includes a one-dimensional fixed space, not merely uniqueness as an eigenvalue
set. No nonvanishing assumption at short ring lengths is imposed. -/
theorem pureCanonical_mpvState_inner_self_tendsto_one :
    Tendsto (fun L : ℕ => ⟪mpvState A L, mpvState A L⟫_ℂ) atTop
      (nhds (1 : ℂ)) := by
  obtain ⟨hIrr, hPrim⟩ := pureCanonical_isIrreducibleMap_and_isPrimitive
    A Λ hΛpos hΛfix hNorm hPure
  have hlim : Tendsto
      (fun L : ℕ => LinearMap.trace ℂ Mat (Kraus.transferMap A ^ L))
      atTop (nhds (1 : ℂ)) := by
    simpa only [one_mul, Module.End.one_apply, Matrix.mul_one, hΛtr] using
      canonical_trace_mul_transfer_pow_tendsto
        A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm (1 : Module.End ℂ Mat)
  convert hlim using 1
  funext L
  exact inner_mpvState_self_eq_trace A L

/-- Periodic vectors of a faithful pure canonical tensor are nonzero on an
eventual tail. This derives the nonzero normalization in the thermodynamic
interpretation of arXiv:0802.0447, `MPS`; it does not assert nonvanishing at
every finite length. -/
theorem pureCanonical_eventually_mpvState_ne_zero :
    ∀ᶠ L : ℕ in atTop, mpvState A L ≠ 0 := by
  have hlim := pureCanonical_mpvState_inner_self_tendsto_one
    A Λ hΛpos hΛtr hΛfix hNorm hPure
  filter_upwards [hlim.eventually_ne one_ne_zero] with L hL
  intro hzero
  apply hL
  simp only [hzero, inner_zero_left]

/-- For each fixed physical block observable `O`, its actual normalized
periodic expectation converges as the identity exterior grows to the stationary
transfer expression. Source: arXiv:0802.0447, lines 137–162 and `SOPMP`, lines
176–181. The block and its operator are fixed before the ambient-ring limit.
This theorem provides neither a simultaneous string-length limit nor a uniform
rate, and is not a statement about the growing-support full-ring quantity `RL`.
-/
theorem pureCanonical_mpvExpectation_appendObservable_tendsto
    (k : ℕ) (O : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) :
    Tendsto
      (fun n : ℕ => mpvExpectation A (k + n)
        (appendObservable O
          (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)))
      atTop (nhds (Matrix.trace (Λ * physicalObservableTransfer A k O 1))) := by
  obtain ⟨hIrr, hPrim⟩ := pureCanonical_isIrreducibleMap_and_isPrimitive
    A Λ hΛpos hΛfix hNorm hPure
  have hnum : Tendsto
      (fun n : ℕ => ⟪mpvState A (k + n),
        Matrix.toEuclideanLin (appendObservable O
          (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ))
          (mpvState A (k + n))⟫_ℂ)
      atTop (nhds (Matrix.trace (Λ * physicalObservableTransfer A k O 1))) := by
    simp_rw [inner_mpvState_toEuclideanLin,
      physicalObservableTransfer_appendObservable, physicalObservableTransfer_one]
    exact canonical_trace_mul_transfer_pow_tendsto
      A hIrr hPrim Λ hΛpos hΛtr hΛfix hNorm (physicalObservableTransfer A k O)
  have hshift : Tendsto (fun n : ℕ => k + n) atTop atTop := by
    refine tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b, ?_⟩
    intro n hn
    omega
  have hden : Tendsto
      (fun n : ℕ => ⟪mpvState A (k + n), mpvState A (k + n)⟫_ℂ)
      atTop (nhds (1 : ℂ)) :=
    (pureCanonical_mpvState_inner_self_tendsto_one
      A Λ hΛpos hΛtr hΛfix hNorm hPure).comp hshift
  have hlim := hnum.div hden (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [div_one] at hlim
  apply hlim.congr'
  filter_upwards [] with n
  exact (mpvExpectation_eq_div A (k + n) (appendObservable O 1)).symm

/-- For fixed endpoint blocks and fixed middle length, the actual normalized
periodic string expectation tends to its stationary transfer expression as the
identity exterior grows. Source: arXiv:0802.0447, `SOPMP`, lines 176–181, and
the finite endpoint extensions at lines 278–291. No string-length limit is
exchanged with the ambient-ring limit. -/
theorem pureCanonical_mpvExpectation_block_string_tendsto
    (p q N : ℕ)
    (x : Matrix (Fin p → Fin d) (Fin p → Fin d) ℂ)
    (y : Matrix (Fin q → Fin d) (Fin q → Fin d) ℂ)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    Tendsto
      (fun n : ℕ => mpvExpectation A (p + N + q + n)
        (appendObservable
          (appendObservable
            (appendObservable x (Matrix.finKronecker fun _ : Fin N => u)) y)
          (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)))
      atTop (nhds (Matrix.trace (Λ * physicalObservableTransfer A p x
        (twistedTransferIter A u N (physicalObservableTransfer A q y 1))))) := by
  have h := pureCanonical_mpvExpectation_appendObservable_tendsto
    A Λ hΛpos hΛtr hΛfix hNorm hPure (p + N + q)
    (appendObservable
      (appendObservable x (Matrix.finKronecker fun _ : Fin N => u)) y)
  simpa only [physicalObservableTransfer_appendObservable,
    physicalObservableTransfer_finKronecker_const, Module.End.mul_apply] using h

/-- The one-site physical string parameter is the thermodynamic limit of the
literal normalized finite periodic expectations, at each fixed middle length.
This justifies the source's `SOPMP`, arXiv:0802.0447, lines 176–181, before a
subsequent `N → ∞` limit is considered. -/
theorem pureCanonical_mpvExpectation_string_tendsto
    (x y u : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Tendsto
      (fun n : ℕ => mpvExpectation A (1 + N + 1 + n)
        (appendObservable
          (appendObservable
            (appendObservable (Matrix.of fun τ σ : Fin 1 → Fin d => x (τ 0) (σ 0))
              (Matrix.finKronecker fun _ : Fin N => u))
            (Matrix.of fun τ σ : Fin 1 → Fin d => y (τ 0) (σ 0)))
          (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)))
      atTop (nhds (physicalStringOrderParam A Λ x y u N)) := by
  have h := pureCanonical_mpvExpectation_block_string_tendsto
    A Λ hΛpos hΛtr hΛfix hNorm hPure 1 1 N
    (Matrix.of fun τ σ : Fin 1 → Fin d => x (τ 0) (σ 0))
    (Matrix.of fun τ σ : Fin 1 → Fin d => y (τ 0) (σ 0)) u
  simpa only [physicalObservableTransfer_singleton, physicalStringOrderParam] using h

end PureCanonical
end MPSTensor

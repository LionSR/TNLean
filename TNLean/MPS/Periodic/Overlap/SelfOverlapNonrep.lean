/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.CanonicalForm.CyclicSectors.FixedAdjoint
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.MPS.Periodic.SectorIrreducibility.ProjectionOrtho
import TNLean.Channel.Peripheral.PeriodicityRemoval
import TNLean.QPF.Assembly

/-!
# Periodic overlap: the spectral non-repetition crux

This module isolates the off-diagonal vanishing lemma used by the periodic
overlap dichotomy.  For a periodic block, an off-diagonal modulus-one
eigenvector of the blocked transfer map must vanish; this is the faithful
port of the contradiction at arXiv:1708.00029, Appendix A, lines 404--423.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Spectral non-repetition (off-diagonal part of Lemma bdcf).**

For a periodic block `A` of period `m`, an off-diagonal modulus-one eigenvector of
the period transfer map $\mathcal E_A^m$ must vanish: if
`U = P u * U * P v` with `u ≠ v` and `P u * P v = 0`, and
$\mathcal E_A^m(U)=\zeta U$ with `‖ζ‖ = 1`, then `U = 0`.

This is the faithful port of the contradiction at arXiv:1708.00029 lines 404--423.
The paper concludes from "`𝓔_A^m` has `1` as its only modulus-one eigenvalue, with
fixed points the diagonal corners `{P_w Λ_A P_w}`"; the proof below realizes the
same conclusion without the eigenspace-structure theorem:

* The peripheral spectrum of $\mathcal E_A$ consists of the $m$-th roots of
  unity, so the peripheral-eigenvalue singleton theorem gives `ζ = 1`: `U` is
  a genuine fixed point of $\mathcal E_A^m$.
* `tr U = tr (P u * U * P v) = tr (P v * P u * U) = 0` since `P u * P v = 0`.
* $W := \sum_{t=0}^{m-1}\mathcal E_A^t(U)$ is an $\mathcal E_A$-fixed point
  (reindex using
  $\mathcal E_A^m(U)=U$) of trace zero ($\mathcal E_A$ is trace preserving), so
  `W = 0` by the trace-zero fixed-point vanishing lemma for irreducible transfer
  maps.
* The single-site shift `P (k+1) * A i = A i * P k` is the inverse-indexed form
  of arXiv:1708.00029, eq:Aoffdiag; it makes
  $\mathcal E_A^t(U)$ supported on the `(u + t, v + t)` block, whence
  $P_u\mathcal E_A^t(U)P_v=0$ for $0<t<m$ and $P_uUP_v=U$ at $t=0$; therefore
  $U=P_uWP_v=0$. -/
lemma offDiag_eigenvector_eq_zero_of_isPeriodic
    [NeZero D] (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, transferMap (d := d) (D := D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    {u v : Fin m} (hOrth : P u * P v = 0)
    {U : MatrixAlg D} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hSupp : U = P u * U * P v)
    (hEig : ((transferMap (d := d) (D := D) A) ^ m) U = ζ • U) :
    U = 0 := by
  classical
  set E := transferMap (d := d) (D := D) A with hE_def
  -- The original transfer map is irreducible and trace preserving.
  have hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1 := hP.leftCanonical
  -- Trace preservation: `tr (E X) = tr X` for every `X`.
  have hTrace_pres : ∀ X : MatrixAlg D, Matrix.trace (E X) = Matrix.trace X := by
    intro X
    have hsum : Matrix.trace (E X) =
        Matrix.trace ((∑ i : Fin d, (A i)ᴴ * A i) * X) := by
      simp only [hE_def, transferMap_apply, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.trace_mul_cycle (A i) X (A i)ᴴ, Matrix.mul_assoc]
    rw [hsum, hNorm, Matrix.one_mul]
  -- Step 1: `ζ = 1`.  `ζ` is a modulus-one eigenvalue of `E ^ m`, whose peripheral
  -- spectrum is the singleton `{1}` (the period-`m` peripheral spectrum of `E`
  -- raised to the `m`-th power).
  have hperiph_pow : ∀ μ : ℂ, μ ∈ peripheralEigenvalues E → μ ^ m = 1 := by
    intro μ hμ
    have hμroot : μ ∈ {z : ℂ | z ^ m = 1} := by rw [← hP.peripheral_eq]; exact hμ
    simpa using hμroot
  obtain ⟨ρ, _hρ_psd, hρ_ne, hρ_fix⟩ :=
    exists_posSemidef_fixedPoint A hP.leftCanonical (NeZero.pos D)
  have hsingleton : peripheralEigenvalues (E ^ m) = {1} :=
    peripheralEigenvalues_pow_eq_singleton (E := E) (p := m) (NeZero.pos m)
      hperiph_pow ρ hρ_fix hρ_ne
  by_cases hU_ne : U = 0
  · exact hU_ne
  replace hU_ne : U ≠ 0 := hU_ne
  -- `ζ ∈ peripheralEigenvalues (E ^ m) = {1}`, hence `ζ = 1`.
  have hζ_eig : Module.End.HasEigenvalue (E ^ m) ζ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hEig, hU_ne⟩)
  have hζ_mem : ζ ∈ peripheralEigenvalues (E ^ m) := ⟨hζ_eig, hζ⟩
  have hζ_one : ζ = 1 := by rw [hsingleton] at hζ_mem; simpa using hζ_mem
  -- So `U` is a genuine fixed point of `E ^ m`.
  have hFix : (E ^ m) U = U := by rw [hEig, hζ_one, one_smul]
  -- Step 3a: `tr U = 0`.
  have hOrth' : P v * P u = 0 := by
    have := congrArg Matrix.conjTranspose hOrth
    simpa [Matrix.conjTranspose_mul, (hPproj u).1.eq, (hPproj v).1.eq] using this
  have htrU : Matrix.trace U = 0 := by
    have heq : Matrix.trace U = Matrix.trace (P v * P u * U) := by
      conv_lhs => rw [hSupp]
      rw [Matrix.trace_mul_cycle (P u) U (P v)]
    rw [heq, hOrth', Matrix.zero_mul, Matrix.trace_zero]
  -- The single-site off-diagonal shift `P (k+1) * A i = A i * P k`.
  have hShiftLetter : ∀ (k : Fin m) (i : Fin d), P (k + 1) * A i = A i * P k :=
    offDiag_shift_of_adjoint_cyclic_shift A hP.leftCanonical hPproj hCyclic
  -- `E` carries the `(a, b)` block to the `(a + 1, b + 1)` block.
  have hE_block : ∀ (a b : Fin m) (X : MatrixAlg D),
      E (P a * X * P b) = P (a + 1) * E (P a * X * P b) * P (b + 1) := by
    intro a b X
    have hAP : ∀ i : Fin d, A i * P a = P (a + 1) * A i := fun i =>
      (hShiftLetter a i).symm
    have hPB : ∀ i : Fin d, P b * (A i)ᴴ = (A i)ᴴ * P (b + 1) := by
      intro i
      have hc := congrArg Matrix.conjTranspose (hShiftLetter b i)
      simp only [Matrix.conjTranspose_mul, (hPproj b).1.eq, (hPproj (b + 1)).1.eq] at hc
      exact hc.symm
    -- Each matrix summand already carries the projectors: `A i (P a X P b) A iᴴ` is
    -- supported on the `(a + 1, b + 1)` block.
    have hterm : ∀ i : Fin d,
        A i * (P a * X * P b) * (A i)ᴴ =
          P (a + 1) * (A i * (P a * X * P b) * (A i)ᴴ) * P (b + 1) := by
      intro i
      -- `Y` is left-supported on `P (a+1)` and right-supported on `P (b+1)`.
      have hY_eq : A i * (P a * X * P b) * (A i)ᴴ =
          P (a + 1) * A i * X * ((A i)ᴴ * P (b + 1)) := by
        have h1 : A i * (P a * X * P b) * (A i)ᴴ
            = (A i * P a) * X * (P b * (A i)ᴴ) := by simp only [Matrix.mul_assoc]
        rw [h1, hAP i, hPB i, Matrix.mul_assoc]
      have hPa1 : P (a + 1) * P (a + 1) = P (a + 1) := (hPproj (a + 1)).2
      have hPb1 : P (b + 1) * P (b + 1) = P (b + 1) := (hPproj (b + 1)).2
      rw [hY_eq]
      -- Reassociate and absorb the idempotent projections on both ends.
      simp only [← Matrix.mul_assoc]
      rw [hPa1]
      simp only [Matrix.mul_assoc]
      rw [hPb1]
    calc
      E (P a * X * P b)
          = ∑ i : Fin d, A i * (P a * X * P b) * (A i)ᴴ := by
            rw [hE_def, transferMap_apply]
      _ = ∑ i : Fin d, P (a + 1) * (A i * (P a * X * P b) * (A i)ᴴ) * P (b + 1) := by
            exact Finset.sum_congr rfl fun i _ => hterm i
      _ = P (a + 1) * (∑ i : Fin d, A i * (P a * X * P b) * (A i)ᴴ) * P (b + 1) := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = P (a + 1) * E (P a * X * P b) * P (b + 1) := by
            rw [hE_def, transferMap_apply]
  -- By induction, `E^t U` is supported on the `(u + t • 1, v + t • 1)` block.
  have hEt_supp : ∀ t : ℕ,
      (E ^ t) U = P (u + t • (1 : Fin m)) * ((E ^ t) U) * P (v + t • (1 : Fin m)) := by
    intro t
    induction t with
    | zero => simpa using hSupp
    | succ t ih =>
        have hstep : (E ^ (t + 1)) U = E ((E ^ t) U) := by
          rw [pow_succ', Module.End.mul_apply]
        have hidx_u : u + (t + 1) • (1 : Fin m) = (u + t • (1 : Fin m)) + 1 := by
          rw [succ_nsmul, ← add_assoc]
        have hidx_v : v + (t + 1) • (1 : Fin m) = (v + t • (1 : Fin m)) + 1 := by
          rw [succ_nsmul, ← add_assoc]
        calc
          (E ^ (t + 1)) U = E ((E ^ t) U) := hstep
          _ = E (P (u + t • (1 : Fin m)) * ((E ^ t) U) * P (v + t • (1 : Fin m))) := by
                rw [← ih]
          _ = P (u + t • (1 : Fin m) + 1) *
                E (P (u + t • (1 : Fin m)) * ((E ^ t) U) * P (v + t • (1 : Fin m))) *
                P (v + t • (1 : Fin m) + 1) :=
              hE_block (u + t • (1 : Fin m)) (v + t • (1 : Fin m)) ((E ^ t) U)
          _ = P (u + (t + 1) • (1 : Fin m)) * ((E ^ (t + 1)) U) *
                P (v + (t + 1) • (1 : Fin m)) := by
                rw [← ih, ← hstep, hidx_u, hidx_v]
  -- `tr (E^t U) = tr U = 0` for all `t`.
  have htrEt : ∀ t : ℕ, Matrix.trace ((E ^ t) U) = 0 := by
    intro t
    induction t with
    | zero => simpa using htrU
    | succ t ih =>
        rw [pow_succ', Module.End.mul_apply, hTrace_pres, ih]
  -- `W := ∑_{t < m} E^t U` is an `E`-fixed point of trace zero, hence zero.
  set W : MatrixAlg D := ∑ t : Fin m, (E ^ (t : ℕ)) U with hW_def
  have hW_fix : E W = W := by
    have hEW : E W = ∑ t : Fin m, (E ^ ((t : ℕ) + 1)) U := by
      rw [hW_def, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    rw [hEW]
    -- Reindex `t ↦ t + 1` over `Fin m`, using `E ^ m U = U` for the wrap-around.
    have hcycle : (E ^ m) U = U := hFix
    rw [hW_def]
    -- `∑_{t} E^{t+1} U = ∑_{t} E^t U` since the orbit has period `m`.
    have key : ∀ N : ℕ, ∑ t ∈ Finset.range N, (E ^ (t + 1)) U =
        (∑ t ∈ Finset.range N, (E ^ t) U) - U + (E ^ N) U := by
      intro N
      induction N with
      | zero => simp
      | succ N ihN =>
          rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => (E ^ t) U), ihN]
          ring_nf
          abel
    have hsum_eq : ∑ t : Fin m, (E ^ ((t : ℕ) + 1)) U = ∑ t : Fin m, (E ^ (t : ℕ)) U := by
      rw [Fin.sum_univ_eq_sum_range (fun t => (E ^ (t + 1)) U) m,
        Fin.sum_univ_eq_sum_range (fun t => (E ^ t) U) m, key m, hcycle]
      abel
    exact hsum_eq
  have hW_tr : Matrix.trace W = 0 := by
    rw [hW_def, Matrix.trace_sum]
    exact Finset.sum_eq_zero fun t _ => htrEt (t : ℕ)
  have hW_zero : W = 0 :=
    transferMap_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible A hP.irreducible
      hNorm W hW_fix hW_tr
  -- Step 3d: `U = P u * W * P v`, because only the `t = 0` term survives the
  -- compression to the `(u, v)` block.
  have hPairwise : Pairwise fun i j : Fin m => P i * P j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one P hPproj hPsum
  -- `(n • (1 : Fin m)).val = n % m`, hence `(t : ℕ) • (1 : Fin m) = t`.
  have hnsmul_val : ∀ n : ℕ, ((n • (1 : Fin m)) : Fin m).val = n % m := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [succ_nsmul, Fin.val_add, ih]; simp
  have hnsmul : ∀ t : Fin m, (t : ℕ) • (1 : Fin m) = t := by
    intro t
    apply Fin.ext
    rw [hnsmul_val, Nat.mod_eq_of_lt t.is_lt]
  have hUW : U = P u * W * P v := by
    rw [hW_def, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single (0 : Fin m)]
    · -- `t = 0` term equals `U`.
      simp only [Fin.val_zero, pow_zero, Module.End.one_apply]
      exact hSupp
    · -- `t ≠ 0` terms vanish.
      intro t _ ht
      rw [hEt_supp (t : ℕ), hnsmul t]
      have hne : u + t ≠ u := by
        intro heq
        apply ht
        have hut : u + t = u + 0 := by rw [add_zero]; exact heq
        exact (add_right_inj u).mp hut
      have hzero_left : P u * P (u + t) = 0 := hPairwise (Ne.symm hne)
      calc
        P u * (P (u + t) * ((E ^ (t : ℕ)) U) * P (v + t)) * P v
            = (P u * P (u + t)) * ((E ^ (t : ℕ)) U) * P (v + t) * P v := by
              simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hzero_left]; simp
    · simp
  rw [hUW, hW_zero, Matrix.mul_zero, Matrix.zero_mul]

end MPSTensor

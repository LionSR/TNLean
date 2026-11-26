/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Irreducible.Periodic
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.FixedAdjoint
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Channel.Peripheral.Spectrum.Spectrum
import QICLean.Kraus.PrimitiveFixedPoint.Assembly
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.PeriodicSectorDecomposition

/-!
# Periodic overlap: the spectral non-repetition crux

This module isolates the off-diagonal vanishing lemma used by the periodic
overlap dichotomy.  For a periodic block, an off-diagonal modulus-one
eigenvector of the blocked transfer map must vanish; this is the faithful
port of the contradiction at arXiv:1708.00029, Appendix A, lines 404--423.

It also contains the following results.

* `MPSTensor.sectorBlocks_not_gaugePhaseEquiv_of_ne`, `MPSTensor.periodicSelfOverlap_tendsto`:
  periodic overlap dichotomy: self-overlap.

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

section SelfOverlapNonrep

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
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    {u v : Fin m} (hOrth : P u * P v = 0)
    {U : MatrixAlg D} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hSupp : U = P u * U * P v)
    (hEig : ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) ^ m) U = ζ • U) :
    U = 0 := by
  have : NeZero D := ⟨hP.bondDim_ne_zero⟩
  classical
  set E := Kraus.transferMap (ι := Fin d) (n := Fin D) A with hE_def
  -- The original transfer map is irreducible and trace preserving.
  have hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1 := hP.leftCanonical
  -- Trace preservation: `tr (E X) = tr X` for every `X`.
  have hTrace_pres : ∀ X : MatrixAlg D, Matrix.trace (E X) = Matrix.trace X := by
    intro X
    have hsum : Matrix.trace (E X) =
        Matrix.trace ((∑ i : Fin d, (A i)ᴴ * A i) * X) := by
      simp only [hE_def, Kraus.transferMap_apply, Finset.sum_mul, Matrix.trace_sum]
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
    Kraus.exists_posSemidef_fixedPoint A hP.leftCanonical (NeZero.pos D)
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
            rw [hE_def, Kraus.transferMap_apply]
      _ = ∑ i : Fin d, P (a + 1) * (A i * (P a * X * P b) * (A i)ᴴ) * P (b + 1) := by
            exact Finset.sum_congr rfl fun i _ => hterm i
      _ = P (a + 1) * (∑ i : Fin d, A i * (P a * X * P b) * (A i)ᴴ) * P (b + 1) := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = P (a + 1) * E (P a * X * P b) * P (b + 1) := by
            rw [hE_def, Kraus.transferMap_apply]
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
    Kraus.mapLM_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible A hP.irreducible
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

end SelfOverlapNonrep

section SelfOverlap

/-!
## Periodic overlap dichotomy: self-overlap

This module contains the self-overlap results from the first paragraph of
Appendix A of arXiv:1708.00029, using the cyclic-sector setup and auxiliary
non-repetition lemmas developed in `SelfOverlapSetup`.

### Main declarations

* `sectorOverlap_tendsto_delta_of_cyclicSectorDecomp`
* `blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp`
* `periodicSelfOverlap_tendsto`

### References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace Kraus
open Filter Matrix
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-- Distinct compressed cyclic sectors cannot be gauge-phase equivalent.

This is the **non-repetition** half of Lemma bdcf of arXiv:1708.00029
(the proof is at lines 409--423): the blocks C_u = P_u A^{(m)} of a periodic
block form a basis of *non-repeated* normal tensors. The hypotheses here repackage
the Lemma bdcf hypotheses: `P` are the orthogonal projectors of the off-diagonal
decomposition (`hPproj`, `hPsum`), `hCyclic` is the adjoint-transfer shift
𝓔_A^{*}(P_{k+1}) = P_k, `hComm` is the commutation of each P_k with the
blocked letters, and `hTrace` realizes each compressed MPV as
tr(P_k · Kraus.evalWord …). The orthogonality P_u P_v = 0 (u ≠ v) is the
off-diagonal support condition.

**Paper's argument (Lemma bdcf, lines 409--423).** Since `A` is a periodic
block, 𝓔_A is irreducible with peripheral spectrum {ω^r}_{r=0}^{m-1},
ω = e^{2πi/m}. The blocked map 𝓔_A^m then has 1 as its *only* modulus-one
eigenvalue (with multiplicity `m`), and its fixed-point set is exactly
{P_u Λ_A P_u}_u (with Λ_A the fixed point of 𝓔_A), while the fixed points
of the adjoint 𝓔_A^{*m} are exactly {P_u}_u. Suppose, for u ≠ v, a
gauge-phase equivalence C_u^{i} = e^{iξ} U C_v^{i} U† held, with U = P_u U P_v
(U U† = P_u, U† U = P_v). Then
𝓔_A^m(U) = Σ_i C_u^i U C_v^{i†} = e^{iξ} U Σ_i C_v^i C_v^{i†} = e^{iξ} U,
using 𝓔_{C_v}(P_v) = P_v. Thus U is a modulus-one eigenvector of 𝓔_A^m;
but the only such eigenvalue is 1 with the *diagonal* fixed points
{P_w Λ_A P_w}, whereas U = P_u U P_v is off-diagonal for u ≠ v — a
contradiction. Hence no such equivalence exists.

**Correctness — the `IsPeriodic m A` hypothesis is load-bearing.** The spectral
argument requires `A` to be a periodic (irreducible) block: that is what gives
𝓔_A the peripheral spectrum {ω^r} and makes each cyclic sector primitive. Without
it the statement is FALSE — the bare cyclic-projection data (orthogonal `P_k`
summing to `1`, the adjoint shift, blocked commutation, the trace formula) is
consistent with a *reducible* `A` (e.g. `B ⊕ B` for an irreducible period-`m`
block `B`) whose distinct sectors are gauge-phase equivalent. `hP` is supplied at
the unique call site `sectorBlocks_not_gaugePhaseEquiv_of_ne`. -/
private lemma not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    {P : Fin m → MatrixAlg D}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclic :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
          (fun i => (blocks k i)ᴴ) X)).1 =
        Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (_huv : u ≠ v) (hdim : dim v = dim u)
    (hOrth : P u * P v = 0) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim.symm) (blocks u))
      (blocks v) := by
  have : NeZero D := ⟨hP.bondDim_ne_zero⟩
  intro hGPE
  have hCyclicDecomp : IsCyclicSectorDecomp A blocks :=
    ⟨P, φ, hPproj, hPsum, hCyclic, hComm, hTrace, hIntertwine, hMul, hStar⟩
  have hIrr_v : Kraus.IsIrreducibleFamily (blocks v) :=
    (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hCyclicDecomp v (hNondeg v)).2
  have hCorner_u : ∀ i : Fin (blockPhysDim d m),
      V u * blocks u i * (V u)ᴴ = P u * (blockTensor A m) i * P u := by
    intro i
    calc
      V u * blocks u i * (V u)ᴴ = (φ u (blocks u i)).1 := by
        exact (hEmbed u (blocks u i)).symm
      _ = P u * (blockTensor A m) i * P u := hLetter u i
  have hCorner_v : ∀ i : Fin (blockPhysDim d m),
      V v * blocks v i * (V v)ᴴ = P v * (blockTensor A m) i * P v := by
    intro i
    calc
      V v * blocks v i * (V v)ᴴ = (φ v (blocks v i)).1 := by
        exact (hEmbed v (blocks v i)).symm
      _ = P v * (blockTensor A m) i * P v := hLetter v i
  -- The gauge-phase relation gives a nonzero vector in the `(u,v)` corner; the
  -- period-transfer contradiction then forces it to vanish.
  obtain ⟨U, ζ, hζ, hU_ne, hSupp, hEig⟩ :
      ∃ (U : MatrixAlg D) (ζ : ℂ), ‖ζ‖ = 1 ∧ U ≠ 0 ∧ U = P u * U * P v ∧
        ((Kraus.transferMap (ι := Fin d) (n := Fin D) A) ^ m) U = ζ • U := by
    have : NeZero (dim u) := ⟨hNondeg u⟩
    obtain ⟨U, ζ, hζ, hU_ne, hSupp, hEig_block⟩ :=
      exists_offDiag_eigenvector_of_gaugePhase_cast_left
        (D := D) (d₀ := blockPhysDim d m) (Du := dim u) (Dv := dim v) hdim
        (C := blockTensor A m) (Au := blocks u) (Av := blocks v)
        (hBlocks_lc u) (hBlocks_lc v) hIrr_v
        (fun i => hComm u i) (fun i => hComm v i)
        (hV_iso u) (hV_iso v) (hV_range u) (hV_range v)
        hCorner_u hCorner_v hGPE
    refine ⟨U, ζ, hζ, hU_ne, hSupp, ?_⟩
    simpa [transferMap_blockTensor] using hEig_block
  exact hU_ne
    (offDiag_eigenvector_eq_zero_of_isPeriodic A hP hPproj hPsum hCyclic hOrth
      hζ hSupp hEig)

/-- Distinct compressed sectors of a cyclic sector decomposition are not gauge-phase
equivalent.

Source: DCCSP17, arXiv:1708.00029, Lemma `bdcf`, lines 404--423.
A hypothetical gauge-phase equivalence produces a nonzero peripheral
eigenvector supported between two distinct cyclic corners. Periodicity of
the original irreducible tensor forces this eigenvector to vanish.
The periodicity hypothesis is essential: orthogonality of the corners alone
does not exclude gauge-phase equivalent sectors. -/
lemma sectorBlocks_not_gaugePhaseEquiv_of_ne
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
          (fun i => (blocks k i)ᴴ) X)).1 =
        Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    {u v : Fin m} (huv : u ≠ v) (hdim : dim u = dim v) :
    ¬ GaugePhaseEquiv
      (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
      (blocks v) := by
  have hPairwise : Pairwise fun i j : Fin m => P i * P j = 0 :=
    pairwise_mul_zero_of_orthogonalProjection_sum_one P hPproj hPsum
  have hOrth : P u * P v = 0 := hPairwise huv
  exact
    not_gaugePhaseEquiv_of_orthogonal_cyclicSector_traces
      A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
      hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg huv hdim.symm hOrth

/-- Sector-asymptotic step for the self-overlap proof.

After blocking by the period, the cyclic sector decomposition should make each
compressed sector a primitive normalized tensor, while distinct sectors are
asymptotically orthogonal.

This theorem isolates the passage from cyclic-sector decomposition data to the
overlap-asymptotic statement. -/
private theorem sectorOverlap_tendsto_delta_of_cyclicSectorDecomp
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
          (fun i => (blocks k i)ᴴ) X)).1 =
        Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0)
    (u v : Fin m) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
      atTop (nhds (if u = v then (1 : ℂ) else 0)) := by
  classical
  have hCyclic : IsCyclicSectorDecomp A blocks :=
    ⟨P, φ, hPproj, hPsum, hCyclicP, hComm, hTrace, hIntertwine, hMul, hStar⟩
  by_cases huv : u = v
  · subst v
    have : NeZero (dim u) := ⟨hNondeg u⟩
    obtain ⟨hPrim, hIrr⟩ :=
      primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic u (hNondeg u)
    obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩ :=
      Kraus.spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
        (blocks u) hIrr (hBlocks_lc u) hPrim
    have hSelf :
        Tendsto
          (fun k =>
            mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks u) k)
          atTop (nhds (1 : ℂ)) :=
      mpvOverlap_tendsto_one_of_transfer_spectralRadius_compl_lt_one
        (blocks u) (hBlocks_lc u) ρ hρ_fix hρ_ne hρ_psd (by
          simpa using hgap)
    simpa using hSelf
  · have hIrr_u : Kraus.IsIrreducibleFamily (blocks u) :=
      (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic u (hNondeg u)).2
    have hIrr_v : Kraus.IsIrreducibleFamily (blocks v) :=
      (primitive_and_irreducible_sectorBlocks_of_cyclicDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hCyclic v (hNondeg v)).2
    have : NeZero (dim u) := ⟨hNondeg u⟩
    have : NeZero (dim v) := ⟨hNondeg v⟩
    by_cases hdim : dim u = dim v
    · have hNot :
          ¬ GaugePhaseEquiv
            (cast (congr_arg (MPSTensor (blockPhysDim d m)) hdim) (blocks u))
            (blocks v) :=
        sectorBlocks_not_gaugePhaseEquiv_of_ne
          A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
          hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg huv hdim
      have hZero :
          Tendsto
            (fun k =>
              mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
            atTop (nhds (0 : ℂ)) :=
        mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
          hdim (blocks u) (blocks v) hIrr_u hIrr_v
          (hBlocks_lc u) (hBlocks_lc v) hNot
      simpa [huv] using hZero
    · have hZero :
          Tendsto
            (fun k =>
              mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) k)
            atTop (nhds (0 : ℂ)) :=
        mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
          (blocks u) (blocks v) hIrr_u hIrr_v
          (hBlocks_lc u) (hBlocks_lc v) hdim
      simpa [huv] using hZero

/-- Self-overlap limit for a blocked tensor from a cyclic sector decomposition.

If `blockTensor A m` splits as the sum of compressed cyclic sector tensors
`blocks u`, each sector is normalized to have self-overlap tending to `1`, and
distinct sectors are asymptotically orthogonal. Expanding the blocked
self-overlap as the finite double sum over sector overlaps therefore gives the
limit `m`, one contribution from each sector. -/
private theorem blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp
    (A : MPSTensor d D) {m : ℕ} [NeZero m]
    (hP : IsPeriodic m A)
    {dim : Fin m → ℕ}
    (blocks :
      (k : Fin m) → MPSTensor (blockPhysDim d m) (dim k))
    (hBlocks_lc :
      ∀ k, ∑ i : Fin (blockPhysDim d m),
        (blocks k i)ᴴ * blocks k i = 1)
    (hBlocks_mpv :
      SameMPV₂ (blockTensor A m)
        (toTensorFromBlocks (μ := fun _ => 1) blocks))
    {P : Fin m → MatrixAlg D}
    {φ : (k : Fin m) →
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ ≃ₗ[ℂ] cornerSubmodule (P k)}
    (hPproj : ∀ k, IsOrthogonalProjection (P k))
    (hPsum : ∑ k : Fin m, P k = 1)
    (hCyclicP :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k)
    (hComm :
      ∀ k (i : Fin (blockPhysDim d m)),
        P k * (blockTensor A m) i = (blockTensor A m) i * P k)
    (hTrace :
      ∀ k (N : ℕ) (σ : Fin N → Fin (blockPhysDim d m)),
        mpv (blocks k) σ = (P k * Kraus.evalWord (blockTensor A m) (List.ofFn σ)).trace)
    (hIntertwine : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin (dim k))
          (fun i => (blocks k i)ᴴ) X)).1 =
        Kraus.transferMap (ι := Fin (blockPhysDim d m)) (n := Fin D)
          (fun i => (P k * blockTensor A m i)ᴴ) ((φ k X).1))
    (hMul : ∀ k (X Y : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k (X * Y)).1 = (φ k X).1 * (φ k Y).1)
    (hStar : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k Xᴴ).1 = ((φ k X).1)ᴴ)
    (hLetter : ∀ k (i : Fin (blockPhysDim d m)),
      (φ k (blocks k i)).1 = P k * (blockTensor A m) i * P k)
    {V : (k : Fin m) → Matrix (Fin D) (Fin (dim k)) ℂ}
    (hV_iso : ∀ k, (V k)ᴴ * V k = 1)
    (hV_range : ∀ k, V k * (V k)ᴴ = P k)
    (hEmbed : ∀ k (X : Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (φ k X).1 = V k * X * (V k)ᴴ)
    (hNondeg : ∀ k, dim k ≠ 0) :
    Tendsto
      (fun k => mpvOverlap (d := blockPhysDim d m)
        (blockTensor (d := d) (n := Fin D) A m)
        (blockTensor (d := d) (n := Fin D) A m) k)
      atTop (nhds (m : ℂ)) := by
  classical
  have hOverlap_eq : ∀ N,
      mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (n := Fin D) A m)
          (blockTensor (d := d) (n := Fin D) A m) N =
        ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N := by
    intro N
    exact mpvOverlap_eq_sum_of_sameMPV₂_toTensorFromBlocks_one
      (blockTensor (d := d) (n := Fin D) A m)
      (blockTensor (d := d) (n := Fin D) A m)
      blocks blocks hBlocks_mpv hBlocks_mpv N
  have hInner : ∀ u : Fin m,
      Tendsto
        (fun N => ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N)
        atTop (nhds (∑ v : Fin m, if u = v then (1 : ℂ) else 0)) := by
    intro u
    exact tendsto_finsetSum (s := Finset.univ) fun v _ =>
      sectorOverlap_tendsto_delta_of_cyclicSectorDecomp
        A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
        hIntertwine hMul hStar hLetter hV_iso hV_range hEmbed hNondeg u v
  have hSum :
      Tendsto
        (fun N => ∑ u : Fin m, ∑ v : Fin m,
          mpvOverlap (d := blockPhysDim d m) (blocks u) (blocks v) N)
        atTop (nhds (∑ u : Fin m, ∑ v : Fin m, if u = v then (1 : ℂ) else 0)) := by
    exact tendsto_finsetSum (s := Finset.univ) fun u _ => hInner u
  have hLimit :
      (∑ u : Fin m, ∑ v : Fin m, if u = v then (1 : ℂ) else 0) = (m : ℂ) := by
    simp
  simpa [hLimit] using Filter.Tendsto.congr (fun N => (hOverlap_eq N).symm) hSum

/-- Self-overlap of a periodic tensor: `⟨V_N(A)|V_N(A)⟩ = tr(E_A^N)`, and
since the peripheral eigenvalues are `m`-th roots of unity, each contributing 1
at multiples of `m`, the limit along `m·ℕ` equals `m`.

This is the first displayed equation of Appendix A. -/
theorem periodicSelfOverlap_tendsto
    (A : MPSTensor d D) {m : ℕ}
    (hP : IsPeriodic m A) :
    Tendsto (fun k => mpvOverlap A A (m * k)) atTop (nhds (m : ℂ)) := by
  have : NeZero D := ⟨hP.bondDim_ne_zero⟩
  let : NeZero m := ⟨Nat.ne_of_gt hP.period_pos⟩
  obtain ⟨dim, blocks, P, φ, V, hBlocks_lc, hBlocks_mpv, hPproj, hPsum, hCyclicRaw,
    hComm, hTrace, hIntertwine, hMul, hStar, hNondeg, hLetterRaw, hV_iso, hV_range,
    hEmbed⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hP
  have hCyclicP :
      ∀ k, Kraus.transferMap (ι := Fin d) (n := Fin D) (fun i => (A i)ᴴ) (P (k + 1)) = P k := by
    intro k
    simpa [cyclicNextOfPos, Fin.add_def] using hCyclicRaw k
  have hBlocked :
      Tendsto
        (fun k => mpvOverlap (d := blockPhysDim d m)
          (blockTensor (d := d) (n := Fin D) A m)
          (blockTensor (d := d) (n := Fin D) A m) k)
        atTop (nhds (m : ℂ)) :=
    blockTensor_selfOverlap_tendsto_of_cyclicSectorDecomp
      A hP blocks hBlocks_lc hBlocks_mpv hPproj hPsum hCyclicP hComm hTrace
      hIntertwine hMul hStar hLetterRaw hV_iso hV_range hEmbed hNondeg
  refine hBlocked.congr' ?_
  filter_upwards with k
  rw [mpvOverlap_blockTensor_self_eq]
  simp [Nat.mul_comm]


end MPSTensor

end SelfOverlap

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Supplier
import TNLean.MPS.SharedInfra.Scaling

/-!
# Normalized SectorBNT supplier after blocking

The canonical form of arXiv:1606.00608 (eq:II_CF1,
`Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246) writes a tensor as
$A^i = \oplus_{k=1}^r \mu_k A_k^i$ with each $A_k$ a normal tensor, and line 246 fixes the
weight normalization: since the states are not normalized, one can always choose
$|\mu_k| \le 1$ with at least one weight of unit modulus, "something which we will assume from
now on."  The arbitrary-input supplier of the basis of normal tensors leaves that
normalization choice as a hypothesis on the produced weights.  This file discharges it:
dividing every weight by the largest modulus $m = \max_k |\mu_k|$ realizes the line-246
choice, and the discarded factor reappears as the scalar $m^N$ multiplying the length-$N$
matrix product coefficients.

## Main declarations

* `MPSTensor.exists_weight_normalization` — for a nonempty family of nonzero weights
  $\mu_1, \dots, \mu_r$ there is $m > 0$ with $|\mu_k / m| \le 1$ for every $k$, equality for
  some $k$, and $\mu_k / m \ne 0$ for every $k$ (the choice at line 246 of the source, with
  $m = \max_k |\mu_k|$).
* `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos_normalized` — for a tensor whose
  matrix product family has a nonzero positive-length coefficient, some blocking length $p$
  admits a basis-of-normal-tensors canonical form $P$ and a scale $m > 0$ with
  $V^{(N)}(A^{[p]}) = m^N V^{(N)}(P)$ at every positive length $N$.

## References

* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246 — the canonical form eq:II_CF1 and
  the line-246 weight normalization discharged here.
* `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 271-279 — the basis-of-normal-tensors
  definition and the characterization prop:char-BNT.
-/

namespace MPSTensor

variable {d : ℕ}

/-- If a matrix has nonzero trace, then for every positive-step subsequence of its powers,
some trace in that subsequence is nonzero. -/
private lemma exists_trace_pow_mul_ne_zero {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) (hM : Matrix.trace M ≠ 0)
    (p : ℕ) (_hp : 0 < p) :
    ∃ q : ℕ, 0 < q ∧ Matrix.trace (M ^ (p * q)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have htrace : ∀ q : ℕ, 0 < q →
      Matrix.trace ((M ^ p) ^ q) = Matrix.trace ((0 : Matrix (Fin D) (Fin D) ℂ) ^ q) := by
    intro q hq
    rw [← pow_mul]
    simp [h q hq, hq.ne']
  have hchar := Matrix.charpoly_eq_of_forall_trace_pow_eq
    (M ^ p) (0 : Matrix (Fin D) (Fin D) ℂ) htrace
  have hnilLin : IsNilpotent (Matrix.toLin' (M ^ p)) := by
    rw [LinearMap.isNilpotent_iff_charpoly, Matrix.charpoly_toLin', hchar,
      Matrix.charpoly_zero]
    simp
  have hnilPow : IsNilpotent (M ^ p) :=
    (Matrix.isNilpotent_toLin'_iff (M ^ p)).mp hnilLin
  have hnilM : IsNilpotent M := IsNilpotent.of_pow hnilPow
  exact hM (Matrix.isNilpotent_trace_of_isNilpotent hnilM).eq_zero

/-- A nonzero positive-length matrix product coefficient remains nonzero at some positive
length after every physical blocking. -/
private lemma exists_mpv_blockTensor_ne_zero {D : ℕ} (A : MPSTensor d D)
    (hNZ : ∃ N : ℕ, 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    ∃ N : ℕ, 0 < N ∧ ∃ σ : Fin N → Fin (blockPhysDim d p),
      mpv (blockTensor (d := d) (D := D) A p) σ ≠ 0 := by
  classical
  obtain ⟨N₀, hN₀, σ₀, hσ₀⟩ := hNZ
  let w := List.ofFn σ₀
  let M := evalWord A w
  have hM : Matrix.trace M ≠ 0 := by
    simpa [mpv, coeff, M, w] using hσ₀
  obtain ⟨q, hq, htrace⟩ := exists_trace_pow_mul_ne_zero M hM p hp
  have heval : ∀ r : ℕ, evalWord A (List.replicate r w).flatten = M ^ r := by
    intro r
    induction r with
    | zero => simp [M]
    | succ r ih =>
      rw [List.replicate_succ, List.flatten_cons, evalWord_append, ih, pow_succ']
  have hlenPow : ∀ r : ℕ, (List.replicate r w).flatten.length = r * N₀ := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
      simp [w, Nat.succ_mul, Nat.add_comm]
  let flatWord := (List.replicate (p * q) w).flatten
  have hlen : flatWord.length = (N₀ * q) * p := by
    calc
      flatWord.length = (p * q) * N₀ := hlenPow (p * q)
      _ = (N₀ * q) * p := by ac_rfl
  let flatConfig : Fin ((N₀ * q) * p) → Fin d :=
    fun i => flatWord.get (Fin.cast hlen.symm i)
  have hofFn : List.ofFn flatConfig = flatWord := by
    simp only [flatConfig]
    conv_rhs => rw [← List.ofFn_get flatWord]
    have hcongr :=
      List.ofFn_congr hlen.symm
        (fun i : Fin ((N₀ * q) * p) => flatWord.get (Fin.cast hlen.symm i))
    simpa [Function.comp, Fin.cast_cast] using hcongr
  let σ : Fin (N₀ * q) → Fin (blockPhysDim d p) :=
    (blockedConfigEquiv d (N₀ * q) p).symm flatConfig
  refine ⟨N₀ * q, Nat.mul_pos hN₀ hq, σ, ?_⟩
  have hflat : flattenBlockedWord d p (List.ofFn σ) = flatWord := by
    calc
      flattenBlockedWord d p (List.ofFn σ) =
          List.ofFn (blockedConfigEquiv d (N₀ * q) p σ) :=
        (ofFn_blockedConfigEquiv d (N₀ * q) p σ).symm
      _ = List.ofFn flatConfig := by
        simp [σ]
      _ = flatWord := hofFn
  simpa [mpv, coeff, evalWord_blockTensor, hflat, flatWord, heval] using htrace

/-- **The weight normalization at line 246 of the source.**

Source: arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, line 246: since the states
are not normalized, one can always choose $|\mu_k| \le 1$ with at least one weight of unit
modulus.  For a nonempty family of nonzero weights $\mu_1, \dots, \mu_r$, dividing by the
largest modulus $m = \max_k |\mu_k| > 0$ produces weights $\mu_k / m$ that are still nonzero,
have modulus at most one, and include one of modulus exactly one. -/
theorem exists_weight_normalization {r : ℕ} (hr : 0 < r)
    (μ : Fin r → ℂ) (hμ : ∀ k, μ k ≠ 0) :
    ∃ m : ℝ, 0 < m ∧
      (∀ k, ‖μ k / (m : ℂ)‖ ≤ 1) ∧ (∃ k, ‖μ k / (m : ℂ)‖ = 1) ∧
      ∀ k, μ k / (m : ℂ) ≠ 0 := by
  classical
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' hne fun k => ‖μ k‖
  have hle : ∀ k, ‖μ k‖ ≤ Finset.univ.sup' hne fun k => ‖μ k‖ := fun k =>
    Finset.le_sup' (fun k => ‖μ k‖) (Finset.mem_univ k)
  have hm_pos : 0 < Finset.univ.sup' hne fun k => ‖μ k‖ := by
    rw [hk₀]
    exact norm_pos_iff.mpr (hμ k₀)
  have hm_norm : ‖((Finset.univ.sup' hne fun k => ‖μ k‖ : ℝ) : ℂ)‖ =
      Finset.univ.sup' hne fun k => ‖μ k‖ := by
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hm_pos.le
  have hm_ne : ((Finset.univ.sup' hne fun k => ‖μ k‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hm_pos.ne'
  refine ⟨Finset.univ.sup' hne fun k => ‖μ k‖, hm_pos, ?_, ⟨k₀, ?_⟩,
    fun k => div_ne_zero (hμ k) hm_ne⟩
  · intro k
    rw [norm_div, hm_norm]
    exact (div_le_one hm_pos).mpr (hle k)
  · rw [norm_div, hm_norm, ← hk₀]
    exact div_self hm_pos.ne'

/-- **Normalized basis-of-normal-tensors supplier for a nonzero MPV family.**

Source: arXiv:1606.00608, `Papers/1606.00608/MPDO-22-12-17-2.tex`, lines 237-246 for the
canonical form eq:II_CF1 with the line-246 weight normalization, and lines 271-279 for the
basis-of-normal-tensors definition and prop:char-BNT.

For a tensor $A$ satisfying the nonvanishing hypothesis below, there are a positive blocking
length $p$, a scale $m > 0$, and a sector decomposition $P$ in basis-of-normal-tensors
canonical form such that at every positive length $N$ the matrix product coefficients satisfy
$V^{(N)}(A^{[p]}) = m^N \, V^{(N)}(P)$, where $A^{[p]}$ denotes the $p$-blocked tensor.  The
scale $m$ is the largest weight modulus of the prepared block family; dividing the weights by
$m$ realizes the line-246 choice $|\mu_k| \le 1$ with some $|\mu_k| = 1$, so the sector
decomposition carries the normalized weights and the factor $m^N$ records the original ones.

The hypothesis says exactly that the positive-length matrix product family is not the zero
family.  It also suffices after every blocking.  Indeed, choose a word with evaluated matrix
$M$ and $\operatorname{tr}(M) \ne 0$.  For each blocking length $p$, some $q > 0$ satisfies
$\operatorname{tr}(M^{pq}) \ne 0$: otherwise Newton--Girard gives the characteristic polynomial of
$M^p$ equal to that of the zero matrix, so $M^p$, and hence $M$, is nilpotent, contradicting
$\operatorname{tr}(M) \ne 0$.  Repeating the word $pq$ times therefore gives a nonzero
coefficient at a length divisible by $p$, which is a coefficient of the $p$-blocked tensor.

The nonzero-family condition is the precise boundary for the line-246 unit-modulus choice:
an empty weight family cannot contain a unit-modulus weight.

**Scope restriction (nonzero MPV family):** the source proposition says "for any tensor,"
but the zero MPV family cannot satisfy the global unit-modulus condition imposed immediately
before that proposition.  The hypothesis below is the weakest exclusion of this degenerate
case.  This boundary and its possible resolution by a separate zero-family clause are
recorded in `docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`. -/
theorem exists_isBNTCanonicalForm_afterBlocking_pos_normalized
    {d D : ℕ} (A : MPSTensor d D)
    (hNZ : ∃ N : ℕ, 0 < N ∧ ∃ σ : Fin N → Fin d, mpv A σ ≠ 0) :
    ∃ p : ℕ, 0 < p ∧ ∃ m : ℝ, 0 < m ∧
      ∃ P : SectorDecomposition (blockPhysDim d p),
        IsBNTCanonicalForm P ∧
        ∀ N : ℕ, 0 < N → ∀ σ : Fin N → Fin (blockPhysDim d p),
          mpv (blockTensor (d := d) (D := D) A p) σ = (m : ℂ) ^ N * mpv P.toTensor σ := by
  classical
  obtain ⟨p, hp, r, dim, μ, blocks, hDim, hTP, hPrim, hIrr, -, hμne, hSamePos⟩ :=
    exists_prepared_BNT_blocks_afterBlocking_pos (d := d) (D := D) A
  -- The nonvanishing hypothesis forces a nonempty block family.
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr0 | hpos
    · exfalso
      obtain ⟨N, hN, σ, hσ⟩ := exists_mpv_blockTensor_ne_zero A hNZ p hp
      apply hσ
      rw [hSamePos N hN σ, mpv_toTensorFromBlocks_eq_sum]
      subst hr0
      simp
    · exact hpos
  -- Normalize the weights by the largest modulus.
  obtain ⟨m, hm, hLe, hUnit, hne⟩ := exists_weight_normalization hr μ hμne
  have hm0 : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
  -- The block properties do not involve the weights, so the normalized weights feed the
  -- prepared-block constructor directly.
  obtain ⟨P, hSame, hBNT⟩ :=
    exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks
      (d := blockPhysDim d p) (r := r) (dim := dim)
      (fun k => μ k / (m : ℂ)) blocks hDim hTP hPrim hIrr hne hLe hUnit
  refine ⟨p, hp, m, hm, P, hBNT, ?_⟩
  intro N hN σ
  have hμeq : (fun k => (m : ℂ) * (μ k / (m : ℂ))) = μ := by
    funext k
    rw [mul_comm]
    exact div_mul_cancel₀ (μ k) hm0
  calc
    mpv (blockTensor (d := d) (D := D) A p) σ
        = mpv (toTensorFromBlocks (d := blockPhysDim d p) (μ := μ) blocks) σ :=
      hSamePos N hN σ
    _ = mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun k => (m : ℂ) * (μ k / (m : ℂ))) blocks) σ := by
      rw [hμeq]
    _ = (m : ℂ) ^ N * mpv (toTensorFromBlocks (d := blockPhysDim d p)
          (μ := fun k => μ k / (m : ℂ)) blocks) σ :=
      mpv_toTensorFromBlocks_weight_mul_left (m : ℂ) _ blocks σ
    _ = (m : ℂ) ^ N * mpv P.toTensor σ := by
      rw [hSame N hN σ]

end MPSTensor

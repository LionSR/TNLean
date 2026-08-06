/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFP
import TNLean.MPS.MPDO.RFPViaTS

/-!
# The renormalization fixed-point maps for the rescaling-stable example

This file continues `TNLean.MPS.MPDO.RescalingStableLengthDependentRFP`,
constructing the two trace-preserving completely positive maps of
Definition 4.1 (`MPOTensor.IsRFPViaTS`) for the explicit MPO tensor `R` of
that file, and concludes that `R` satisfies `IsRFPViaTS`.

`IsRFPViaTS M` (`TNLean/MPS/MPDO/RFPViaTS.lean`) does not presuppose the
source's canonical-form hypothesis: it is the bare existence of
trace-preserving completely positive maps `S`, `T` on the physical indices
with `S[physClose2 M X] = physClose1 M X` and `T[physClose1 M X] = physClose2
M X` for all virtual operators `X`.

## Main results

* `physClose1_R_entry`, `physClose2_R_entry` — closed-form entrywise
  formulas for `R`'s one- and two-site physical operators, showing
  `physClose2 R X` is a gate-restricted, rescaled pullback of `physClose1 R
  X` along `combine p q := bondEquiv (bit1 p, bit2 q)`, with the
  bond-matching condition `gate p q := bit2 p = bit1 q`.
* `refineMap` (`T`) — two Kraus operators built from `wMat`'s
  Walsh–Hadamard eigendecomposition (`eigVecs`, `eigVals`).
* `refineMap_isKrausCPTP` — `T` is trace-preserving completely positive.
* `refineMap_physClose1` — `T[physClose1 R X] = physClose2 R X` for all `X`
  (the `eq:Tmap` equation of Definition 4.1).
* `coarseMap` (`S`) — four Kraus operators: two gated (`coarseKrausGated`,
  sharing `T`'s Walsh–Hadamard amplitude `coarseAmp = 1/√2`) and two
  ungated (`coarseKrausUngated`, a deterministic assignment resolving the
  identity on bond-mismatched pairs).
* `coarseMap_isKrausCPTP` — `S` is trace-preserving completely positive.
* `coarseMap_physClose2` — `S[physClose2 R X] = physClose1 R X` for all `X`
  (the `eq:Smap` equation of Definition 4.1).
* `isRFPViaTS_R` — `R` satisfies `IsRFPViaTS`, witnessed by `S := coarseMap`
  and `T := refineMap`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1, lines 645--659, and Theorem 4.14
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor.RescalingStableLengthDependentRFP

/-! ### IsRFPViaTS — the tp-CP renormalization maps

The physical index `Fin 4` of `R` factors through the same bit reading used
above: a physical index `p` carries the pair `(bit1 p, bit2 p)`.  `combine p q`
glues the first bit of `p` to the second bit of `q`, and `gate p q` is the
bond-matching condition between two consecutive letters.  The two-site
physical operator `physClose2 R X` is a rescaled, gate-restricted pullback of
the one-site physical operator `physClose1 R X` along `combine`. -/

/-- The physical index gluing the first bit of `p` to the second bit of `q`. -/
def combine (p q : Fin 4) : Fin 4 := bondEquiv (bit1 p, bit2 q)

@[simp] lemma bit1_combine (p q : Fin 4) : bit1 (combine p q) = bit1 p := by
  simp [combine, bit1_eq_bondEquiv_symm_fst]

@[simp] lemma bit2_combine (p q : Fin 4) : bit2 (combine p q) = bit2 q := by
  simp [combine, bit2_eq_bondEquiv_symm_snd]

/-- The bond-matching condition between two consecutive physical letters:
the second bit of `p` equals the first bit of `q`. -/
def gate (p q : Fin 4) : Prop := bit2 p = bit1 q

instance decidableGate (p q : Fin 4) : Decidable (gate p q) :=
  inferInstanceAs (Decidable (bit2 p = bit1 q))

/-- The one-site physical operator of `R`, as a bilinear pairing of the
letter-column vectors through `X`: `physClose1 R X i j = (25/32) *
(u_{ij} ⬝ᵥ (v_{ij} ᵥ* X))`. -/
lemma physClose1_R_entry (X : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    physClose1 R X i j = (25/32 : ℂ) *
      ((fun a => A a (bit1 i) (bit1 j)) ⬝ᵥ
        ((fun b => A b (bit2 i) (bit2 j)) ᵥ* X)) := by
  rw [physClose1_apply, R_eq_vecMulVec, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, smul_eq_mul]

/-- **The two-site physical operator of `R` is a gate-restricted, rescaled
pullback of the one-site physical operator along `combine`.** When both
`(i1, i2)` and `(j1, j2)` satisfy the bond-matching condition `gate`, the
`(i1,i2),(j1,j2)` entry of `physClose2 R X` is `(25/32) · wMat (bit2 i1)
(bit2 j1)` times the `combine i1 i2, combine j1 j2` entry of `physClose1 R X`;
otherwise it vanishes. -/
lemma physClose2_R_entry (X : Matrix (Fin 4) (Fin 4) ℂ) (i1 i2 j1 j2 : Fin 4) :
    physClose2 R X (i1, i2) (j1, j2) =
      (25/32 : ℂ) * (if gate i1 i2 ∧ gate j1 j2 then wMat (bit2 i1) (bit2 j1) else 0) *
        physClose1 R X (combine i1 i2) (combine j1 j2) := by
  rw [physClose2_apply, R_eq_vecMulVec, R_eq_vecMulVec]
  simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul]
  rw [Matrix.trace_smul, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, smul_eq_mul]
  rw [physClose1_R_entry]
  simp only [bit1_combine, bit2_combine]
  have hdot : (fun b : Fin 4 => A b (bit2 i1) (bit2 j1)) ⬝ᵥ
      (fun a : Fin 4 => A a (bit1 i2) (bit1 j2)) =
      if gate i1 i2 ∧ gate j1 j2 then wMat (bit2 i1) (bit2 j1) else 0 :=
    dotProduct_A_col _ _ _ _
  rw [hdot]
  by_cases h : gate i1 i2 ∧ gate j1 j2
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

/-! ### The Walsh–Hadamard eigenbasis of `wMat`, reused as Kraus data -/

/-- The two (unnormalized) Walsh–Hadamard eigenvectors of `wMat`. -/
def eigVecs : Fin 2 → Fin 2 → ℂ
  | 0 => ![1, 1]
  | 1 => ![1, -1]

/-- The eigenvalues of `wMat` matching `eigVecs`. -/
def eigVals : Fin 2 → ℝ
  | 0 => 1
  | 1 => lambda

lemma wMat_mulVec_eigVecs (s : Fin 2) :
    wMat.mulVec (eigVecs s) = (eigVals s : ℂ) • eigVecs s := by
  fin_cases s
  · exact wMat_mulVec_ones
  · exact wMat_mulVec_alt

lemma eigVecs_sq_sum (s : Fin 2) : (eigVecs s 0) ^ 2 + (eigVecs s 1) ^ 2 = 2 := by
  fin_cases s <;> norm_num [eigVecs]

/-- **The gated fiber of `combine` over a physical index `k` has exactly two
elements, indexed by the shared bond bit `b`.** For any function `f` of the
first-site's second bit, the sum over gated pairs `(p, q)` with `combine p q
= k` of `f (bit2 p)` collapses to `f 0 + f 1`. -/
lemma gated_combine_fiber_sum (k : Fin 4) (f : Fin 2 → ℂ) :
    (∑ pq : Fin 4 × Fin 4,
        if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then f (bit2 pq.1) else 0) =
      f 0 + f 1 := by
  rw [Fintype.sum_prod_type]
  fin_cases k <;>
    simp [gate, combine, bit1, bit2, bondEquiv_val, Fin.sum_univ_four]

/-! ### The refinement map `T`: one-site to two-site physical operators -/

lemma eigVals_pos (s : Fin 2) : 0 < eigVals s := by
  fin_cases s <;> norm_num [eigVals, lambda]

/-- The Kraus amplitude of the refinement map's `s`-th component. -/
noncomputable def refineAmp (s : Fin 2) : ℝ := Real.sqrt (25 * eigVals s / 64)

lemma refineAmp_sq (s : Fin 2) : (refineAmp s) ^ 2 = 25 * eigVals s / 64 := by
  rw [refineAmp, Real.sq_sqrt (by have := eigVals_pos s; linarith)]

/-- The `s`-th Kraus operator of the refinement map `T` sending the one-site
physical operator to the two-site physical operator: it places the
amplitude `refineAmp s * eigVecs s (bit2 p)` at the gated pair `(p, q)`
whose `combine` equals `k`, and vanishes elsewhere. -/
noncomputable def refineKraus (s : Fin 2) : Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  Matrix.of fun pq k =>
    if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then
      (refineAmp s : ℂ) * eigVecs s (bit2 pq.1)
    else 0

/-- The refinement map `T` from one-site to two-site physical operators. -/
noncomputable def refineMap :
    Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.rectangularKrausMap refineKraus

lemma refineAmp_star (s : Fin 2) : star ((refineAmp s : ℝ) : ℂ) = (refineAmp s : ℂ) :=
  Complex.conj_ofReal _

lemma eigVecs_star (s b : Fin 2) : star (eigVecs s b) = eigVecs s b := by
  fin_cases s <;> fin_cases b <;> simp [eigVecs]

lemma refineKraus_apply_conj_mul (s : Fin 2) (pq : Fin 4 × Fin 4) (k : Fin 4) :
    star (refineKraus s pq k) * refineKraus s pq k =
      if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then
        (refineAmp s : ℂ) ^ 2 * (eigVecs s (bit2 pq.1)) ^ 2
      else 0 := by
  simp only [refineKraus, Matrix.of_apply]
  by_cases h : gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k
  · simp only [if_pos h, star_mul', refineAmp_star, eigVecs_star]
    ring
  · simp [h]

lemma refineAmp_sq_sum :
    (refineAmp (0 : Fin 2) : ℂ) ^ 2 * 2 + (refineAmp (1 : Fin 2) : ℂ) ^ 2 * 2 = 1 := by
  have h0 := refineAmp_sq (0 : Fin 2)
  have h1 := refineAmp_sq (1 : Fin 2)
  have e0 : ((refineAmp (0 : Fin 2) : ℝ) : ℂ) ^ 2 = ((refineAmp (0 : Fin 2)) ^ 2 : ℝ) := by
    push_cast; ring
  have e1 : ((refineAmp (1 : Fin 2) : ℝ) : ℂ) ^ 2 = ((refineAmp (1 : Fin 2)) ^ 2 : ℝ) := by
    push_cast; ring
  rw [e0, e1, h0, h1]
  norm_num [eigVals, lambda]

/-- **The refinement Kraus family resolves the identity.** -/
lemma refineKraus_resolution :
    ∑ s : Fin 2, (refineKraus s)ᴴ * refineKraus s = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext k k'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hkk' : k = k'
  · subst hkk'
    rw [Matrix.one_apply_eq]
    have hstep : ∀ s : Fin 2,
        (∑ pq : Fin 4 × Fin 4, star (refineKraus s pq k) * refineKraus s pq k) =
          (refineAmp s : ℂ) ^ 2 * 2 := by
      intro s
      simp_rw [refineKraus_apply_conj_mul]
      rw [gated_combine_fiber_sum k (fun b => (refineAmp s : ℂ) ^ 2 * (eigVecs s b) ^ 2)]
      have := eigVecs_sq_sum s
      have heq : (eigVecs s 0) ^ 2 + (eigVecs s 1) ^ 2 = (2 : ℂ) := by exact_mod_cast this
      rw [← mul_add, heq]
    rw [Finset.sum_congr rfl fun s _ => hstep s]
    simpa [Fin.sum_univ_two] using refineAmp_sq_sum
  · rw [Matrix.one_apply_ne hkk']
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro pq _
    simp only [refineKraus, Matrix.of_apply]
    by_cases h1 : gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k
    · have h2 : ¬ (gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k') := by
        rintro ⟨_, hc⟩
        exact hkk' (h1.2.symm.trans hc)
      rw [if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]

/-- **`refineMap` is trace-preserving completely positive.** -/
theorem refineMap_isKrausCPTP : IsKrausCPTP refineMap :=
  Matrix.rectangularKrausMap_isKrausCPTP refineKraus refineKraus_resolution

lemma wMat_eigen_reconstruction (b b' : Fin 2) :
    ∑ s : Fin 2, (eigVals s : ℂ) * eigVecs s b * eigVecs s b' = 2 * wMat b b' := by
  fin_cases b <;> fin_cases b' <;> simp [Fin.sum_univ_two, eigVecs, eigVals, wMat, lambda] <;> ring

/-- **`refineMap` sends the one-site physical operator of `R` to the two-site
physical operator.** Together with `refineMap_isKrausCPTP`, this supplies the
`T`-map equation of Definition 4.1 for `R`. -/
theorem refineMap_physClose1 (X : Matrix (Fin 4) (Fin 4) ℂ) :
    refineMap (physClose1 R X) = physClose2 R X := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  rw [physClose2_R_entry]
  change (∑ s : Fin 2, refineKraus s * physClose1 R X * (refineKraus s)ᴴ) (i1, i2) (j1, j2) = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases h : gate i1 i2 ∧ gate j1 j2
  · have hstep : ∀ s : Fin 2,
        (∑ k : Fin 4, (∑ l : Fin 4, refineKraus s (i1, i2) l * physClose1 R X l k) *
            star (refineKraus s (j1, j2) k)) =
          (refineAmp s : ℂ) ^ 2 * eigVecs s (bit2 i1) * eigVecs s (bit2 j1) *
            physClose1 R X (combine i1 i2) (combine j1 j2) := by
      intro s
      have hl : ∀ k : Fin 4, (∑ l : Fin 4, refineKraus s (i1, i2) l * physClose1 R X l k) =
          (refineAmp s : ℂ) * eigVecs s (bit2 i1) * physClose1 R X (combine i1 i2) k := by
        intro k
        rw [Finset.sum_eq_single (combine i1 i2)]
        · simp [refineKraus, h.1]
        · intro l _ hl
          simp only [refineKraus, Matrix.of_apply]
          rw [if_neg (fun hc => hl hc.2.symm)]
          ring
        · simp
      simp_rw [hl]
      rw [Finset.sum_eq_single (combine j1 j2)]
      · simp only [refineKraus, Matrix.of_apply, h.2, true_and, if_true, star_mul',
          refineAmp_star, eigVecs_star]
        ring
      · intro k _ hk
        simp only [refineKraus, Matrix.of_apply]
        rw [if_neg (fun hc => hk hc.2.symm), star_zero, mul_zero]
      · simp
    rw [Finset.sum_congr rfl fun s _ => hstep s, ← Finset.sum_mul]
    have hcomb :
        (∑ s : Fin 2, (refineAmp s : ℂ) ^ 2 * eigVecs s (bit2 i1) * eigVecs s (bit2 j1)) =
        (25/32 : ℂ) * wMat (bit2 i1) (bit2 j1) := by
      have hrw : ∀ s : Fin 2,
          (refineAmp s : ℂ) ^ 2 * eigVecs s (bit2 i1) * eigVecs s (bit2 j1) =
          (25/64 : ℂ) * ((eigVals s : ℂ) * eigVecs s (bit2 i1) * eigVecs s (bit2 j1)) := by
        intro s
        have hsq := refineAmp_sq s
        have : ((refineAmp s : ℝ) : ℂ) ^ 2 = ((refineAmp s) ^ 2 : ℝ) := by push_cast; ring
        rw [this, hsq]
        push_cast
        ring
      simp_rw [hrw]
      rw [← Finset.mul_sum, wMat_eigen_reconstruction]
      ring
    rw [hcomb, if_pos h]
  · rw [if_neg h, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.sum_eq_zero
    intro k _
    rw [not_and_or] at h
    rcases h with h1 | h2
    · apply mul_eq_zero_of_left
      apply Finset.sum_eq_zero
      intro l _
      simp only [refineKraus, Matrix.of_apply]
      rw [if_neg (fun hc => h1 hc.1), zero_mul]
    · apply mul_eq_zero_of_right
      simp only [refineKraus, Matrix.of_apply]
      rw [if_neg (fun hc => h2 hc.1), star_zero]

/-! ### The coarse-graining map `S`: two-site to one-site physical operators -/

/-- The common Kraus amplitude of `S`'s gated component: `1 / √2`. -/
noncomputable def coarseAmp : ℝ := 1 / Real.sqrt 2

lemma coarseAmp_sq : coarseAmp ^ 2 = 1 / 2 := by
  rw [coarseAmp, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), one_pow]

/-- The `s`-th gated Kraus operator of the coarse-graining map `S`. -/
noncomputable def coarseKrausGated (s : Fin 2) : Matrix (Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.of fun k pq =>
    if gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k then
      (coarseAmp : ℂ) * eigVecs s (bit2 pq.1)
    else 0

/-- The `t`-th ungated Kraus operator of the coarse-graining map `S`: a
deterministic assignment of the (exactly one) ungated pair with `combine`
value `k` and first-site second bit `t`. -/
noncomputable def coarseKrausUngated (t : Fin 2) : Matrix (Fin 4) (Fin 4 × Fin 4) ℂ :=
  Matrix.of fun k pq =>
    if ¬ gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k ∧ bit2 pq.1 = t then 1 else 0

/-- The coarse-graining map `S`, with four Kraus operators: two gated
(sharing the Walsh–Hadamard structure with `T`) and two ungated (a
deterministic assignment filling out the trace-preserving resolution on
pairs that fail the bond-matching condition). -/
noncomputable def coarseMap :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.rectangularKrausMap
    (Sum.elim coarseKrausGated coarseKrausUngated :
      Fin 2 ⊕ Fin 2 → Matrix (Fin 4) (Fin 4 × Fin 4) ℂ)

/-- A physical index is determined by its two bits. -/
lemma eq_of_bit1_bit2 (p q : Fin 4) (h1 : bit1 p = bit1 q) (h2 : bit2 p = bit2 q) : p = q := by
  have h : bondEquiv.symm p = bondEquiv.symm q := by
    apply Prod.ext
    · rw [← bit1_eq_bondEquiv_symm_fst, ← bit1_eq_bondEquiv_symm_fst, h1]
    · rw [← bit2_eq_bondEquiv_symm_snd, ← bit2_eq_bondEquiv_symm_snd, h2]
  exact bondEquiv.symm.injective h

/-- `Σ_s eigVecs s b ^ 2 = 2` for a fixed bit `b`, summing over the eigenbasis label. -/
lemma eigVecs_sq_sum' (b : Fin 2) : (eigVecs 0 b) ^ 2 + (eigVecs 1 b) ^ 2 = 2 := by
  fin_cases b <;> norm_num [eigVecs]

/-- Two elements of `Fin 2` that both differ from a common third element agree. -/
lemma fin2_eq_of_ne_ne {a b c : Fin 2} (hac : a ≠ c) (hbc : b ≠ c) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

/-- An ungated pair is determined by its `combine` value and the first
site's second bit. -/
lemma eq_of_ungated_combine_bit2 {pq pq' : Fin 4 × Fin 4} (h1 : ¬ gate pq.1 pq.2)
    (h1' : ¬ gate pq'.1 pq'.2) (hc : combine pq.1 pq.2 = combine pq'.1 pq'.2)
    (hb : bit2 pq.1 = bit2 pq'.1) : pq = pq' := by
  have e1 : bit1 pq.1 = bit1 pq'.1 := by
    have h := congrArg bit1 hc
    rwa [bit1_combine, bit1_combine] at h
  have e2 : bit2 pq.2 = bit2 pq'.2 := by
    have h := congrArg bit2 hc
    rwa [bit2_combine, bit2_combine] at h
  have e3 : bit1 pq.2 = bit1 pq'.2 := by
    have h1b : bit1 pq.2 ≠ bit2 pq.1 := fun h => h1 h.symm
    have h1'b : bit1 pq'.2 ≠ bit2 pq.1 := by
      rw [hb]; exact fun h => h1' h.symm
    exact fin2_eq_of_ne_ne h1b h1'b
  apply Prod.ext
  · exact eq_of_bit1_bit2 _ _ e1 hb
  · exact eq_of_bit1_bit2 _ _ e3 e2

lemma coarseAmp_star : star ((coarseAmp : ℝ) : ℂ) = (coarseAmp : ℂ) :=
  Complex.conj_ofReal _

/-- Two `gate`-satisfying pairs sharing a `combine` value and distinct from
each other cannot share their first site's second bit: if they did,
`eq_of_bit1_bit2` would force the pairs to coincide. -/
lemma bit2_ne_of_gate_combine_eq {pq pq' : Fin 4 × Fin 4} (hg : gate pq.1 pq.2)
    (hg' : gate pq'.1 pq'.2) (hc : combine pq.1 pq.2 = combine pq'.1 pq'.2) (hne : pq ≠ pq') :
    bit2 pq.1 ≠ bit2 pq'.1 := by
  intro hb
  apply hne
  have h1 : bit1 pq.1 = bit1 pq'.1 := by
    have := congrArg bit1 hc
    rwa [bit1_combine, bit1_combine] at this
  have hp1 : pq.1 = pq'.1 := eq_of_bit1_bit2 _ _ h1 hb
  have h2 : bit1 pq.2 = bit1 pq'.2 := hg.symm.trans (hb.trans hg')
  have h3 : bit2 pq.2 = bit2 pq'.2 := by
    have := congrArg bit2 hc
    rwa [bit2_combine, bit2_combine] at this
  exact Prod.ext hp1 (eq_of_bit1_bit2 _ _ h2 h3)

/-- The off-diagonal cancellation between the eigenbasis rows for distinct
bits: the two gated Kraus operators of `S` are orthogonal on any pair of
physical indices whose shared bond bits differ. -/
lemma eigVecs_orthogonal' {b b' : Fin 2} (h : b ≠ b') :
    eigVecs 0 b * eigVecs 0 b' + eigVecs 1 b * eigVecs 1 b' = 0 := by
  fin_cases b <;> fin_cases b' <;> simp_all [eigVecs]

/-- **The coarse-graining Kraus family resolves the identity.** -/
lemma coarseKraus_resolution :
    ∑ α : Fin 2 ⊕ Fin 2,
        (Sum.elim coarseKrausGated coarseKrausUngated α)ᴴ *
          Sum.elim coarseKrausGated coarseKrausUngated α =
      (1 : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ) := by
  ext pq pq'
  rw [Matrix.one_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  -- The gated contribution at a fixed label `s`, as a sum over the domain `Fin 4`.
  have hgated_term : ∀ s : Fin 2,
      (∑ k : Fin 4, star (coarseKrausGated s k pq) * coarseKrausGated s k pq') =
        if gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2 then
          (coarseAmp : ℂ) ^ 2 * eigVecs s (bit2 pq.1) * eigVecs s (bit2 pq'.1)
        else 0 := by
    intro s
    by_cases h : gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2
    · rw [if_pos h]
      have e1 : coarseKrausGated s (combine pq.1 pq.2) pq =
          (coarseAmp : ℂ) * eigVecs s (bit2 pq.1) := by
        simp [coarseKrausGated, Matrix.of_apply, h.1]
      have e2 : coarseKrausGated s (combine pq.1 pq.2) pq' =
          (coarseAmp : ℂ) * eigVecs s (bit2 pq'.1) := by
        simp only [coarseKrausGated, Matrix.of_apply]
        exact if_pos ⟨h.2.1, h.2.2.symm⟩
      rw [Finset.sum_eq_single (combine pq.1 pq.2)]
      · rw [e1, e2, star_mul', eigVecs_star, coarseAmp_star]; ring
      · intro k _ hk
        have e : coarseKrausGated s k pq = 0 := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_neg (fun hcond => hk hcond.2.symm)
        rw [e]; simp
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro k _
      rw [not_and_or, not_and_or] at h
      rcases h with h1 | h1 | h1
      · have e : coarseKrausGated s k pq = 0 := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_neg (fun hcond => h1 hcond.1)
        rw [e]; simp
      · have e : coarseKrausGated s k pq' = 0 := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_neg (fun hcond => h1 hcond.1)
        rw [e]; simp
      · by_cases hpk : gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k
        · have hpk' : ¬ (gate pq'.1 pq'.2 ∧ combine pq'.1 pq'.2 = k) := by
            rintro ⟨_, hc⟩; exact h1 (hpk.2.trans hc.symm)
          have e : coarseKrausGated s k pq' = 0 := by
            simp only [coarseKrausGated, Matrix.of_apply]
            exact if_neg hpk'
          rw [e]; simp
        · have e : coarseKrausGated s k pq = 0 := by
            simp only [coarseKrausGated, Matrix.of_apply]
            exact if_neg hpk
          rw [e]; simp
  -- The ungated contribution at a fixed label `t`, as a sum over the domain `Fin 4`.
  have hungated_term : ∀ t : Fin 2,
      (∑ k : Fin 4, star (coarseKrausUngated t k pq) * coarseKrausUngated t k pq') =
        if ¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = t ∧ bit2 pq'.1 = t ∧
            combine pq.1 pq.2 = combine pq'.1 pq'.2 then 1 else 0 := by
    intro t
    by_cases h : ¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = t ∧ bit2 pq'.1 = t ∧
        combine pq.1 pq.2 = combine pq'.1 pq'.2
    · rw [if_pos h]
      obtain ⟨hg1, hg2, hb1, hb2, hc⟩ := h
      have e1 : coarseKrausUngated t (combine pq.1 pq.2) pq = 1 := by
        simp only [coarseKrausUngated, Matrix.of_apply]
        exact if_pos ⟨hg1, trivial, hb1⟩
      have e2 : coarseKrausUngated t (combine pq.1 pq.2) pq' = 1 := by
        simp only [coarseKrausUngated, Matrix.of_apply]
        exact if_pos ⟨hg2, hc.symm, hb2⟩
      rw [Finset.sum_eq_single (combine pq.1 pq.2)]
      · rw [e1, e2]; simp
      · intro k _ hk
        have e : coarseKrausUngated t k pq = 0 := by
          simp only [coarseKrausUngated, Matrix.of_apply]
          exact if_neg (fun hcond => hk hcond.2.1.symm)
        rw [e]; simp
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hpk : ¬ gate pq.1 pq.2 ∧ combine pq.1 pq.2 = k ∧ bit2 pq.1 = t
      · have hpk' : ¬ (¬ gate pq'.1 pq'.2 ∧ combine pq'.1 pq'.2 = k ∧ bit2 pq'.1 = t) := by
          rintro ⟨hg', hc', hb'⟩
          exact h ⟨hpk.1, hg', hpk.2.2, hb', hpk.2.1.trans hc'.symm⟩
        have e : coarseKrausUngated t k pq' = 0 := by
          simp only [coarseKrausUngated, Matrix.of_apply]
          exact if_neg hpk'
        rw [e]; simp
      · have e : coarseKrausUngated t k pq = 0 := by
          simp only [coarseKrausUngated, Matrix.of_apply]
          exact if_neg hpk
        rw [e]; simp
  simp only [hgated_term, hungated_term, Fin.sum_univ_two]
  by_cases heq : pq = pq'
  · subst heq
    rw [if_pos rfl]
    by_cases hg : gate pq.1 pq.2
    · have hCg : gate pq.1 pq.2 ∧ gate pq.1 pq.2 ∧ combine pq.1 pq.2 = combine pq.1 pq.2 :=
        ⟨hg, hg, rfl⟩
      have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
          bit2 pq.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2) := fun hc => hc.1 hg
      have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
          bit2 pq.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2) := fun hc => hc.1 hg
      rw [if_pos hCg, if_pos hCg, if_neg hCu0, if_neg hCu1]
      have hsum : (eigVecs 0 (bit2 pq.1)) ^ 2 + (eigVecs 1 (bit2 pq.1)) ^ 2 = (2 : ℂ) := by
        exact_mod_cast eigVecs_sq_sum' (bit2 pq.1)
      have hamp : (coarseAmp : ℂ) ^ 2 = (1 / 2 : ℂ) := by
        have hcast : ((coarseAmp : ℝ) : ℂ) ^ 2 = ((coarseAmp ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, coarseAmp_sq]; norm_num
      have step : (coarseAmp : ℂ) ^ 2 * eigVecs 0 (bit2 pq.1) * eigVecs 0 (bit2 pq.1) +
          (coarseAmp : ℂ) ^ 2 * eigVecs 1 (bit2 pq.1) * eigVecs 1 (bit2 pq.1) + (0 + 0) =
          (coarseAmp : ℂ) ^ 2 * ((eigVecs 0 (bit2 pq.1)) ^ 2 + (eigVecs 1 (bit2 pq.1)) ^ 2) := by
        ring
      rw [step, hsum, hamp]; norm_num
    · have hCg : ¬ (gate pq.1 pq.2 ∧ gate pq.1 pq.2 ∧ combine pq.1 pq.2 = combine pq.1 pq.2) :=
        fun hc => hg hc.1
      rw [if_neg hCg, if_neg hCg]
      by_cases hb : bit2 pq.1 = (0 : Fin 2)
      · have hCu0 : ¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
            bit2 pq.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2 :=
          ⟨hg, hg, hb, hb, rfl⟩
        have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
            bit2 pq.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2) := by
          rintro ⟨_, _, hb1, _, _⟩
          rw [hb] at hb1; exact absurd hb1 (by decide)
        rw [if_pos hCu0, if_neg hCu1]; norm_num
      · have hb1 : bit2 pq.1 = (1 : Fin 2) := by omega
        have hCu1 : ¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
            bit2 pq.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2 :=
          ⟨hg, hg, hb1, hb1, rfl⟩
        have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq.1 pq.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
            bit2 pq.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq.1 pq.2) := by
          rintro ⟨_, _, hb0, _, _⟩
          exact hb hb0
        rw [if_neg hCu0, if_pos hCu1]; norm_num
  · rw [if_neg heq]
    by_cases hg : gate pq.1 pq.2
    · by_cases hg' : gate pq'.1 pq'.2
      · by_cases hc : combine pq.1 pq.2 = combine pq'.1 pq'.2
        · have hCg : gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2 :=
            ⟨hg, hg', hc⟩
          have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
              bit2 pq'.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
            fun hcon => hcon.1 hg
          have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
              bit2 pq'.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
            fun hcon => hcon.1 hg
          rw [if_pos hCg, if_pos hCg, if_neg hCu0, if_neg hCu1]
          have hbne : bit2 pq.1 ≠ bit2 pq'.1 := bit2_ne_of_gate_combine_eq hg hg' hc heq
          have step : (coarseAmp : ℂ) ^ 2 * eigVecs 0 (bit2 pq.1) * eigVecs 0 (bit2 pq'.1) +
              (coarseAmp : ℂ) ^ 2 * eigVecs 1 (bit2 pq.1) * eigVecs 1 (bit2 pq'.1) + (0 + 0) =
              (coarseAmp : ℂ) ^ 2 *
                (eigVecs 0 (bit2 pq.1) * eigVecs 0 (bit2 pq'.1) +
                  eigVecs 1 (bit2 pq.1) * eigVecs 1 (bit2 pq'.1)) := by
            ring
          rw [step, eigVecs_orthogonal' hbne, mul_zero]
        · have hCg : ¬ (gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧
              combine pq.1 pq.2 = combine pq'.1 pq'.2) := fun hcon => hc hcon.2.2
          have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
              bit2 pq'.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
            fun hcon => hcon.1 hg
          have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
              bit2 pq'.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
            fun hcon => hcon.1 hg
          rw [if_neg hCg, if_neg hCg, if_neg hCu0, if_neg hCu1]; norm_num
      · have hCg : ¬ (gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧
            combine pq.1 pq.2 = combine pq'.1 pq'.2) := fun hcon => hg' hcon.2.1
        have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
            bit2 pq'.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
          fun hcon => hcon.1 hg
        have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
            bit2 pq'.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) :=
          fun hcon => hcon.1 hg
        rw [if_neg hCg, if_neg hCg, if_neg hCu0, if_neg hCu1]; norm_num
    · have hCg : ¬ (gate pq.1 pq.2 ∧ gate pq'.1 pq'.2 ∧
          combine pq.1 pq.2 = combine pq'.1 pq'.2) := fun hcon => hg hcon.1
      have hCu0 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (0 : Fin 2) ∧
          bit2 pq'.1 = (0 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) := by
        rintro ⟨hg1, hg1', hb1, hb1', hceq⟩
        exact heq (eq_of_ungated_combine_bit2 hg1 hg1' hceq (hb1.trans hb1'.symm))
      have hCu1 : ¬ (¬ gate pq.1 pq.2 ∧ ¬ gate pq'.1 pq'.2 ∧ bit2 pq.1 = (1 : Fin 2) ∧
          bit2 pq'.1 = (1 : Fin 2) ∧ combine pq.1 pq.2 = combine pq'.1 pq'.2) := by
        rintro ⟨hg1, hg1', hb1, hb1', hceq⟩
        exact heq (eq_of_ungated_combine_bit2 hg1 hg1' hceq (hb1.trans hb1'.symm))
      rw [if_neg hCg, if_neg hCg, if_neg hCu0, if_neg hCu1]; norm_num

/-- **`coarseMap` is trace-preserving completely positive.** -/
theorem coarseMap_isKrausCPTP : IsKrausCPTP coarseMap :=
  Matrix.rectangularKrausMap_isKrausCPTP _ coarseKraus_resolution

/-- **`coarseMap` sends the two-site physical operator of `R` back to the
one-site physical operator.** Together with `coarseMap_isKrausCPTP`, this
supplies the `S`-map equation of Definition 4.1 for `R`. -/
theorem coarseMap_physClose2 (X : Matrix (Fin 4) (Fin 4) ℂ) :
    coarseMap (physClose2 R X) = physClose1 R X := by
  ext i j
  change (∑ α : Fin 2 ⊕ Fin 2,
      Sum.elim coarseKrausGated coarseKrausUngated α * physClose2 R X *
        (Sum.elim coarseKrausGated coarseKrausUngated α)ᴴ) i j = physClose1 R X i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  -- The ungated Kraus operators annihilate every entry: `physClose2 R X p q`
  -- vanishes whenever `p` fails the bond-matching condition, which is exactly
  -- the domain of `coarseKrausUngated`.
  have hungated_zero : ∀ t : Fin 2,
      (∑ q : Fin 4 × Fin 4, (∑ p : Fin 4 × Fin 4, coarseKrausUngated t i p * physClose2 R X p q) *
          star (coarseKrausUngated t j q)) = 0 := by
    intro t
    apply Finset.sum_eq_zero
    intro q _
    have hinner : (∑ p : Fin 4 × Fin 4, coarseKrausUngated t i p * physClose2 R X p q) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : ¬ gate p.1 p.2 ∧ combine p.1 p.2 = i ∧ bit2 p.1 = t
      · have hz : physClose2 R X p q = 0 := by
          rw [physClose2_R_entry, if_neg (fun hcon : gate p.1 p.2 ∧ gate q.1 q.2 => hp.1 hcon.1)]
          ring
        rw [hz, mul_zero]
      · have e : coarseKrausUngated t i p = 0 := by
          simp only [coarseKrausUngated, Matrix.of_apply]
          exact if_neg hp
        rw [e, zero_mul]
    rw [hinner]; simp
  have hungated_sum_zero :
      (∑ t : Fin 2, ∑ q : Fin 4 × Fin 4, (∑ p : Fin 4 × Fin 4,
          coarseKrausUngated t i p * physClose2 R X p q) *
        star (coarseKrausUngated t j q)) = 0 := by
    rw [Fin.sum_univ_two, hungated_zero 0, hungated_zero 1, add_zero]
  rw [hungated_sum_zero, add_zero]
  -- The gated contribution: on the fiber of `i`, `physClose2 R X p q` rescales
  -- and restricts `physClose1 R X` along `combine`; the two-level fiber sum
  -- (over the shared bond bits of `p` and of `q`) reassembles the `wMat`
  -- eigendecomposition and collapses to `physClose1 R X i j` exactly.
  have hinner : ∀ s : Fin 2, ∀ q : Fin 4 × Fin 4,
      (∑ p : Fin 4 × Fin 4, coarseKrausGated s i p * physClose2 R X p q) =
        (if gate q.1 q.2 then
            (coarseAmp : ℂ) * (25 / 32 : ℂ) * physClose1 R X i (combine q.1 q.2) *
              (eigVecs s 0 * wMat 0 (bit2 q.1) + eigVecs s 1 * wMat 1 (bit2 q.1))
          else 0) := by
    intro s q
    by_cases hq : gate q.1 q.2
    · rw [if_pos hq]
      have hcongr : (∑ p : Fin 4 × Fin 4, coarseKrausGated s i p * physClose2 R X p q) =
          ∑ p : Fin 4 × Fin 4, if gate p.1 p.2 ∧ combine p.1 p.2 = i then
              (coarseAmp : ℂ) * (25 / 32 : ℂ) * physClose1 R X i (combine q.1 q.2) *
                (eigVecs s (bit2 p.1) * wMat (bit2 p.1) (bit2 q.1))
            else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : gate p.1 p.2 ∧ combine p.1 p.2 = i
        · rw [if_pos hp]
          have e : coarseKrausGated s i p = (coarseAmp : ℂ) * eigVecs s (bit2 p.1) := by
            simp only [coarseKrausGated, Matrix.of_apply]
            exact if_pos hp
          have c1 : (if gate p.1 p.2 ∧ gate q.1 q.2 then wMat (bit2 p.1) (bit2 q.1) else 0) =
              wMat (bit2 p.1) (bit2 q.1) := if_pos ⟨hp.1, hq⟩
          rw [e, physClose2_R_entry, hp.2, c1]; ring
        · rw [if_neg hp]
          have e : coarseKrausGated s i p = 0 := by
            simp only [coarseKrausGated, Matrix.of_apply]
            exact if_neg hp
          rw [e, zero_mul]
      rw [hcongr, gated_combine_fiber_sum i (fun b => (coarseAmp : ℂ) * (25 / 32 : ℂ) *
          physClose1 R X i (combine q.1 q.2) * (eigVecs s b * wMat b (bit2 q.1)))]
      ring
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : gate p.1 p.2 ∧ combine p.1 p.2 = i
      · have e : coarseKrausGated s i p = (coarseAmp : ℂ) * eigVecs s (bit2 p.1) := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_pos hp
        have c1 : (if gate p.1 p.2 ∧ gate q.1 q.2 then wMat (bit2 p.1) (bit2 q.1) else 0) = 0 :=
          if_neg (fun hcon => hq hcon.2)
        rw [e, physClose2_R_entry, c1]; ring
      · have e : coarseKrausGated s i p = 0 := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_neg hp
        rw [e, zero_mul]
  have houter : ∀ s : Fin 2,
      (∑ q : Fin 4 × Fin 4, (∑ p : Fin 4 × Fin 4,
          coarseKrausGated s i p * physClose2 R X p q) * star (coarseKrausGated s j q)) =
        (coarseAmp : ℂ) ^ 2 * (25 / 32 : ℂ) * physClose1 R X i j *
          (eigVecs s 0 * wMat 0 0 * eigVecs s 0 + eigVecs s 1 * wMat 1 0 * eigVecs s 0 +
            (eigVecs s 0 * wMat 0 1 * eigVecs s 1 + eigVecs s 1 * wMat 1 1 * eigVecs s 1)) := by
    intro s
    have hcongr : (∑ q : Fin 4 × Fin 4, (∑ p : Fin 4 × Fin 4,
        coarseKrausGated s i p * physClose2 R X p q) * star (coarseKrausGated s j q)) =
        ∑ q : Fin 4 × Fin 4, if gate q.1 q.2 ∧ combine q.1 q.2 = j then
            (coarseAmp : ℂ) ^ 2 * (25 / 32 : ℂ) * physClose1 R X i j *
              (eigVecs s 0 * wMat 0 (bit2 q.1) + eigVecs s 1 * wMat 1 (bit2 q.1)) *
              eigVecs s (bit2 q.1)
          else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hinner]
      by_cases hqj : gate q.1 q.2 ∧ combine q.1 q.2 = j
      · rw [if_pos hqj.1, if_pos hqj, hqj.2]
        have e : coarseKrausGated s j q = (coarseAmp : ℂ) * eigVecs s (bit2 q.1) := by
          simp only [coarseKrausGated, Matrix.of_apply]
          exact if_pos hqj
        rw [e, star_mul', eigVecs_star, coarseAmp_star]
        ring
      · by_cases hq : gate q.1 q.2
        · have hqne : combine q.1 q.2 ≠ j := fun hcon => hqj ⟨hq, hcon⟩
          rw [if_pos hq, if_neg hqj]
          have e : coarseKrausGated s j q = 0 := by
            simp only [coarseKrausGated, Matrix.of_apply]
            exact if_neg (fun hcon => hqne hcon.2)
          rw [e]; simp
        · rw [if_neg hq, if_neg hqj]; simp
    rw [hcongr, gated_combine_fiber_sum j (fun b => (coarseAmp : ℂ) ^ 2 * (25 / 32 : ℂ) *
        physClose1 R X i j * (eigVecs s 0 * wMat 0 b + eigVecs s 1 * wMat 1 b) * eigVecs s b)]
    ring
  rw [Fin.sum_univ_two, houter, houter]
  have hamp : (coarseAmp : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    have hcast : ((coarseAmp : ℝ) : ℂ) ^ 2 = ((coarseAmp ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, coarseAmp_sq]; norm_num
  have hw00 : wMat 0 0 = (16 / 25 : ℂ) := by simp [wMat]; norm_num
  have hw01 : wMat 0 1 = (9 / 25 : ℂ) := by simp [wMat]; norm_num
  have hw10 : wMat 1 0 = (9 / 25 : ℂ) := by simp [wMat]; norm_num
  have hw11 : wMat 1 1 = (16 / 25 : ℂ) := by simp [wMat]; norm_num
  have hev00 : eigVecs 0 0 = (1 : ℂ) := by simp [eigVecs]
  have hev01 : eigVecs 0 1 = (1 : ℂ) := by simp [eigVecs]
  have hev10 : eigVecs 1 0 = (1 : ℂ) := by simp [eigVecs]
  have hev11 : eigVecs 1 1 = (-1 : ℂ) := by simp [eigVecs]
  rw [hamp, hw00, hw01, hw10, hw11, hev00, hev01, hev10, hev11]
  ring

/-- **`R` satisfies the source's renormalization fixed-point condition
of Definition 4.1.** `coarseMap` and `refineMap` are the trace-preserving
completely positive maps `S` and `T` witnessing `IsRFPViaTS R`. -/
theorem isRFPViaTS_R : IsRFPViaTS R :=
  ⟨coarseMap, refineMap, coarseMap_isKrausCPTP, refineMap_isKrausCPTP,
    coarseMap_physClose2, refineMap_physClose1⟩

end MPOTensor.RescalingStableLengthDependentRFP

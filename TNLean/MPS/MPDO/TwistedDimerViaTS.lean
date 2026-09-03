/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimerRefine

/-!
# The twisted quantum dimer is a renormalization fixed point

**Scope: the coarse-graining map and the fixed-point statement.** This file
completes `TNLean.MPS.MPDO.TwistedDimerRefine` with the second of the two
trace-preserving completely positive maps of arXiv:1606.00608, Definition 4.1,
and concludes that the $\mathbb Z_2$-twisted quantum dimer satisfies that
definition.  The tensor is a project example motivated by the
length-dependence question after Theorem 4.14 of that paper (lines 995--1010);
it is not a tensor stated in the source.

## The coarse-graining channel

The coarse-graining map measures the two bond qubits shared by a two-site
letter in the orthonormal basis
$(|00\rangle \pm |11\rangle)/\sqrt2$, $|01\rangle$, $|10\rangle$, reads the two
site flags, and returns the one-site letter carrying the outer site qubits and
the flag $f_1 + f_2 + s$, where $s$ is one for the antisymmetric bond outcome
and zero otherwise.  On the support of the two-site physical closure the two
bond qubits agree, so only the two symmetric-basis outcomes contribute, and
their recombination is exactly the flag sign $\tau_1$ of the twisted dimer.

## Main results

* `bondVec_completeness` — the bond basis is orthonormal;
* `coarseWeight_sum` — the scalar identity behind the coarse-graining
  channel;
* `coarseKraus_resolution` — the coarse-graining Kraus family resolves the
  identity;
* `coarseMap_isKrausCPTP` — the coarse-graining map is trace-preserving
  completely positive;
* `coarseMap_physClose2` — the coarse-graining map carries the two-site
  physical closure back to the one-site physical closure;
* `isRFPViaTS_T` — the twisted quantum dimer satisfies the renormalization
  fixed-point condition of Definition 4.1.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 (lines 645--659) and Theorem 4.14 with lines 995--1010
  (the twisted dimer is a project example, not a tensor stated in the source)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### The bond basis -/

/-- The amplitude $1/\sqrt2$ of the symmetric and antisymmetric bond states. -/
def invSqrt2 : ℝ := 1 / Real.sqrt 2

/-- The square of the bond amplitude is one half. -/
lemma invSqrt2_mul_self : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [invSqrt2, div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The orthonormal basis of the bond pair used by the coarse-graining map:
the two states $(|00\rangle \pm |11\rangle)/\sqrt2$ followed by $|01\rangle$
and $|10\rangle$. -/
def bondVec : Fin 4 → Fin 2 → Fin 2 → ℝ
  | 0, b₁, b₂ => if b₁ = b₂ then invSqrt2 else 0
  | 1, b₁, b₂ => if b₁ = b₂ then invSqrt2 * tau 1 b₁ else 0
  | 2, b₁, b₂ => if b₁ = 0 ∧ b₂ = 1 then 1 else 0
  | 3, b₁, b₂ => if b₁ = 1 ∧ b₂ = 0 then 1 else 0

/-- The flag shift attached to a bond outcome: the antisymmetric outcome
flips the decoded flag, the others leave it alone. -/
def bondShift : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0

/-- **The bond basis is orthonormal.** -/
lemma bondVec_completeness (b₁ b₂ c₁ c₂ : Fin 2) :
    ∑ v : Fin 4, bondVec v b₁ b₂ * bondVec v c₁ c₂ = if b₁ = c₁ ∧ b₂ = c₂ then 1 else 0 := by
  have h2 := invSqrt2_mul_self
  fin_cases b₁ <;> fin_cases b₂ <;> fin_cases c₁ <;> fin_cases c₂ <;>
    simp [Fin.sum_univ_four, bondVec, tau] <;> nlinarith [h2]

/-- The real weight contributed by one coarse-graining Kraus label to the
one-site physical closure. -/
def coarseWeight (v : Fin 4) (k f₁ f₂ L L' : Fin 2) : ℝ :=
  ∑ b : Fin 2, ∑ c : Fin 2,
    bondVec v b b * bondVec v c c * (Cmat k L L' * tau k f₁ / 2 * (Cmat k b c * tau k f₂ / 2))

/-- **The scalar identity behind the coarse-graining channel.**  Summed over
the bond outcomes and the two site flags compatible with a prescribed one-site
flag, the weights of the two symmetric bond outcomes recombine into half the
bond matrix $C_k$ of the twisted dimer, with the flag sign $\tau_k$. -/
lemma coarseWeight_sum (k F L L' : Fin 2) :
    ∑ t : Fin 4 × Fin 2 × Fin 2,
        (if t.2.1 + t.2.2 + bondShift t.1 = F then coarseWeight t.1 k t.2.1 t.2.2 L L' else 0) =
      Cmat k L L' * tau k F / 2 := by
  have h2 := invSqrt2_mul_self
  fin_cases k <;> fin_cases F <;> fin_cases L <;> fin_cases L' <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two, coarseWeight, bondVec,
      bondShift, tau, Cmat, cDiag_eq, cOff_eq] <;> nlinarith [h2]

/-- **The two-site physical closure on a fibre of the coarse-graining map.** -/
lemma physClose2_T_fiber (X : Matrix (Fin 8) (Fin 8) ℂ) (L L' R R' f₁ f₂ b₁ b₂ c₁ c₂ : Fin 2) :
    physClose2 T X (physIdx L b₁ f₁, physIdx b₂ R f₂) (physIdx L' c₁ f₁, physIdx c₂ R' f₂) =
      if b₁ = b₂ ∧ c₁ = c₂ then
        ∑ k : Fin 2, ((Cmat k L L' * tau k f₁ / 2 * (Cmat k b₂ c₂ * tau k f₂ / 2) : ℝ) : ℂ) *
          X (physIdx R R' k) (physIdx L L' k)
      else 0 := by
  rw [physClose2_T]
  by_cases h : b₁ = b₂ ∧ c₁ = c₂
  · rw [ite_eq_left (show IsBondMatchedPair (physIdx L b₁ f₁) (physIdx b₂ R f₂) ∧
      IsBondMatchedPair (physIdx L' c₁ f₁) (physIdx c₂ R' f₂) from
        ⟨by simp [IsBondMatchedPair, h.1], by simp [IsBondMatchedPair, h.2]⟩),
      ite_eq_left h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coef_physIdx, coef_physIdx, ite_eq_left rfl, ite_eq_left rfl]
    simp only [bitL_physIdx, bitR_physIdx]
    push_cast
    ring
  · rw [ite_eq_right h]
    refine ite_eq_right fun hc => ?_
    exact absurd
      ⟨by simpa [IsBondMatchedPair] using hc.1, by simpa [IsBondMatchedPair] using hc.2⟩ h

/-! ### The coarse-graining Kraus family -/

/-- The support condition of the coarse-graining Kraus operators. -/
def IsCoarseSupported (v : Fin 4) (f₁ f₂ : Fin 2) (j : Fin 8) (i : Fin 8 × Fin 8) : Prop :=
  ((bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j)) ∧
    bitF j = f₁ + f₂ + bondShift v

instance decidableIsCoarseSupported (v : Fin 4) (f₁ f₂ : Fin 2) (j : Fin 8) (i : Fin 8 × Fin 8) :
    Decidable (IsCoarseSupported v f₁ f₂ j i) :=
  inferInstanceAs (Decidable (((_ ∧ _) ∧ (_ ∧ _)) ∧ _))

/-- The Kraus operator of the coarse-graining channel at the label
$(v, f_1, f_2)$: it reads the bond pair in the basis vector `v`, requires the
site flags $f_1, f_2$, and returns the one-site letter with the decoded flag. -/
def coarseKraus (v : Fin 4) (f₁ f₂ : Fin 2) : Matrix (Fin 8) (Fin 8 × Fin 8) ℂ :=
  Matrix.of fun j i =>
    if IsCoarseSupported v f₁ f₂ j i then ((bondVec v (bitR i.1) (bitL i.2) : ℝ) : ℂ) else 0

/-- The coarse-graining map, from two-site to one-site physical operators. -/
def coarseMap :
    Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.rectangularKrausMap fun t : Fin 4 × Fin 2 × Fin 2 => coarseKraus t.1 t.2.1 t.2.2

/-- The coarse-graining Kraus entries are real. -/
lemma coarseKraus_star (v : Fin 4) (f₁ f₂ : Fin 2) (j : Fin 8) (i : Fin 8 × Fin 8) :
    star (coarseKraus v f₁ f₂ j i) = coarseKraus v f₁ f₂ j i := by
  simp only [coarseKraus, Matrix.of_apply]
  split_ifs
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-- Contracting a coarse-graining Kraus operator against a two-site vector
sums over the bond bits of its fibre. -/
lemma coarseKraus_row_sum (v : Fin 4) (f₁ f₂ : Fin 2) (j : Fin 8) (g : Fin 8 × Fin 8 → ℂ) :
    (∑ i : Fin 8 × Fin 8, coarseKraus v f₁ f₂ j i * g i) =
      if bitF j = f₁ + f₂ + bondShift v then
        ∑ b₁ : Fin 2, ∑ b₂ : Fin 2, ((bondVec v b₁ b₂ : ℝ) : ℂ) *
          g (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂)
      else 0 := by
  by_cases hf : bitF j = f₁ + f₂ + bondShift v
  · rw [ite_eq_left hf]
    have hcongr : ∀ i : Fin 8 × Fin 8, coarseKraus v f₁ f₂ j i * g i =
        if (bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j) then
          ((bondVec v (bitR i.1) (bitL i.2) : ℝ) : ℂ) * g i else 0 := by
      intro i
      simp only [coarseKraus, Matrix.of_apply]
      by_cases hi : (bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j)
      · rw [ite_eq_left (show IsCoarseSupported v f₁ f₂ j i from ⟨hi, hf⟩), ite_eq_left hi]
      · rw [ite_eq_right fun hc => hi hc.1, ite_eq_right hi, zero_mul]
    rw [Finset.sum_congr rfl fun i _ => hcongr i, pair_fiber_sum]
    simp only [bitR_physIdx, bitL_physIdx]
  · rw [ite_eq_right hf]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [coarseKraus, Matrix.of_apply]
    rw [ite_eq_right fun hc => hf hc.2, zero_mul]

/-- One diagonal term of the coarse-graining resolution of the identity. -/
lemma coarseKraus_res_term (v : Fin 4) (f₁ f₂ : Fin 2) (i i' : Fin 8 × Fin 8) :
    (∑ j : Fin 8, star (coarseKraus v f₁ f₂ j i) * coarseKraus v f₁ f₂ j i') =
      if ((bitF i.1 = f₁ ∧ bitF i.2 = f₂) ∧ (bitF i'.1 = f₁ ∧ bitF i'.2 = f₂)) ∧
          (bitL i.1 = bitL i'.1 ∧ bitR i.2 = bitR i'.2) then
        ((bondVec v (bitR i.1) (bitL i.2) * bondVec v (bitR i'.1) (bitL i'.2) : ℝ) : ℂ)
      else 0 := by
  by_cases h : ((bitF i.1 = f₁ ∧ bitF i.2 = f₂) ∧ (bitF i'.1 = f₁ ∧ bitF i'.2 = f₂)) ∧
      (bitL i.1 = bitL i'.1 ∧ bitR i.2 = bitR i'.2)
  · rw [ite_eq_left h]
    have hcongr : ∀ j : Fin 8, star (coarseKraus v f₁ f₂ j i) * coarseKraus v f₁ f₂ j i' =
        if bitF j = f₁ + f₂ + bondShift v ∧ bitL j = bitL i.1 ∧ bitR j = bitR i.2 then
          ((bondVec v (bitR i.1) (bitL i.2) * bondVec v (bitR i'.1) (bitL i'.2) : ℝ) : ℂ)
        else 0 := by
      intro j
      rw [coarseKraus_star]
      simp only [coarseKraus, Matrix.of_apply]
      by_cases hj : bitF j = f₁ + f₂ + bondShift v ∧ bitL j = bitL i.1 ∧ bitR j = bitR i.2
      · rw [ite_eq_left (show IsCoarseSupported v f₁ f₂ j i from
          ⟨⟨⟨h.1.1.1, hj.2.1.symm⟩, h.1.1.2, hj.2.2.symm⟩, hj.1⟩),
          ite_eq_left (show IsCoarseSupported v f₁ f₂ j i' from
          ⟨⟨⟨h.1.2.1, (hj.2.1.trans h.2.1).symm⟩, h.1.2.2, (hj.2.2.trans h.2.2).symm⟩, hj.1⟩),
          ← Complex.ofReal_mul, ite_eq_left hj]
      · have hz : ¬ IsCoarseSupported v f₁ f₂ j i := fun hc =>
          hj ⟨hc.2, hc.1.1.2.symm, hc.1.2.2.symm⟩
        rw [ite_eq_right hz, zero_mul, ite_eq_right hj]
    rw [Finset.sum_congr rfl fun j _ => hcongr j]
    exact one_site_fiber_sum _ _ _ _
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coarseKraus_star]
    simp only [coarseKraus, Matrix.of_apply]
    by_cases h1 : IsCoarseSupported v f₁ f₂ j i
    · by_cases h2 : IsCoarseSupported v f₁ f₂ j i'
      · exact absurd ⟨⟨⟨h1.1.1.1, h1.1.2.1⟩, h2.1.1.1, h2.1.2.1⟩,
          h1.1.1.2.trans h2.1.1.2.symm, h1.1.2.2.trans h2.1.2.2.symm⟩ h
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- Summing over the Kraus labels whose flags are prescribed leaves a sum over
the bond outcome. -/
lemma sum_bond_selector (F₁ F₂ : Fin 2) (V : Fin 4 × Fin 2 × Fin 2 → ℂ) :
    (∑ t : Fin 4 × Fin 2 × Fin 2, if t.2.1 = F₁ ∧ t.2.2 = F₂ then V t else 0) =
      ∑ v : Fin 4, V (v, F₁, F₂) := by
  fin_cases F₁ <;> fin_cases F₂ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **The coarse-graining Kraus family resolves the identity.** -/
theorem coarseKraus_resolution :
    ∑ t : Fin 4 × Fin 2 × Fin 2,
        (coarseKraus t.1 t.2.1 t.2.2)ᴴ * coarseKraus t.1 t.2.1 t.2.2 =
      (1 : Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ) := by
  ext i i'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_congr rfl fun t _ => coarseKraus_res_term t.1 t.2.1 t.2.2 i i']
  by_cases hb : (bitF i.1 = bitF i'.1 ∧ bitF i.2 = bitF i'.2) ∧
      (bitL i.1 = bitL i'.1 ∧ bitR i.2 = bitR i'.2)
  · have hiff : ∀ t : Fin 4 × Fin 2 × Fin 2,
        ((((bitF i.1 = t.2.1 ∧ bitF i.2 = t.2.2) ∧ (bitF i'.1 = t.2.1 ∧ bitF i'.2 = t.2.2)) ∧
          (bitL i.1 = bitL i'.1 ∧ bitR i.2 = bitR i'.2)) ↔
            (t.2.1 = bitF i.1 ∧ t.2.2 = bitF i.2)) := by
      intro t
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, _⟩, _⟩
        exact ⟨h1.symm, h2.symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨⟨h1.symm, h2.symm⟩, by rw [← hb.1.1, h1], by rw [← hb.1.2, h2]⟩, hb.2⟩
    simp only [hiff]
    rw [sum_bond_selector, ← Complex.ofReal_sum, bondVec_completeness, Matrix.one_apply]
    by_cases hc : bitR i.1 = bitR i'.1 ∧ bitL i.2 = bitL i'.2
    · rw [ite_eq_left hc, ite_eq_left (show i = i' from Prod.ext
        (eq_of_bits hb.2.1 hc.1 hb.1.1) (eq_of_bits hc.2 hb.2.2 hb.1.2))]
      norm_num
    · rw [ite_eq_right hc, ite_eq_right (show ¬ i = i' from fun hii => hc
        ⟨by rw [hii], by rw [hii]⟩)]
      norm_num
  · have hzero : ∀ t : Fin 4 × Fin 2 × Fin 2,
        ¬ (((bitF i.1 = t.2.1 ∧ bitF i.2 = t.2.2) ∧ (bitF i'.1 = t.2.1 ∧ bitF i'.2 = t.2.2)) ∧
          (bitL i.1 = bitL i'.1 ∧ bitR i.2 = bitR i'.2)) := by
      rintro t ⟨⟨⟨h1, h2⟩, h1', h2'⟩, h3⟩
      exact hb ⟨⟨h1.trans h1'.symm, h2.trans h2'.symm⟩, h3⟩
    rw [Finset.sum_congr rfl fun t _ => ite_eq_right (hzero t), Finset.sum_const_zero,
      Matrix.one_apply]
    refine (ite_eq_right fun hii => ?_).symm
    exact absurd ⟨⟨by rw [hii], by rw [hii]⟩, by rw [hii], by rw [hii]⟩ hb

/-- **The coarse-graining map is trace-preserving completely positive.** -/
theorem coarseMap_isKrausCPTP : IsKrausCPTP coarseMap :=
  Matrix.rectangularKrausMap_isKrausCPTP _ coarseKraus_resolution

/-! ### The coarse-graining map on the physical closures -/

/-- One Kraus term of the coarse-graining map, evaluated at a pair of one-site
letters. -/
lemma coarseKraus_conj_term (v : Fin 4) (f₁ f₂ : Fin 2) (X : Matrix (Fin 8) (Fin 8) ℂ)
    (j j' : Fin 8) :
    (∑ i' : Fin 8 × Fin 8, (∑ i : Fin 8 × Fin 8, coarseKraus v f₁ f₂ j i * physClose2 T X i i') *
        star (coarseKraus v f₁ f₂ j' i')) =
      if bitF j = f₁ + f₂ + bondShift v ∧ bitF j' = f₁ + f₂ + bondShift v then
        ∑ k : Fin 2, ((coarseWeight v k f₁ f₂ (bitL j) (bitL j') : ℝ) : ℂ) *
          X (physIdx (bitR j) (bitR j') k) (physIdx (bitL j) (bitL j') k)
      else 0 := by
  rw [Finset.sum_congr rfl fun i' _ => by
    rw [coarseKraus_row_sum v f₁ f₂ j fun i => physClose2 T X i i']]
  by_cases hj : bitF j = f₁ + f₂ + bondShift v
  · rw [Finset.sum_congr rfl fun i' _ => by rw [ite_eq_left hj]]
    have hswap : ∀ (W : Fin 2 → Fin 2 → Fin 8 × Fin 8 → ℂ) (S : Fin 8 × Fin 8 → ℂ),
        (∑ i' : Fin 8 × Fin 8, (∑ b₁ : Fin 2, ∑ b₂ : Fin 2, W b₁ b₂ i') * S i') =
          ∑ b₁ : Fin 2, ∑ b₂ : Fin 2, ∑ i' : Fin 8 × Fin 8, W b₁ b₂ i' * S i' := by
      intro W S
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b₁ _ => Finset.sum_comm
    rw [hswap (fun b₁ b₂ i' => ((bondVec v b₁ b₂ : ℝ) : ℂ) *
      physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂) i')
      fun i' => star (coarseKraus v f₁ f₂ j' i')]
    have hinner : ∀ b₁ b₂ : Fin 2,
        (∑ i' : Fin 8 × Fin 8, ((bondVec v b₁ b₂ : ℝ) : ℂ) *
            physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂) i' *
            star (coarseKraus v f₁ f₂ j' i')) =
          ((bondVec v b₁ b₂ : ℝ) : ℂ) *
            (if bitF j' = f₁ + f₂ + bondShift v then
              ∑ c₁ : Fin 2, ∑ c₂ : Fin 2, ((bondVec v c₁ c₂ : ℝ) : ℂ) *
                physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂)
                  (physIdx (bitL j') c₁ f₁, physIdx c₂ (bitR j') f₂)
            else 0) := by
      intro b₁ b₂
      have hterm : ∀ i' : Fin 8 × Fin 8,
          ((bondVec v b₁ b₂ : ℝ) : ℂ) *
              physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂) i' *
              star (coarseKraus v f₁ f₂ j' i') =
            ((bondVec v b₁ b₂ : ℝ) : ℂ) * (coarseKraus v f₁ f₂ j' i' *
              physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂) i') := by
        intro i'
        rw [coarseKraus_star]
        ring
      rw [Finset.sum_congr rfl fun i' _ => hterm i', ← Finset.mul_sum,
        coarseKraus_row_sum v f₁ f₂ j' fun i' =>
          physClose2 T X (physIdx (bitL j) b₁ f₁, physIdx b₂ (bitR j) f₂) i']
    rw [Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => hinner b₁ b₂]
    by_cases hj' : bitF j' = f₁ + f₂ + bondShift v
    · rw [ite_eq_left ⟨hj, hj'⟩]
      simp only [ite_eq_left hj', physClose2_T_fiber, coarseWeight, Fin.sum_univ_two]
      norm_num
      ring
    · rw [ite_eq_right fun hc => hj' hc.2]
      simp [ite_eq_right hj']
  · rw [ite_eq_right fun hc => hj hc.1]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [ite_eq_right hj, zero_mul]

/-- **The coarse-graining map carries the two-site physical closure of the
twisted dimer back to its one-site physical closure.**  Together with
`coarseMap_isKrausCPTP`, this is the map `S` of arXiv:1606.00608,
Definition 4.1 (paper label eq:Smap). -/
theorem coarseMap_physClose2 (X : Matrix (Fin 8) (Fin 8) ℂ) :
    coarseMap (physClose2 T X) = physClose1 T X := by
  ext j j'
  change (∑ t : Fin 4 × Fin 2 × Fin 2, coarseKraus t.1 t.2.1 t.2.2 * physClose2 T X *
      (coarseKraus t.1 t.2.1 t.2.2)ᴴ) j j' = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_congr rfl fun t _ => coarseKraus_conj_term t.1 t.2.1 t.2.2 X j j', physClose1_T]
  by_cases e : bitF j = bitF j'
  · have hiff : ∀ t : Fin 4 × Fin 2 × Fin 2,
        ((bitF j = t.2.1 + t.2.2 + bondShift t.1 ∧ bitF j' = t.2.1 + t.2.2 + bondShift t.1) ↔
          (t.2.1 + t.2.2 + bondShift t.1 = bitF j)) := by
      intro t
      exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, e ▸ h.symm⟩⟩
    simp only [hiff]
    have hdist : ∀ t : Fin 4 × Fin 2 × Fin 2,
        (if t.2.1 + t.2.2 + bondShift t.1 = bitF j then
            ∑ k : Fin 2, ((coarseWeight t.1 k t.2.1 t.2.2 (bitL j) (bitL j') : ℝ) : ℂ) *
              X (physIdx (bitR j) (bitR j') k) (physIdx (bitL j) (bitL j') k)
          else 0) =
          ∑ k : Fin 2,
            ((if t.2.1 + t.2.2 + bondShift t.1 = bitF j then
              coarseWeight t.1 k t.2.1 t.2.2 (bitL j) (bitL j') else 0 : ℝ) : ℂ) *
              X (physIdx (bitR j) (bitR j') k) (physIdx (bitL j) (bitL j') k) := by
      intro t
      by_cases hc : t.2.1 + t.2.2 + bondShift t.1 = bitF j
      · simp only [ite_eq_left hc]
      · simp [hc]
    rw [Finset.sum_congr rfl fun t _ => hdist t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, coarseWeight_sum, coef, ite_eq_left e]
  · have hzero : ∀ t : Fin 4 × Fin 2 × Fin 2,
        ¬ (bitF j = t.2.1 + t.2.2 + bondShift t.1 ∧ bitF j' = t.2.1 + t.2.2 + bondShift t.1) := by
      rintro t ⟨h1, h2⟩
      exact e (h1.trans h2.symm)
    rw [Finset.sum_congr rfl fun t _ => ite_eq_right (hzero t), Finset.sum_const_zero]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [coef, ite_eq_right e, zero_mul]

/-- **The $\mathbb Z_2$-twisted quantum dimer is a renormalization fixed
point.**  The coarse-graining map and the refinement map are the
trace-preserving completely positive maps `S` and `T` of arXiv:1606.00608,
Definition 4.1 (paper label RFPMixedTS, line 657).  The tensor is a project
example, not a tensor stated in the source. -/
theorem isRFPViaTS_T : IsRFPViaTS T :=
  ⟨coarseMap, refineMap, coarseMap_isKrausCPTP, refineMap_isKrausCPTP,
    coarseMap_physClose2, refineMap_physClose1⟩

end MPOTensor.TwistedDimer

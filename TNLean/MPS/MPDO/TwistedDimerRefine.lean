/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.TwistedDimer
import TNLean.MPS.MPDO.RFPViaTS

/-!
# The refinement channel of the twisted quantum dimer

**Scope: the refinement map only.** This file continues
`TNLean.MPS.MPDO.TwistedDimer` and builds the first of the two
trace-preserving completely positive maps required by the renormalization
fixed-point condition of arXiv:1606.00608, Definition 4.1: a map carrying the
one-site physical closure of the twisted quantum dimer to its two-site
physical closure.  The tensor is a project example motivated by the
length-dependence question after Theorem 4.14 of that paper (lines 995--1010);
it is not a tensor stated in the source.  The coarse-graining map in the
opposite direction, and the resulting fixed-point statement, are in
`TNLean.MPS.MPDO.TwistedDimerViaTS`.

## The refinement channel

Reading a physical index as a pair of site qubits together with a flag qubit,
the refinement map measures the incoming flag, prepares a fresh pair of flags
$(f_1, f_2)$ and a fresh bond qubit in one of the two states
$(|00\rangle \pm |11\rangle)/\sqrt2$, and returns the two-site letter whose bond
qubits carry the prepared bond state.  The two bond states are prepared with
the weights $x = 7/8$ and $y = 1/8$, and the incoming flag is constrained to
$f_1 + f_2 + \varepsilon$, where $\varepsilon$ labels the prepared bond state.
The resulting Kraus family is indexed by $(f_1, f_2, \varepsilon)$.

## Main results

* `pair_fiber_sum` — the fibre of a two-site letter over prescribed flags and
  outer bits is a square of bond bits;
* `refineAmp_tau_sum` — the scalar identity behind the refinement channel: the
  weighted sum of the two prepared bond states reproduces the bond matrices
  $C_0$ and $C_1$ of the twisted dimer;
* `refineKraus_resolution` — the refinement Kraus family resolves the identity;
* `refineMap_isKrausCPTP` — the refinement map is trace-preserving completely
  positive;
* `refineMap_physClose1` — the refinement map carries the one-site physical
  closure to the two-site physical closure.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 (lines 645--659) and Theorem 4.14 with lines 995--1010
  (the twisted dimer is a project example, not a tensor stated in the source)
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPOTensor.TwistedDimer

/-! ### Fibres of the bit encoding -/

/-- A physical index is determined by its three bits. -/
lemma eq_of_bits {i j : Fin 8} (hL : bitL i = bitL j) (hR : bitR i = bitR j)
    (hF : bitF i = bitF j) : i = j := by
  rw [← physIdx_bits i, ← physIdx_bits j, hL, hR, hF]

/-- A sum over the physical index is a threefold sum over its bits. -/
lemma sum_fin_eight (h : Fin 8 → ℂ) :
    ∑ i : Fin 8, h i = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, h (physIdx a b c) := by
  rw [← physEquiv.sum_comp h, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **The fibre over all three bits is a single index.** -/
lemma one_site_fiber_sum (F l r : Fin 2) (h : Fin 8 → ℂ) :
    (∑ j : Fin 8, if bitF j = F ∧ bitL j = l ∧ bitR j = r then h j else 0) =
      h (physIdx l r F) := by
  rw [sum_fin_eight]
  fin_cases F <;> fin_cases l <;> fin_cases r <;> simp [Fin.sum_univ_two]

/-- **The fibre over the flag and the first bit is indexed by the second bit.** -/
lemma left_fiber_sum (f l : Fin 2) (h : Fin 8 → ℂ) :
    (∑ i : Fin 8, if bitF i = f ∧ bitL i = l then h i else 0) =
      ∑ b : Fin 2, h (physIdx l b f) := by
  rw [sum_fin_eight]
  fin_cases f <;> fin_cases l <;> simp [Fin.sum_univ_two]

/-- **The fibre over the flag and the second bit is indexed by the first bit.** -/
lemma right_fiber_sum (f r : Fin 2) (h : Fin 8 → ℂ) :
    (∑ i : Fin 8, if bitF i = f ∧ bitR i = r then h i else 0) =
      ∑ b : Fin 2, h (physIdx b r f) := by
  rw [sum_fin_eight]
  fin_cases f <;> fin_cases r <;> simp [Fin.sum_univ_two]

/-- **The fibre of a two-site letter over prescribed flags and outer bits is a
square of bond bits.** -/
lemma pair_fiber_sum (f₁ f₂ l r : Fin 2) (h : Fin 8 × Fin 8 → ℂ) :
    (∑ i : Fin 8 × Fin 8,
        if (bitF i.1 = f₁ ∧ bitL i.1 = l) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = r) then h i else 0) =
      ∑ b₁ : Fin 2, ∑ b₂ : Fin 2, h (physIdx l b₁ f₁, physIdx b₂ r f₂) := by
  rw [Fintype.sum_prod_type]
  have step : ∀ i₁ : Fin 8,
      (∑ i₂ : Fin 8, if (bitF i₁ = f₁ ∧ bitL i₁ = l) ∧ (bitF i₂ = f₂ ∧ bitR i₂ = r)
          then h (i₁, i₂) else 0) =
        if bitF i₁ = f₁ ∧ bitL i₁ = l then ∑ b₂ : Fin 2, h (i₁, physIdx b₂ r f₂) else 0 := by
    intro i₁
    by_cases hP : bitF i₁ = f₁ ∧ bitL i₁ = l
    · rw [ite_eq_left hP]
      rw [Finset.sum_congr rfl fun i₂ _ => (by simp [hP] :
        (if (bitF i₁ = f₁ ∧ bitL i₁ = l) ∧ (bitF i₂ = f₂ ∧ bitR i₂ = r) then h (i₁, i₂) else 0) =
          if bitF i₂ = f₂ ∧ bitR i₂ = r then h (i₁, i₂) else 0)]
      exact right_fiber_sum f₂ r fun i₂ => h (i₁, i₂)
    · rw [ite_eq_right hP]
      exact Finset.sum_eq_zero fun i₂ _ => ite_eq_right fun hc => hP hc.1
  rw [Finset.sum_congr rfl fun i₁ _ => step i₁]
  exact left_fiber_sum f₁ l fun i₁ => ∑ b₂ : Fin 2, h (i₁, physIdx b₂ r f₂)

/-- **The one-site physical closure in bit coordinates.** -/
lemma physClose1_T_bits (X : Matrix (Fin 8) (Fin 8) ℂ) (L R F L' R' F' : Fin 2) :
    physClose1 T X (physIdx L R F) (physIdx L' R' F') =
      if F = F' then
        ∑ k : Fin 2, ((Cmat k L L' * tau k F / 2 : ℝ) : ℂ) *
          X (physIdx R R' k) (physIdx L L' k)
      else 0 := by
  rw [physClose1_T]
  simp only [bitL_physIdx, bitR_physIdx, coef_physIdx]
  by_cases h : F = F'
  · simp [h]
  · simp [h]

/-! ### The prepared bond states -/

/-- The weight of the prepared bond state: $x$ for $(|00\rangle + |11\rangle)/\sqrt2$
and $y$ for $(|00\rangle - |11\rangle)/\sqrt2$. -/
def bondWeight : Fin 2 → ℝ
  | 0 => x
  | 1 => y

/-- Both bond weights are nonnegative. -/
lemma bondWeight_nonneg (ε : Fin 2) : 0 ≤ bondWeight ε := by
  fin_cases ε <;> norm_num [bondWeight, x, y]

/-- The Kraus amplitude of the refinement channel at the bond outcome `ε`. -/
def refineAmp (ε : Fin 2) : ℝ := Real.sqrt (bondWeight ε) / 2

/-- The squared refinement amplitude is a quarter of the bond weight. -/
lemma refineAmp_sq (ε : Fin 2) : refineAmp ε ^ 2 = bondWeight ε / 4 := by
  rw [refineAmp, div_pow, Real.sq_sqrt (bondWeight_nonneg ε)]
  norm_num

/-- The flag signs square to one. -/
lemma tau_mul_self (k b : Fin 2) : tau k b * tau k b = 1 := by
  fin_cases k <;> fin_cases b <;> norm_num [tau]

/-- **The scalar identity behind the refinement channel.**  Summed over the two
prepared bond states, the weights $x/4$ and $y/4$ together with the bond sign
$(-1)^{\varepsilon(b + b')}$ and the flag sign reproduce half the bond matrix
$C_k[b, b']$ of the twisted dimer. -/
lemma refineAmp_tau_sum (k b b' f₁ f₂ : Fin 2) :
    ∑ ε : Fin 2, refineAmp ε ^ 2 * tau ε b * tau ε b' * tau k (f₁ + f₂ + ε) =
      tau k f₁ * tau k f₂ * Cmat k b b' / 2 := by
  have h0 : refineAmp 0 ^ 2 = 7 / 32 := by rw [refineAmp_sq]; norm_num [bondWeight, x]
  have h1 : refineAmp 1 ^ 2 = 1 / 32 := by rw [refineAmp_sq]; norm_num [bondWeight, y]
  fin_cases k <;> fin_cases b <;> fin_cases b' <;> fin_cases f₁ <;> fin_cases f₂ <;>
    simp [Fin.sum_univ_two, h0, h1, tau, Cmat, cDiag_eq, cOff_eq] <;> norm_num

/-- The scalar identity of `refineAmp_tau_sum`, with the bond matrix of the outer
bits carried along. -/
lemma refineAmp_Cmat_sum (k b b' f₁ f₂ L L' : Fin 2) :
    ∑ ε : Fin 2,
        refineAmp ε ^ 2 * tau ε b * tau ε b' * (Cmat k L L' * tau k (f₁ + f₂ + ε) / 2) =
      Cmat k L L' * tau k f₁ / 2 * (Cmat k b b' * tau k f₂ / 2) := by
  have h := refineAmp_tau_sum k b b' f₁ f₂
  rw [Fin.sum_univ_two] at h ⊢
  linear_combination (Cmat k L L' / 2) * h

/-! ### The refinement Kraus family -/

/-- The support condition of the refinement Kraus operators: the outer bits and
the flags of the two-site letter are prescribed by the one-site letter and the
Kraus label, the two-site letter satisfies the bond-matching condition, and the
one-site flag is the sum of the two prepared flags and the bond label. -/
def IsRefineSupported (f₁ f₂ ε : Fin 2) (i : Fin 8 × Fin 8) (j : Fin 8) : Prop :=
  ((bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j)) ∧
    (gate i.1 i.2 ∧ bitF j = f₁ + f₂ + ε)

instance decidableIsRefineSupported (f₁ f₂ ε : Fin 2) (i : Fin 8 × Fin 8) (j : Fin 8) :
    Decidable (IsRefineSupported f₁ f₂ ε i j) :=
  inferInstanceAs (Decidable (((_ ∧ _) ∧ (_ ∧ _)) ∧ (_ ∧ _)))

/-- The support condition, read as a condition on the one-site letter for a
fixed two-site letter. -/
lemma isRefineSupported_iff_col (f₁ f₂ ε : Fin 2) (i : Fin 8 × Fin 8) (j : Fin 8) :
    IsRefineSupported f₁ f₂ ε i j ↔
      (gate i.1 i.2 ∧ bitF i.1 = f₁ ∧ bitF i.2 = f₂) ∧
        (bitF j = f₁ + f₂ + ε ∧ bitL j = bitL i.1 ∧ bitR j = bitR i.2) := by
  simp only [IsRefineSupported]
  constructor
  · rintro ⟨⟨⟨hf₁, hl⟩, hf₂, hr⟩, hg, hf⟩
    exact ⟨⟨hg, hf₁, hf₂⟩, hf, hl.symm, hr.symm⟩
  · rintro ⟨⟨hg, hf₁, hf₂⟩, hf, hl, hr⟩
    exact ⟨⟨⟨hf₁, hl.symm⟩, hf₂, hr.symm⟩, hg, hf⟩

/-- The Kraus operator of the refinement channel at the label
$(f_1, f_2, \varepsilon)$: it prepares the flags $f_1, f_2$ on the two output
sites and the bond state labelled by $\varepsilon$, with the bond sign
$(-1)^{\varepsilon b}$ at the shared bond bit `b`. -/
def refineKraus (f₁ f₂ ε : Fin 2) : Matrix (Fin 8 × Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j =>
    if IsRefineSupported f₁ f₂ ε i j then ((refineAmp ε * tau ε (bitR i.1) : ℝ) : ℂ) else 0

/-- The refinement map, from one-site to two-site physical operators. -/
def refineMap :
    Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 8 × Fin 8) (Fin 8 × Fin 8) ℂ :=
  Matrix.rectangularKrausMap fun t : Fin 2 × Fin 2 × Fin 2 => refineKraus t.1 t.2.1 t.2.2

/-- The refinement Kraus entries are real. -/
lemma refineKraus_star (f₁ f₂ ε : Fin 2) (i : Fin 8 × Fin 8) (j : Fin 8) :
    star (refineKraus f₁ f₂ ε i j) = refineKraus f₁ f₂ ε i j := by
  simp only [refineKraus, Matrix.of_apply]
  split_ifs
  · exact Complex.conj_ofReal _
  · exact star_zero _

/-- Contracting a refinement Kraus operator against a one-site vector selects
the single one-site letter in its support. -/
lemma refineKraus_col_sum (f₁ f₂ ε : Fin 2) (i : Fin 8 × Fin 8) (g : Fin 8 → ℂ) :
    (∑ j : Fin 8, refineKraus f₁ f₂ ε i j * g j) =
      if gate i.1 i.2 ∧ bitF i.1 = f₁ ∧ bitF i.2 = f₂ then
        ((refineAmp ε * tau ε (bitR i.1) : ℝ) : ℂ) *
          g (physIdx (bitL i.1) (bitR i.2) (f₁ + f₂ + ε))
      else 0 := by
  by_cases hi : gate i.1 i.2 ∧ bitF i.1 = f₁ ∧ bitF i.2 = f₂
  · rw [ite_eq_left hi]
    have hcongr : ∀ j : Fin 8, refineKraus f₁ f₂ ε i j * g j =
        if bitF j = f₁ + f₂ + ε ∧ bitL j = bitL i.1 ∧ bitR j = bitR i.2 then
          ((refineAmp ε * tau ε (bitR i.1) : ℝ) : ℂ) * g j else 0 := by
      intro j
      simp only [refineKraus, Matrix.of_apply]
      by_cases hj : bitF j = f₁ + f₂ + ε ∧ bitL j = bitL i.1 ∧ bitR j = bitR i.2
      · rw [ite_eq_left ((isRefineSupported_iff_col f₁ f₂ ε i j).2 ⟨hi, hj⟩), ite_eq_left hj]
      · rw [ite_eq_right fun hc => hj ((isRefineSupported_iff_col f₁ f₂ ε i j).1 hc).2,
          ite_eq_right hj, zero_mul]
    rw [Finset.sum_congr rfl fun j _ => hcongr j]
    exact one_site_fiber_sum _ _ _ _
  · rw [ite_eq_right hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [refineKraus, Matrix.of_apply]
    rw [ite_eq_right fun hc => hi ((isRefineSupported_iff_col f₁ f₂ ε i j).1 hc).1, zero_mul]

/-- Summing over the two-site letters in the support of a refinement Kraus
operator leaves the two gated fibre points. -/
lemma refineKraus_row_sum (f₁ f₂ ε : Fin 2) (j : Fin 8) (g : Fin 8 × Fin 8 → ℂ) :
    (∑ i : Fin 8 × Fin 8, if IsRefineSupported f₁ f₂ ε i j then g i else 0) =
      if bitF j = f₁ + f₂ + ε then
        g (physIdx (bitL j) 0 f₁, physIdx 0 (bitR j) f₂) +
          g (physIdx (bitL j) 1 f₁, physIdx 1 (bitR j) f₂)
      else 0 := by
  have hcongr : ∀ i : Fin 8 × Fin 8, (if IsRefineSupported f₁ f₂ ε i j then g i else 0) =
      if (bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j) then
        (if gate i.1 i.2 ∧ bitF j = f₁ + f₂ + ε then g i else 0) else 0 := by
    intro i
    by_cases h1 : (bitF i.1 = f₁ ∧ bitL i.1 = bitL j) ∧ (bitF i.2 = f₂ ∧ bitR i.2 = bitR j)
    · rw [ite_eq_left h1]
      by_cases h2 : gate i.1 i.2 ∧ bitF j = f₁ + f₂ + ε
      · rw [ite_eq_left h2, ite_eq_left (show IsRefineSupported f₁ f₂ ε i j from ⟨h1, h2⟩)]
      · rw [ite_eq_right h2, ite_eq_right fun hc => h2 hc.2]
    · rw [ite_eq_right h1, ite_eq_right fun hc => h1 hc.1]
  rw [Finset.sum_congr rfl fun i _ => hcongr i, pair_fiber_sum]
  by_cases hf : bitF j = f₁ + f₂ + ε
  · rw [ite_eq_left hf]
    simp [Fin.sum_univ_two, gate, hf]
  · rw [ite_eq_right hf]
    simp [gate, hf]

/-- **The refinement Kraus family resolves the identity.** -/
theorem refineKraus_resolution :
    ∑ t : Fin 2 × Fin 2 × Fin 2,
        (refineKraus t.1 t.2.1 t.2.2)ᴴ * refineKraus t.1 t.2.1 t.2.2 =
      (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  have h0 : ((refineAmp 0 : ℝ) : ℂ) ^ 2 = 7 / 32 := by
    rw [← Complex.ofReal_pow, refineAmp_sq]
    norm_num [bondWeight, x]
  have h1 : ((refineAmp 1 : ℝ) : ℂ) ^ 2 = 1 / 32 := by
    rw [← Complex.ofReal_pow, refineAmp_sq]
    norm_num [bondWeight, y]
  ext j j'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hjj : j = j'
  · subst hjj
    rw [Matrix.one_apply_eq]
    have hstep : ∀ t : Fin 2 × Fin 2 × Fin 2,
        (∑ i : Fin 8 × Fin 8, star (refineKraus t.1 t.2.1 t.2.2 i j) *
            refineKraus t.1 t.2.1 t.2.2 i j) =
          if bitF j = t.1 + t.2.1 + t.2.2 then ((2 * refineAmp t.2.2 ^ 2 : ℝ) : ℂ) else 0 := by
      rintro ⟨f₁, f₂, ε⟩
      have hcongr : ∀ i : Fin 8 × Fin 8,
          star (refineKraus f₁ f₂ ε i j) * refineKraus f₁ f₂ ε i j =
            if IsRefineSupported f₁ f₂ ε i j then ((refineAmp ε ^ 2 : ℝ) : ℂ) else 0 := by
        intro i
        rw [refineKraus_star]
        simp only [refineKraus, Matrix.of_apply]
        split_ifs
        · rw [← Complex.ofReal_mul]
          congr 1
          have := tau_mul_self ε (bitR i.1)
          nlinarith [this]
        · exact mul_zero _
      rw [Finset.sum_congr rfl fun i _ => hcongr i, refineKraus_row_sum]
      by_cases hf : bitF j = f₁ + f₂ + ε
      · rw [ite_eq_left hf, ite_eq_left hf]
        push_cast
        ring
      · rw [ite_eq_right hf, ite_eq_right hf]
    rw [Finset.sum_congr rfl fun t _ => hstep t]
    have hcase : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hcase (bitF j) with hb | hb <;>
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hb, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_ofNat] <;>
      norm_num [h0, h1, show (1 : Fin 2) + 1 = 0 from rfl, show (1 : Fin 2) + 1 + 1 = 1 from rfl]
  · rw [Matrix.one_apply_ne hjj]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => ?_
    simp only [refineKraus, Matrix.of_apply]
    by_cases h : IsRefineSupported t.1 t.2.1 t.2.2 i j
    · have h' : ¬ IsRefineSupported t.1 t.2.1 t.2.2 i j' := by
        rintro h2
        exact hjj (eq_of_bits (h.1.1.2.symm.trans h2.1.1.2)
          (h.1.2.2.symm.trans h2.1.2.2) (h.2.2.trans h2.2.2.symm))
      rw [ite_eq_right h', mul_zero]
    · rw [ite_eq_right h, star_zero, zero_mul]

/-- **The refinement map is trace-preserving completely positive.** -/
theorem refineMap_isKrausCPTP : IsKrausCPTP refineMap :=
  Matrix.rectangularKrausMap_isKrausCPTP _ refineKraus_resolution

/-! ### The refinement map on the physical closures -/

/-- Summing over the Kraus labels whose flags are prescribed leaves a sum over
the bond label. -/
lemma sum_flag_selector (F₁ F₂ : Fin 2) (V : Fin 2 × Fin 2 × Fin 2 → ℂ) :
    (∑ t : Fin 2 × Fin 2 × Fin 2, if t.1 = F₁ ∧ t.2.1 = F₂ then V t else 0) =
      ∑ ε : Fin 2, V (F₁, F₂, ε) := by
  fin_cases F₁ <;> fin_cases F₂ <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two]

/-- One Kraus term of the refinement map, evaluated at a pair of two-site
letters. -/
lemma refineKraus_conj_term (f₁ f₂ ε : Fin 2) (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (i₁ i₂ j₁ j₂ : Fin 8) :
    (∑ a' : Fin 8, (∑ a : Fin 8, refineKraus f₁ f₂ ε (i₁, i₂) a * Y a a') *
        star (refineKraus f₁ f₂ ε (j₁, j₂) a')) =
      if (gate i₁ i₂ ∧ bitF i₁ = f₁ ∧ bitF i₂ = f₂) ∧
          (gate j₁ j₂ ∧ bitF j₁ = f₁ ∧ bitF j₂ = f₂) then
        ((refineAmp ε ^ 2 * tau ε (bitR i₁) * tau ε (bitR j₁) : ℝ) : ℂ) *
          Y (physIdx (bitL i₁) (bitR i₂) (f₁ + f₂ + ε))
            (physIdx (bitL j₁) (bitR j₂) (f₁ + f₂ + ε))
      else 0 := by
  have hinner : ∀ a' : Fin 8, (∑ a : Fin 8, refineKraus f₁ f₂ ε (i₁, i₂) a * Y a a') =
      if gate i₁ i₂ ∧ bitF i₁ = f₁ ∧ bitF i₂ = f₂ then
        ((refineAmp ε * tau ε (bitR i₁) : ℝ) : ℂ) *
          Y (physIdx (bitL i₁) (bitR i₂) (f₁ + f₂ + ε)) a' else 0 :=
    fun a' => refineKraus_col_sum f₁ f₂ ε (i₁, i₂) fun a => Y a a'
  rw [Finset.sum_congr rfl fun a' _ => by rw [hinner a']]
  by_cases hi : gate i₁ i₂ ∧ bitF i₁ = f₁ ∧ bitF i₂ = f₂
  · rw [Finset.sum_congr rfl fun a' _ => by
      rw [ite_eq_left hi, refineKraus_star, mul_comm]]
    rw [refineKraus_col_sum f₁ f₂ ε (j₁, j₂)]
    by_cases hj : gate j₁ j₂ ∧ bitF j₁ = f₁ ∧ bitF j₂ = f₂
    · rw [ite_eq_left hj, ite_eq_left ⟨hi, hj⟩]
      push_cast
      ring
    · rw [ite_eq_right hj, ite_eq_right fun hc => hj hc.2]
  · rw [ite_eq_right fun hc => hi hc.1]
    exact Finset.sum_eq_zero fun a' _ => by rw [ite_eq_right hi, zero_mul]

/-- **The refinement map carries the one-site physical closure of the twisted
dimer to its two-site physical closure.**  Together with
`refineMap_isKrausCPTP`, this is the map `T` of arXiv:1606.00608,
Definition 4.1 (paper label eq:Tmap). -/
theorem refineMap_physClose1 (X : Matrix (Fin 8) (Fin 8) ℂ) :
    refineMap (physClose1 T X) = physClose2 T X := by
  ext ii jj
  obtain ⟨i₁, i₂⟩ := ii
  obtain ⟨j₁, j₂⟩ := jj
  rw [physClose2_T]
  change (∑ t : Fin 2 × Fin 2 × Fin 2, refineKraus t.1 t.2.1 t.2.2 * physClose1 T X *
      (refineKraus t.1 t.2.1 t.2.2)ᴴ) (i₁, i₂) (j₁, j₂) = _
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_congr rfl fun t _ =>
    refineKraus_conj_term t.1 t.2.1 t.2.2 (physClose1 T X) i₁ i₂ j₁ j₂]
  by_cases hg : gate i₁ i₂ ∧ gate j₁ j₂
  · rw [ite_eq_left hg]
    by_cases e : bitF i₁ = bitF j₁ ∧ bitF i₂ = bitF j₂
    · have hiff : ∀ t : Fin 2 × Fin 2 × Fin 2,
          (((gate i₁ i₂ ∧ bitF i₁ = t.1 ∧ bitF i₂ = t.2.1) ∧
            (gate j₁ j₂ ∧ bitF j₁ = t.1 ∧ bitF j₂ = t.2.1)) ↔
              (t.1 = bitF i₁ ∧ t.2.1 = bitF i₂)) := by
        intro t
        constructor
        · rintro ⟨⟨_, h1, h2⟩, _⟩
          exact ⟨h1.symm, h2.symm⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨hg.1, h1.symm, h2.symm⟩, hg.2, by rw [← e.1, h1], by rw [← e.2, h2]⟩
      simp only [hiff]
      rw [sum_flag_selector]
      have hval : ∀ ε : Fin 2,
          ((refineAmp ε ^ 2 * tau ε (bitR i₁) * tau ε (bitR j₁) : ℝ) : ℂ) *
              physClose1 T X (physIdx (bitL i₁) (bitR i₂) (bitF i₁ + bitF i₂ + ε))
                (physIdx (bitL j₁) (bitR j₂) (bitF i₁ + bitF i₂ + ε)) =
            ∑ k : Fin 2,
              ((refineAmp ε ^ 2 * tau ε (bitR i₁) * tau ε (bitR j₁) *
                (Cmat k (bitL i₁) (bitL j₁) * tau k (bitF i₁ + bitF i₂ + ε) / 2) : ℝ) : ℂ) *
                X (physIdx (bitR i₂) (bitR j₂) k) (physIdx (bitL i₁) (bitL j₁) k) := by
        intro ε
        rw [physClose1_T_bits, ite_eq_left rfl, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [Finset.sum_congr rfl fun ε _ => hval ε, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, refineAmp_Cmat_sum]
      have hb : bitL i₂ = bitR i₁ := Eq.symm hg.1
      have hb' : bitL j₂ = bitR j₁ := Eq.symm hg.2
      have hc1 : coef k i₁ j₁ = ((Cmat k (bitL i₁) (bitL j₁) * tau k (bitF i₁) / 2 : ℝ) : ℂ) := by
        rw [coef, ite_eq_left e.1]
      have hc2 : coef k i₂ j₂ = ((Cmat k (bitR i₁) (bitR j₁) * tau k (bitF i₂) / 2 : ℝ) : ℂ) := by
        rw [coef, ite_eq_left e.2, hb, hb']
      rw [hc1, hc2]
      push_cast
      ring
    · have hzero : ∀ t : Fin 2 × Fin 2 × Fin 2,
          ¬ ((gate i₁ i₂ ∧ bitF i₁ = t.1 ∧ bitF i₂ = t.2.1) ∧
            (gate j₁ j₂ ∧ bitF j₁ = t.1 ∧ bitF j₂ = t.2.1)) := by
        rintro t ⟨⟨_, h1, h2⟩, _, h1', h2'⟩
        exact e ⟨h1.trans h1'.symm, h2.trans h2'.symm⟩
      rw [Finset.sum_congr rfl fun t _ => ite_eq_right (hzero t), Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rcases not_and_or.mp e with h | h
      · rw [coef, ite_eq_right h, zero_mul, zero_mul]
      · rw [coef, coef, ite_eq_right h, mul_zero, zero_mul]
  · rw [ite_eq_right hg]
    refine Finset.sum_eq_zero fun t _ => ite_eq_right fun hc => hg ⟨hc.1.1, hc.2.1⟩

end MPOTensor.TwistedDimer

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LengthIndependentCoefficients

/-!
# A candidate two-label coefficient family

**Scope: abstract coefficient family only.** Motivated by the proposed
$\mathbb Z_2$-twisted quantum dimer, this file defines a two-label diagonal
$\chi$-family and proves that its trace-power coefficients remain length
dependent after every positive rescaling of the labels. It does not identify
these labels with basis-of-normal-tensors blocks of a tensor; the same-length
product law attaching this family to the flag-sector operators of the twisted
dimer is proved in `TNLean.MPS.MPDO.TwistedDimerProductLaw`.

For bond weights $x, y > 0$ with $x + y = 1$, the candidate weights are
$$
  \alpha = \frac{x}{\sqrt{2(x^2+y^2)}},\qquad
  \beta = \frac{y}{\sqrt{2(x^2+y^2)}} .
$$
At the rational point $x = 7/8$, $y = 1/8$ one has $\alpha = 7/10$ and
$\beta = 1/10$, which is the abstract instance formalized here.

## Main results

* `twoLabelChi` — the diagonal $\chi$-family with the single entry $\alpha$ on the
  channel $g = f + f'$ and $\beta$ on the channel $g = f + f' + 1$;
* `twoLabelCoeffs_coeff` — $c^{(L)}_{f f' g} = \alpha^L$ or $\beta^L$;
* `twoLabelCoeffs_not_lengthIndependent` — the family depends on the length;
* `twoLabelCoeffs_rescaling_stable_not_lengthIndependent` — for every pair of
  positive block rescalings $(s_0, s_1)$, the rescaled family
  $(s_f s_{f'} / s_g)^L c^{(L)}_{f f' g}$ still depends on the length.  The proof
  is the inconsistency of the system $s_f s_{f'} \chi_{f f' g} = s_g$: the
  triples $(0,0,0)$ and $(0,1,0)$ force $s_0 = 1/\alpha$ and $s_1 = 1/\beta$,
  after which the triple $(0,0,1)$ demands $\beta^2 = \alpha^2$.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and lines 995--1010 (the length-dependence question; the
  coefficient family is a project example)
-/

open scoped BigOperators

noncomputable section

namespace MPOTensor.TwistedDimer

/-- The **fusion-channel condition** on three flag labels: the outgoing label
$g$ is the sum $f + f'$ of the two incoming ones, as opposed to its complement
$f + f' + 1$. -/
def IsSameChannel (f f' g : Fin 2) : Prop := g = f + f'

/-- The fusion-channel condition is an equality of flag labels, hence
decidable. -/
instance decidableIsSameChannel (f f' g : Fin 2) : Decidable (IsSameChannel f f' g) :=
  inferInstanceAs (Decidable (g = f + f'))

/-- The fusion weight $\alpha = 7/10$ on the channel $g = f + f'$ (rational point
$x = 7/8$, $y = 1/8$). -/
def alpha : ℝ := 7 / 10

/-- The fusion weight $\beta = 1/10$ on the channel $g = f + f' + 1$. -/
def beta : ℝ := 1 / 10

/-- The candidate two-label diagonal $\chi$-family: every $\chi_{f f' g}$ is a
$1 \times 1$ block with entry $\alpha$ or $\beta$. No tensor attachment is
asserted. -/
def twoLabelChi : DiagonalChiFamily (Fin 2) where
  dim _ _ _ := 1
  entry f f' g _ := if IsSameChannel f f' g then (alpha : ℂ) else (beta : ℂ)

lemma twoLabelChi_posEntries : twoLabelChi.PosEntries := by
  intro f f' g k
  by_cases h : IsSameChannel f f' g
  · simp only [twoLabelChi, h, ite_true]
    exact Complex.zero_lt_real.mpr (by norm_num [alpha])
  · simp only [twoLabelChi, h, ite_false]
    exact Complex.zero_lt_real.mpr (by norm_num [beta])

/-- The coefficient family $c^{(L)}_{f f' g} = \operatorname{tr}(\chi_{f f' g}^L)$. -/
def twoLabelCoeffs : BNTLabelCoefficientFamily (Fin 2) :=
  BNTLabelCoefficientFamily.ofChi twoLabelChi

theorem twoLabelCoeffs_coeff (L : ℕ) (f f' g : Fin 2) :
    twoLabelCoeffs.coeff L f f' g =
      if IsSameChannel f f' g then (alpha : ℂ) ^ L else (beta : ℂ) ^ L := by
  dsimp [twoLabelCoeffs, BNTLabelCoefficientFamily.ofChi,
    DiagonalChiFamily.tracePowerCoeff, twoLabelChi]
  by_cases h : IsSameChannel f f' g <;> simp [h]

/-- The channel-$\alpha$ coefficient $(7/10)^L$ differs between lengths one and two. -/
theorem twoLabelCoeffs_not_lengthIndependent : ¬ twoLabelCoeffs.LengthIndependent := by
  intro h
  have := h.coeff_eq one_pos (by norm_num : (0 : ℕ) < 2) 0 0 0
  rw [twoLabelCoeffs_coeff, twoLabelCoeffs_coeff] at this
  have hs : IsSameChannel 0 0 0 := by decide
  simp only [hs, ite_true, alpha] at this
  norm_num at this

/-- The rescaled candidate $\chi$-family. Abstract label rescalings act by
$\chi_{f f' g} \mapsto (s_f s_{f'} / s_g)\,\chi_{f f' g}$, matching the
covariance of Theorem 4.14(iii) under the normalization freedom of Proposition
4.12 in arXiv:1606.00608. -/
def twoLabelChiScaled (s : Fin 2 → ℝ) : DiagonalChiFamily (Fin 2) where
  dim _ _ _ := 1
  entry f f' g _ :=
    ((s f * s f' / s g : ℝ) : ℂ) * (if IsSameChannel f f' g then (alpha : ℂ) else (beta : ℂ))

/-- The coefficient family of the rescaled candidate data. -/
def rescaledCoeffs (s : Fin 2 → ℝ) : BNTLabelCoefficientFamily (Fin 2) :=
  BNTLabelCoefficientFamily.ofChi (twoLabelChiScaled s)

theorem rescaledCoeffs_coeff (s : Fin 2 → ℝ) (L : ℕ) (f f' g : Fin 2) :
    (rescaledCoeffs s).coeff L f f' g =
      (((s f * s f' / s g : ℝ) : ℂ) *
        (if IsSameChannel f f' g then (alpha : ℂ) else (beta : ℂ))) ^ L := by
  dsimp [rescaledCoeffs, BNTLabelCoefficientFamily.ofChi,
    DiagonalChiFamily.tracePowerCoeff, twoLabelChiScaled]
  simp

/-- A positive real with $t = t^2$ equals one. -/
private lemma eq_one_of_pos_of_sq_eq {t : ℝ} (ht : 0 < t) (h : t = t ^ 2) : t = 1 := by
  nlinarith

/-- **Rescaling-stable length dependence.** For every pair of positive block
rescalings $(s_0, s_1)$ the rescaled two-label family is not length independent.
Length independence would force $s_0\alpha = 1$ (triple $(0,0,0)$),
$s_1\beta = 1$ (triple $(0,1,0)$) and $s_0^2\beta/s_1 = 1$ (triple $(0,0,1)$),
hence $\beta^2 = \alpha^2$, contradicting $\alpha = 7/10 \ne 1/10 = \beta$.

Source: arXiv:1606.00608, Theorem 4.14 and lines 995--1010 (the
length-dependence question); this abstract coefficient family is a project
example and is not attached here to a tensor. -/
theorem twoLabelCoeffs_rescaling_stable_not_lengthIndependent (s : Fin 2 → ℝ)
    (hs : ∀ f, 0 < s f) : ¬ (rescaledCoeffs s).LengthIndependent := by
  intro hLI
  have h0 := hs 0
  have h1 := hs 1
  -- a positive-length coefficient equal at lengths 1 and 2 is a real number t with t = t^2
  have key : ∀ f f' g : Fin 2,
      (s f * s f' / s g) * (if IsSameChannel f f' g then alpha else beta) = 1 := by
    intro f f' g
    have e := hLI.coeff_eq (show (0 : ℕ) < 2 by norm_num) (show (0 : ℕ) < 1 by norm_num) f f' g
    rw [rescaledCoeffs_coeff, rescaledCoeffs_coeff] at e
    have hq : 0 < s f * s f' / s g := div_pos (mul_pos (hs f) (hs f')) (hs g)
    have hw : 0 < (if IsSameChannel f f' g then alpha else beta) := by
      split_ifs <;> norm_num [alpha, beta]
    set t : ℝ := (s f * s f' / s g) * (if IsSameChannel f f' g then alpha else beta) with ht
    have et : ((t : ℝ) : ℂ) ^ 2 = ((t : ℝ) : ℂ) ^ 1 := by
      rw [ht]
      push_cast
      split_ifs at e ⊢ <;> simpa using e
    rw [pow_one] at et
    have et' : t ^ 2 = t := by exact_mod_cast et
    have htpos : 0 < t := mul_pos hq hw
    exact eq_one_of_pos_of_sq_eq htpos et'.symm
  have e000 := key 0 0 0
  have e010 := key 0 1 0
  have e001 := key 0 0 1
  have hs000 : IsSameChannel 0 0 0 := by decide
  have hs010 : ¬ IsSameChannel 0 1 0 := by decide
  have hs001 : ¬ IsSameChannel 0 0 1 := by decide
  simp only [hs000, hs010, hs001, ite_true, ite_false] at e000 e010 e001
  -- e000 : s 0 * s 0 / s 0 * alpha = 1, e010 : s 0 * s 1 / s 0 * beta = 1,
  -- e001 : s 0 * s 0 / s 1 * beta = 1
  have h0ne : s 0 ≠ 0 := h0.ne'
  have h1ne : s 1 ≠ 0 := h1.ne'
  have a0 : s 0 * alpha = 1 := by
    field_simp at e000
    linarith [e000]
  have a1 : s 1 * beta = 1 := by
    field_simp at e010
    linarith [e010]
  have a2 : s 0 ^ 2 * beta = s 1 := by
    field_simp at e001
    linarith [e001]
  simp only [alpha, beta] at a0 a1 a2
  nlinarith [a0, a1, a2]

end MPOTensor.TwistedDimer

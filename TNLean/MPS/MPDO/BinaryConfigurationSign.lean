/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The binary $Z$-string sign calculus

A binary configuration $\sigma : \{0,\dots,N-1\} \to \{0,1\}$ carries the sign
\[
  \prod_{k} z_{\sigma_k}, \qquad z_0 = 1,\ z_1 = -1,
\]
the eigenvalue of $\sigma_z^{\otimes N}$ on the computational basis vector
$\lvert \sigma \rangle$.  The site weight $z_a$ is the diagonal entry
$(\sigma_z)_{aa}$ of the Pauli matrix.

This sign is the whole content of the diagonal $\rho^{(N)} = I^{\otimes N} +
\sigma_z^{\otimes N}$ family: it takes only the values $\pm 1$, it sums to zero
over the binary configurations of any positive length, and it is multiplicative
under concatenation of configurations.  Those three facts are what turn the
reduced state of a proper block into a maximally mixed state.

## Main contents

* `MPOTensor.siteSign` — the one-site weight $z_a = (\sigma_z)_{aa}$.
* `MPOTensor.configurationSign` — the $Z$-string sign of a configuration.
* `MPOTensor.configurationSign_eq_one_or_neg_one` — the sign is $\pm 1$.
* `MPOTensor.sum_configurationSign_eq_zero` — the sign sums to zero over all
  binary configurations of positive length.
* `MPOTensor.configurationSign_append` and
  `MPOTensor.configurationSign_append_cast` — multiplicativity under
  concatenation.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Example 4.12,
  lines 932--939.
* K. Kato, *Exact renormalization group flow for matrix product density
  operators*, arXiv:2410.22696, lines 712--721.
-/

open scoped BigOperators

namespace MPOTensor

/-- The sign carried by one physical letter: the diagonal entry
$(\sigma_z)_{aa}$ of the Pauli matrix, so $z_0 = 1$ and $z_1 = -1$. -/
noncomputable def siteSign (i : Fin 2) : ℂ :=
  SpinCover.pauli 2 i i

/-- The eigenvalue of $\sigma_z^{\otimes N}$ on a binary configuration:
the product of the site signs along the configuration. -/
noncomputable def configurationSign {N : ℕ} (σ : Fin N → Fin 2) : ℂ :=
  ∏ k, siteSign (σ k)

/-- The site sign takes only the values $1$ and $-1$. -/
lemma siteSign_eq_one_or_neg_one (i : Fin 2) :
    siteSign i = 1 ∨ siteSign i = -1 := by
  fin_cases i <;> simp [siteSign, SpinCover.pauli]

/-- The configuration sign takes only the values $1$ and $-1$. -/
lemma configurationSign_eq_one_or_neg_one {N : ℕ} (σ : Fin N → Fin 2) :
    configurationSign σ = 1 ∨ configurationSign σ = -1 := by
  induction N with
  | zero =>
      left
      simp [configurationSign]
  | succ N ih =>
      have hprod :
          configurationSign σ =
            siteSign (σ 0) * configurationSign (σ ∘ Fin.succ) := by
        rw [configurationSign, Fin.prod_univ_succ]
        rfl
      rw [hprod]
      rcases siteSign_eq_one_or_neg_one (σ 0) with hhead | hhead
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · left
          rw [hhead, htail, one_mul]
        · right
          rw [hhead, htail, one_mul]
      · rcases ih (σ ∘ Fin.succ) with htail | htail
        · right
          rw [hhead, htail, neg_one_mul]
        · left
          rw [hhead, htail]
          norm_num

/-- The site-sum vanishes: $\sum_{a=0,1} z_a = 1 + (-1) = 0$. -/
lemma sum_siteSign_eq_zero : (∑ a : Fin 2, siteSign a) = (0 : ℂ) := by
  calc
    (∑ a : Fin 2, siteSign a) = siteSign 0 + siteSign 1 := Fin.sum_univ_two _
    _ = (1 : ℂ) + (-1 : ℂ) := by simp [siteSign, SpinCover.pauli]
    _ = 0 := by ring

/-- The configuration sign sums to zero over all binary words of positive
length $n$.  This is the distributive-law identity
$\sum_{w} \prod_k z_{w_k} = \prod_k \sum_a z_a = 0^n$. -/
lemma sum_configurationSign_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ w : Fin n → Fin 2, configurationSign w = 0 := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  calc
    ∑ w : Fin n → Fin 2, configurationSign w
        = ∑ w : Fin n → Fin 2, (∏ k : Fin n, siteSign (w k)) := rfl
    _ = ∑ w ∈ (Fintype.piFinset fun (_ : Fin n) => (Finset.univ : Finset (Fin 2))),
        (∏ k : Fin n, siteSign (w k)) := by simp [Fintype.piFinset_univ]
    _ = ∏ k : Fin n, (∑ a ∈ (Finset.univ : Finset (Fin 2)), siteSign a) := by
      rw [← Finset.prod_univ_sum (fun (_ : Fin n) => (Finset.univ : Finset (Fin 2)))
        (fun (_ : Fin n) a => siteSign a)]
    _ = ∏ k : Fin n, (∑ a : Fin 2, siteSign a) := by simp
    _ = ∏ k : Fin n, (0 : ℂ) := by rw [sum_siteSign_eq_zero]
    _ = 0 := by
      rw [Finset.prod_const, Finset.card_univ, hcard]
      exact zero_pow hn.ne'

/-- The configuration sign factorises through `Fin.append`:
$\operatorname{sign}(u \mathbin{+\!\!+} w) =
  \operatorname{sign}(u) \cdot \operatorname{sign}(w)$. -/
lemma configurationSign_append {L M : ℕ}
    (u : Fin L → Fin 2) (w : Fin M → Fin 2) :
    configurationSign (Fin.append u w) = configurationSign u * configurationSign w := by
  rw [configurationSign, configurationSign, configurationSign]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The configuration sign is invariant under the canonical bijection
$\operatorname{Fin} N \simeq \operatorname{Fin}(L+M)$ given by $h_N : N = L+M$,
so that $\operatorname{sign}((u \mathbin{+\!\!+} w) \circ e_{h_N}) =
\operatorname{sign}(u) \cdot \operatorname{sign}(w)$. -/
lemma configurationSign_append_cast {L M N : ℕ} (hN : N = L + M)
    (u : Fin L → Fin 2) (w : Fin M → Fin 2) :
    configurationSign (Fin.append u w ∘ Fin.cast hN) =
      configurationSign u * configurationSign w := by
  subst hN
  simp [configurationSign_append]

end MPOTensor

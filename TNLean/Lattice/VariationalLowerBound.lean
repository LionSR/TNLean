/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Permutation
import TNLean.Algebra.PermutationMatrixUnitary

/-!
# A variational lower bound on the ground energy

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, eq. `varnum`, lines 856–877): for a translation
invariant Hamiltonian `H = ∑_i H_i` on `N` sites, with all `H_i` translates of one another,
`E₀/N ≥ λ_min(H_i + i a₁ [H_i, H] + a₂ [[H_i, H], H] + ⋯)` for all real constants `a_k`.
The commutator terms sum to zero over the translates, because `∑_i [H_i, H] = [H, H] = 0`, and
the ground energy of a sum of terms is at least the sum of their lowest eigenvalues.

The bound is stated here without reference to a lattice. The terms are the conjugates
`U_i H₀ U_i†` of one operator `H₀` by unitaries that commute with their sum `H`, and the
commutator series is `K = H₀ + ∑_{k=1}^{m} a_k iᵏ ad_Hᵏ(H₀)`, with `ad_H(X) = H X − X H`.
The source's `[H_i, H] = −ad_H(H_i)`, so its constants differ from the `a_k` here only by signs.
`λ_min(K)` is the largest `λ` with `K − λ ≥ 0`, so the statement for every such `λ` is the
source's bound. On a finite graph, or any finite set of sites, a finite group `G` acting on the
sites gives such unitaries by permuting the sites; `E₀/|G| ≥ λ_min(K)` then holds with `N = |G|`
the number of translates.

Lines 1005–1009 of the source record that the filtered terms `H̃ᵢ⁰` are one choice of the
constants `a_k`; that instance is not part of this file.

## Main definitions

* `Matrix.commutatorIter H A k`: the iterated commutator `ad_Hᵏ(A)`.
* `Matrix.sitePermMatrix`: the permutation of the configurations of finitely many sites induced by
  a group element acting on the sites.

## Main results

* `Matrix.isHermitian_smul_commutatorIter`: `a iᵏ ad_Hᵏ(A)` is Hermitian for Hermitian `H`, `A`
  and real `a`.
* `Matrix.posSemidef_sub_card_smul_of_conj`: the bound for the conjugates by unitaries.
* `Matrix.card_mul_le_of_mulVec_eq_smul_of_conj`: the same as a lower bound on every eigenvalue.
* `Matrix.card_mul_le_of_mulVec_eq_smul_of_sitePerm`: the bound for the translates of a local
  term under a finite group acting on the sites.
-/

open Matrix Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The iterated commutator `ad_Hᵏ(A)`, with `ad_H(X) = H X − X H`. This is
`(LieAlgebra.ad ℂ _ H ^ k) A` for the commutator Lie bracket; it is defined by recursion here
because `Matrix n n ℂ` carries no `LieRing` instance. -/
def commutatorIter (H A : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => A
  | k + 1 => H * commutatorIter H A k - commutatorIter H A k * H

@[simp] theorem commutatorIter_zero (H A : Matrix n n ℂ) : commutatorIter H A 0 = A := rfl

theorem commutatorIter_succ (H A : Matrix n n ℂ) (k : ℕ) :
    commutatorIter H A (k + 1) = H * commutatorIter H A k - commutatorIter H A k * H := rfl

/-- `(ad_Hᵏ A)† = (−1)ᵏ ad_Hᵏ(A†)` for Hermitian `H`. -/
theorem conjTranspose_commutatorIter {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    (k : ℕ) : (commutatorIter H A k)ᴴ = ((-1 : ℂ) ^ k) • commutatorIter H Aᴴ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [commutatorIter_succ, commutatorIter_succ, conjTranspose_sub, conjTranspose_mul,
      conjTranspose_mul, ih, hH.eq, smul_mul_assoc, mul_smul_comm, pow_succ, mul_neg_one,
      neg_smul, smul_sub]
    abel

/-- For Hermitian `H`, `A` and real `a`, the operator `a iᵏ ad_Hᵏ(A)` is Hermitian. -/
theorem isHermitian_smul_commutatorIter {H A : Matrix n n ℂ} (hH : H.IsHermitian)
    (hA : A.IsHermitian) (a : ℝ) (k : ℕ) :
    (((a : ℂ) * Complex.I ^ k) • commutatorIter H A k).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, conjTranspose_commutatorIter hH, hA.eq, smul_smul]
  congr 1
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal, star_pow, Complex.conj_I]
  rw [mul_assoc, ← mul_pow]
  simp

/-- The iterated commutator is additive in its argument. -/
theorem commutatorIter_sum {ι : Type*} (s : Finset ι) (H : Matrix n n ℂ)
    (A : ι → Matrix n n ℂ) (k : ℕ) :
    commutatorIter H (∑ i ∈ s, A i) k = ∑ i ∈ s, commutatorIter H (A i) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [commutatorIter_succ, ih, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]

/-- `ad_Hᵏ(H) = 0` for `k ≥ 1`. -/
theorem commutatorIter_self_succ (H : Matrix n n ℂ) (k : ℕ) : commutatorIter H H (k + 1) = 0 := by
  induction k with
  | zero => simp [commutatorIter_succ]
  | succ k ih => rw [commutatorIter_succ, ih, mul_zero, zero_mul, sub_zero]

variable [DecidableEq n]

/-- Conjugation by a unitary that commutes with `H` commutes with `ad_H`. -/
theorem commutatorIter_conj {H U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hUH : Commute U H) (A : Matrix n n ℂ) (k : ℕ) :
    U * commutatorIter H A k * Uᴴ = commutatorIter H (U * A * Uᴴ) k := by
  have hUstar : Uᴴ * U = 1 := by
    simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hU
  have hUU : U * Uᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp hU
  have hHUstar : H * Uᴴ = Uᴴ * H := by
    calc H * Uᴴ = Uᴴ * U * H * Uᴴ := by rw [hUstar, Matrix.one_mul]
      _ = Uᴴ * (H * U) * Uᴴ := by rw [Matrix.mul_assoc Uᴴ U H, hUH.eq]
      _ = Uᴴ * H * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * H := by rw [hUU, Matrix.mul_one]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [commutatorIter_succ, commutatorIter_succ, ← ih, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    · rw [← Matrix.mul_assoc, hUH.eq]; simp only [Matrix.mul_assoc]
    · simp only [Matrix.mul_assoc, hHUstar]

/-- **The variational lower bound, for conjugates by unitaries.** Let `H = ∑_i U_i H₀ U_i†` be a
sum of `N` conjugates of one operator `H₀` by unitaries `U_i` that commute with `H`, and let
`K = H₀ + ∑_{k=1}^{m} a_k iᵏ ad_Hᵏ(H₀)` for real constants `a_k`. If `K − λ ≥ 0`, then
`H − N λ ≥ 0`. With `λ = λ_min(K)` this is `E₀ ≥ N λ_min(K)`.
Hastings, arXiv:cond-mat/0508554v3, eq. `varnum`, lines 856–877. -/
theorem posSemidef_sub_card_smul_of_conj {ι : Type*} [Fintype ι] (U : ι → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) (H₀ : Matrix n n ℂ)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ)) (a : ℕ → ℝ) (m : ℕ) {c : ℝ}
    (hK : (H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
        commutatorIter (∑ j, U j * H₀ * (U j)ᴴ) H₀ (k + 1) - (c : ℂ) • 1).PosSemidef) :
    ((∑ j, U j * H₀ * (U j)ᴴ) - ((Fintype.card ι * c : ℝ) : ℂ) • 1).PosSemidef := by
  set H := ∑ j, U j * H₀ * (U j)ᴴ with hHdef
  set K := H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
    commutatorIter H H₀ (k + 1) with hKdef
  have hsum : (∑ i, U i * (K - (c : ℂ) • 1) * (U i)ᴴ).PosSemidef :=
    posSemidef_sum _ fun i _ ↦ by
      simpa [Matrix.mul_assoc] using hK.mul_mul_conjTranspose_same (U i)
  have hconjK : ∑ i, U i * K * (U i)ᴴ = H := by
    simp only [hKdef, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul,
      Finset.sum_add_distrib, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_comm, ← hHdef, add_eq_left]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [← Finset.smul_sum]
    simp only [commutatorIter_conj (hU _) (hcomm _), ← commutatorIter_sum, ← hHdef,
      commutatorIter_self_succ, smul_zero]
  have hconj1 : ∑ i, U i * ((c : ℂ) • (1 : Matrix n n ℂ)) * (U i)ᴴ =
      ((Fintype.card ι * c : ℝ) : ℂ) • 1 := by
    have hUU : ∀ i, U i * (U i)ᴴ = 1 := fun i ↦ by
      simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp (hU i)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, Finset.sum_const,
      Finset.card_univ]
    push_cast
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h : ∑ i, U i * (K - (c : ℂ) • 1) * (U i)ᴴ =
      H - ((Fintype.card ι * c : ℝ) : ℂ) • 1 := by
    rw [← hconjK, ← hconj1, ← Finset.sum_sub_distrib]
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  rw [← h]
  exact hsum

/-- **The variational lower bound on every eigenvalue.** Under the hypotheses of
`posSemidef_sub_card_smul_of_conj`, every eigenvalue `E` of `H`, in particular the ground energy
`E₀`, satisfies `N λ ≤ E`. Hastings, arXiv:cond-mat/0508554v3, eq. `varnum`, lines 856–877. -/
theorem card_mul_le_of_mulVec_eq_smul_of_conj {ι : Type*} [Fintype ι] (U : ι → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ unitaryGroup n ℂ) (H₀ : Matrix n n ℂ)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ)) (a : ℕ → ℝ) (m : ℕ) {c : ℝ}
    (hK : (H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
        commutatorIter (∑ j, U j * H₀ * (U j)ᴴ) H₀ (k + 1) - (c : ℂ) • 1).PosSemidef)
    {E : ℝ} {Ω : n → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ j, U j * H₀ * (U j)ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card ι * c ≤ E := by
  have h := (posSemidef_sub_card_smul_of_conj U hU H₀ hcomm a m hK).dotProduct_mulVec_nonneg Ω
  rw [sub_mulVec, hE, smul_mulVec, one_mulVec, ← sub_smul, dotProduct_smul, smul_eq_mul] at h
  have hpos : 0 < star Ω ⬝ᵥ Ω := dotProduct_star_self_pos_iff.mpr hΩ
  have h' : (0 : ℂ) ≤ ((E - Fintype.card ι * c : ℝ) : ℂ) := by
    push_cast
    exact le_of_mul_le_mul_right (by simpa using h) hpos
  exact sub_nonneg.mp (Complex.zero_le_real.mp h')

section SitePermutation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]

attribute [local instance] arrowAction

/-- The unitary that moves a configuration of the sites `V` along `g`:
`(P_g ψ)(x) = ψ(x ∘ g)`, as the image of `g` under the action `(g • x)(v) = x(g⁻¹ • v)` on
configurations and the permutation-matrix homomorphism. -/
noncomputable def sitePermMatrix (q : ℕ) (g : G) : Matrix (V → Fin q) (V → Fin q) ℂ :=
  permMatrixHom (MulAction.toPermHom G (V → Fin q) g)

theorem sitePermMatrix_mul (q : ℕ) (g h : G) :
    sitePermMatrix (V := V) q (g * h) = sitePermMatrix q g * sitePermMatrix q h := by
  simp only [sitePermMatrix, map_mul]

theorem sitePermMatrix_mem_unitaryGroup (q : ℕ) (g : G) :
    sitePermMatrix (V := V) q g ∈ unitaryGroup (V → Fin q) ℂ :=
  Equiv.Perm.permMatrix_mem_unitaryGroup _

/-- Every site permutation commutes with the sum of the translates `∑_g P_g H₀ P_g†`. -/
theorem commute_sitePermMatrix_sum [Fintype G] (q : ℕ) (H₀ : Matrix (V → Fin q) (V → Fin q) ℂ)
    (h : G) :
    Commute (sitePermMatrix (V := V) q h)
      (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) := by
  have hu : (sitePermMatrix (V := V) q h)ᴴ * sitePermMatrix q h = 1 := by
    simpa [star_eq_conjTranspose] using
      (mem_unitaryGroup_iff').mp (sitePermMatrix_mem_unitaryGroup (V := V) q h)
  have hconj : sitePermMatrix (V := V) q h *
      (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) * (sitePermMatrix q h)ᴴ =
        ∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g ↦ ?_
    simp only [Equiv.coe_mulLeft, sitePermMatrix_mul, conjTranspose_mul, Matrix.mul_assoc]
  calc sitePermMatrix q h * (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ)
      = sitePermMatrix q h * (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) *
          ((sitePermMatrix q h)ᴴ * sitePermMatrix q h) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hconj]

/-- **The variational lower bound for translates on finitely many sites.** Let a finite group
`G`, such as the translations of a periodic lattice or any group of automorphisms of a finite
graph, act on the sites `V`, and let `H = ∑_{g ∈ G} P_g H₀ P_g†` be the sum of the translates of
one term `H₀`. For real constants `a_k` and
`K = H₀ + ∑_{k=1}^{m} a_k iᵏ ad_Hᵏ(H₀)`, if `K − λ ≥ 0` then every eigenvalue `E` of `H`, in
particular the ground energy `E₀`, satisfies `E ≥ |G| λ`: with `λ = λ_min(K)` and `N = |G|` the
number of summands, `E₀/N ≥ λ_min(K)`. When `G` acts simply transitively on the sites, as the
translations of a periodic lattice do, `N` is the number of sites.
Hastings, arXiv:cond-mat/0508554v3, eq. `varnum`, lines 856–877. -/
theorem card_mul_le_of_mulVec_eq_smul_of_sitePerm [Fintype G] (q : ℕ)
    (H₀ : Matrix (V → Fin q) (V → Fin q) ℂ) (a : ℕ → ℝ) (m : ℕ) {c : ℝ}
    (hK : (H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
        commutatorIter (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) H₀ (k + 1) -
          (c : ℂ) • 1).PosSemidef)
    {E : ℝ} {Ω : (V → Fin q) → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ g : G, sitePermMatrix q g * H₀ * (sitePermMatrix q g)ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card G * c ≤ E :=
  card_mul_le_of_mulVec_eq_smul_of_conj (fun g ↦ sitePermMatrix q g)
    (sitePermMatrix_mem_unitaryGroup q) H₀ (commute_sitePermMatrix_sum q H₀) a m hK hΩ hE

end SitePermutation

end Matrix

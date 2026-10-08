/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.PositiveConstraints
import QICLean.Analysis.RootChannel

/-!
# Square roots of the positive constraints and their local channels

For a positive contraction `k` with `k Ω = 0` and its expectation `k_l = E_K(k)` onto a set
of sites `K`, the square roots `G = (I - k)^{1/2}`, `K = k^{1/2}` and their local versions are
positive contractions, `G Ω = Ω`, `K Ω = 0`, and the root tails are bounded by the square
root of `‖k - k_l‖`. The root channels `ℰ(B) = G B G + K B K` are unital, completely
positive, and contractive after adjoining an arbitrary auxiliary system, and their
difference is bounded uniformly in the auxiliary dimension. The local channel fixes every
operator commuting with all operators acting on `K`, in particular every operator acting
outside `K`. Applied to the constraints of Proposition 4.3, whose tails are
`C e^{-c l^α}`, all these bounds are `C' e^{-(c/2) l^α}`.

## Main results

* `TNLean.PEPS.AreaLaw.quasilocalRoots`: Lemma 4.4 for one constraint and one radius.
* `TNLean.PEPS.AreaLaw.sqrt_mul_exp_neg`: `√(C e^{-c x}) = √C e^{-(c/2) x}`.
* `TNLean.PEPS.AreaLaw.rootChannel_kronecker_eq_self_of_commute`: with an auxiliary system,
  the local channel fixes every operator commuting with `A ⊗ I` for all `A` acting on `K`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 4.4 (`lem:quasilocal-roots`), section file `03-quasilocal.tex`, lines 336–389.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
  formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

open QuantumCircuit Matrix

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `√(C e^{-c x}) = √C e^{-(c/2) x}`. -/
theorem sqrt_mul_exp_neg (C c x : ℝ) :
    Real.sqrt (C * Real.exp (-(c * x))) = Real.sqrt C * Real.exp (-(c / 2 * x)) := by
  rw [Real.sqrt_mul' _ (Real.exp_pos _).le]
  congr 1
  rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- **Square roots and local channels** (Lemma 4.4, `lem:quasilocal-roots`,
`03-quasilocal.tex`, lines 336–389), for one constraint `k` with `0 ≤ k ≤ I`, `k Ω = 0`,
and its expectation `k_l = E_K(k)` with `‖k - k_l‖ ≤ ε`. With `G = (I - k)^{1/2}`,
`K = k^{1/2}`, `G_l = (I - k_l)^{1/2}`, `K_l = k_l^{1/2}`:
the four roots are positive contractions; `G Ω = Ω`, `K Ω = 0`;
`‖G - G_l‖ + ‖K - K_l‖ ≤ 2 √ε` and `G_l² + K_l² = I` (`eq:quasilocal-root-tail`);
both root channels are unital, and for every finite auxiliary system they are positive and
contractive on the extended algebra, with
`‖(ℰ - ℰ_l) ⊗ id‖ ≤ 4 √ε` (`eq:quasilocal-channel-tail`); and `ℰ_l` fixes every operator
commuting with all operators acting on `K`. -/
theorem quasilocalRoots [NeZero q] (K : Finset ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1) {Ω : (ι → Fin q) → ℂ} (hkΩ : k *ᵥ Ω = 0) {ε : ℝ}
    (hε : ‖k - siteExpectation q K k‖ ≤ ε) :
    let kl := siteExpectation q K k
    let G := CFC.sqrt (1 - k)
    let Kr := CFC.sqrt k
    let Gl := CFC.sqrt (1 - kl)
    let Kl := CFC.sqrt kl
    (0 ≤ G ∧ G ≤ 1) ∧ (0 ≤ Kr ∧ Kr ≤ 1) ∧ (0 ≤ Gl ∧ Gl ≤ 1) ∧ (0 ≤ Kl ∧ Kl ≤ 1) ∧
      G *ᵥ Ω = Ω ∧ Kr *ᵥ Ω = 0 ∧
      ‖G - Gl‖ + ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε ∧ Gl * Gl + Kl * Kl = 1 ∧
      rootChannel G Kr 1 = 1 ∧ rootChannel Gl Kl 1 = 1 ∧
      (∀ (κ : Type*) [Fintype κ] [DecidableEq κ] (B : Matrix ((ι → Fin q) × κ) _ ℂ),
        (0 ≤ B → 0 ≤ rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B ∧
          0 ≤ rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B) ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤ ‖B‖ ∧
        ‖rootChannel (G ⊗ₖ (1 : Matrix κ κ ℂ)) (Kr ⊗ₖ 1) B -
            rootChannel (Gl ⊗ₖ (1 : Matrix κ κ ℂ)) (Kl ⊗ₖ 1) B‖ ≤
          4 * Real.sqrt ε * ‖B‖) ∧
      (∀ B : Matrix (ι → Fin q) (ι → Fin q) ℂ,
        (∀ A ∈ supportedOperators q (K : Set ι), Commute A B) → rootChannel Gl Kl B = B) := by
  intro kl G Kr Gl Kl
  have hl₀ : 0 ≤ kl := siteExpectation_nonneg K hk₀
  have hl₁ : kl ≤ 1 := siteExpectation_le_one K hk₁
  have hG : 0 ≤ G := CFC.sqrt_nonneg _
  have hKr : 0 ≤ Kr := CFC.sqrt_nonneg _
  have hGl : 0 ≤ Gl := CFC.sqrt_nonneg _
  have hKl : 0 ≤ Kl := CFC.sqrt_nonneg _
  have hG1 : G ≤ 1 := sqrt_le_one (sub_le_self _ hk₀)
  have hKr1 : Kr ≤ 1 := sqrt_le_one hk₁
  have hGl1 : Gl ≤ 1 := sqrt_le_one (sub_le_self _ hl₀)
  have hKl1 : Kl ≤ 1 := sqrt_le_one hl₁
  have hGn : ‖G‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hG hG1
  have hKrn : ‖Kr‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hKr hKr1
  have hGln : ‖Gl‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hGl hGl1
  have hKln : ‖Kl‖ ≤ 1 := norm_le_one_of_nonneg_of_le_one hKl hKl1
  have hsq : G * G + Kr * Kr = 1 := sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁
  have hsql : Gl * Gl + Kl * Kl = 1 := sqrt_one_sub_mul_add_sqrt_mul hl₀ hl₁
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have htG : ‖G - Gl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_one_sub_sub_le hk₁ hl₁).trans (Real.sqrt_le_sqrt hε)
  have htK : ‖Kr - Kl‖ ≤ Real.sqrt ε :=
    (norm_sqrt_sub_le hk₀ hl₀).trans (Real.sqrt_le_sqrt hε)
  have hGh : G.IsHermitian := hG.isSelfAdjoint
  have hKh : Kr.IsHermitian := hKr.isSelfAdjoint
  have hGlh : Gl.IsHermitian := hGl.isSelfAdjoint
  have hKlh : Kl.IsHermitian := hKl.isSelfAdjoint
  refine ⟨⟨hG, hG1⟩, ⟨hKr, hKr1⟩, ⟨hGl, hGl1⟩, ⟨hKl, hKl1⟩,
    sqrt_one_sub_mulVec_eq_self hk₁ hkΩ, sqrt_mulVec_eq_zero hk₀ hkΩ, by linarith, hsql,
    rootChannel_one hsq, rootChannel_one hsql, fun κ _ _ B => ⟨fun hB =>
      ⟨rootChannel_kronecker_nonneg hGh hKh hB, rootChannel_kronecker_nonneg hGlh hKlh hB⟩,
      norm_rootChannel_kronecker_le hGh hKh hsq B, norm_rootChannel_kronecker_le hGlh hKlh hsql B,
      ?_⟩, fun B hB => ?_⟩
  · refine (norm_rootChannel_kronecker_sub_le G Kr Gl Kl B).trans ?_
    have hs := Real.sqrt_nonneg ε
    have hB := norm_nonneg B
    have h1 : (‖G‖ + ‖Gl‖) * ‖G - Gl‖ + (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤ 4 * Real.sqrt ε := by
      have a1 : (‖G‖ + ‖Gl‖) * ‖G - Gl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htG (norm_nonneg _) (by norm_num)
      have a2 : (‖Kr‖ + ‖Kl‖) * ‖Kr - Kl‖ ≤ 2 * Real.sqrt ε :=
        mul_le_mul (by linarith) htK (norm_nonneg _) (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right h1 hB
  · exact rootChannel_sqrt_eq_self_of_commute hl₀ hl₁
      (hB _ (siteExpectation_mem_supportedOperators K k))

/-- **Local channels fix the commutant, with spectators** (Lemma 4.4, `03-quasilocal.tex`,
lines 366–368 and 386–389): if `0 ≤ k_l ≤ I` acts on `K`, then for every finite auxiliary
system the channel `ℰ_l ⊗ id` with Kraus operators `(I - k_l)^{1/2} ⊗ I`, `k_l^{1/2} ⊗ I`
fixes every operator commuting with `A ⊗ I` for all `A` acting on `K`. -/
theorem rootChannel_kronecker_eq_self_of_commute [NeZero q] (K : Finset ι)
    {k : Matrix (ι → Fin q) (ι → Fin q) ℂ} (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q (K : Set ι)) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix ((ι → Fin q) × κ) ((ι → Fin q) × κ) ℂ)
    (hB : ∀ A ∈ supportedOperators q (K : Set ι), Commute (A ⊗ₖ (1 : Matrix κ κ ℂ)) B) :
    rootChannel (CFC.sqrt (1 - k) ⊗ₖ (1 : Matrix κ κ ℂ)) (CFC.sqrt k ⊗ₖ 1) B = B := by
  refine rootChannel_eq_self_of_commute ?_
    (hB _ (sqrt_mem_supportedOperators K (sub_nonneg.mpr hk₁)
      (sub_mem (one_mem_supportedOperators _) hk)))
    (hB _ (sqrt_mem_supportedOperators K hk₀ hk))
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.add_kronecker,
    sqrt_one_sub_mul_add_sqrt_mul hk₀ hk₁, Matrix.mul_one, Matrix.one_kronecker_one]

end TNLean.PEPS.AreaLaw

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeAncillaSites
import TNLean.PEPS.AreaLaw.Amplification.SupportedPolarCorrection

/-!
# Steps of the proof of Proposition 10.2 on the enlarged sites

The proof of Proposition 10.2 (`prop:amplification`) works on the physical sites enlarged by
two copies `s', e'` of the target `X`. This module states its last two steps on those sites.

* The polar correction: from the estimates of a good clock realization, stated in the
  coordinates `physical × (s', e')`, some unitary acting on `N ⊔ s'` moves the copied vector
  `φ` to within `a + √(2a + 6ε + 9ε²)` of the restored vector `η`, when the restoring
  operator acts on `N ⊔ s'` and the truncated product acts on the physical region `N`.
* The entropy comparison: if such a unitary moves `φ` to within `C₁ n^(-K/2)` of `η`, then
  every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` in `Ω` with every
  physical set avoiding `N`, where `|X| log q ≤ C₂ n²`.

It also records the supports of the restoring and column operators on these sites.

## Main statements

* `TNLean.PEPS.AreaLaw.exists_ancilla_unitary_of_good_realization`: the polar correction on
  the enlarged sites.
* `TNLean.PEPS.AreaLaw.mutualInformation_le_of_ancilla_unitary`: the entropy comparison on
  the enlarged sites.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 330–356 (the
  enlarged sites and the restoring operator), 501–545 (the polar correction) and 547–561
  (the entropy comparison).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix QuantumCircuit
open scoped Kronecker Matrix.Norms.L2Operator
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- **The support of a sum of restoring blocks on the enlarged sites.** A sum of operators
`P_i ⊗ (b_i ⊗ 1_{e'})`, with every `P_i` acting on a physical region `S`, acts on `S ⊔ s'`.
Source: `eq:amplification-restoring-operator`, `09-amplification.tex`, lines 350–356 and
524–525. -/
theorem sum_kronecker_submatrix_ancillaSplit_mem_supportedOperators {X S : Finset (Site Λ)}
    {κ : Type*} (s : Finset κ) {P : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hP : ∀ i, P i ∈ supportedOperators q (S : Set (Site Λ)))
    (b : κ → Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) :
    (∑ i ∈ s, P i ⊗ₖ (b i ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
        (ancillaSplit q X) (ancillaSplit q X) ∈
      supportedOperators q ((S.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X)) :
        Set (AncillaSites Λ X)) := by
  have hsum : (∑ i ∈ s, P i ⊗ₖ (b i ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
        (ancillaSplit q X) (ancillaSplit q X) = ∑ i ∈ s, (P i ⊗ₖ (b i ⊗ₖ
      (1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ))).submatrix
        (ancillaSplit q X) (ancillaSplit q X) := by
    ext c c'
    simp only [submatrix_apply, Matrix.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    kronecker_submatrix_ancillaSplit_mem_supportedOperators (hP i) (b i)

/-- **The blocks of a column operator act on a physical region.** If `B = ∑_i P_i ⊗ A_i` with
every `P_i` acting on a physical region `S`, then for all ancillary labels `x, y` the block
`σ, τ ↦ B (σ, x) (τ, y)` acts on `S`.
Source: `eq:amplification-column-operator`, `09-amplification.tex`, lines 359–364. -/
theorem block_mem_supportedOperators_of_eq_sum {S : Finset (Site Λ)} {α κ : Type*}
    (s : Finset κ) {P : κ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hP : ∀ i, P i ∈ supportedOperators q (S : Set (Site Λ))) (A : κ → Matrix α α ℂ)
    (x y : α) :
    (Matrix.of fun σ τ => (∑ i ∈ s, P i ⊗ₖ A i) (σ, x) (τ, y)) ∈
      supportedOperators q (S : Set (Site Λ)) := by
  have hblock : (Matrix.of fun σ τ => (∑ i ∈ s, P i ⊗ₖ A i) (σ, x) (τ, y)) =
      ∑ i ∈ s, A i x y • P i := by
    ext σ τ
    simp only [of_apply, Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hblock]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i)

/-- **The polar correction on the enlarged sites.** Work in the coordinates
`physical × (s', e')` of the enlarged sites. Let the restoring operator `R₀` act on `N ⊔ s'`
and the truncated product `L'` act on the physical region `N`, and let `D, D_ret` be
physical operators. For unit vectors `φ, η`, suppose that the ground component `g` of
`ζ = R₀ φ` is fixed by `D` with `‖g‖ ≤ 1`, that `‖ζ‖ ≤ M₀`, that the excited component
`‖D (ζ - g)‖`, the omitted events `‖(D - D_ret) ζ‖` and `M₀ ‖D_ret - L'‖` are at most `ε`,
and that the adjoint error of `L' R₀` is at most `a`. Then some unitary acting on `N ⊔ s'`
moves `φ` to within `a + √(2a + 6ε + 9ε²)` of `η`.
Source: `09-amplification.tex`, lines 501–545. -/
theorem exists_ancilla_unitary_of_good_realization {X N : Finset (Site Λ)}
    {R₀ : Matrix (Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X))
      (Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X)) ℂ}
    (hR₀ : R₀.submatrix (ancillaSplit q X) (ancillaSplit q X) ∈
      supportedOperators q ((N.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X)) :
        Set (AncillaSites Λ X)))
    {L' D Dret : Matrix (Configuration Λ q) (Configuration Λ q) ℂ}
    (hL : L' ∈ supportedOperators q (N : Set (Site Λ)))
    {φ η g : Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ}
    (hφ : ‖WithLp.toLp 2 φ‖ = 1) (hη : ‖WithLp.toLp 2 η‖ = 1) {M₀ ε a : ℝ}
    (hζ : ‖WithLp.toLp 2 (R₀ *ᵥ φ)‖ ≤ M₀)
    (hg : (D ⊗ₖ (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
      (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ g = g)
    (hgn : ‖WithLp.toLp 2 g‖ ≤ 1)
    (hexc : ‖WithLp.toLp 2 ((D ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (R₀ *ᵥ φ - g))‖ ≤ ε)
    (hret : ‖WithLp.toLp 2 (((D - Dret) ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *ᵥ
        (R₀ *ᵥ φ))‖ ≤ ε)
    (htrunc : M₀ * ‖Dret - L'‖ ≤ ε)
    (hadj : ‖WithLp.toLp 2 (((L' ⊗ₖ (1 : Matrix (RegionalConfiguration q X ×
      RegionalConfiguration q X) (RegionalConfiguration q X × RegionalConfiguration q X) ℂ)) *
        R₀)ᴴ *ᵥ η) - WithLp.toLp 2 φ‖ ≤ a) :
    ∃ U : Matrix (AncillaSites Λ X → Fin q) (AncillaSites Λ X → Fin q) ℂ,
      U ∈ supportedOperators q ((N.disjSum (Finset.univ.disjSum ∅) :
        Finset (AncillaSites Λ X)) : Set (AncillaSites Λ X)) ∧ Uᴴ * U = 1 ∧
      ‖WithLp.toLp 2 (U *ᵥ (φ ∘ ancillaSplit q X)) - WithLp.toLp 2 (η ∘ ancillaSplit q X)‖ ≤
        a + √(2 * a + 6 * ε + 9 * ε ^ 2) := by
  set sp := ancillaSplit q X with hspdef
  set I₂ := (1 : Matrix (RegionalConfiguration q X × RegionalConfiguration q X)
    (RegionalConfiguration q X × RegionalConfiguration q X) ℂ) with hI₂def
  have hT (A : Matrix (Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X)) (Configuration Λ q × (RegionalConfiguration q X ×
        RegionalConfiguration q X)) ℂ)
      (v : Configuration Λ q × (RegionalConfiguration q X × RegionalConfiguration q X) → ℂ) :
      A.submatrix sp sp *ᵥ (v ∘ sp) = (A *ᵥ v) ∘ sp := by
    rw [submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hTn (v : Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ) : ‖WithLp.toLp 2 (v ∘ sp)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv sp v
  have hsubk (A B : Matrix (Configuration Λ q) (Configuration Λ q) ℂ) :
      (A - B) ⊗ₖ I₂ = A ⊗ₖ I₂ - B ⊗ₖ I₂ := by
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  refine exists_supported_unitary_of_good_realization _ hR₀
    (kronecker_one_submatrix_ancillaSplit_mem_supportedOperators hL)
    (D := (D ⊗ₖ I₂).submatrix sp sp) (Dret := (Dret ⊗ₖ I₂).submatrix sp sp) (g := g ∘ sp)
    (M₀ := M₀) (ε := ε) (a := a)
    (by rw [hTn]; exact hφ) (by rw [hTn]; exact hη) (by rw [hT, hTn]; exact hζ)
    (by rw [hT, hg]) (by rw [hTn]; exact hgn) ?_ ?_ ?_ ?_
  · have hsub : R₀.submatrix sp sp *ᵥ (φ ∘ sp) - g ∘ sp = (R₀ *ᵥ φ - g) ∘ sp := by
      rw [hT]
      rfl
    rw [hsub, hT, hTn]
    exact hexc
  · have hsub : (D ⊗ₖ I₂).submatrix sp sp - (Dret ⊗ₖ I₂).submatrix sp sp =
        ((D - Dret) ⊗ₖ I₂).submatrix sp sp := by
      rw [hsubk]
      rfl
    rw [hT, hsub, hT, hTn]
    exact hret
  · have hsub : (Dret ⊗ₖ I₂).submatrix sp sp - (L' ⊗ₖ I₂).submatrix sp sp =
        ((Dret - L') ⊗ₖ I₂).submatrix sp sp := by
      rw [hsubk]
      rfl
    rw [hsub]
    exact (mul_le_mul_of_nonneg_left ((norm_submatrix_equiv_le _ _).trans
      (l2_opNorm_kronecker_one_le _)) ((norm_nonneg _).trans hζ)).trans htrunc
  · have hprod : (L' ⊗ₖ I₂).submatrix sp sp * R₀.submatrix sp sp =
        ((L' ⊗ₖ I₂) * R₀).submatrix sp sp := by
      rw [submatrix_mul_equiv]
    rw [hprod, conjTranspose_submatrix, hT, ← WithLp.toLp_sub]
    have hcomp : (((L' ⊗ₖ I₂) * R₀)ᴴ *ᵥ η) ∘ sp - φ ∘ sp =
        (((L' ⊗ₖ I₂) * R₀)ᴴ *ᵥ η - φ) ∘ sp := rfl
    rw [hcomp, hTn, WithLp.toLp_sub]
    exact hadj

/-- The copy `e'` of a part of the target is disjoint from every physical region. -/
theorem disjoint_ancillaCopyRegion_ancillaPhysicalRegion {X : Finset (Site Λ)}
    (X' : Finset ↥X) (J : Finset (Site Λ)) :
    Disjoint (ancillaCopyRegion X') (ancillaPhysicalRegion X J) := by
  rw [Finset.disjoint_left]
  rintro (v | x | x) h1 h2
  · simp only [ancillaCopyRegion, Finset.inl_mem_disjSum, Finset.notMem_empty] at h1
  · simp only [ancillaPhysicalRegion, Finset.inr_mem_disjSum, Finset.notMem_empty] at h2
  · simp only [ancillaPhysicalRegion, Finset.inr_mem_disjSum, Finset.notMem_empty] at h2

/-- The region `N ⊔ s'` of the enlarged sites is disjoint from the copy `e'` of the target
together with any physical region avoiding `N`. -/
theorem disjoint_disjSum_ancillaCopyRegion_union {X N J : Finset (Site Λ)}
    (hJ : Disjoint J N) (X' : Finset ↥X) :
    Disjoint (N.disjSum (Finset.univ.disjSum ∅) : Finset (AncillaSites Λ X))
      (ancillaCopyRegion X' ∪ ancillaPhysicalRegion X J) := by
  rw [Finset.disjoint_left]
  rintro (v | x | x) h1 h2
  · simp only [Finset.inl_mem_disjSum] at h1
    simp only [ancillaCopyRegion, ancillaPhysicalRegion, Finset.mem_union,
      Finset.inl_mem_disjSum, Finset.notMem_empty, false_or] at h2
    exact Finset.disjoint_left.mp hJ h2 h1
  · simp only [ancillaCopyRegion, ancillaPhysicalRegion, Finset.mem_union,
      Finset.inr_mem_disjSum, Finset.inl_mem_disjSum, Finset.notMem_empty, or_self] at h2
  · simp only [Finset.inr_mem_disjSum, Finset.notMem_empty] at h1

/-- **The entropy comparison on the enlarged sites.** Let `X, Y` be disjoint physical regions,
let `φ` be the copied vector built from unit blank vectors on `s'` and on the target, and
let `η` be a restored vector, both of unit norm. If a unitary acting on `N ⊔ s'`, with `X ⊆ N`,
moves `φ` to within `C₁ n^(-K/2)` of `η` with `K ≥ 4(M + 2)`, and `|X| log q ≤ C₂ n²`,
then every part of `X` has mutual information at most `8 √C₁ (1 + C₂) n^(-M)` in `Ω` with
every physical set avoiding `N`.
Source: `09-amplification.tex`, lines 547–561. -/
theorem mutualInformation_le_of_ancilla_unitary {Ω : StateSpace Λ q} (hΩ : ‖Ω‖ = 1)
    {X Y N J : Finset (Site Λ)} (hXY : Disjoint X Y) (hXN : X ⊆ N) (hJ : Disjoint J N)
    {sBlank xBlank : RegionalConfiguration q X → ℂ} (hs : ‖WithLp.toLp 2 sBlank‖ = 1)
    (hx : ‖WithLp.toLp 2 xBlank‖ = 1) {p : RegionalConfiguration q X → ℝ}
    (hφ : ‖WithLp.toLp 2 (restoringTransport Ω X Y hXY *ᵥ
      (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp)‖ = 1)
    (hη : ‖WithLp.toLp 2 (restoringTransport Ω X Y hXY *ᵥ
      (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp)‖ = 1)
    {U : Matrix (AncillaSites Λ X → Fin q) (AncillaSites Λ X → Fin q) ℂ}
    (hU : U ∈ supportedOperators q ((N.disjSum (Finset.univ.disjSum ∅) :
      Finset (AncillaSites Λ X)) : Set (AncillaSites Λ X))) (hUu : Uᴴ * U = 1)
    {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n) (hK : 4 * (M + 2) ≤ K)
    (hδ : ‖WithLp.toLp 2 (U *ᵥ ((restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp) ∘
          ancillaSplit q X)) -
      WithLp.toLp 2 ((restoringTransport Ω X Y hXY *ᵥ
        (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp) ∘ ancillaSplit q X)‖ ≤
      C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : (X.card : ℝ) * Real.log q ≤ C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω X' J ≤
      8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  intro X' hX'
  set sp := ancillaSplit q X with hspdef
  set φ := restoringTransport Ω X Y hXY *ᵥ
    (Entropy.restoringCopy sBlank xBlank (restoringVector Ω X Y hXY)).ofLp with hφdef
  set η := restoringTransport Ω X Y hXY *ᵥ
    (Entropy.restoringRestored p (restoringVector Ω X Y hXY)).ofLp with hηdef
  set copyAll := ancillaCopyRegion (Finset.univ : Finset ↥X) with hcopyAll
  set physJ := ancillaPhysicalRegion X J with hphysJ
  have hJX : Disjoint J X := Finset.disjoint_of_subset_right hXN hJ
  have hTn (v : Configuration Λ q × (RegionalConfiguration q X ×
      RegionalConfiguration q X) → ℂ) : ‖WithLp.toLp 2 (v ∘ sp)‖ = ‖WithLp.toLp 2 v‖ :=
    EuclideanSpace.norm_toLp_comp_equiv sp v
  have hφform : φ = fun c => sBlank c.2.1 *
      (restoringEigenbasis Ω X *ᵥ xBlank) (restoringSplit q X Y hXY c.1).1.1 *
      Ω ((restoringSplit q X Y hXY).symm ((c.2.2, (restoringSplit q X Y hXY c.1).1.2),
        (restoringSplit q X Y hXY c.1).2)) := restoringTransport_copy Ω X Y hXY sBlank xBlank
  have hUx : ‖WithLp.toLp 2 (restoringEigenbasis Ω X *ᵥ xBlank)‖ = 1 := by
    rw [norm_toLp_mulVec_of_conjTranspose_mul_self (restoringEigenbasis_unitary Ω X).2, hx]
  -- `η` is `Ω` tensored with a unit ancillary vector.
  set χ0 : RegionalConfiguration q X × RegionalConfiguration q X → ℂ :=
    fun a => if a.1 = a.2 then (Real.sqrt (p a.1) : ℂ) else 0
  set χ := ((1 : Matrix (RegionalConfiguration q X) (RegionalConfiguration q X) ℂ) ⊗ₖ
    restoringEigenbasis Ω X) *ᵥ χ0
  have hηform : η = fun c => Ω c.1 * χ c.2 := restoringTransport_restored Ω X Y hXY p
  have hχ : ‖WithLp.toLp 2 χ‖ = 1 := by
    have h := EuclideanSpace.norm_vecKron Ω (WithLp.toLp 2 χ)
    rw [hΩ, one_mul] at h
    rw [← h, ← hη, hηform]
    rfl
  have hprod : FiniteProduct.mutualInformation (fun _ : AncillaSites Λ X => Fin q)
      (WithLp.toLp 2 (η ∘ sp)) copyAll physJ = 0 := by
    rw [hηform]
    exact mutualInformation_ancillaProduct_copy_eq_zero hΩ hχ _ _
  have hdim' : Real.log (Fintype.card (FiniteProduct.Configuration
      (fun _ : AncillaSites Λ X => Fin q) copyAll)) ≤ C₂ * (n : ℝ) ^ 2 := by
    have hc : copyAll.card = X.card := by
      rw [hcopyAll, ancillaCopyRegion, Finset.card_disjSum, Finset.card_disjSum,
        Finset.card_empty, Finset.card_empty, Finset.card_univ, Fintype.card_coe, zero_add,
        zero_add]
    rw [Fintype.card_pi, Finset.prod_const, Fintype.card_fin, Finset.card_univ,
      Fintype.card_coe, hc, Nat.cast_pow, Real.log_pow]
    exact hdim
  have hfinal := mutualInformation_le_inv_pow_of_supported_unitary (φ := WithLp.toLp 2 (φ ∘ sp))
    (η := WithLp.toLp 2 (η ∘ sp)) (by rw [hTn]; exact hφ) (by rw [hTn]; exact hη)
    (disjoint_ancillaCopyRegion_ancillaPhysicalRegion _ _)
    (by rw [Finset.disjoint_coe]; exact disjoint_disjSum_ancillaCopyRegion_union hJ _)
    hU hUu hprod hn hK hδ hdim'
  -- Back to `Ω` and the part `X'` of the target.
  set X'' : Finset ↥X := X'.subtype (· ∈ X)
  have hX''map : X''.map (Function.Embedding.subtype _) = X' :=
    Finset.subtype_map_of_mem fun x hx => hX' hx
  have hcopy := mutualInformation_ancillaCopy_eq hXY hΩ hs hUx X'' hJX
  rw [hX''map, ← hφform] at hcopy
  rw [← hcopy]
  exact hfinal _ (Finset.disjSum_mono le_rfl (Finset.disjSum_mono le_rfl
    (Finset.subset_univ _)))

end TNLean.PEPS.AreaLaw

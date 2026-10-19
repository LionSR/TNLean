/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem
import TNLean.PEPS.AreaLaw.Amplification.EntropyComparison
import TNLean.PEPS.AreaLaw.Geometry.TemplateCutBoundary
import TNLean.PEPS.AreaLaw.Geometry.TemplateLayers
import TNLean.PEPS.AreaLaw.Scan.CompactCollarCounting

/-!
# The deterministic steps of the sublinear collar bound

The proof of the sublinear collar bound (Proposition 9.6) has three steps that use
no scanner estimate. This module proves them.

* At each leaf of the scan, the physical sites are partitioned into `X, U, Y, V`.
  For a pure state the two quantities `g_pre = S(XU) + S(V) - S(Y)` and
  `g_post = S(U) + S(UY) - S(Y)` of the sharp comparisons satisfy the exact identity
  `2 S(X) + g_pre - g_post = I(X : V) + I(X : YV)`. If a fixed region `W` lies in
  every far part `V`, monotonicity bounds the left side below by `2 I(X : W)`, and
  the bound survives any average over the leaves.
* The mutual information of `X` with any disjoint region changes, between two pure
  states, by at most `8 √δ log(e dim X)`, where `δ` is the trace distance of the
  states. Only the dimension of `X` enters. A trace distance `C n^(-500)` and
  `log dim X ≤ C n²` give the correction `O(n^(-248))`.
* For a template separated from the cut with `L ≤ s₀`, the cuts of `X = A ∩ T`,
  `S₀ = A ∩ T_L` and `S₀ ∖ X` have `O(n)` edges and `|S₀| = O(n²)`. These are the
  final assertions of Proposition 9.6, obtained from Lemma 9.4.

Consequently `SublinearCollarBound` reduces to its mutual-information inequality.

## Main definitions

* `FiniteProduct.collarPreQuantity`, `FiniteProduct.collarPostQuantity`: the leaf
  quantities `g_pre` and `g_post`.

## Main statements

* `FiniteProduct.collarLeaf_entropy_identity`: the identity
  `2 S(X) + g_pre - g_post = I(X : V) + I(X : YV)`.
* `FiniteProduct.two_mutualInformation_le_collarLeaf_average`: the lower bound by
  `2 I(X : W)` after an average over leaves.
* `FiniteProduct.abs_mutualInformation_sub_le_of_traceDistance`: continuity of mutual
  information with only the dimension of the first region.
* `FiniteProduct.mutualInformation_le_add_of_traceDistance_le_rpow`: the transfer
  from the truncated to the original ground state.
* `Geometry.Template.collar_cut_card_le`: the cut and size assertions.
* `sublinearCollarBound_of_mutualInformation_le`: Proposition 9.6 follows from its
  mutual-information inequality alone.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, Proposition 9.6 (`prop:collar`), `08-scanner.tex` lines 808–827 and its proof,
  lines 868–873, 900–911 and 936–943; Lemma 9.4 (`scanner:templates`), lines
  571–590; Lemma 2.1 (`lem:continuity`), `01-preliminaries.tex` lines 33–46.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix
open scoped ComplexOrder
open TNLean.Lattice

namespace FiniteProduct

open TNLean.PEPS.AreaLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The leaf quantity `g_pre = S(XU) + S(V) - S(Y)` of the sharp comparisons.
Source: `08-scanner.tex`, lines 868–873. -/
noncomputable def collarPreQuantity (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (X U Y V : Finset ι) : ℝ :=
  entropy β ψ (X ∪ U) + entropy β ψ V - entropy β ψ Y

/-- The leaf quantity `g_post = S(U) + S(UY) - S(Y)` of the sharp comparisons.
Source: `08-scanner.tex`, lines 868–873. -/
noncomputable def collarPostQuantity (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (U Y : Finset ι) : ℝ :=
  entropy β ψ U + entropy β ψ (U ∪ Y) - entropy β ψ Y

/-- Mutual information of two regions is symmetric. -/
theorem mutualInformation_comm (ψ : EuclideanSpace ℂ ((v : ι) → β v)) (R T : Finset ι) :
    mutualInformation β ψ R T = mutualInformation β ψ T R := by
  unfold mutualInformation
  rw [Finset.union_comm]
  ring

/-- Discarding part of the second region cannot increase mutual information. -/
theorem mutualInformation_mono_right (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    {X W V : Finset ι} (hWV : W ⊆ V) (hXV : Disjoint X V) :
    mutualInformation β ψ X W ≤ mutualInformation β ψ X V := by
  rw [mutualInformation_comm β ψ X W, mutualInformation_comm β ψ X V]
  exact mutualInformation_mono_left β ψ W V X hWV hXV.symm

/-- **The leaf entropy identity.** Let `X, U, Y, V` be pairwise disjoint regions
covering all sites. For every vector `ψ`, purity gives
`2 S(X) + g_pre - g_post = I(X : V) + I(X : YV)`. No normalization is needed.
Source: `08-scanner.tex`, lines 868–873 and 900–905 (`scanner:entropy-identity`). -/
theorem collarLeaf_entropy_identity (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    {X U Y V : Finset ι} (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hcover : X ∪ U ∪ Y ∪ V = Finset.univ) :
    2 * entropy β ψ X + (collarPreQuantity β ψ X U Y V - collarPostQuantity β ψ U Y) =
      mutualInformation β ψ X V + mutualInformation β ψ X (Y ∪ V) := by
  have hmem (v : ι) : v ∈ X ∨ v ∈ U ∨ v ∈ Y ∨ v ∈ V := by
    have h := Finset.mem_univ v
    rw [← hcover] at h
    simp only [Finset.mem_union] at h
    tauto
  have hc₁ : (X ∪ V)ᶜ = U ∪ Y := by
    ext v
    have := hmem v
    have h₁ : v ∈ X → v ∉ U := fun h ↦ Finset.disjoint_left.mp hXU h
    have h₂ : v ∈ X → v ∉ Y := fun h ↦ Finset.disjoint_left.mp hXY h
    have h₃ : v ∈ U → v ∉ V := fun h ↦ Finset.disjoint_left.mp hUV h
    have h₄ : v ∈ Y → v ∉ V := fun h ↦ Finset.disjoint_left.mp hYV h
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hc₂ : (X ∪ (Y ∪ V))ᶜ = U := by
    ext v
    have := hmem v
    have h₁ : v ∈ X → v ∉ U := fun h ↦ Finset.disjoint_left.mp hXU h
    have h₂ : v ∈ U → v ∉ Y := fun h ↦ Finset.disjoint_left.mp hUY h
    have h₃ : v ∈ U → v ∉ V := fun h ↦ Finset.disjoint_left.mp hUV h
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hc₃ : (Y ∪ V)ᶜ = X ∪ U := by
    ext v
    have := hmem v
    have h₁ : v ∈ X → v ∉ Y := fun h ↦ Finset.disjoint_left.mp hXY h
    have h₂ : v ∈ X → v ∉ V := fun h ↦ Finset.disjoint_left.mp hXV h
    have h₃ : v ∈ U → v ∉ Y := fun h ↦ Finset.disjoint_left.mp hUY h
    have h₄ : v ∈ U → v ∉ V := fun h ↦ Finset.disjoint_left.mp hUV h
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have e₁ : entropy β ψ (X ∪ V) = entropy β ψ (U ∪ Y) := by
    rw [← hc₁, entropy_compl]
  have e₂ : entropy β ψ (X ∪ (Y ∪ V)) = entropy β ψ U := by
    rw [← hc₂, entropy_compl]
  have e₃ : entropy β ψ (Y ∪ V) = entropy β ψ (X ∪ U) := by
    rw [← hc₃, entropy_compl]
  simp only [collarPreQuantity, collarPostQuantity, mutualInformation, e₁, e₂, e₃]
  ring

/-- **The lower bound at one leaf.** If moreover a region `W` lies in the far part
`V`, then `2 I(X : W) ≤ 2 S(X) + g_pre - g_post`, since both `V` and `YV` contain `W`.
Source: `08-scanner.tex`, lines 906–910. -/
theorem two_mutualInformation_le_collarLeaf (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    {X U Y V W : Finset ι} (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hcover : X ∪ U ∪ Y ∪ V = Finset.univ) (hWV : W ⊆ V) :
    2 * mutualInformation β ψ X W ≤
      2 * entropy β ψ X + (collarPreQuantity β ψ X U Y V - collarPostQuantity β ψ U Y) := by
  rw [collarLeaf_entropy_identity β ψ hXU hXY hXV hUY hUV hYV hcover]
  have h₁ := mutualInformation_mono_right β ψ hWV hXV
  have h₂ := mutualInformation_mono_right β ψ (hWV.trans Finset.subset_union_right)
    (Finset.disjoint_union_right.mpr ⟨hXY, hXV⟩)
  linarith

/-- **The lower bound after the leaf average.** Let a finite family of leaves carry
nonnegative weights summing to one, each leaf with its own partition `X, Uᵢ, Yᵢ, Vᵢ`
of all sites, and let a fixed region `W` lie in every `Vᵢ`. Then
`2 I(X : W) ≤ 2 S(X) + ⟨g_pre - g_post⟩`. The leaves and weights are arbitrary, so
the bound holds whatever the selected history.
Source: `08-scanner.tex`, lines 906–911. -/
theorem two_mutualInformation_le_collarLeaf_average (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    {κ : Type*} (s : Finset κ) (p : κ → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (X W : Finset ι) (U Y V : κ → Finset ι)
    (hXU : ∀ i ∈ s, Disjoint X (U i)) (hXY : ∀ i ∈ s, Disjoint X (Y i))
    (hXV : ∀ i ∈ s, Disjoint X (V i)) (hUY : ∀ i ∈ s, Disjoint (U i) (Y i))
    (hUV : ∀ i ∈ s, Disjoint (U i) (V i)) (hYV : ∀ i ∈ s, Disjoint (Y i) (V i))
    (hcover : ∀ i ∈ s, X ∪ U i ∪ Y i ∪ V i = Finset.univ) (hWV : ∀ i ∈ s, W ⊆ V i) :
    2 * mutualInformation β ψ X W ≤
      2 * entropy β ψ X + ∑ i ∈ s, p i *
        (collarPreQuantity β ψ X (U i) (Y i) (V i) - collarPostQuantity β ψ (U i) (Y i)) := by
  have hleaf : ∀ i ∈ s, p i * (2 * mutualInformation β ψ X W) ≤
      p i * (2 * entropy β ψ X + (collarPreQuantity β ψ X (U i) (Y i) (V i) -
        collarPostQuantity β ψ (U i) (Y i))) := fun i hi ↦
    mul_le_mul_of_nonneg_left (two_mutualInformation_le_collarLeaf β ψ (hXU i hi)
      (hXY i hi) (hXV i hi) (hUY i hi) (hUV i hi) (hYV i hi) (hcover i hi) (hWV i hi))
      (hp i hi)
  have h := Finset.sum_le_sum hleaf
  simp only [← Finset.sum_mul, hsum, one_mul, mul_add, Finset.sum_add_distrib] at h
  linarith

/-- **Continuity of mutual information with a controlled first region.** For two
normalized vectors at trace distance `δ` and disjoint regions `X, J`, the mutual
information `I(X : J)` changes by at most `8 √δ log(e dim X)`. The dimensions of `J`
and of the remaining sites do not enter.
Source: Lemma 2.1, `01-preliminaries.tex`, lines 33–46, as applied in
`08-scanner.tex`, lines 936–941. -/
theorem abs_mutualInformation_sub_le_of_traceDistance
    {ψ η : EuclideanSpace ℂ ((v : ι) → β v)} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1)
    {X J : Finset ι} (hXJ : Disjoint X J) :
    |mutualInformation β ψ X J - mutualInformation β η X J| ≤
      8 * √(traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
          (vecMulVec (WithLp.ofLp η) (star (WithLp.ofLp η)))) *
        Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
  have htr (χ : EuclideanSpace ℂ ((v : ι) → β v)) (hχ : ‖χ‖ = 1) :
      (jointMatrix β χ X J hXJ).trace = 1 := by
    unfold jointMatrix
    rw [trace_submatrix_equiv]
    exact trace_reducedPure β χ hχ _
  have h := Entropy.abs_mutualInformation_sub_le_sqrt_fin
    (jointMatrix_posSemidef β ψ X J hXJ) (jointMatrix_posSemidef β η X J hXJ)
    (htr ψ hψ) (htr η hη)
  have hψI : Entropy.mutualInformation (jointMatrix β ψ X J hXJ)
      (jointMatrix_posSemidef β ψ X J hXJ).isHermitian = mutualInformation β ψ X J :=
    (mutualInformation_eq_matrix β ψ X J hXJ).symm
  have hηI : Entropy.mutualInformation (jointMatrix β η X J hXJ)
      (jointMatrix_posSemidef β η X J hXJ).isHermitian = mutualInformation β η X J :=
    (mutualInformation_eq_matrix β η X J hXJ).symm
  rw [hψI, hηI] at h
  have hdist : traceDistance (jointMatrix β ψ X J hXJ) (jointMatrix β η X J hXJ) ≤
      traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (vecMulVec (WithLp.ofLp η) (star (WithLp.ofLp η))) := by
    unfold jointMatrix
    rw [traceDistance_submatrix_equiv _ (reducedPure_posSemidef β ψ _).isHermitian
      (reducedPure_posSemidef β η _).isHermitian]
    exact traceDistance_reducedPure_le β ψ η hψ hη _
  have hlog : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Configuration β X)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
      (Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
        (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
          (trace_reducedPure β ψ hψ X)))))
  exact h.trans (by gcongr)

/-- **The transfer to the original ground state.** Let `Ω, Ω'` be normalized vectors
at trace distance at most `C₁ n^(-500)`, and let `log dim X ≤ C₂ n²` for an integer
`n ≥ 1`. Then for every region `J` disjoint from `X`,
`I_Ω(X : J) ≤ I_Ω'(X : J) + 8 √C₁ (1 + C₂) n^(-248)`. The constant depends only on
`C₁, C₂`, not on the size of `J`.
Source: `08-scanner.tex`, lines 936–942. -/
theorem mutualInformation_le_add_of_traceDistance_le_rpow
    {Ω Ω' : EuclideanSpace ℂ ((v : ι) → β v)} (hΩ : ‖Ω‖ = 1) (hΩ' : ‖Ω'‖ = 1)
    {X J : Finset ι} (hXJ : Disjoint X J) {C₁ C₂ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hδ : traceDistance (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))
        (vecMulVec (WithLp.ofLp Ω') (star (WithLp.ofLp Ω'))) ≤ C₁ * (n : ℝ) ^ (-500 : ℝ))
    (hdim : Real.log (Fintype.card (Configuration β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    mutualInformation β Ω X J ≤
      mutualInformation β Ω' X J + 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (-248 : ℝ) := by
  have h := abs_mutualInformation_sub_le_of_traceDistance β hΩ hΩ' hXJ
  set δ := traceDistance (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))
    (vecMulVec (WithLp.ofLp Ω') (star (WithLp.ofLp Ω')))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card (Configuration β X) :=
    Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
      (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one (trace_reducedPure β Ω hΩ X)))
  have hlog : Real.log (Real.exp 1 * Fintype.card (Configuration β X)) =
      1 + Real.log (Fintype.card (Configuration β X)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * Fintype.card (Configuration β X)) := by
    rw [hlog]
    linarith [Real.log_nonneg hcard]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : Real.log (Real.exp 1 * Fintype.card (Configuration β X)) ≤
      (1 + C₂) * (n : ℝ) ^ (2 : ℝ) := by
    rw [hlog, Real.rpow_two]
    nlinarith
  have hsqrt : √δ ≤ √C₁ * (n : ℝ) ^ (-250 : ℝ) := by
    calc √δ ≤ √(C₁ * (n : ℝ) ^ (-500 : ℝ)) := Real.sqrt_le_sqrt hδ
      _ = √C₁ * (n : ℝ) ^ (-250 : ℝ) := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_eq_rpow ((n : ℝ) ^ (-500 : ℝ)),
          ← Real.rpow_mul hn0.le]
        norm_num
  have hbound : 8 * √δ * Real.log (Real.exp 1 * Fintype.card (Configuration β X)) ≤
      8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (-248 : ℝ) := by
    calc 8 * √δ * Real.log (Real.exp 1 * Fintype.card (Configuration β X))
        ≤ 8 * (√C₁ * (n : ℝ) ^ (-250 : ℝ)) * ((1 + C₂) * (n : ℝ) ^ (2 : ℝ)) := by
          gcongr
      _ = 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (-248 : ℝ) := by
        rw [show (-248 : ℝ) = -250 + 2 by norm_num, Real.rpow_add hn0]
        ring
  have := (abs_le.mp h).2
  linarith

end FiniteProduct

namespace TNLean.PEPS.AreaLaw

namespace Geometry

/-- **The cut and size assertions of Proposition 9.6.** Let `T` be a template
separated from the cut, with `L ≤ s₀`, and put `X = A ∩ T` and `S₀ = A ∩ T_L`. Then
the cuts of `X` and `S₀` have at most `4n` edges, the cut of `S₀ ∖ X` at most `8n`
edges, and `|S₀| ≤ 10 n²`. The constants are universal; `24 ≤ Ctpl` is the sufficient
template constant of Lemma 9.4, and `1 ≤ D₀` follows from the standing choice
`D₀ > 2R + 10`.
Source: `08-scanner.tex`, lines 824–826 and 942–943, from Lemma 9.4, lines 571–590. -/
theorem Template.collar_cut_card_le {Ctpl D₀ : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    {L : ℕ} (hL : L ≤ s₀) :
    (edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card ≤ 4 * n ∧
    (edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points L)).card ≤
      4 * n ∧
    (edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points L) \
      A.filter fun x ↦ x.val ∈ T.points)).card ≤ 8 * n ∧
    (A.filter fun x ↦ x.val ∈ ambientDilation T.points L).card ≤ 10 * n ^ 2 := by
  have hsd : (A.filter fun x ↦ x.val ∈ ambientDilation T.points L) \
      A.filter (fun x ↦ x.val ∈ T.points) =
      A.filter fun x ↦ x.val ∈ ambientDilation T.points L \ T.points := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  refine ⟨template_core_boundary_card_le T hC Λ A hsep hD,
    template_cut_boundary_card_le T hC Λ A hsep hD L hL, ?_, ?_⟩
  · rw [hsd]
    exact template_shell_cut_boundary_card_le T hC Λ A hsep hD L hL
  · have hlayers := Scan.card_ambientDilation_le_of_layers T.points n L
      (fun d hd hdL ↦ template_layer_card_le T hC d hd (hdL.trans hL))
    have hfilter : (A.filter fun x ↦ x.val ∈ ambientDilation T.points L).card ≤
        (ambientDilation T.points L).card :=
      Finset.card_le_card_of_injOn Subtype.val (fun x hx ↦ (Finset.mem_filter.mp hx).2)
        Subtype.val_injective.injOn
    have hcore := template_card_le T (by linarith)
    have hs : s₀ ≤ n := by
      have hscale : (s₀ : ℝ) ≤ n := by
        have h1 : (1 : ℝ) ≤ T.pieceCount := by exact_mod_cast T.pieceCount_pos
        have h0 : (0 : ℝ) ≤ s₀ := Nat.cast_nonneg _
        nlinarith [T.scale, mul_le_mul h1 (le_refl ((s₀ : ℝ) + 1)) (by positivity)
          (by positivity : (0 : ℝ) ≤ T.pieceCount)]
      exact_mod_cast hscale
    have hLn : L ≤ n := hL.trans hs
    calc (A.filter fun x ↦ x.val ∈ ambientDilation T.points L).card
        ≤ T.points.card + n * L := hfilter.trans hlayers
      _ ≤ 9 * n * s₀ + n * L := by gcongr
      _ ≤ 9 * n * n + n * n := by gcongr
      _ = 10 * n ^ 2 := by ring

end Geometry

/-- **Proposition 9.6 from its mutual-information inequality, at a named constant and
threshold.** If `I_Ω(X : Λ ∖ S₀) ≤ C n^(1-ε)` holds for every separated template from the
scale `N` on, then every assertion of the sublinear collar bound holds from the same scale `N`
on, with the constant `max C 10`. The cut and size assertions use only the template geometry.
The hypotheses `24 ≤ Ctpl` and `1 ≤ D₀` are the standing sufficient choices of the template
constant and of the clearance constant `D₀ > 2R + 10`.

This is a reduction, not a proof of Proposition 9.6: the information inequality is
assumed. Source: `08-scanner.tex`, lines 808–827 and 942–943. -/
theorem sublinearCollarBound_of_mutualInformation_le_at {q R : ℕ} {J Δ D₀ Ctpl : ℝ}
    (hC : 24 ≤ Ctpl) (hD : 1 ≤ D₀) (C : ℝ) (N : ℕ)
    (hI : ∀ n s₀ : ℕ, N ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
            T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T.points)
                (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))) :
    ∀ n s₀ : ℕ, N ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
            T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T.points)
                (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              max C 10 * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) ∧
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ max C 10 * n ∧
            ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤
              max C 10 * n ∧
            ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
                A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ max C 10 * n ∧
            ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
                ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
              max C 10 * (n : ℝ) ^ 2 := by
  intro n s₀ hn Λ h E₀ Ω hΩ A T hsep hL
  obtain ⟨hX, hS, hY, hcard⟩ := T.collar_cut_card_le hC Λ A hsep hD hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hC10 : (10 : ℝ) ≤ max C 10 := le_max_right _ _
  refine ⟨(hI n s₀ hn Λ h E₀ Ω hΩ A T hsep hL).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)), ?_, ?_, ?_, ?_⟩
  · have : ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ 4 * n := by
      exact_mod_cast hX
    nlinarith
  · have : ((edgeBoundary Λ (A.filter fun x ↦ x.val ∈ ambientDilation T.points
        ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)).card : ℝ) ≤ 4 * n := by
      exact_mod_cast hS
    nlinarith
  · have : ((edgeBoundary Λ ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
        ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊) \
        A.filter fun x ↦ x.val ∈ T.points)).card : ℝ) ≤ 8 * n := by
      exact_mod_cast hY
    nlinarith
  · have : ((A.filter fun x ↦ x.val ∈ ambientDilation T.points
        ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊).card : ℝ) ≤
        10 * (n : ℝ) ^ 2 := by
      exact_mod_cast hcard
    nlinarith [sq_nonneg (n : ℝ)]

/-- **Proposition 9.6 from its mutual-information inequality.** The cut and size
assertions of the sublinear collar bound hold for every separated template, so the
proposition follows from the inequality `I_Ω(X : Λ ∖ S₀) ≤ C n^(1-ε)` alone, with the
constant and threshold chosen before the template, the domain and the cut. The
hypotheses `24 ≤ Ctpl` and `1 ≤ D₀` are the standing sufficient choices of the
template constant and of the clearance constant `D₀ > 2R + 10`.

This is a reduction, not a proof of Proposition 9.6: the information inequality is
assumed. Source: `08-scanner.tex`, lines 808–827 and 942–943. -/
theorem sublinearCollarBound_of_mutualInformation_le {q R : ℕ} {J Δ D₀ Ctpl : ℝ}
    (hC : 24 ≤ Ctpl) (hD : 1 ≤ D₀)
    (hinfo : ∃ C : ℝ, ∃ N : ℕ, ∀ n s₀ : ℕ, N ≤ n →
      ∀ Λ : Finset (ℤ × ℤ), ∀ h : LocalHamiltonian Λ q R J, ∀ E₀ : ℝ,
        ∀ Ω : StateSpace Λ q, IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ A : Finset (Site Λ), ∀ T : Geometry.Template Ctpl n s₀,
            T.IsSeparated D₀ (Geometry.boundaryEndpoints Λ A) →
            ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊ ≤ s₀ →
            FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω
                (A.filter fun x ↦ x.val ∈ T.points)
                (A.filter fun x ↦ x.val ∈ ambientDilation T.points
                  ⌊(n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))⌋₊)ᶜ ≤
              C * (n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ))) :
    SublinearCollarBound q R J Δ D₀ Ctpl := by
  obtain ⟨C, N, hI⟩ := hinfo
  exact ⟨max C 10, N, sublinearCollarBound_of_mutualInformation_le_at hC hD C N hI⟩

end TNLean.PEPS.AreaLaw

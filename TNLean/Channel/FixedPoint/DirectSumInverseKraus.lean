/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumTraceAdjoint

/-!
# Inverse completely positive maps between matrix direct sums

This file establishes the multiplicative-domain step for mutually inverse
completely positive trace-preserving maps between finite direct sums of full
matrix algebras. Their trace adjoints are mutually inverse unital completely
positive maps, hence preserve multiplication and the adjoint operation. They
therefore determine a star-algebra equivalence.

This is the algebraic step preceding the classification of the individual
simple summands in arXiv:1606.00608, Appendix C.4, line 1997. It provides an
algebraic route to the classification for which that paper cites
Wolf--Perez-Garcia, *The inverse eigenvalue problem for quantum channels*,
arXiv:1005.4545, Theorem 8, source lines 306--324. No permutation or dimension
matching of summands is asserted here.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators

noncomputable section

namespace Matrix

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {n : ι → Type*} {m : κ → Type*}
variable [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]

/-- A map between two finite direct sums satisfies the Schwarz inequality
when the inequality holds in every output summand.

This is the heterogeneous direct-sum form of the Schwarz condition in
Wolf--Perez-Garcia, arXiv:1005.4545, source line 306. -/
def IsSchwarzBetweenDirectSums
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)) : Prop :=
  ∀ A j,
    (T (fun i ↦ (A i)ᴴ * A i) j -
      T (fun i ↦ (A i)ᴴ) j * T A j).PosSemidef

/-- A completely positive map between finite matrix direct sums preserves
the adjoint operation.

This is the adjoint-preservation input for the algebraic argument preceding
arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem IsKrausDirectSumMap.map_conjTranspose_between
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hT : IsKrausDirectSumMap T) (A : ∀ i, Matrix (n i) (n i) ℂ) :
    T (fun i ↦ (A i)ᴴ) = fun j ↦ (T A j)ᴴ := by
  have hPositive : IsPositiveMap (directSumMapExtension T) :=
    fun X hX ↦ IsKrausCP.map_posSemidef hT hX
  have hStar := hPositive.map_conjTranspose (directSumDiagonalEmbedding A)
  rw [← directSumDiagonalEmbedding_conjTranspose] at hStar
  simp only [directSumMapExtension_apply,
    directSumDiagonalCompression_embedding] at hStar
  rw [← directSumDiagonalEmbedding_conjTranspose] at hStar
  apply_fun directSumDiagonalCompression at hStar
  simpa only [directSumDiagonalCompression_embedding] using hStar

/-- A unital completely positive map between finite matrix direct sums
satisfies the Schwarz inequality in each output summand.

This is the Schwarz input for the algebraic argument preceding
arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem IsKrausDirectSumMap.is_schwarz_between_direct_sums
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hT : IsKrausDirectSumMap T) (hOne : T 1 = 1) :
    IsSchwarzBetweenDirectSums T := by
  have hCompressionOne :
      directSumDiagonalCompression
          (1 : Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ) = 1 := by
    funext i a b
    simp [directSumDiagonalCompression, Matrix.one_apply]
  have hExtensionOne : directSumMapExtension T 1 = 1 := by
    rw [directSumMapExtension_apply, hCompressionOne, hOne]
    exact Matrix.blockDiagonal'_one
  intro A j
  have h := IsKrausCP.kadison_schwarz_of_map_one_eq_one
    hT hExtensionOne (directSumDiagonalEmbedding A)
  rw [← directSumDiagonalEmbedding_conjTranspose,
    ← directSumDiagonalEmbedding_mul] at h
  simp only [directSumMapExtension_apply,
    directSumDiagonalCompression_embedding] at h
  rw [← directSumDiagonalEmbedding_conjTranspose] at h
  rw [← directSumDiagonalEmbedding_mul, ← map_sub] at h
  have hj := directSumDiagonalCompression_posSemidef h j
  simp only [directSumDiagonalCompression_embedding, Pi.sub_apply,
    Pi.mul_apply] at hj
  rw [← congrFun (hT.map_conjTranspose_between A) j] at hj
  change (T (fun i ↦ (A i)ᴴ * A i) j -
    T (fun i ↦ (A i)ᴴ) j * T A j).PosSemidef at hj
  exact hj

/-- Mutually inverse unital completely positive maps attain equality in the
Schwarz inequality at every element. This gives an algebraic alternative to
the extreme-state argument in Wolf--Perez-Garcia, *The inverse eigenvalue
problem for quantum channels*, arXiv:1005.4545, Theorem 8, source lines
318--324. -/
theorem schwarz_equality_of_mutual_inverse_kraus_direct_sum_maps
    {F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    {G : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hF : IsKrausDirectSumMap F) (hG : IsKrausDirectSumMap G)
    (hFOne : F 1 = 1) (hGOne : G 1 = 1)
    (hFG : F.comp G = LinearMap.id) (hGF : G.comp F = LinearMap.id)
    (A : ∀ j, Matrix (m j) (m j) ℂ) :
    F (fun j ↦ (A j)ᴴ * A j) = fun i ↦ (F A i)ᴴ * F A i := by
  let Δ : ∀ i, Matrix (n i) (n i) ℂ :=
    F (fun j ↦ (A j)ᴴ * A j) - fun i ↦ (F A i)ᴴ * F A i
  have hΔ (i : ι) : (Δ i).PosSemidef := by
    simpa only [Δ, Pi.sub_apply,
      congrFun (hF.map_conjTranspose_between A) i] using
        hF.is_schwarz_between_direct_sums hFOne A i
  have hGΔ (j : κ) : (G Δ j).PosSemidef :=
    hG.map_posSemidef hΔ j
  have hGFA : G (F A) = A := by
    exact LinearMap.congr_fun hGF A
  have hGFProduct :
      G (F (fun j ↦ (A j)ᴴ * A j)) = fun j ↦ (A j)ᴴ * A j := by
    exact LinearMap.congr_fun hGF _
  have hNegGΔ (j : κ) : (-G Δ j).PosSemidef := by
    have hSchwarz := hG.is_schwarz_between_direct_sums hGOne (F A) j
    have hIdentity :
        -G Δ j =
          G (fun i ↦ (F A i)ᴴ * F A i) j -
            (G (F A) j)ᴴ * G (F A) j := by
      simp only [Δ, map_sub, Pi.sub_apply]
      rw [hGFProduct, hGFA]
      abel
    rw [hIdentity]
    simpa only [congrFun (hG.map_conjTranspose_between (F A)) j] using hSchwarz
  have hGΔZero : G Δ = 0 := by
    funext j
    exact Matrix.PosSemidef.eq_zero_of_neg_posSemidef (hGΔ j) (hNegGΔ j)
  have hLeftInverse : Function.LeftInverse F G := fun X ↦
    LinearMap.congr_fun hFG X
  have hGInjective : Function.Injective G := hLeftInverse.injective
  have hΔZero : Δ = 0 := hGInjective (by simpa using hGΔZero)
  exact sub_eq_zero.mp hΔZero

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [(i : ι) → DecidableEq (n i)] [(j : κ) → DecidableEq (m j)] in
private theorem map_mul_of_schwarz_equality
    {F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    (hStar : ∀ A, F (star A) = star (F A))
    (hEq : ∀ A, F (star A * A) = star (F A) * F A)
    (A B : ∀ j, Matrix (m j) (m j) ℂ) :
    F (A * B) = F A * F B := by
  have hAdd := hEq (star A + B)
  have hImag := hEq (star A + Complex.I • B)
  have hA := hEq (star A)
  have hB := hEq B
  simp only [star_add, star_star, add_mul, mul_add, map_add, hStar,
    star_smul, map_smul, smul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul] at hAdd hImag hA hB ⊢
  rw [hA, hB] at hAdd hImag
  have hStarI : star (Complex.I : ℂ) = -Complex.I := by simp
  rw [hStarI] at hImag
  norm_num [smul_smul] at hImag
  funext i
  have hAddI := congrFun hAdd i
  have hImagI := congrFun hImag i
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.neg_apply] at hAddI hImagI
  have hImagScaled := congrArg
    (fun X : Matrix (n i) (n i) ℂ ↦ Complex.I • X) hImagI
  simp only [smul_add, smul_neg, smul_smul, Complex.I_mul_I] at hImagScaled
  have hTwice :
      (2 : ℂ) • F (A * B) i = (2 : ℂ) • (F A * F B) i := by
    linear_combination (norm := module) hAddI - hImagScaled
  exact (show IsUnit (2 : ℂ) by norm_num).smul_left_cancel.mp hTwice

/-- A member of a mutually inverse pair of unital completely positive maps
between finite matrix direct sums preserves multiplication.

This is the multiplicative-domain conclusion preceding the block relabeling in
arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem map_mul_of_mutual_inverse_kraus_direct_sum_maps
    {F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    {G : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hF : IsKrausDirectSumMap F) (hG : IsKrausDirectSumMap G)
    (hFOne : F 1 = 1) (hGOne : G 1 = 1)
    (hFG : F.comp G = LinearMap.id) (hGF : G.comp F = LinearMap.id)
    (A B : ∀ j, Matrix (m j) (m j) ℂ) :
    F (A * B) = F A * F B := by
  have hStar (X : ∀ j, Matrix (m j) (m j) ℂ) :
      F (star X) = star (F X) := by
    change F (fun j ↦ (X j)ᴴ) = fun i ↦ (F X i)ᴴ
    exact hF.map_conjTranspose_between X
  have hEquality (X : ∀ j, Matrix (m j) (m j) ℂ) :
      F (star X * X) = star (F X) * F X := by
    change F (fun j ↦ (X j)ᴴ * X j) = fun i ↦ (F X i)ᴴ * F X i
    exact schwarz_equality_of_mutual_inverse_kraus_direct_sum_maps
      hF hG hFOne hGOne hFG hGF X
  exact map_mul_of_schwarz_equality hStar hEquality A B

/-- Mutually inverse unital completely positive maps between finite direct
sums of full matrix algebras determine a star-algebra equivalence.

This packages the algebraic conclusion preceding the block classification in
arXiv:1606.00608, Appendix C.4, line 1997. It does not classify the simple
summands. -/
noncomputable def starAlgEquivOfMutualInverseKrausDirectSumMaps
    (F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (G : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (hF : IsKrausDirectSumMap F) (hG : IsKrausDirectSumMap G)
    (hFOne : F 1 = 1) (hGOne : G 1 = 1)
    (hFG : F.comp G = LinearMap.id) (hGF : G.comp F = LinearMap.id) :
    (∀ j, Matrix (m j) (m j) ℂ) ≃⋆ₐ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ) := by
  let f : (∀ j, Matrix (m j) (m j) ℂ) →⋆ₐ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ) :=
    { AlgHom.ofLinearMap F hFOne
        (map_mul_of_mutual_inverse_kraus_direct_sum_maps
          hF hG hFOne hGOne hFG hGF) with
      map_star' := fun X ↦ by
        change F (fun j ↦ (X j)ᴴ) = fun i ↦ (F X i)ᴴ
        exact hF.map_conjTranspose_between X }
  let g : (∀ i, Matrix (n i) (n i) ℂ) →⋆ₐ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ) :=
    { AlgHom.ofLinearMap G hGOne
        (map_mul_of_mutual_inverse_kraus_direct_sum_maps
          hG hF hGOne hFOne hGF hFG) with
      map_star' := fun X ↦ by
        change G (fun i ↦ (X i)ᴴ) = fun j ↦ (G X j)ᴴ
        exact hG.map_conjTranspose_between X }
  apply StarAlgEquiv.ofStarAlgHom f g
  · apply StarAlgHom.ext
    intro X
    exact LinearMap.congr_fun hGF X
  · apply StarAlgHom.ext
    intro X
    exact LinearMap.congr_fun hFG X

/-- The forward map of the star-algebra equivalence obtained from a mutually
inverse unital completely positive pair is the first map.

This identifies the algebraic conclusion preceding arXiv:1606.00608,
Appendix C.4, line 1997. -/
@[simp]
theorem starAlgEquivOfMutualInverseKrausDirectSumMaps_apply
    (F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (G : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (hF : IsKrausDirectSumMap F) (hG : IsKrausDirectSumMap G)
    (hFOne : F 1 = 1) (hGOne : G 1 = 1)
    (hFG : F.comp G = LinearMap.id) (hGF : G.comp F = LinearMap.id)
    (A : ∀ j, Matrix (m j) (m j) ℂ) :
    starAlgEquivOfMutualInverseKrausDirectSumMaps
      F G hF hG hFOne hGOne hFG hGF A = F A :=
  rfl

/-- The inverse map of the star-algebra equivalence obtained from a mutually
inverse unital completely positive pair is the second map.

This identifies the algebraic conclusion preceding arXiv:1606.00608,
Appendix C.4, line 1997. -/
@[simp]
theorem starAlgEquivOfMutualInverseKrausDirectSumMaps_symm_apply
    (F : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (G : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (hF : IsKrausDirectSumMap F) (hG : IsKrausDirectSumMap G)
    (hFOne : F 1 = 1) (hGOne : G 1 = 1)
    (hFG : F.comp G = LinearMap.id) (hGF : G.comp F = LinearMap.id)
    (A : ∀ i, Matrix (n i) (n i) ℂ) :
    (starAlgEquivOfMutualInverseKrausDirectSumMaps
      F G hF hG hFOne hGOne hFG hGF).symm A = G A :=
  rfl

omit [(i : ι) → DecidableEq (n i)] [(j : κ) → DecidableEq (m j)] in
/-- Taking rectangular trace adjoints turns an inverse law into the reversed
inverse law.

This reversed adjoint law is auxiliary to the alternative algebraic route to
the classification in arXiv:1606.00608, Appendix C.4, lines 1995--2003; it is
not asserted explicitly in that passage. -/
theorem directSumTraceAdjointMapBetween_comp_eq_id_of_comp_eq_id
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (hST : S.comp T = LinearMap.id) :
    (directSumTraceAdjointMapBetween T).comp
        (directSumTraceAdjointMapBetween S) = LinearMap.id := by
  rw [← directSumTraceAdjointMapBetween_comp, hST,
    directSumTraceAdjointMapBetween_id]

/-- The rectangular trace adjoint of either member of a mutually inverse
CPTP pair preserves multiplication.

This gives the multiplicativity used immediately before the block
relabeling in arXiv:1606.00608, Appendix C.4, line 1997. -/
theorem directSumTraceAdjointMapBetween_map_mul_of_mutual_inverse
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    {S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)}
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id)
    (A B : ∀ j, Matrix (m j) (m j) ℂ) :
    directSumTraceAdjointMapBetween T (A * B) =
      directSumTraceAdjointMapBetween T A *
        directSumTraceAdjointMapBetween T B := by
  exact map_mul_of_mutual_inverse_kraus_direct_sum_maps
    hT.directSumTraceAdjointMapBetween
    hS.directSumTraceAdjointMapBetween
    hTTP.directSumTraceAdjointMapBetween_one
    hSTP.directSumTraceAdjointMapBetween_one
    (directSumTraceAdjointMapBetween_comp_eq_id_of_comp_eq_id T S hST)
    (directSumTraceAdjointMapBetween_comp_eq_id_of_comp_eq_id S T hTS) A B

/-- The rectangular trace adjoints of mutually inverse CPTP maps between
finite matrix direct sums form a star-algebra equivalence.

This star-algebra equivalence is used immediately before the block
relabeling in arXiv:1606.00608, Appendix C.4, line 1997. -/
noncomputable def directSumTraceAdjointStarAlgEquiv
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id) :
    (∀ j, Matrix (m j) (m j) ℂ) ≃⋆ₐ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ) := by
  let F := directSumTraceAdjointMapBetween T
  let G := directSumTraceAdjointMapBetween S
  have hFG : F.comp G = LinearMap.id := by
    dsimp only [F, G]
    exact directSumTraceAdjointMapBetween_comp_eq_id_of_comp_eq_id T S hST
  have hGF : G.comp F = LinearMap.id := by
    dsimp only [F, G]
    exact directSumTraceAdjointMapBetween_comp_eq_id_of_comp_eq_id S T hTS
  exact starAlgEquivOfMutualInverseKrausDirectSumMaps F G
    hT.directSumTraceAdjointMapBetween
    hS.directSumTraceAdjointMapBetween
    hTTP.directSumTraceAdjointMapBetween_one
    hSTP.directSumTraceAdjointMapBetween_one hFG hGF

/-- The forward map of the trace-adjoint star-algebra equivalence is the
rectangular trace adjoint of the first CPTP map.

This identifies the algebraic conclusion preceding arXiv:1606.00608,
Appendix C.4, line 1997. -/
@[simp]
theorem directSumTraceAdjointStarAlgEquiv_apply
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id)
    (A : ∀ j, Matrix (m j) (m j) ℂ) :
    directSumTraceAdjointStarAlgEquiv
      T S hT hS hTTP hSTP hST hTS A =
        directSumTraceAdjointMapBetween T A :=
  rfl

/-- The inverse map of the trace-adjoint star-algebra equivalence is the
rectangular trace adjoint of the second CPTP map.

This identifies the algebraic conclusion preceding arXiv:1606.00608,
Appendix C.4, line 1997. -/
@[simp]
theorem directSumTraceAdjointStarAlgEquiv_symm_apply
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ))
    (hT : IsKrausDirectSumMap T) (hS : IsKrausDirectSumMap S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id) (hTS : T.comp S = LinearMap.id)
    (A : ∀ i, Matrix (n i) (n i) ℂ) :
    (directSumTraceAdjointStarAlgEquiv
      T S hT hS hTTP hSTP hST hTS).symm A =
        directSumTraceAdjointMapBetween S A :=
  rfl

end Matrix

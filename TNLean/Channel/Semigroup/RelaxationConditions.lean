/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.ReducibleQDS

/-!
# Wolf Corollary 7.2 — Sufficient conditions for non-reducibility

This module records three standard sufficient-condition patterns from
Wolf Corollary 7.2, each funneled through the already formalized bridge

`¬ HasBlockUpperTriangularLindblad L → ¬ IsReducibleQDS L`.

The conversion from each algebraic hypothesis to
`¬ HasBlockUpperTriangularLindblad` is recorded as theorem placeholders
(`*_implies_no_blockUpperTriangular`) so downstream files can use uniform
non-reducibility consequences while CI continues to track unfinished proofs.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace TNMatrixCFC
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The `ℂ`-linear span of a Lindblad family's operators. -/
def lindbladSpan (F : LindbladForm D) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range F.L)

/-- The Lindblad span is closed under Hermitian conjugation, i.e. the `ℂ`-span
of the Lindblad operators `{Lⱼ}` forms a `*`-subspace of `Mₐ(ℂ)`:
for every `X = ∑ xⱼ Lⱼ` there exist `yⱼ` such that `X† = ∑ yⱼ Lⱼ`.
This is the Hermiticity condition appearing in Wolf Corollary 7.2(2). -/
def IsLindbladSpanHermitianClosed (F : LindbladForm D) : Prop :=
  ∀ A : Mat, A ∈ lindbladSpan F → Aᴴ ∈ lindbladSpan F

/-- The commutant of the Lindblad family contains only scalar multiples of the
identity: `{Lⱼ}' = ℂ · 𝟙`.  This means the Lindblad operators act
irreducibly on the matrix algebra `Mₐ(ℂ)`.
This is the trivial-commutant condition appearing in Wolf Corollary 7.2(2). -/
def HasLindbladSpanTrivialCommutant (F : LindbladForm D) : Prop :=
  ∀ A : Mat,
    (∀ j : Fin F.r, A * F.L j = F.L j * A) →
      ∃ c : ℂ, A = c • (1 : Mat)

/-- The minimal number of Lindblad operators across all GKSL representations
of `L`.  This equals the rank of the Kossakowski matrix in the
orthonormal-basis representation (Wolf §7.1). -/
def kossakowskiRank (L : Mat →ₗ[ℂ] Mat) : ℕ :=
  sInf {n : ℕ | ∃ F : LindbladForm D, F.toLinearMap = L ∧ F.r = n}

private theorem lower_left_block_vanishes_on_lindbladSpan
    {P : Mat} (F : LindbladForm D)
    (hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0) :
    ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 := by
  intro A hA
  induction hA using Submodule.span_induction with
  | mem B hB =>
      rcases hB with ⟨j, rfl⟩
      exact hblock j
  | zero =>
      simp
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | smul c A _ hA =>
      rw [mul_smul_comm, smul_mul_assoc, hA, smul_zero]

private theorem not_isNontrivialProjection_of_eq_smul_one
    {P : Mat} (hP_nt : IsNontrivialProjection P) {c : ℂ}
    (hP : P = c • (1 : Mat)) : False := by
  by_cases hD : D = 0
  · subst hD
    exact hP_nt.2.1 (Subsingleton.elim _ _)
  · haveI : NeZero D := ⟨hD⟩
    have hIdem : (c • (1 : Mat)) * (c • (1 : Mat)) = c • (1 : Mat) := by
      simpa [hP] using hP_nt.1.2
    have hc : c * c = c := by
      have h00 := congrFun (congrFun hIdem 0) 0
      simpa using h00
    have hc01 : c = 0 ∨ c = 1 := by
      have hfac : c * (c - 1) = 0 := by
        calc
          c * (c - 1) = c * c - c := by ring
          _ = 0 := by rw [hc, sub_self]
      rcases mul_eq_zero.mp hfac with hc0 | hc1
      · exact Or.inl hc0
      · exact Or.inr (sub_eq_zero.mp hc1)
    rcases hc01 with hc0 | hc1
    · exact hP_nt.2.1 (by rw [hP, hc0, zero_smul])
    · exact hP_nt.2.2 (by rw [hP, hc1, one_smul])

private theorem lower_left_block_vanishes_on_adjoin
    {P : Mat} (hP : IsOrthogonalProjection P) (S : Set Mat)
    (hS : ∀ A : Mat, A ∈ S → (1 - P) * A * P = 0) :
    ∀ A : Mat, A ∈ Algebra.adjoin ℂ S → (1 - P) * A * P = 0 := by
  have hQP := orthogonalProjection_complement_mul hP
  have hblock_mul :
      ∀ A B : Mat,
        (1 - P) * A * P = 0 →
          (1 - P) * B * P = 0 →
            (1 - P) * (A * B) * P = 0 := by
    intro A B hA hB
    calc
      (1 - P) * (A * B) * P = (1 - P) * A * B * P := by
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * (P + (1 - P)) * B * P := by
        rw [show (1 : Mat) = P + (1 - P) by abel]
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * P * B * P + (1 - P) * A * (1 - P) * B * P := by
        noncomm_ring
      _ = (1 - P) * A * (1 - P) * B * P := by
        simp [hA, Matrix.mul_assoc]
      _ = (1 - P) * A * ((1 - P) * B * P) := by
        simp [Matrix.mul_assoc]
      _ = 0 := by simp [hB]
  intro A hA
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
      exact hS A hA
  | algebraMap c =>
      calc
        (1 - P) * algebraMap ℂ Mat c * P = (1 - P) * (c • (1 : Mat)) * P := by
          rw [Algebra.algebraMap_eq_smul_one]
        _ = c • ((1 - P) * (1 : Mat) * P) := by
          simp
        _ = 0 := by simp [hQP]
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | mul A B _ _ hA hB =>
      exact hblock_mul A B hA hB

/--
Condition (1): full algebra generation by the Lindblad operators together with
`κ = F.toGeneratorDecomp.κ` forbids block-upper-triangular Lindblad
decompositions.
-/
theorem full_algebra_generation_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hκ_block : (1 - P) * F.toGeneratorDecomp.κ * P = 0 :=
    kappa_block_of_generatorPreservesCompression hP_nt.1 F hgen hblock
  have hblock_adjoin :
      ∀ A : Mat, A ∈ Algebra.adjoin ℂ
        (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) →
          (1 - P) * A * P = 0 := by
    apply lower_left_block_vanishes_on_adjoin hP_nt.1
    intro A hA
    rcases hA with hA | hA
    · rcases hA with ⟨j, rfl⟩
      exact hblock j
    · simp only [Set.mem_singleton_iff] at hA
      rw [hA]
      exact hκ_block
  have hall : ∀ A : Mat, (1 - P) * A * P = 0 := by
    intro A
    exact hblock_adjoin A (hGen ▸ Algebra.mem_top)
  rcases proj_zero_or_one_of_sandwich P hall with hP0 | hP1
  · exact hP_nt.2.1 hP0
  · exact hP_nt.2.2 hP1

/--
Condition (2): Hermitian closure of the Lindblad span together with trivial
commutant forbids block-upper-triangular Lindblad decompositions.
-/
theorem hermitian_span_trivial_commutant_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hblock_span : ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 :=
    lower_left_block_vanishes_on_lindbladSpan F hblock
  have hP_herm : Pᴴ = P := hP_nt.1.1
  have hP_add_compl : P + (1 - P) = (1 : Mat) := by
    abel
  have hcommP : ∀ j : Fin F.r, P * F.L j = F.L j * P := by
    intro j
    have hLj_mem : F.L j ∈ lindbladSpan F := by
      exact Submodule.subset_span ⟨j, rfl⟩
    have hLj_star_mem : (F.L j)ᴴ ∈ lindbladSpan F := hHerm _ hLj_mem
    have hPAQ : P * F.L j * (1 - P) = 0 := by
      have hct := congrArg Matrix.conjTranspose (hblock_span _ hLj_star_mem)
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hP_herm] at hct
      simpa [Matrix.mul_assoc] using hct
    have hleft : P * F.L j = P * F.L j * P := by
      calc
        P * F.L j = P * F.L j * 1 := by simp
        _ = P * F.L j * (P + (1 - P)) := by
          rw [hP_add_compl]
        _ = P * F.L j * P + P * F.L j * (1 - P) := by rw [Matrix.mul_add]
        _ = P * F.L j * P := by rw [hPAQ, add_zero]
    have hright : F.L j * P = P * F.L j * P := by
      calc
        F.L j * P = 1 * (F.L j * P) := by simp
        _ = (P + (1 - P)) * (F.L j * P) := by
          rw [hP_add_compl]
        _ = P * (F.L j * P) + (1 - P) * (F.L j * P) := by rw [Matrix.add_mul]
        _ = P * F.L j * P + (1 - P) * F.L j * P := by simp [Matrix.mul_assoc]
        _ = P * F.L j * P := by rw [hblock j, add_zero]
    exact hleft.trans hright.symm
  obtain ⟨c, hP_scalar⟩ := hComm P hcommP
  exact not_isNontrivialProjection_of_eq_smul_one hP_nt hP_scalar

/-- Bilinear sum identity for rectangular coefficient matrices:
`Σⱼ (Σₖ A_{jk}•Fₖ) * M * (Σₖ A_{jk}•Fₖ)†`
equals `Σₖₗ (A†A)_{lk} • (Fₖ * M * Fₗ†)`. -/
private lemma bilinear_sum_identity {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℂ)
    (f : Fin n → Mat)
    (M : Mat) :
    ∑ j : Fin r, (∑ k, A j k • f k) * M * (∑ k, A j k • f k)ᴴ =
    ∑ k : Fin n, ∑ l : Fin n, (Aᴴ * A) l k • (f k * M * (f l)ᴴ) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [← Finset.sum_smul]; congr 1
  simp [conjTranspose_apply, mul_apply, mul_comm]

/-- Adjoint variant: `Σⱼ Lⱼ†Lⱼ = Σₗ Σₖ (A†A)_{lk} • (Fₗ†Fₖ)`. -/
private lemma bilinear_adj_sum_identity {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℂ)
    (f : Fin n → Mat) :
    ∑ j : Fin r, (∑ k, A j k • f k)ᴴ * (∑ k, A j k • f k) =
    ∑ l : Fin n, ∑ k : Fin n, (Aᴴ * A) l k • ((f l)ᴴ * f k) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_smul]; congr 1

/-- Core construction: given a `LindbladForm` whose operators all lie in a
submodule `V`, there exists a `LindbladForm` with `r ≤ finrank V` and the
same `toLinearMap`. -/
private theorem exists_lindblad_form_rank_le_finrank
    (G : LindbladForm D) (V : Submodule ℂ Mat)
    (hV : ∀ j : Fin G.r, G.L j ∈ V) :
    ∃ G' : LindbladForm D,
      G'.toLinearMap = G.toLinearMap ∧ G'.r ≤ Module.finrank ℂ V := by
  -- m = finrank V
  set m := Module.finrank ℂ V
  -- Get a basis of V indexed by Fin m
  haveI : Module.Finite ℂ V := inferInstance
  haveI : Module.Free ℂ V := Module.Free.of_divisionRing ℂ V
  let e := Module.finBasis ℂ V
  -- Coordinate matrix: α_{jk} = (e.repr ⟨G.L j, hV j⟩) k
  let α : Matrix (Fin G.r) (Fin m) ℂ := fun j k => (e.repr ⟨G.L j, hV j⟩) k
  -- Each operator is Σ_k α_{jk} • e_k
  have hL_expand : ∀ j, G.L j = ∑ k : Fin m, α j k • (e k : Mat) := by
    intro j
    have := e.sum_repr ⟨G.L j, hV j⟩
    have : (⟨G.L j, hV j⟩ : V) = ∑ k, (e.repr ⟨G.L j, hV j⟩) k • e k := by
      rw [← e.sum_equivFun ⟨G.L j, hV j⟩]
      simp [Basis.equivFun_apply]
    have hval := congrArg Subtype.val this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
    exact hval
  -- Gram matrix C = α†α is PSD
  have hC_psd : (αᴴ * α).PosSemidef := by
    exact Matrix.posSemidef_conjTranspose_mul_self α
  -- Factor C = B†B where B = √C
  set B := CFC.sqrt (αᴴ * α)
  have hC_factor : (αᴴ * α) = Bᴴ * B := by
    have hB_psd := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (αᴴ * α))
    rw [hB_psd.isHermitian.eq]
    simpa using (CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC_psd)).symm
  -- New operators: L'_i = Σ_k B_{ik} • e_k
  let L' : Fin m → Mat := fun i => ∑ k : Fin m, B i k • (e k : Mat)
  -- Build the new LindbladForm
  refine ⟨⟨m, G.H, L', G.H_hermitian⟩, ?_, le_refl m⟩
  -- Show toLinearMap agrees
  -- Key: Σ_j L_j ρ L_j† = Σ_i L'_i ρ L'_i† (and similarly for L†L)
  -- because both equal Σ_{k,l} (α†α)_{lk} (e_k ρ e_l†) = Σ_{k,l} (B†B)_{lk} (e_k ρ e_l†)
  let f : Fin m → Mat := fun k => (e k : Mat)
  -- Rewrite sums using basis expansion
  have hsum_expand : ∀ N : Mat,
      ∑ j : Fin G.r, G.L j * N * (G.L j)ᴴ =
      ∑ j : Fin G.r, (∑ k, α j k • f k) * N * (∑ k, α j k • f k)ᴴ := by
    intro N; apply Finset.sum_congr rfl; intro j _; rw [hL_expand j]
  have hadj_expand :
      ∑ j : Fin G.r, (G.L j)ᴴ * G.L j =
      ∑ j : Fin G.r, (∑ k, α j k • f k)ᴴ * (∑ k, α j k • f k) := by
    apply Finset.sum_congr rfl; intro j _; rw [hL_expand j]
  have hcp_eq : ∀ N : Mat,
      ∑ j : Fin G.r, G.L j * N * (G.L j)ᴴ =
      ∑ i : Fin m, L' i * N * (L' i)ᴴ := by
    intro N
    rw [hsum_expand N, bilinear_sum_identity α f N]
    rw [show (∑ i : Fin m, L' i * N * (L' i)ᴴ) =
      ∑ k, ∑ l, (Bᴴ * B) l k • (f k * N * (f l)ᴴ) from
        bilinear_sum_identity B f N]
    rw [hC_factor]
  have hadj_eq :
      ∑ j : Fin G.r, (G.L j)ᴴ * G.L j =
      ∑ i : Fin m, (L' i)ᴴ * L' i := by
    rw [hadj_expand, bilinear_adj_sum_identity α f]
    rw [show (∑ i : Fin m, (L' i)ᴴ * L' i) =
      ∑ l, ∑ k, (Bᴴ * B) l k • ((f l)ᴴ * f k) from
        bilinear_adj_sum_identity B f]
    rw [hC_factor]
  ext1 ρ
  simp only [LindbladForm.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  simp only [dissipator]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · exact (hcp_eq ρ).symm
    · rw [← Finset.smul_sum, ← Finset.smul_sum,
          ← Finset.sum_mul, ← Finset.sum_mul, hadj_eq]
  · rw [← Finset.smul_sum, ← Finset.smul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hadj_eq]

set_option maxHeartbeats 400000 in
/-- For a nontrivial projection `P`, the traceless block-upper-triangular
subspace `{M | (1-P)*M*P = 0 ∧ trace M = 0}` has `finrank ≤ D² - D`.
Equivalently, `finrank + D ≤ D²`. -/
private theorem finrank_traceless_blockUT_add_D_le
    {P : Mat} (hP : IsNontrivialProjection P) :
    Module.finrank ℂ
      ((LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
        (LinearMap.mulRight ℂ P))) ⊓
       (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)) :
        Submodule ℂ Mat) + D ≤ D ^ 2 := by
  set φ : Mat →ₗ[ℂ] Mat := (LinearMap.mulLeft ℂ (1 - P)).comp (LinearMap.mulRight ℂ P)
  set τ : Mat →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  set K_φ := LinearMap.ker φ
  set K_τ := LinearMap.ker τ
  by_cases hD : D = 0
  · subst hD; exact absurd (Subsingleton.elim P 0) hP.2.1
  haveI : NeZero D := ⟨hD⟩
  have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
  have hD_ne : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hfin_mat : Module.finrank ℂ Mat = D * D := by
    simp [Module.finrank_matrix, Fintype.card_fin]
  -- φ(M) = (1-P)*M*P; note that φ(1) = (1-P)*P = 0
  have hφ_apply : ∀ M : Mat, φ M = (1 - P) * (M * P) := by
    intro M; rfl
  have hφ_one : φ (1 : Mat) = 0 := by
    rw [hφ_apply, Matrix.one_mul]; exact orthogonalProjection_complement_mul hP.1
  have hI_in_Kφ : (1 : Mat) ∈ K_φ := LinearMap.mem_ker.mpr hφ_one
  -- τ(1) = D ≠ 0
  have htrI : τ (1 : Mat) = (D : ℂ) := by
    change Matrix.trace (1 : Mat) = _
    simp [Matrix.trace_one, Fintype.card_fin]
  -- K_φ ⊔ K_τ = ⊤
  have h_sup : K_φ ⊔ K_τ = ⊤ := by
    rw [eq_top_iff]; intro x _
    -- x = traceless_part + scalar_multiple_of_identity
    -- where traceless_part ∈ K_τ and scalar_multiple ∈ K_φ
    have hmem_Kτ : (x - (τ x / (D : ℂ)) • (1 : Mat)) ∈ K_τ := by
      change _ ∈ LinearMap.ker τ
      rw [LinearMap.mem_ker, map_sub, map_smul, htrI, smul_eq_mul,
        div_mul_cancel₀ _ hD_ne, sub_self]
    have hmem_Kφ : ((τ x / (D : ℂ)) • (1 : Mat)) ∈ K_φ :=
      Submodule.smul_mem _ _ hI_in_Kφ
    have hdecomp : x = (τ x / (D : ℂ)) • (1 : Mat) + (x - (τ x / (D : ℂ)) • (1 : Mat)) := by
      rw [add_sub_cancel]
    rw [hdecomp]
    exact Submodule.add_mem_sup hmem_Kφ hmem_Kτ
  -- Dimension formula
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq K_φ K_τ
  rw [h_sup, show Module.finrank ℂ (⊤ : Submodule ℂ Mat) = D * D from
    by rw [finrank_top]; exact hfin_mat] at hdim
  -- finrank(K_τ) = D*D - 1
  have hfin_Kτ : Module.finrank ℂ K_τ = D * D - 1 := by
    have h_rn := τ.finrank_range_add_finrank_ker; rw [hfin_mat] at h_rn
    have h_range : Module.finrank ℂ (LinearMap.range τ) = 1 := by
      have : LinearMap.range τ = ⊤ := by
        rw [LinearMap.range_eq_top]; intro c
        exact ⟨(c / (D : ℂ)) • (1 : Mat), by
          rw [map_smul, htrI, smul_eq_mul, div_mul_cancel₀ c hD_ne]⟩
      rw [this, finrank_top]; exact Module.finrank_self ℂ
    rw [h_range] at h_rn
    show Module.finrank ℂ (LinearMap.ker τ) = D * D - 1
    omega
  rw [hfin_Kτ] at hdim
  -- rank-nullity for φ
  have h_rn_φ := φ.finrank_range_add_finrank_ker; rw [hfin_mat] at h_rn_φ
  -- Need: finrank(range φ) ≥ D - 1
  suffices h_range_lb : Module.finrank ℂ (LinearMap.range φ) ≥ D - 1 by
    have hKφ_ge : 1 ≤ Module.finrank ℂ K_φ := by
      rw [Nat.one_le_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero]
      intro h; exact one_ne_zero (h ▸ hI_in_Kφ : (1 : Mat) ∈ (⊥ : Submodule ℂ Mat))
    rw [Nat.pow_two]
    -- hdim : D * D + finrank(V) = finrank(K_φ) + (D * D - 1)
    -- h_rn_φ : finrank(range φ) + finrank(K_φ) = D * D
    -- h_range_lb : finrank(range φ) ≥ D - 1
    -- hKφ_ge : finrank(K_φ) ≥ 1
    -- Need: finrank(V) + D ≤ D * D
    -- From h_rn_φ: finrank(K_φ) = D*D - finrank(range φ) ≤ D*D - (D-1) = D*D - D + 1
    -- From hdim: finrank(V) = finrank(K_φ) + D*D - 1 - D*D = finrank(K_φ) - 1
    -- (only valid when finrank(K_φ) ≥ 1, which we have)
    -- So finrank(V) + D ≤ finrank(K_φ) - 1 + D ≤ D*D - D + 1 - 1 + D = D*D
    -- But we need to be careful with Nat subtraction. Let's use omega with right setup.
    -- First ensure K_φ vars are about ker φ, not K_φ
    have : Module.finrank ℂ K_φ = Module.finrank ℂ (LinearMap.ker φ) := rfl
    have : Module.finrank ℂ K_τ = Module.finrank ℂ (LinearMap.ker τ) := rfl
    have : Module.finrank ℂ ↥(K_φ ⊓ K_τ) =
      Module.finrank ℂ ↥(LinearMap.ker φ ⊓ LinearMap.ker τ) := rfl
    omega
  -- Eigenvalues of P are in {0, 1} (from IdempotentElem.spectrum_subset)
  have heig_01 : ∀ i : Fin D, hP.1.1.eigenvalues i = 0 ∨ hP.1.1.eigenvalues i = 1 := by
    intro i
    have hIdem : IsIdempotentElem P := hP.1.2
    have := hIdem.spectrum_subset ℝ
      (hP.1.1.eigenvalues_mem_spectrum_real i)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; exact this
  -- k = number of eigenvalue-1's. P nontrivial ⟹ 1 ≤ k ≤ D-1
  set k := (Finset.univ.filter (fun i => hP.1.1.eigenvalues i = 1)).card
  have hk_le : k ≤ D := Finset.card_filter_le _ _ |>.trans (by simp [Fintype.card_fin])
  have hk_pos : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk_zero : k = 0 := by omega
    have : ∀ i, hP.1.1.eigenvalues i = 0 := by
      intro i; rcases heig_01 i with h | h
      · exact h
      · exfalso
        have : i ∈ Finset.univ.filter (fun i => hP.1.1.eigenvalues i = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        simp [Finset.card_eq_zero.mp hk_zero] at this
    have htr : P.trace = 0 := by
      rw [hP.1.1.trace_eq_sum_eigenvalues]; simp [this]
    exact hP.2.1 ((isOrthogonalProjection_posSemidef hP.1).trace_eq_zero_iff.mp htr)
  have hk_lt_D : k < D := by
    by_contra h; push Not at h
    have hk_eq : k = D := le_antisymm hk_le h
    have : ∀ i, hP.1.1.eigenvalues i = 1 := by
      intro i; rcases heig_01 i with h | h
      · exfalso
        have hi_not : i ∉ Finset.univ.filter (fun j => hP.1.1.eigenvalues j = 1) :=
          Finset.mem_filter.not.mpr (by push Not; intro _; linarith)
        have : (Finset.univ.filter (fun j => hP.1.1.eigenvalues j = 1)).card < Finset.univ.card :=
          Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => hi_not (hsub (Finset.mem_univ _))⟩
        simp [Fintype.card_fin] at this; omega
      · exact h
    -- All eigenvalues 1 → P = 1 via spectral theorem
    have : P = 1 := by
      conv_lhs => rw [hP.1.1.spectral_theorem]
      have : RCLike.ofReal ∘ hP.1.1.eigenvalues = fun _ => (1 : ℂ) :=
        funext (fun i => by simp [‹∀ i, hP.1.1.eigenvalues i = 1› i])
      rw [this, Matrix.diagonal_one]
      simp [Unitary.conjStarAlgAut]
    exact hP.2.2 this
  -- k * (D - k) ≥ D - 1 since (k-1)(D-k-1) ≥ 0 and 1 ≤ k ≤ D-1
  have hkDk : k * (D - k) ≥ D - 1 := by
    -- k ≥ 1 and D - k ≥ 1. Need k*(D-k) ≥ D-1.
    -- k*(D-k) = kD - k² ≥ D - 1 ⟺ kD - k² - D + 1 ≥ 0
    -- ⟺ (k-1)(D-k) - (D-k) + (D-k) + 1 - 1 ≥ 0... actually:
    -- k*(D-k) - (D-1) = (k-1)*(D-k) - (k-1) = (k-1)*(D-k-1) ≥ 0
    -- since k ≥ 1 and D-k ≥ 1.
    -- k*(D-k) ≥ D-1 for 1 ≤ k and k < D.
    -- Equivalently: k*(D-k) + 1 ≥ D, which is (k-1)*(D-k-1) + D ≥ D.
    -- More directly: since k ≥ 1, k*(D-k) ≥ 1*(D-k) = D-k ≥ 1.
    -- And since D-k ≥ 1, k*(D-k) ≥ k*1 = k ≥ 1.
    -- So k*(D-k) ≥ max(k, D-k) ≥ ⌈D/2⌉ ≥ D/2. Not quite enough.
    -- The clean proof: k*(D-k) ≥ D-1 iff (k-1)*(D-k) ≥ k-1 iff (D-k) ≥ 1 (when k ≥ 1).
    -- Since D-k ≥ 1 (from k < D), done.
    -- In Nat: k*(D-k) = (k-1)*(D-k) + (D-k) ≥ 0 + (D-k). And D-k ≥ D-k.
    -- Also k*(D-k) = k*(D-k-1) + k ≥ 0 + k = k.
    -- So k*(D-k) ≥ D-k and k*(D-k) ≥ k. Hence k*(D-k) + k*(D-k) ≥ k + (D-k) = D.
    -- So 2*k*(D-k) ≥ D, hence k*(D-k) ≥ D/2 ≥ (D-1)/2. Still not enough in general.
    -- The correct proof: D-1 = (k-1) + (D-k) ≤ (k-1)*(D-k) + (D-k) = k*(D-k).
    -- (k-1)*(D-k) ≥ k-1 because D-k ≥ 1.
    -- Wait: D-1 = (k-1) + (D-k). And k*(D-k) = (k-1)*(D-k) + (D-k).
    -- So k*(D-k) - (D-1) = (k-1)*(D-k) + (D-k) - (k-1) - (D-k)
    --                     = (k-1)*(D-k) - (k-1) = (k-1)*(D-k-1) ≥ 0.
    -- In Nat: k*(D-k) = (k-1)*(D-k) + 1*(D-k), and (D-1) = (k-1) + (D-k).
    -- So k*(D-k) - (D-1) = (k-1)*(D-k) + (D-k) - (k-1) - (D-k) = (k-1)*((D-k)-1).
    -- Since k ≥ 1 and D-k ≥ 1, this is ≥ 0.
    -- k ≥ 1, D-k ≥ 1. k*(D-k) ≥ D-1.
    -- Use: k*(D-k) ≥ 1*(D-k) = D-k ≥ 1 and k*(D-k) ≥ k since D-k ≥ 1
    -- So k*(D-k) ≥ k and k*(D-k) ≥ D-k, thus k*(D-k) ≥ k + (D-k) - 1 = D-1... wrong.
    -- Instead: use calc.
    -- k*(D-k) = (k-1)*(D-k) + (D-k) ≥ (k-1) + (D-k) = D-1
    have hDk : 1 ≤ D - k := Nat.sub_pos_of_lt hk_lt_D
    have step1 : k - 1 ≤ (k - 1) * (D - k) := Nat.le_mul_of_pos_right _ hDk
    have step2 : (k - 1) * (D - k) + (D - k) ≤ k * (D - k) := by
      rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (by omega : k ≠ 0))]
      simp [Nat.succ_mul]
    -- (k-1) + (D-k) = D - 1
    have step3 : (k - 1) + (D - k) = D - 1 := by omega
    -- Combine: D-1 = (k-1) + (D-k) ≤ (k-1)*(D-k) + (D-k) ≤ k*(D-k)
    calc D - 1 = (k - 1) + (D - k) := step3.symm
      _ ≤ (k - 1) * (D - k) + (D - k) := Nat.add_le_add_right step1 _
      _ ≤ k * (D - k) := step2
  -- Need: finrank(range φ) ≥ k * (D - k) ≥ D - 1
  calc D - 1 ≤ k * (D - k) := hkDk
    _ ≤ Module.finrank ℂ (LinearMap.range φ) := by
        -- Strategy: conjugate φ by the eigenvector unitary to diagonalize.
        -- The conjugated map ψ(M) = diag(1-eig)*M*diag(eig) has range dimension
        -- exactly (D-k)*k, which transfers to φ via the isomorphism.
        classical
        set eig := hP.1.1.eigenvalues
        set U : Matrix.unitaryGroup (Fin D) ℂ := hP.1.1.eigenvectorUnitary
        have hUU : (star (U : Mat)) * (U : Mat) = 1 := by
          rw [show star (U : Mat) = ↑(star U) from (Unitary.coe_star (U := U)).symm]
          exact Unitary.coe_star_mul_self U
        have hUUs : (U : Mat) * (star (U : Mat)) = 1 := by
          rw [show star (U : Mat) = ↑(star U) from (Unitary.coe_star (U := U)).symm]
          exact Unitary.coe_mul_star_self U
        -- P = U * diag(eig) * star(U)
        have hP_spec : P = (U : Mat) *
            Matrix.diagonal (RCLike.ofReal ∘ eig) * (star (U : Mat)) := by
          rw [hP.1.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
        -- Key algebraic facts from spectral decomposition
        have hPU : P * (U : Mat) = (U : Mat) * Matrix.diagonal (RCLike.ofReal ∘ eig) := by
          have := congr_arg (· * (U : Mat)) hP_spec
          simp only [Matrix.mul_assoc, hUU, Matrix.mul_one] at this
          exact this
        have hUsP : (star (U : Mat)) * P = Matrix.diagonal (RCLike.ofReal ∘ eig) * (star (U : Mat)) := by
          have := congr_arg ((star (U : Mat)) * ·) hP_spec
          simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul] at this
          exact this
        -- Define the conjugated map ψ(M) = diag(1-eig) * M * diag(eig)
        -- Range(ψ) = span{Matrix.single a b 1 | eig_a ≠ 1 ∧ eig_b ≠ 0}
        -- For eig ∈ {0,1}, this = span{Matrix.single a b 1 | eig_a = 0 ∧ eig_b = 1}
        -- which has dimension (D-k)*k.
        -- The conjugation Ψ: M ↦ U*M*star(U) maps range(ψ) to range(φ) bijectively.
        -- So we construct k*(D-k) linearly independent elements of range(φ).
        -- For a with eig a = 0, b with eig b = 1:
        -- φ(U*E_{ab}*star(U)) = (1-P)*(U*E_{ab}*star(U))*P
        -- = (1-P)*U*E_{ab}*star(U)*P
        -- using algebra: (1-P)*U = U*(1-diag(eig)) = U*diag(1-eig)
        --   and star(U)*P = diag(eig)*star(U)
        -- so = U*diag(1-eig)*E_{ab}*diag(eig)*star(U)
        -- Now diag(1-eig)*E_{ab}*diag(eig) has (i,j) entry = (1-eig_i)*(if i=a,j=b then 1 else 0)*eig_j
        -- When eig_a=0, eig_b=1: this = E_{ab}
        -- So φ(U*E_{ab}*star(U)) = U*E_{ab}*star(U).
        -- Key fact: for eig a = 0, eig b = 1, the matrix U*E_{ab}*U* is a fixed point of φ
        -- Strategy: rewrite P via spectral theorem, then use noncomm_ring after
        -- establishing key identities star(U)*U = 1, diag(1-eig)*E*diag(eig) = E.
        set D₁ : Mat := Matrix.diagonal (RCLike.ofReal ∘ eig) with hD₁_def
        -- P = U * D₁ * star U
        have hP_eq : P = (U : Mat) * D₁ * star (U : Mat) := hP_spec
        -- star(U) * U = 1 and U * star(U) = 1 (already have hUU, hUUs)
        have hφ_fix : ∀ a b : Fin D, eig a = 0 → eig b = 1 →
            φ ((U : Mat) * Matrix.single a b 1 * star (U : Mat)) =
            (U : Mat) * Matrix.single a b 1 * star (U : Mat) := by
          intro a b ha hb
          set E := Matrix.single a b (1 : ℂ)
          -- D₁ * star(U) * U = D₁ (from hUU)
          -- star(U) * U * D₁ = D₁ (from hUU)
          -- diag(1-eig) * E * diag(eig) = E when eig a=0, eig b=1
          have hDE : (1 - D₁) * E * D₁ = E := by
            have hD₁_diag : D₁ = Matrix.diagonal (fun i => (eig i : ℂ)) := by
              simp [D₁, Function.comp]
            have h1D₁ : 1 - D₁ = Matrix.diagonal (fun i => 1 - (eig i : ℂ)) := by
              rw [hD₁_diag]; ext i j
              simp [Matrix.diagonal_apply, Matrix.one_apply]
              split_ifs <;> ring
            rw [h1D₁, hD₁_diag]
            ext i j
            simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, E, Matrix.single_apply]
            split_ifs with h1
            · obtain ⟨rfl, rfl⟩ := h1; simp [ha, hb]
            · simp
          -- φ(X) = (1-P)*(X*P) where X = U*E*star(U)
          -- = (1 - U*D₁*star(U)) * (U*E*star(U) * U*D₁*star(U))
          -- = (1 - U*D₁*star(U)) * U*E*D₁*star(U)     [using star(U)*U*D₁ = D₁]
          -- = U*E*D₁*star(U) - U*D₁*star(U)*U*E*D₁*star(U)
          -- = U*E*D₁*star(U) - U*D₁*E*D₁*star(U)
          -- = U*(E*D₁ - D₁*E*D₁)*star(U)
          -- = U*((1-D₁)*E*D₁)*star(U)   [since E*D₁ - D₁*E*D₁ = (1-D₁)*E*D₁]
          -- = U*E*star(U)               [by hDE]
          show (1 - P) * ((U : Mat) * E * star (U : Mat) * P) =
            (U : Mat) * E * star (U : Mat)
          have h1PU : (1 - P) * (U : Mat) = (U : Mat) * (1 - D₁) := by
            rw [Matrix.sub_mul, Matrix.one_mul, hPU, Matrix.mul_sub, Matrix.mul_one]
          calc (1 - P) * ((U : Mat) * E * star (U : Mat) * P)
              = ((1 - P) * ((U : Mat) * E * star (U : Mat))) * P := by
                rw [← Matrix.mul_assoc]
            _ = ((1 - P) * (U : Mat) * E * star (U : Mat)) * P := by
                rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
            _ = ((U : Mat) * (1 - D₁) * E * star (U : Mat)) * P := by
                rw [h1PU]
            _ = (U : Mat) * (1 - D₁) * E * (star (U : Mat) * P) := by
                rw [Matrix.mul_assoc]
            _ = (U : Mat) * (1 - D₁) * E * (D₁ * star (U : Mat)) := by
                rw [hUsP]
            _ = (U : Mat) * ((1 - D₁) * E * D₁) * star (U : Mat) := by
                -- LHS: ((U*(1-D₁))*E) * (D₁*star(U))
                -- Step: A*(B*C) = (A*B)*C where A=U*(1-D₁)*E, B=D₁, C=star(U)
                rw [← Matrix.mul_assoc ((U : Mat) * (1 - D₁) * E) D₁]
                -- Now: ((U*(1-D₁))*E*D₁) * star(U) = (U*((1-D₁)*E*D₁)) * star(U)
                -- Need: (U*(1-D₁))*E*D₁ = U*((1-D₁)*E*D₁)
                -- (U*(1-D₁))*E*D₁ = ((U*(1-D₁))*E)*D₁
                -- = U * ((1-D₁)*E) * D₁       [by mul_assoc U (1-D₁) E backward]
                -- = U * ((1-D₁)*E*D₁)          [by mul_assoc U ((1-D₁)*E) D₁]
                congr 1
                rw [Matrix.mul_assoc (U : Mat) (1 - D₁) E,
                    Matrix.mul_assoc (U : Mat) ((1 - D₁) * E) D₁]
            _ = (U : Mat) * E * star (U : Mat) := by
                rw [hDE]
        -- Now construct the linearly independent family
        set S₀ := Finset.univ.filter (fun i : Fin D => eig i = 0)
        set S₁ := Finset.univ.filter (fun i : Fin D => eig i = 1)
        have hS₁_card : S₁.card = k := rfl
        have hS₀_card : S₀.card = D - k := by
          have hunion : S₀ ∪ S₁ = Finset.univ := by
            ext i
            simp only [S₀, S₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                        iff_true]
            exact heig_01 i
          have hdisj : Disjoint S₀ S₁ := by
            simp only [S₀, S₁, Finset.disjoint_filter]
            intro i _ h0 h1; linarith
          have := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ, Fintype.card_fin] at this
          omega
        -- The family indexed by S₀ × S₁
        have hcard : Fintype.card (↥S₀ × ↥S₁) = (D - k) * k := by
          rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, hS₀_card, hS₁_card]
        -- Define a family in range(φ)
        set fam : (↥S₀ × ↥S₁) → LinearMap.range φ :=
          fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ =>
            ⟨(U : Mat) * Matrix.single a b (1 : ℂ) * star (U : Mat),
             LinearMap.mem_range.mpr ⟨_, hφ_fix a b
               (by simpa [S₀] using ha) (by simpa [S₁] using hb)⟩⟩
        -- The family is linearly independent
        have hfam_li : LinearIndependent ℂ fam := by
          -- Suffices: the Subtype.val-composed family is lin indep in Mat
          apply LinearIndependent.of_comp (LinearMap.range φ).subtype
          show LinearIndependent ℂ (fun p : ↥S₀ × ↥S₁ => (fam p : Mat))
          -- fam(a,b) = U * Matrix.single a b 1 * star(U) = conjStarAlgAut(E_{ab})
          -- Use: conjStarAlgAut is injective, and E_{ab} are lin indep
          -- Step 1: express the family as a composition
          have hfam_eq : (fun p : ↥S₀ × ↥S₁ => (fam p : Mat)) =
              (fun M : Mat => (U : Mat) * M * star (U : Mat)) ∘
              (fun p : ↥S₀ × ↥S₁ => Matrix.single p.1.1 p.2.1 (1 : ℂ)) := by
            ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; rfl
          rw [hfam_eq]
          -- Step 2: the conjugation map is injective (linear map with ker = ⊥)
          set conjMap : Mat →ₗ[ℂ] Mat :=
            (LinearMap.mulLeft ℂ (U : Mat)).comp (LinearMap.mulRight ℂ (star (U : Mat)))
          have hconj_ker : LinearMap.ker conjMap = ⊥ := by
            rw [LinearMap.ker_eq_bot]
            intro M₁ M₂ h
            simp only [conjMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
              LinearMap.mulRight_apply] at h
            -- h : U * (M₁ * star U) = U * (M₂ * star U)
            -- Left-cancel U, right-cancel star U
            have := congr_arg ((star (U : Mat)) * · * (U : Mat)) h
            simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul] at this
            simpa [Matrix.mul_assoc, hUUs, Matrix.mul_one] using this
          have hfam_eq2 : (fun M : Mat => (U : Mat) * M * star (U : Mat)) = conjMap := by
            ext M
            simp only [conjMap, LinearMap.comp_apply,
              LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]
          rw [hfam_eq2]
          apply LinearIndependent.map' _ conjMap hconj_ker
          -- Step 3: Matrix.single a b 1 for distinct (a,b) ∈ S₀×S₁ are lin indep
          -- They form a sub-family of the standard basis
          let ι : ↥S₀ × ↥S₁ → Fin D × Fin D := fun p => (p.1.1, p.2.1)
          have hι_inj : Function.Injective ι := by
            intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
            simp only [ι, Prod.mk.injEq] at h
            exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
          have hv_eq : (fun p : ↥S₀ × ↥S₁ => Matrix.single p.1.1 p.2.1 (1 : ℂ)) =
              (fun ij : Fin D × Fin D => Matrix.stdBasis ℂ (Fin D) (Fin D) ij) ∘ ι := by
            ext ⟨⟨a, _⟩, ⟨b, _⟩⟩
            simp [ι, Matrix.stdBasis_eq_single]
          rw [hv_eq]
          exact ((Matrix.stdBasis ℂ (Fin D) (Fin D)).linearIndependent).comp ι hι_inj
        -- finrank(range φ) ≥ card(S₀ × S₁) = (D-k)*k
        calc k * (D - k) = (D - k) * k := Nat.mul_comm k (D - k)
          _ = Fintype.card (↥S₀ × ↥S₁) := hcard.symm
          _ ≤ Module.finrank ℂ (LinearMap.range φ) := hfam_li.fintype_card_le_finrank

/-- Shifting Lindblad operators by scalar multiples of identity preserves
`toLinearMap` while making operators traceless.  Block-UT is preserved. -/
private theorem exists_traceless_blockUT_lindblad_form
    {P : Mat} (hP : IsNontrivialProjection P)
    (G : LindbladForm D)
    (L : Mat →ₗ[ℂ] Mat)
    (hL_eq : L = G.toLinearMap)
    (hBlock : ∀ j : Fin G.r, (1 - P) * G.L j * P = 0) :
    ∃ G' : LindbladForm D,
      G'.toLinearMap = L ∧
      (∀ j : Fin G'.r, G'.L j ∈
        ((LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
          (LinearMap.mulRight ℂ P))) ⊓
         (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)) :
          Submodule ℂ Mat)) := by
  -- D > 0 from nontrivial projection
  by_cases hD : D = 0
  · subst hD; exact absurd (Subsingleton.elim P 0) hP.2.1
  haveI : NeZero D := ⟨hD⟩
  -- Get traceless shifts: c_j = -trace(L_j)/D
  obtain ⟨c, hc⟩ := exists_traceless_kraus_shift G.L
  -- Shifted operators L'_j = G.L j + c_j · I
  set L' : Fin G.r → Mat := fun j => G.L j + c j • (1 : Mat) with hL'_def
  -- Shifted Hamiltonian: H' = G.H - (I/2)·(Σ c̄ⱼ Lⱼ - Σ cⱼ Lⱼ†)
  set Δ : Mat := ∑ j : Fin G.r,
    (starRingEnd ℂ (c j) • G.L j - c j • (G.L j)ᴴ) with hΔ_def
  set H' : Mat := G.H - (Complex.I / 2) • Δ with hH'_def
  -- H' is Hermitian
  have hH'_herm : H'.IsHermitian := by
    rw [hH'_def]
    apply Matrix.IsHermitian.sub G.H_hermitian
    rw [Matrix.IsHermitian, conjTranspose_smul]
    have hstar_I2 : star (Complex.I / 2 : ℂ) = -(Complex.I / 2) := by
      simp [Complex.conj_I]; ring
    rw [hstar_I2, hΔ_def, conjTranspose_sum]
    simp_rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_conjTranspose,
      RCLike.star_def, Complex.conj_conj]
    rw [neg_smul, ← smul_neg]
    congr 1
    rw [show -(∑ x, (c x • (G.L x)ᴴ - starRingEnd ℂ (c x) • G.L x)) =
      ∑ x, (starRingEnd ℂ (c x) • G.L x - c x • (G.L x)ᴴ) from by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _
        simp only [neg_sub]]
  -- Construct the new LindbladForm
  refine ⟨⟨G.r, H', L', hH'_herm⟩, ?_, ?_⟩
  · -- Show toLinearMap agrees: use generator_shift_invariance
    rw [hL_eq]
    -- Both forms have the same generator via generator_shift_invariance.
    rw [LindbladForm.toLinearMap_eq_generatorDecomp,
        LindbladForm.toLinearMap_eq_generatorDecomp]
    set κ_old : Mat := G.toGeneratorDecomp.κ
    -- generator_shift_invariance with mu = 0
    have hshift := generator_shift_invariance G.L κ_old c 0
    simp only [Complex.ofReal_zero, mul_zero, zero_smul, add_zero] at hshift
    -- Key: the new form's κ = shifted κ
    set κ_shift : Mat := κ_old + ∑ i, starRingEnd ℂ (c i) • G.L i +
      (1/2 : ℂ) • ∑ i, (starRingEnd ℂ (c i) * c i) • (1 : Mat)
    -- The new form's κ
    have hκ_new : (Complex.I • H' + (1/2 : ℂ) • ∑ j : Fin G.r, (L' j)ᴴ * L' j) =
        κ_shift := by
      -- Step 1: iH' = iG.H + (1/2)Δ
      have h_iH' : Complex.I • H' =
          Complex.I • G.H + (1/2 : ℂ) • Δ := by
        rw [hH'_def, smul_sub, smul_smul]
        have : Complex.I * (Complex.I / 2) = -(1/2 : ℂ) := by
          field_simp; rw [Complex.I_sq]
        rw [this, neg_smul, sub_neg_eq_add]
      -- Step 2: ½Σ L'†L' = ½Σ G.L†G.L + ½Σ c̄ G.L + ½Σ c G.L† + ½Σ|c|² I
      have h_adj : (1/2 : ℂ) • ∑ j : Fin G.r, (L' j)ᴴ * L' j =
          (1/2 : ℂ) • ∑ j, (G.L j)ᴴ * G.L j +
          (1/2 : ℂ) • ∑ j, starRingEnd ℂ (c j) • G.L j +
          (1/2 : ℂ) • ∑ j, c j • (G.L j)ᴴ +
          (1/2 : ℂ) • ∑ j, (starRingEnd ℂ (c j) * c j) • (1 : Mat) := by
        rw [hL'_def]
        simp_rw [conjTranspose_add, conjTranspose_smul, conjTranspose_one,
          Matrix.add_mul, Matrix.mul_add, smul_mul_assoc, mul_smul_comm,
          Matrix.one_mul, Matrix.mul_one, Finset.sum_add_distrib, smul_smul,
          smul_add, Finset.smul_sum]
        simp only [Complex.star_def]
        abel
      -- Step 3: Combine h_iH' and h_adj
      rw [h_iH', h_adj, hΔ_def, Finset.smul_sum]
      simp_rw [smul_sub]
      simp_rw [Finset.sum_sub_distrib]
      -- The key cancellation: ½Σc̄L - ½ΣcL† + ½Σc̄L + ½ΣcL† = Σc̄L
      have hcancel :
          (∑ x, (1 / 2 : ℂ) • starRingEnd ℂ (c x) • G.L x -
           ∑ x, (1 / 2 : ℂ) • c x • (G.L x)ᴴ) +
          ((1 / 2 : ℂ) • ∑ j, starRingEnd ℂ (c j) • G.L j +
           (1 / 2 : ℂ) • ∑ j, c j • (G.L j)ᴴ) =
          ∑ i, starRingEnd ℂ (c i) • G.L i := by
        rw [← Finset.smul_sum, ← Finset.smul_sum]
        -- ½Σc̄L - ½ΣcL† + ½Σc̄L + ½ΣcL† = Σc̄L
        module
      -- Now assemble
      have : κ_shift = κ_old +
          ∑ i, starRingEnd ℂ (c i) • G.L i +
          (1 / 2 : ℂ) • ∑ i, (starRingEnd ℂ (c i) * c i) • (1 : Mat) := rfl
      rw [this]; clear this
      -- Group the sums on the LHS
      -- LHS = iG.H + (½Σc̄L - ½ΣcL†) + ½ΣG.L†G.L + ½Σc̄L + ½ΣcL† + ½Σ|c|²I
      -- = iG.H + ½ΣG.L†G.L + (½Σc̄L - ½ΣcL† + ½Σc̄L + ½ΣcL†) + ½Σ|c|²I
      -- = iG.H + ½ΣG.L†G.L + Σc̄L + ½Σ|c|²I
      -- = κ_old + Σc̄L + ½Σ|c|²I
      have hκ_old_eq : κ_old = Complex.I • G.H +
          (1 / 2 : ℂ) • ∑ j, (G.L j)ᴴ * G.L j := rfl
      rw [hκ_old_eq]
      -- Use hcancel to rewrite
      -- LHS: iG.H + (½Σc̄L - ½ΣcL†) + (½ΣG.L†G.L + ½Σc̄L + ½ΣcL† + ½Σ|c|²I)
      -- Group (½Σc̄L - ½ΣcL†) + (½Σc̄L + ½ΣcL†) = Σc̄L using hcancel
      -- Then LHS = iG.H + ½ΣG.L†G.L + Σc̄L + ½Σ|c|²I = RHS
      -- Set abbreviations for readability
      set A := Complex.I • G.H
      set B := ∑ x, (1 / 2 : ℂ) • starRingEnd ℂ (c x) • G.L x -
               ∑ x, (1 / 2 : ℂ) • c x • (G.L x)ᴴ
      set C := (1 / 2 : ℂ) • ∑ j, (G.L j)ᴴ * G.L j
      set D := (1 / 2 : ℂ) • ∑ j, starRingEnd ℂ (c j) • G.L j
      set E := (1 / 2 : ℂ) • ∑ j, c j • (G.L j)ᴴ
      set F := (1 / 2 : ℂ) • ∑ j, (starRingEnd ℂ (c j) * c j) • (1 : Mat)
      set S := ∑ i, starRingEnd ℂ (c i) • G.L i
      -- hcancel : B + (D + E) = S
      -- Goal: A + B + (C + D + E + F) = A + C + S + F
      -- = A + C + (B + (D + E)) + F (by hcancel)
      calc A + B + (C + D + E + F)
          = A + C + (B + (D + E)) + F := by abel
        _ = A + C + S + F := by rw [hcancel]
    ext1 ρ
    simp only [GeneratorDecomp.toLinearMap_apply, LindbladForm.toGeneratorDecomp]
    -- Rewrite the new form's κ as κ_shift
    rw [show (Complex.I • H' + (1 / 2 : ℂ) • ∑ x, (L' x)ᴴ * L' x) = κ_shift from hκ_new]
    -- Unfold κ_old
    change (∑ x, L' x * ρ * (L' x)ᴴ) - κ_shift * ρ - ρ * κ_shiftᴴ =
      (∑ j, G.L j * ρ * (G.L j)ᴴ) - κ_old * ρ - ρ * κ_oldᴴ
    exact hshift ρ
  · -- Show each L'_j is in the traceless block-UT subspace
    intro j
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · -- Block-UT: (1-P) * L'_j * P = 0
      simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [hL'_def]
      simp only [Matrix.mul_add, Matrix.add_mul, smul_mul_assoc, mul_smul_comm]
      rw [Matrix.one_mul, orthogonalProjection_complement_mul hP.1, smul_zero, add_zero]
      rw [← Matrix.mul_assoc]
      exact hBlock j
    · -- Traceless
      simp only [Matrix.traceLinearMap_apply]
      exact hc j

theorem large_kossakowski_rank_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro ⟨P, G, hP_nt, hL_eq, hBlock, _hκ_block⟩
  -- The traceless block-UT subspace
  set V : Submodule ℂ Mat :=
    (LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
      (LinearMap.mulRight ℂ P))) ⊓
    (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ))
  -- Get a traceless block-UT form
  obtain ⟨G', hG'_eq, hG'_mem⟩ :=
    exists_traceless_blockUT_lindblad_form hP_nt G F.toLinearMap hL_eq hBlock
  -- Construct a form with rank ≤ finrank V
  obtain ⟨G'', hG''_eq, hG''_r⟩ :=
    exists_lindblad_form_rank_le_finrank G' V hG'_mem
  -- kossakowskiRank ≤ G''.r
  have hkr : kossakowskiRank F.toLinearMap ≤ G''.r := by
    apply Nat.sInf_le
    exact ⟨G'', by rw [hG''_eq, hG'_eq], rfl⟩
  -- finrank V + D ≤ D²
  have hfin : Module.finrank ℂ V + D ≤ D ^ 2 :=
    finrank_traceless_blockUT_add_D_le hP_nt
  -- But kossakowskiRank + D ≥ D² + 1
  omega

/--
If a GKSL generator has no block-upper-triangular Lindblad decomposition,
then the generated quantum dynamical semigroup is not reducible.
-/
theorem not_isReducibleQDS_of_no_blockUpperTriangular_lindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (hNoBlockUT : ¬ HasBlockUpperTriangularLindblad L) :
    ¬ IsReducibleQDS L := by
  intro hReducible
  exact hNoBlockUT (wolf_prop_7_6_three_implies_four hGKSL hReducible)

/-- Wolf Corollary 7.2 condition (1): full algebra generation implies
non-reducibility. -/
theorem not_isReducible_of_generates_full_algebra
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact full_algebra_generation_implies_no_blockUpperTriangular F hGen

/-- Wolf Corollary 7.2 condition (2): Hermitian Lindblad span + trivial
commutant implies non-reducibility. -/
theorem not_isReducible_of_hermitian_span_trivial_commutant
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact hermitian_span_trivial_commutant_implies_no_blockUpperTriangular F hHerm hComm

/-- Wolf Corollary 7.2 condition (3): large Kossakowski rank implies
non-reducibility. -/
theorem not_isReducible_of_kossakowski_rank_ge
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact large_kossakowski_rank_implies_no_blockUpperTriangular F hRank

end -- noncomputable section

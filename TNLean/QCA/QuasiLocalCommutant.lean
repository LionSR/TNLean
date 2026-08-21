/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.ComplementaryWeylTwirl
import TNLean.QCA.DisjointSupport

/-!
# Exact finite support from outside commutation

A quasi-local observable belongs to the algebra of a finite region exactly when it commutes with
all observables supported in finite regions disjoint from it. The reverse implication uses finite
Weyl averaging on the complementary tensor factor and closedness of the finite-region image.

This is UHF-algebra infrastructure used by the QCA development. It is not a theorem stated in the
MPU paper or by Schumacher--Werner.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder Kronecker
open Matrix

namespace SpinChain

attribute [local instance] CStarMatrix.instNorm CStarMatrix.instNormedAddCommGroup
  CStarMatrix.instNormedRing CStarMatrix.instCStarRing

private lemma reindex_one_kronecker_eq_localInclusion_sdiff {d : ℕ} [NeZero d]
    {Λ Δ : Finset ℤ} (h : Λ ⊆ Δ) (B : LocalAlgebra d (Δ \ Λ)) :
    Matrix.reindex (Config.splitEquiv h).symm (Config.splitEquiv h).symm
      ((1 : Matrix (Config d Λ) (Config d Λ) ℂ) ⊗ₖ B) =
      localInclusion (d := d) (Finset.sdiff_subset : Δ \ Λ ⊆ Δ) B := by
  ext x y
  change (if (Config.splitEquiv h x).1 = (Config.splitEquiv h y).1 then 1 else 0) *
      B (Config.splitEquiv h x).2 (Config.splitEquiv h y).2 =
    B (Config.restrict Finset.sdiff_subset x) (Config.restrict Finset.sdiff_subset y) *
      if (Config.splitEquiv Finset.sdiff_subset x).2 =
        (Config.splitEquiv Finset.sdiff_subset y).2 then 1 else 0
  have hrx : Config.restrict (Finset.sdiff_subset : Δ \ Λ ⊆ Δ) x =
      (Config.splitEquiv h x).2 := by
    funext i
    rfl
  have hry : Config.restrict (Finset.sdiff_subset : Δ \ Λ ⊆ Δ) y =
      (Config.splitEquiv h y).2 := by
    funext i
    rfl
  rw [hrx, hry, mul_comm]
  have hp : (Config.splitEquiv h x).1 = (Config.splitEquiv h y).1 ↔
      (Config.splitEquiv (Finset.sdiff_subset : Δ \ Λ ⊆ Δ) x).2 =
        (Config.splitEquiv Finset.sdiff_subset y).2 := by
    constructor
    · intro hxy
      funext i
      by_cases hi : (i : ℤ) ∈ Λ
      · exact congrFun hxy ⟨i, hi⟩
      · exact False.elim ((Finset.mem_sdiff.mp i.2).2 <|
          Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp i.2).1, hi⟩)
    · intro hxy
      funext i
      exact congrFun hxy ⟨i, Finset.mem_sdiff.mpr ⟨h i.2,
        fun hi ↦ (Finset.mem_sdiff.mp hi).2 i.2⟩⟩
  exact congrArg (fun z : ℂ => B (Config.splitEquiv h x).2 (Config.splitEquiv h y).2 * z)
    (if_congr hp rfl rfl)

private lemma reindex_kronecker_one_eq_localInclusion {d : ℕ} [NeZero d]
    {Λ Δ : Finset ℤ} (h : Λ ⊆ Δ) (B : LocalAlgebra d Λ) :
    Matrix.reindex (Config.splitEquiv h).symm (Config.splitEquiv h).symm
      (B ⊗ₖ (1 : Matrix (Config d (Δ \ Λ)) (Config d (Δ \ Λ)) ℂ)) =
      localInclusion (d := d) h B := by
  ext x y
  change B (Config.restrict h x) (Config.restrict h y) *
      (if (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 then 1 else 0) =
    B (Config.restrict h x) (Config.restrict h y) *
      if (Config.splitEquiv h x).2 = (Config.splitEquiv h y).2 then 1 else 0
  rfl

/-- A quasi-local observable has exact support in a finite region if and only if it commutes with
all observables supported in finite regions disjoint from that region.

This is standard UHF-algebra infrastructure. It is not stated in arXiv:1703.09188 or in
Schumacher--Werner, quant-ph/0405174. -/
theorem quasiLocalSupportedIn_iff_commute_disjoint {d : ℕ} [NeZero d]
    (x : QuasiLocalAlgebra d) (Λ : Finset ℤ) :
    QuasiLocalSupportedIn x Λ ↔
      ∀ Γ, Disjoint Γ Λ → ∀ y, QuasiLocalSupportedIn y Γ → Commute x y := by
  constructor
  · intro hx Γ hΓΛ y hy
    exact hx.commute_of_disjoint hy hΓΛ.symm
  · intro hout
    change x ∈ Set.range (quasiLocalObservable d Λ)
    have hclosed : IsClosed (Set.range (quasiLocalObservable d Λ)) :=
      (quasiLocalObservable_isometry d Λ).isClosedEmbedding.isClosed_range
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨z, hz, hxz⟩ :=
      (dense_iUnion_range_quasiLocalObservable d).exists_dist_lt x hε
    simp only [Set.mem_iUnion] at hz
    obtain ⟨Γ, A, rfl⟩ := hz
    let Δ := Γ ∪ Λ
    have hΓΔ : Γ ⊆ Δ := Finset.subset_union_left
    have hΛΔ : Λ ⊆ Δ := Finset.subset_union_right
    let M : LocalAlgebra d Δ := localInclusion hΓΔ A
    let S := Config d Λ
    let C := Config d (Δ \ Λ)
    let dC := Fintype.card C
    let : NeZero dC := ⟨by simp [dC, Fintype.card_ne_zero (α := C)]⟩
    let eC : C ≃ ZMod dC := (Fintype.equivFin C).trans (ZMod.finEquiv dC).toEquiv
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / dC)
    have hζ : IsPrimitiveRoot ζ dC := Complex.isPrimitiveRoot_exp dC (NeZero.ne dC)
    let e : Config d Δ ≃ S × C := Config.splitEquiv hΛΔ
    let Msplit : Matrix (S × C) (S × C) ℂ :=
      Matrix.reindex e e (CStarMatrix.ofMatrix.symm M)
    let Tsplit : Matrix (S × C) (S × C) ℂ := Matrix.complementaryWeylTwirl eC ζ Msplit
    let T : LocalAlgebra d Δ := CStarMatrix.ofMatrix (Matrix.reindex e.symm e.symm Tsplit)
    let B : LocalAlgebra d Λ := (dC : ℂ)⁻¹ • Matrix.partialTraceRight Msplit
    have hT : T = localInclusion hΛΔ B := by
      dsimp only [T, Tsplit, B]
      rw [Matrix.complementaryWeylTwirl_eq_smul_partialTraceRight_kronecker_one eC hζ]
      exact reindex_kronecker_one_eq_localInclusion hΛΔ _
    refine ⟨quasiLocalObservable d Λ B, ⟨B, rfl⟩, ?_⟩
    rw [← quasiLocalObservable_localInclusion d hΛΔ B, ← hT]
    -- The Weyl average stays within the original approximation error because every
    -- complementary conjugation fixes `x`.
    let W (a b : ZMod dC) : LocalAlgebra d (Δ \ Λ) :=
      Matrix.reindexedWeyl eC ζ a b
    let U (a b : ZMod dC) : LocalAlgebra d Δ :=
      CStarMatrix.ofMatrix (Matrix.reindex e.symm e.symm
        ((1 : Matrix S S ℂ) ⊗ₖ Matrix.reindexedWeyl eC ζ a b))
    have hUlocal (a b : ZMod dC) :
        U a b = localInclusion (Finset.sdiff_subset : Δ \ Λ ⊆ Δ) (W a b) := by
      exact reindex_one_kronecker_eq_localInclusion_sdiff hΛΔ _
    have hWunitary (a b : ZMod dC) : W a b ∈ unitary (LocalAlgebra d (Δ \ Λ)) := by
      exact Matrix.reindex_mem_unitaryGroup eC.symm _ (Matrix.weyl_mem_unitary hζ a b)
    have hUunitary (a b : ZMod dC) :
        quasiLocalObservable d Δ (U a b) ∈ unitary (QuasiLocalAlgebra d) := by
      have hWu := hWunitary a b
      rw [Unitary.mem_iff] at hWu ⊢
      rw [hUlocal, quasiLocalObservable_localInclusion d
        (Finset.sdiff_subset : Δ \ Λ ⊆ Δ)]
      constructor
      · rw [← map_star, ← map_mul, hWu.1, map_one]
      · rw [← map_star, ← map_mul, hWu.2, map_one]
    have hUfix (a b : ZMod dC) :
        quasiLocalObservable d Δ (U a b) * x * star (quasiLocalObservable d Δ (U a b)) = x := by
      have hcomm := hout (Δ \ Λ) Finset.sdiff_disjoint
        (quasiLocalObservable d (Δ \ Λ) (W a b))
        (QuasiLocalSupportedIn.quasiLocalObservable (W a b))
      rw [hUlocal, quasiLocalObservable_localInclusion d
        (Finset.sdiff_subset : Δ \ Λ ⊆ Δ)]
      calc
        _ = x * quasiLocalObservable d (Δ \ Λ) (W a b) *
            star (quasiLocalObservable d (Δ \ Λ) (W a b)) := by rw [hcomm.eq.symm]
        _ = x * (quasiLocalObservable d (Δ \ Λ) (W a b) *
            star (quasiLocalObservable d (Δ \ Λ) (W a b))) := by rw [mul_assoc]
        _ = x := by
          have hunit := hUunitary a b
          rw [hUlocal, quasiLocalObservable_localInclusion d
            (Finset.sdiff_subset : Δ \ Λ ⊆ Δ)] at hunit
          rw [(Unitary.mem_iff.mp hunit).2, mul_one]
    have hUnorm (a b : ZMod dC) : ‖quasiLocalObservable d Δ (U a b)‖ = 1 := by
      rw [norm_quasiLocalObservable, hUlocal, localInclusion_norm]
      exact CStarRing.norm_of_mem_unitary (hWunitary a b)
    have hterm (a b : ZMod dC) :
        ‖quasiLocalObservable d Δ (U a b * M * star (U a b)) - x‖ ≤
          ‖quasiLocalObservable d Δ M - x‖ := by
      have heq : quasiLocalObservable d Δ (U a b * M * star (U a b)) - x =
          quasiLocalObservable d Δ (U a b) *
            (quasiLocalObservable d Δ M - x) *
              star (quasiLocalObservable d Δ (U a b)) := by
        rw [map_mul, map_mul, map_star, mul_sub, sub_mul, hUfix]
      rw [heq]
      calc
        _ ≤ ‖quasiLocalObservable d Δ (U a b)‖ *
              ‖quasiLocalObservable d Δ M - x‖ *
                ‖star (quasiLocalObservable d Δ (U a b))‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
        _ = _ := by rw [hUnorm, norm_star, hUnorm, one_mul, mul_one]
    have havg : quasiLocalObservable d Δ T - x =
        ((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
          (quasiLocalObservable d Δ (U a b * M * star (U a b)) - x) := by
      dsimp only [T, Tsplit, Matrix.complementaryWeylTwirl, Msplit]
      let K (a b : ZMod dC) : Matrix (S × C) (S × C) ℂ :=
        (1 : Matrix S S ℂ) ⊗ₖ Matrix.reindexedWeyl eC ζ a b
      have hreindex (a b : ZMod dC) :
          CStarMatrix.ofMatrixStarAlgEquiv ((Matrix.reindexAlgEquiv ℂ ℂ e.symm)
              (K a b * Matrix.reindex e e (CStarMatrix.ofMatrix.symm M) *
                (K a b)ᴴ)) =
            U a b * M * star (U a b) := by
        apply CStarMatrix.ofMatrix.injective
        change (Matrix.reindexAlgEquiv ℂ ℂ e.symm)
              (K a b * Matrix.reindex e e (CStarMatrix.ofMatrix.symm M) * (K a b)ᴴ) =
            Matrix.reindex e.symm e.symm (K a b) * CStarMatrix.ofMatrix.symm M *
              (Matrix.reindex e.symm e.symm (K a b))ᴴ
        rw [map_mul, map_mul]
        change Matrix.reindex e.symm e.symm (K a b) *
              Matrix.reindex e.symm e.symm
                (Matrix.reindex e e (CStarMatrix.ofMatrix.symm M)) *
              Matrix.reindex e.symm e.symm (K a b)ᴴ = _
        have hinv : Matrix.reindex e.symm e.symm
            (Matrix.reindex e e (CStarMatrix.ofMatrix.symm M)) =
              CStarMatrix.ofMatrix.symm M :=
          (Matrix.reindex e e).symm_apply_apply (CStarMatrix.ofMatrix.symm M)
        rw [hinv]
        congr 1
      have hlocalavg :
          CStarMatrix.ofMatrix (Matrix.reindex e.symm e.symm
            (((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
              K a b * Matrix.reindex e e (CStarMatrix.ofMatrix.symm M) * (K a b)ᴴ)) =
            ((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
              (U a b * M * star (U a b)) := by
        change CStarMatrix.ofMatrixStarAlgEquiv
            ((Matrix.reindexAlgEquiv ℂ ℂ e.symm)
              (((dC : ℂ) ^ 2)⁻¹ • ∑ a : ZMod dC, ∑ b : ZMod dC,
                K a b * Matrix.reindex e e (CStarMatrix.ofMatrix.symm M) * (K a b)ᴴ)) = _
        simp only [map_smul, map_sum]
        simp_rw [hreindex]
      rw [hlocalavg, map_smul]
      simp only [map_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ZMod.card, smul_sub]
      rw [← Nat.cast_smul_eq_nsmul ℂ dC, ← Nat.cast_smul_eq_nsmul ℂ dC,
        smul_smul, smul_smul]
      have hdC : (dC : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne dC
      congr 1
      field_simp
      simp
    have hdist : dist x (quasiLocalObservable d Δ T) ≤
        dist x (quasiLocalObservable d Δ M) := by
      rw [dist_comm, dist_eq_norm, dist_eq_norm, havg, norm_smul]
      calc
        _ ≤ ‖((dC : ℂ) ^ 2)⁻¹‖ *
            ∑ _a : ZMod dC, ∑ _b : ZMod dC, ‖quasiLocalObservable d Δ M - x‖ := by
          gcongr
          exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun a _ =>
            (norm_sum_le _ _).trans <| Finset.sum_le_sum fun b _ => hterm a b
        _ = _ := by
          simp only [norm_inv, norm_pow, Complex.norm_natCast, Finset.sum_const,
            Finset.card_univ, ZMod.card, nsmul_eq_mul]
          have hdC : (dC : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne dC
          field_simp
          exact norm_sub_rev _ _
    exact hdist.trans_lt (by
      rw [quasiLocalObservable_localInclusion d hΓΔ A]
      exact hxz)

end SpinChain

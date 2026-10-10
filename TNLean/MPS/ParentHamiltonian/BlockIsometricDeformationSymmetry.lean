/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.IsometricDeformationSymmetry
import TNLean.MPS.ParentHamiltonian.PhysicalActionWordTupleSpan
import TNLean.MPS.Structure.BlockPermutation

/-!
# Symmetry of the isometric deformation for several normal blocks

Let \(A_1,\dots,A_r\) be blocks whose one-site matrices jointly span the
direct sum \(\bigoplus_k M_{D_k}\), and let \(P\) be the joint physical map
\(P_{i,(k,a,b)}=(A_k^i)_{ab}\) of the block-diagonal tensor
\(\bigoplus_k A_k\). Suppose that the matrix product vectors of this tensor
are invariant under \(U_g^{\otimes N}\) for a unitary on-site representation.

Equality of all word traces turns the assignment
\((A_k^{i})_k\mapsto(\sum_j (U_g)_{ij}A_k^{j})_k\) into an algebra
automorphism of \(\bigoplus_k M_{D_k}\). Such an automorphism permutes the
blocks and is inner on each block. In the trace-preserving canonical
normalization \(\sum_i A_k^{i\dagger}A_k^i=I\) of every block, each inner
part is unitary. The joint virtual action is then the block permutation
followed by the blockwise unitary conjugations; it is unitary and satisfies
\(U_gP=PX_g\). Consequently the positive polar factor \(Q\) commutes with
\(U_g\), the original two-site MPS space is invariant, and every canonical
parent projection and inverse-conjugated interaction along
\(P_\gamma=(\gamma Q+(1-\gamma)I)W\) commutes with the symmetry.

Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732, paper_v3.tex,
lines 645--676. The joint one-site span is the source's initial blocking
assumption (lines 575--600), and the per-block normalization is the printed
condition \(\operatorname{tr}_{\mathrm{left}}(P^\dagger P)=I\) at line 653
for the block-diagonal \(P\).

**Scope restriction (exact vector symmetry):** The symmetry is assumed on
the matrix product vectors themselves, not only up to a phase; see
docs/paper-gaps/spc11_isometric_symmetry_unitary_virtual.tex.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-! ### Algebra automorphisms from equal word traces -/

section WordTraceAutomorphism

/-- Word evaluation extended linearly to finitely supported combinations of
words, with values in the product of the block matrix algebras. -/
private noncomputable def wordCombinationTuple (A : (k : Fin r) → MPSTensor d (dim k)) :
    (List (Fin d) →₀ ℂ) →ₗ[ℂ] ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
  Finsupp.linearCombination ℂ (fun w k => Kraus.evalWord (A k) w)

private theorem wordTuple_mul (A : (k : Fin r) → MPSTensor d (dim k))
    (v w : List (Fin d)) :
    ((fun k => Kraus.evalWord (A k) v) * fun k => Kraus.evalWord (A k) w) =
      fun k => Kraus.evalWord (A k) (v ++ w) := by
  funext k
  simp [Kraus.evalWord_append]

/-- The trace pairing against a word is the same on both sides once all word
traces agree. -/
private theorem trace_pairing_wordCombinationTuple
    {A B : (k : Fin r) → MPSTensor d (dim k)}
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (B k) w).trace)
    (v : List (Fin d)) (c : List (Fin d) →₀ ℂ) :
    ∑ k, (wordCombinationTuple A c k * Kraus.evalWord (A k) v).trace =
      ∑ k, (wordCombinationTuple B c k * Kraus.evalWord (B k) v).trace := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, Pi.add_apply, Matrix.add_mul, Matrix.trace_add,
        Finset.sum_add_distrib, hf, hg]
  | single w a =>
      simp only [wordCombinationTuple, Finsupp.linearCombination_single, Pi.smul_apply,
        Matrix.smul_mul, Matrix.trace_smul, ← Kraus.evalWord_append, ← Finset.smul_sum,
        hTr (w ++ v)]

private theorem ker_wordCombinationTuple_le
    {A B : (k : Fin r) → MPSTensor d (dim k)}
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (B k) w).trace)
    (hB : WordTupleSpanTop B 1) :
    LinearMap.ker (wordCombinationTuple A) ≤ LinearMap.ker (wordCombinationTuple B) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  funext k
  refine block_matrices_eq_zero_of_wordTupleSpanTop_trace B hB _ (fun w => ?_) k
  rw [← trace_pairing_wordCombinationTuple hTr, hc]
  simp

private theorem range_wordCombinationTuple_eq_top
    {A : (k : Fin r) → MPSTensor d (dim k)} (hA : WordTupleSpanTop A 1) :
    LinearMap.range (wordCombinationTuple A) = ⊤ := by
  rw [wordCombinationTuple, Finsupp.range_linearCombination, eq_top_iff, ← hA]
  apply Submodule.span_mono
  rintro _ ⟨w, rfl⟩
  exact ⟨List.ofFn w, rfl⟩

/-- Two block families with jointly spanning one-site matrices and equal summed
word traces are related by an algebra automorphism of the product of the block
matrix algebras that carries every word of the first family to the same word
of the second. Source: arXiv:1010.3732, lines 652--660, where state symmetry
is converted to a virtual action. -/
theorem exists_algEquiv_of_sum_trace_evalWord_eq
    {A B : (k : Fin r) → MPSTensor d (dim k)}
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (B k) w).trace)
    (hA : WordTupleSpanTop A 1) (hB : WordTupleSpanTop B 1) :
    ∃ T : ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) ≃ₐ[ℂ]
        ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      ∀ w : List (Fin d),
        T (fun k => Kraus.evalWord (A k) w) = fun k => Kraus.evalWord (B k) w := by
  classical
  set FA := wordCombinationTuple A
  set FB := wordCombinationTuple B
  have hle : LinearMap.ker FA ≤ LinearMap.ker FB := ker_wordCombinationTuple_le hTr hB
  have hle' : LinearMap.ker FB ≤ LinearMap.ker FA :=
    ker_wordCombinationTuple_le (fun w => (hTr w).symm) hA
  have hsurjA : Function.Surjective FA :=
    LinearMap.range_eq_top.mp (range_wordCombinationTuple_eq_top hA)
  have hsurjB : Function.Surjective FB :=
    LinearMap.range_eq_top.mp (range_wordCombinationTuple_eq_top hB)
  let T₀ := (LinearMap.ker FA).liftQ FB hle ∘ₗ
    (FA.quotKerEquivOfSurjective hsurjA).symm.toLinearMap
  have hT₀ : ∀ c, T₀ (FA c) = FB c := by
    intro c
    have hmk : (FA.quotKerEquivOfSurjective hsurjA).symm (FA c) =
        Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [T₀, LinearMap.comp_apply, LinearEquiv.coe_coe, hmk, Submodule.liftQ_apply]
  have hgen : ∀ w : List (Fin d),
      T₀ (fun k => Kraus.evalWord (A k) w) = fun k => Kraus.evalWord (B k) w := by
    intro w
    simpa [FA, FB, wordCombinationTuple] using hT₀ (Finsupp.single w 1)
  have hspan : Submodule.span ℂ
      (Set.range fun w : List (Fin d) => fun k => Kraus.evalWord (A k) w) = ⊤ := by
    rw [← Finsupp.range_linearCombination]
    exact range_wordCombinationTuple_eq_top hA
  have hmulGen : ∀ (w : List (Fin d)) x,
      T₀ (x * fun k => Kraus.evalWord (A k) w) = T₀ x * fun k => Kraus.evalWord (B k) w := by
    intro w x
    have h := LinearMap.ext_on hspan
      (f := T₀ ∘ₗ LinearMap.mulRight ℂ (fun k => Kraus.evalWord (A k) w))
      (g := LinearMap.mulRight ℂ (fun k => Kraus.evalWord (B k) w) ∘ₗ T₀) (by
        rintro _ ⟨v, rfl⟩
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
        rw [wordTuple_mul, hgen, hgen, wordTuple_mul])
    exact LinearMap.congr_fun h x
  have hmul : ∀ x y, T₀ (x * y) = T₀ x * T₀ y := by
    intro x y
    have h := LinearMap.ext_on hspan
      (f := T₀ ∘ₗ LinearMap.mulLeft ℂ x) (g := LinearMap.mulLeft ℂ (T₀ x) ∘ₗ T₀) (by
        rintro _ ⟨w, rfl⟩
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [hmulGen, hgen])
    exact LinearMap.congr_fun h y
  have hone : T₀ 1 = 1 := by
    have h := hgen []
    simp only [Kraus.evalWord_nil] at h
    exact h
  have hinj : Function.Injective T₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, rfl⟩ := hsurjA x
    rw [hT₀] at hx
    exact hle' hx
  have hsurj : Function.Surjective T₀ := fun y => by
    obtain ⟨c, rfl⟩ := hsurjB y
    exact ⟨FA c, hT₀ c⟩
  exact ⟨AlgEquiv.ofBijective (AlgHom.ofLinearMap T₀ hone hmul) ⟨hinj, hsurj⟩, hgen⟩

end WordTraceAutomorphism

/-! ### The symmetry permutes the blocks -/

section BlockPermutation

/-- A property of tensors of every bond dimension transfers along the
identification of two equal bond dimensions. -/
private theorem reindex_finCongr_transport {m n : ℕ} (h : m = n)
    (P : (D : ℕ) → MPSTensor d D → Prop) {B : MPSTensor d m} (hB : P m B) :
    P n (fun i => Matrix.reindex (finCongr h) (finCongr h) (B i)) := by
  subst h
  simpa using hB

private theorem isInjective_of_wordTupleSpanTop_one
    {A : (k : Fin r) → MPSTensor d (dim k)} (hA : WordTupleSpanTop A 1) (k : Fin r) :
    Kraus.IsInjective (A k) := by
  classical
  rw [Kraus.IsInjective, eq_top_iff]
  intro M _
  let π : ((j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ) →ₗ[ℂ]
      Matrix (Fin (dim k)) (Fin (dim k)) ℂ := LinearMap.proj k
  have hM : Pi.single k M ∈ Submodule.span ℂ (Set.range (wordTuple A 1)) := by
    rw [hA]
    exact Submodule.mem_top
  have h := Submodule.mem_map_of_mem (f := π) hM
  rw [Submodule.map_span] at h
  have hπ : π (Pi.single k M) = M := by simp [π]
  rw [hπ] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨w 0, by simp [π, wordTuple, List.ofFn_succ]⟩

variable {G : Type*} [Monoid G]

/-- Exact symmetry of the block-diagonal tensor equates the summed word traces
of the original and physically rotated blocks. -/
private theorem sum_trace_evalWord_eq_of_isOnSiteSymmetric
    (A : (k : Fin r) → MPSTensor d (dim k)) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (w : List (Fin d)) :
    ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (rotatePhysical (U g) (A k)) w).trace := by
  have h := hSymm g w.length w.get
  have htw : twistedTensor (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U g =
      toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) (fun k => rotatePhysical (U g) (A k)) :=
    rotatePhysical_toTensorFromBlocks (U g) _ A
  rw [htw, mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum] at h
  simpa [mpv, coeff, List.ofFn_get] using h

private theorem isUnit_of_mem_unitaryGroup {u : Matrix (Fin d) (Fin d) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ) : IsUnit u :=
  (Unitary.toUnits ⟨u, hu⟩).isUnit

/-- Exact symmetry of the matrix product vectors of a block-diagonal tensor
whose blocks jointly span at one site permutes the blocks: the twist of the
block \(\sigma(k)\) by \(U_g\) is gauge equivalent to the block \(k\).
Source: arXiv:1010.3732, lines 652--660, for several normal blocks. -/
theorem exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (X : ∀ k, GL (Fin (dim k)) ℂ),
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical (U g) (A (σ k)) i) =
        (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          ((X k)⁻¹ : GL (Fin (dim k)) ℂ) := by
  have hB : WordTupleSpanTop (fun k => rotatePhysical (U g) (A k)) 1 :=
    (wordTupleSpanTop_rotatePhysical_iff (U g) (isUnit_of_mem_unitaryGroup (hU g)) A 1).mpr hA
  obtain ⟨T, hT⟩ := exists_algEquiv_of_sum_trace_evalWord_eq
    (sum_trace_evalWord_eq_of_isOnSiteSymmetric A U hSymm g) hA hB
  obtain ⟨σ, hdim, X, hX⟩ := algEquiv_pi_matrix_decomposition_apply T
  refine ⟨σ, hdim, X, fun k i => ?_⟩
  have h := hX (fun j => Kraus.evalWord (A j) [i]) k
  rw [hT [i], Matrix.coe_reindexAlgEquiv] at h
  simpa using h

/-- In the trace-preserving canonical normalization of every block, the
virtual gauges by which an exact on-site symmetry permutes the blocks are
unitary. Source: arXiv:1010.3732, lines 652--660, for several normal blocks
in the standard form \(\operatorname{tr}_{\mathrm{left}}(P^\dagger P)=I\). -/
theorem exists_perm_unitary_rotatePhysical_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (∀ k, V k ∈ Matrix.unitaryGroup (Fin (dim k)) ℂ) ∧
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical (U g) (A (σ k)) i) = V k * A k i * (V k)ᴴ := by
  obtain ⟨σ, hdim, X, hX⟩ :=
    exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetric_blockSum A hA U hU hSymm g
  have hu : U g * (U g)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hU g)
  have hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k) := fun k =>
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (A k)
      (Kraus.injective_implies_irreducibleCP (A k) (isInjective_of_wordTupleSpanTop_one hA k))
  have hV : ∀ k, ∃ V : Matrix.unitaryGroup (Fin (dim k)) ℂ,
      ∀ i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical (U g) (A (σ k)) i) =
        (V : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          (V : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)ᴴ := by
    intro k
    have hCleft := reindex_finCongr_transport (hdim k) (fun _ C => IsLeftCanonical C)
      (isLeftCanonical_rotatePhysical (A (σ k)) (U g) hu (hTP (σ k)))
    have hCirr := reindex_finCongr_transport (hdim k) (fun _ C => Kraus.IsIrreducibleFamily C)
      (isIrreducibleTensor_rotatePhysical (A (σ k)) (U g) hu (hIrr (σ k)))
    obtain ⟨V, -, hV⟩ :=
      exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible (X k) 1 one_ne_zero
        (fun i => by simpa only [one_smul] using hX k i) (hTP k) hCleft (hIrr k) hCirr
    exact ⟨V, fun i => by simpa only [one_smul] using hV i⟩
  choose V hV using hV
  exact ⟨σ, hdim, fun k => V k, fun k => (V k).property, hV⟩

end BlockPermutation

/-! ### The joint virtual action -/

section JointVirtualAction

/-- Block entries are carried along the block permutation, identifying the
equal block dimensions. -/
private def blockEntryPerm (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k) :
    BlockEntryIndex dim ≃ BlockEntryIndex dim :=
  Equiv.sigmaCongr σ fun k => (finCongr (hdim k).symm).prodCongr (finCongr (hdim k).symm)

private theorem blockEntryPerm_apply (σ : Equiv.Perm (Fin r))
    (hdim : ∀ k, dim (σ k) = dim k) (k : Fin r) (a b : Fin (dim k)) :
    blockEntryPerm σ hdim ⟨k, a, b⟩ =
      ⟨σ k, Fin.cast (hdim k).symm a, Fin.cast (hdim k).symm b⟩ :=
  rfl

/-- The joint virtual action: blockwise conjugation by `V k` on the matrix
coordinates, followed by the block permutation. -/
private noncomputable def blockVirtualAction (σ : Equiv.Perm (Fin r))
    (hdim : ∀ k, dim (σ k) = dim k) (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :
    Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ :=
  (Matrix.blockDiagonal' fun k => (V k)ᵀ ⊗ₖ (V k)ᴴ).submatrix id (blockEntryPerm σ hdim).symm

private theorem blockVirtualAction_mem_unitaryGroup (σ : Equiv.Perm (Fin r))
    (hdim : ∀ k, dim (σ k) = dim k) (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (hV : ∀ k, V k ∈ Matrix.unitaryGroup (Fin (dim k)) ℂ) :
    blockVirtualAction σ hdim V ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ := by
  have hW : (Matrix.blockDiagonal' fun k => (V k)ᵀ ⊗ₖ (V k)ᴴ)ᴴ *
      Matrix.blockDiagonal' (fun k => (V k)ᵀ ⊗ₖ (V k)ᴴ) = 1 := by
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_one]
    congr 1
    funext k
    rw [Pi.one_apply]
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.kronecker_mem_unitary (Matrix.transpose_mem_unitaryGroup_iff.mpr (hV k))
        (Unitary.star_mem (hV k)))
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, blockVirtualAction,
    Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hW,
    Matrix.submatrix_one_equiv]

private theorem blockPhysicalMatrix_mul_blockVirtualAction
    (A : (k : Fin r) → MPSTensor d (dim k)) (u : Matrix (Fin d) (Fin d) ℂ)
    (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
    (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (hCov : ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
      (rotatePhysical u (A (σ k)) i) = V k * A k i * (V k)ᴴ) :
    u * blockPhysicalMatrix A = blockPhysicalMatrix A * blockVirtualAction σ hdim V := by
  classical
  ext i p
  obtain ⟨⟨k, a, b⟩, rfl⟩ := (blockEntryPerm σ hdim).surjective p
  have hlocal := congrFun (congrFun (hCov k i) a) b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, rotatePhysical_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, finCongr_symm, finCongr_apply] at hlocal
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [blockVirtualAction, Matrix.submatrix_apply, id, Equiv.symm_apply_apply,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k (fun j _ hj => by
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hj])
    (fun hk => absurd (Finset.mem_univ k) hk)]
  simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Matrix.conjTranspose_apply, blockPhysicalMatrix,
    blockEntryPerm_apply]
  rw [hlocal]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a' _ => ?_
  ring

variable {G : Type*} [Monoid G]

/-- Exact on-site symmetry of a block-diagonal tensor in the trace-preserving
canonical normalization has a unitary virtual action on the joint physical
map: \(U_gP=PX_g\). Source: arXiv:1010.3732, lines 652--660, for several
normal blocks. -/
theorem exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ ∧
      U g * blockPhysicalMatrix A = blockPhysicalMatrix A * X := by
  obtain ⟨σ, hdim, V, hVU, hV⟩ :=
    exists_perm_unitary_rotatePhysical_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g
  exact ⟨blockVirtualAction σ hdim V, blockVirtualAction_mem_unitaryGroup σ hdim V hVU,
    blockPhysicalMatrix_mul_blockVirtualAction A (U g) σ hdim V hV⟩

/-- The positive polar factor of a block-diagonal tensor in trace-preserving
canonical normalization commutes with an exact on-site symmetry.
Source: arXiv:1010.3732, lines 660--676, for several normal blocks. -/
theorem commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    Commute (U g) (leftPolarPhysicalFactor A) := by
  obtain ⟨X, hX, hCov⟩ :=
    exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g
  exact commute_leftPolarPhysicalFactor_of_unitary_covariance A (U g) X (hU g) hX hCov

/-- The virtual unitary derived from exact symmetry of a block-diagonal tensor
intertwines the whole constructed isometric deformation.
Source: arXiv:1010.3732, lines 672--676, for several normal blocks. -/
theorem exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ ∧
      ∀ γ : unitInterval,
        U g * blockPhysicalMatrix (isometricDeformationBlocks A γ) =
          blockPhysicalMatrix (isometricDeformationBlocks A γ) * X := by
  obtain ⟨X, hX, hCov⟩ :=
    exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g
  exact ⟨X, hX, fun γ =>
    blockPhysicalMatrix_isometricDeformationBlocks_covariance A (U g) X (hU g) hX hCov γ⟩

/-- Exact on-site symmetry of a block-diagonal tensor whose blocks jointly span
at one site preserves every local MPS space of the tensor.
Source: arXiv:1010.3732, lines 672--676, for several normal blocks. -/
theorem groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetric
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (L : ℕ) :
    (groundSpaceES (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L (U g))) =
        groundSpaceES (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) L := by
  obtain ⟨σ, hdim, X, hX⟩ :=
    exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetric_blockSum A hA U hU hSymm g
  have hblock : ∀ k, groundSpaceES (rotatePhysical (U g) (A (σ k))) L =
      groundSpaceES (A k) L := by
    intro k
    have hre := reindex_finCongr_transport (hdim k)
      (fun _ C => groundSpaceES C L = groundSpaceES (rotatePhysical (U g) (A (σ k))) L) rfl
    rw [← hre]
    unfold groundSpaceES
    rw [GaugeEquiv.groundSpace_eq (A := A k) ⟨X k, hX k⟩ L]
  rw [← groundSpaceES_rotatePhysical, rotatePhysical_toTensorFromBlocks,
    groundSpaceES_toTensorFromBlocks_eq_iSup _ _ (fun _ => one_ne_zero),
    groundSpaceES_toTensorFromBlocks_eq_iSup _ _ (fun _ => one_ne_zero),
    ← σ.iSup_comp]
  exact iSup_congr hblock

end JointVirtualAction

/-! ### Parent Hamiltonians along the deformation -/

section ParentHamiltonians

variable {G : Type*} [Monoid G]

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the canonical two-site parent projection
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) :
    Commute (parentInteractionES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2)
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) :=
  parentInteractionES_isometricDeformationBlocks_commute A (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g)
    (groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetric A hA U hU hSymm g 2) γ

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the inverse-conjugated positive
interaction along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteractionES A γ).toLinearMap
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) :=
  isometricDeformationInteractionES_commute A (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g)
    (groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetric A hA U hU hSymm g 2) γ

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the periodic canonical parent Hamiltonian
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (parentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [periodicInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_blockSum
        A hA hTP U hU hSymm g γ)

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the open canonical parent Hamiltonian
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openParentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [openInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetric_blockSum
        A hA hTP U hU hSymm g γ)

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the periodic sum of inverse-conjugated
positive interactions along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem
    isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (periodicInteractionHamiltonianES
      (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) :=
  periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g γ)

/-- Exact on-site symmetry of a block-diagonal tensor in trace-preserving
canonical normalization persists in the open sum of inverse-conjugated
positive interactions along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetric_blockSum
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openInteractionHamiltonianES
      (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) :=
  openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetric_blockSum
      A hA hTP U hU hSymm g γ)

end ParentHamiltonians

end MPSTensor

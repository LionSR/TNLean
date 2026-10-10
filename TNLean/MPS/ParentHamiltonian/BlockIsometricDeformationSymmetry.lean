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
are invariant under \(U_g^{\otimes N}\) up to a phase,
\(U_g^{\otimes N}|\psi_N\rangle=\lambda_{g,N}|\psi_N\rangle\), for a unitary
on-site representation.

Comparing the summed traces of words of lengths one, two and three shows that the
phases are powers of one unimodular scalar: the summed word traces of the rotated
blocks are \(c^{|w|}\) times those of the original blocks. Rescaling \(U_g\) by
\(\bar c\) gives a unitary rotation preserving every summed word trace. Equality of
all word traces turns the assignment
\((A_k^{i})_k\mapsto(\bar c\sum_j (U_g)_{ij}A_k^{j})_k\) into an algebra
automorphism of \(\bigoplus_k M_{D_k}\). Such an automorphism permutes the
blocks and is inner on each block. In the trace-preserving canonical
normalization \(\sum_i A_k^{i\dagger}A_k^i=I\) of every block, each inner
part is unitary. The joint virtual action is then \(c\) times the block permutation
followed by the blockwise unitary conjugations; it is unitary and satisfies
\(U_gP=PX_g\). Consequently the positive polar factor \(Q\) commutes with
\(U_g\), the original two-site MPS space is invariant, and every canonical
parent projection and inverse-conjugated interaction along
\(P_\gamma=(\gamma Q+(1-\gamma)I)W\) commutes with the symmetry.

Source: Schuch--Pérez-García--Cirac, arXiv:1010.3732, paper_v3.tex,
lines 645--676. The joint one-site span is the source's standard form
(lines 325--352; in matrix language, lines 1740--1743: the one-site
matrices are block diagonal and span the block-diagonal matrices), and the
per-block normalization is the printed
condition \(\operatorname{tr}_{\mathrm{left}}(P^\dagger P)=I\) at line 653
for the block-diagonal \(P\). The symmetry is a symmetry of the state, so it holds only
up to a phase (lines 440--445 and 655--657).
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

/-! ### Phases of the word traces -/

section WordTracePhase

/-- Let `φ` be a functional on an algebra with `φ 1 ≠ 0` such that `φ (M * N) = 0` for every
`N` forces `M = 0`, and let `x` and `y` be two spanning families of letters.
If `φ` of every word of length one, two and three in `y` is `c₁`, `c₂` and `c₃` times `φ` of
the same word in `x`, then `φ` of every word of length `n` in `y` is `c₁ ^ n` times `φ` of
the same word in `x`.

This is the comparison of words of length `N` with their one-letter extensions that makes
the phase \(\lambda_{g,N}\) of a symmetry of the matrix product vectors multiplicative in
the length; the source does not spell out this step. Source context: arXiv:1010.3732,
lines 655--657 (a symmetry \(U_g^{\otimes N}\) of the MPS) and lines 440--445 (an on-site
symmetry is fixed only up to a one-dimensional representation). -/
theorem map_list_prod_eq_pow_mul_of_length_three
    {𝔄 : Type*} [Ring 𝔄] [Algebra ℂ 𝔄] (φ : 𝔄 →ₗ[ℂ] ℂ)
    (hφ : ∀ M : 𝔄, (∀ N, φ (M * N) = 0) → M = 0) (hφ1 : φ 1 ≠ 0)
    {ι : Type*} [Finite ι] (x y : ι → 𝔄)
    (hx : Submodule.span ℂ (Set.range x) = ⊤) (hy : Submodule.span ℂ (Set.range y) = ⊤)
    (c₁ c₂ c₃ : ℂ)
    (h₁ : ∀ i, φ (y i) = c₁ * φ (x i))
    (h₂ : ∀ i j, φ (y i * y j) = c₂ * φ (x i * x j))
    (h₃ : ∀ i j k, φ (y i * y j * y k) = c₃ * φ (x i * x j * x k)) :
    ∀ w : List ι, φ (w.map y).prod = c₁ ^ w.length * φ (w.map x).prod := by
  classical
  have := Fintype.ofFinite ι
  -- the linear map sending each `x i` to `y i`
  set a := Fintype.linearCombination ℂ x
  set b := Fintype.linearCombination ℂ y
  have ha : LinearMap.range a = ⊤ := by rw [Fintype.range_linearCombination, hx]
  -- vanishing of `φ (M * ·)` on the `y i` forces `M = 0`
  have hzero_y : ∀ M : 𝔄, (∀ j, φ (M * y j) = 0) → M = 0 := by
    intro M hM
    refine hφ M fun N => ?_
    have h := LinearMap.ext_on_range hy (f := φ ∘ₗ LinearMap.mulLeft ℂ M) (g := 0)
      (fun j => by simpa using hM j)
    simpa using LinearMap.congr_fun h N
  have hexp : ∀ (v : ι → 𝔄) (c : ι → ℂ) (z : 𝔄),
      φ (Fintype.linearCombination ℂ v c * z) = ∑ i, c i * φ (v i * z) := by
    intro v c z
    simp [Fintype.linearCombination_apply, Finset.sum_mul]
  have hker : ∀ c, a c = 0 → b c = 0 := by
    intro c hc
    refine hzero_y _ fun j => ?_
    have hc' : φ (a c * x j) = 0 := by rw [hc, zero_mul, map_zero]
    rw [hexp] at hc'
    rw [hexp]
    simp only [h₂]
    calc _ = c₂ * ∑ i, c i * φ (x i * x j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [hc', mul_zero]
  obtain ⟨s, hs⟩ := a.exists_rightInverse_of_surjective ha
  set L := b ∘ₗ s
  have hLa : ∀ c, L (a c) = b c := by
    intro c
    have h : a (s (a c) - c) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
    have := hker _ h
    rw [map_sub, sub_eq_zero] at this
    simpa [L] using this
  have hLx : ∀ i, L (x i) = y i := by
    intro i
    have := hLa (Pi.single i 1)
    simpa [a, b, Fintype.linearCombination_apply, Pi.single_apply] using this
  have hLsurj : ∀ N : 𝔄, ∃ Z, L Z = N := by
    have hle : Submodule.span ℂ (Set.range y) ≤ LinearMap.range L := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, hLx i⟩
    rw [hy, top_le_iff] at hle
    intro N
    exact LinearMap.range_eq_top.mp hle N
  have hzero_L : ∀ M : 𝔄, (∀ Z, φ (M * L Z) = 0) → M = 0 := by
    intro M hM
    refine hφ M fun N => ?_
    obtain ⟨Z, rfl⟩ := hLsurj N
    exact hM Z
  -- multilinear forms of the three trace relations
  have m₁ : ∀ X, φ (L X) = c₁ * φ X := by
    intro X
    have h := LinearMap.ext_on_range hx (f := φ ∘ₗ L) (g := c₁ • φ)
      (fun i => by simp [hLx, h₁])
    simpa using LinearMap.congr_fun h X
  have m₂ : ∀ X Y, φ (L X * L Y) = c₂ * φ (X * Y) := by
    have hi : ∀ i Y, φ (y i * L Y) = c₂ * φ (x i * Y) := by
      intro i Y
      have h := LinearMap.ext_on_range hx (f := φ ∘ₗ LinearMap.mulLeft ℂ (y i) ∘ₗ L)
        (g := c₂ • (φ ∘ₗ LinearMap.mulLeft ℂ (x i))) (fun j => by simp [hLx, h₂])
      simpa using LinearMap.congr_fun h Y
    intro X Y
    have h := LinearMap.ext_on_range hx (f := φ ∘ₗ LinearMap.mulRight ℂ (L Y) ∘ₗ L)
      (g := c₂ • (φ ∘ₗ LinearMap.mulRight ℂ Y)) (fun i => by simp [hLx, hi])
    simpa using LinearMap.congr_fun h X
  have m₃ : ∀ X Y Z, φ (L X * L Y * L Z) = c₃ * φ (X * Y * Z) := by
    have hij : ∀ i j Z, φ (y i * y j * L Z) = c₃ * φ (x i * x j * Z) := by
      intro i j Z
      have h := LinearMap.ext_on_range hx
        (f := φ ∘ₗ LinearMap.mulLeft ℂ (y i * y j) ∘ₗ L)
        (g := c₃ • (φ ∘ₗ LinearMap.mulLeft ℂ (x i * x j))) (fun k => by
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
            smul_eq_mul, hLx]
          exact h₃ i j k)
      simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
        smul_eq_mul] using LinearMap.congr_fun h Z
    have hi : ∀ i Y Z, φ (y i * L Y * L Z) = c₃ * φ (x i * Y * Z) := by
      intro i Y Z
      have h := LinearMap.ext_on_range hx
        (f := φ ∘ₗ LinearMap.mulRight ℂ (L Z) ∘ₗ LinearMap.mulLeft ℂ (y i) ∘ₗ L)
        (g := c₃ • (φ ∘ₗ LinearMap.mulRight ℂ Z ∘ₗ LinearMap.mulLeft ℂ (x i)))
        (fun j => by
          simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            LinearMap.smul_apply, smul_eq_mul, hLx]
          exact hij i j Z)
      simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        LinearMap.smul_apply, smul_eq_mul] using LinearMap.congr_fun h Y
    intro X Y Z
    have h := LinearMap.ext_on_range hx
      (f := φ ∘ₗ LinearMap.mulRight ℂ (L Y * L Z) ∘ₗ L)
      (g := c₃ • (φ ∘ₗ LinearMap.mulRight ℂ (Y * Z)))
      (fun i => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
          smul_eq_mul, hLx, ← mul_assoc]
        exact hi i Y Z)
    simpa only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
      smul_eq_mul, mul_assoc] using LinearMap.congr_fun h X
  -- the image of the identity is the scalar `c₁`
  have hc₁ : c₁ ≠ 0 := by
    obtain ⟨Z, hZ⟩ := hLsurj 1
    intro h0
    apply hφ1
    rw [← hZ, m₁, h0, zero_mul]
  have hu₂ : c₁ • L 1 = c₂ • (1 : 𝔄) := by
    rw [← sub_eq_zero]
    refine hzero_L _ fun Z => ?_
    rw [sub_mul, map_sub, smul_mul_assoc, smul_mul_assoc, one_mul, map_smul, map_smul,
      m₂, one_mul, m₁, smul_eq_mul, smul_eq_mul]
    ring
  have hc₂ : c₂ = c₁ ^ 2 := by
    have h := congrArg φ hu₂
    rw [map_smul, map_smul, m₁, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
    have := mul_right_cancel₀ hφ1 h
    rw [← this]; ring
  have hu : L 1 = c₁ • (1 : 𝔄) := by
    rw [hc₂, pow_two, mul_smul] at hu₂
    exact smul_right_injective 𝔄 hc₁ hu₂
  have hmul : ∀ X Y, L X * L Y = c₁ • L (X * Y) := by
    intro X Y
    rw [← sub_eq_zero]
    refine hzero_L _ fun Z => ?_
    have h := m₃ (X * Y) 1 Z
    rw [hu, mul_smul_comm, mul_one, smul_mul_assoc, map_smul, smul_eq_mul, mul_one] at h
    rw [sub_mul, map_sub, m₃, smul_mul_assoc, map_smul, smul_eq_mul, h, sub_self]
  -- induction along the word
  have hword : ∀ (w : List ι) Z,
      (w.map y).prod * L Z = c₁ ^ w.length • L ((w.map x).prod * Z) := by
    intro w
    induction w with
    | nil => intro Z; simp
    | cons i w ih =>
      intro Z
      rw [List.map_cons, List.prod_cons, mul_assoc, ih, mul_smul_comm, ← hLx i, hmul,
        smul_smul, List.map_cons, List.prod_cons, mul_assoc, List.length_cons, pow_succ]
  intro w
  have h := congrArg φ (hword w 1)
  rw [hu, mul_smul_comm, mul_one, mul_one, map_smul, map_smul, m₁, smul_eq_mul,
    smul_eq_mul] at h
  apply mul_left_cancel₀ hc₁
  rw [h]; ring

/-- The summed block trace `M ↦ ∑ k, tr M_k` on the product of the block matrix algebras. -/
private noncomputable def blockTrace (dim : Fin r → ℕ) :
    ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) →ₗ[ℂ] ℂ :=
  ∑ k, Matrix.traceLinearMap (Fin (dim k)) ℂ ℂ ∘ₗ LinearMap.proj k

private theorem blockTrace_apply (M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :
    blockTrace dim M = ∑ k, (M k).trace := by
  simp [blockTrace]

private theorem eq_zero_of_forall_blockTrace_mul_eq_zero
    (M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (h : ∀ N, blockTrace dim (M * N) = 0) : M = 0 := by
  classical
  funext k
  ext a b
  have hk := h (Pi.single k (Matrix.single b a 1))
  rw [blockTrace_apply, Finset.sum_eq_single k (fun j _ hj => by simp [hj])
    (fun hk => absurd (Finset.mem_univ k) hk)] at hk
  simpa [Matrix.trace_mul_single] using hk

private theorem blockTrace_one_ne_zero [∀ k, NeZero (dim k)] (hr : r ≠ 0) :
    blockTrace dim 1 ≠ 0 := by
  rw [blockTrace_apply]
  simp only [Pi.one_apply, Matrix.trace_one, Fintype.card_fin]
  rw [← Nat.cast_sum, Nat.cast_ne_zero]
  have hpos : 0 < ∑ k, dim k :=
    Finset.sum_pos (fun k _ => Nat.pos_of_ne_zero (NeZero.ne (dim k)))
      ⟨⟨0, Nat.pos_of_ne_zero hr⟩, Finset.mem_univ _⟩
  omega

private theorem list_prod_map_letter (A : (k : Fin r) → MPSTensor d (dim k))
    (w : List (Fin d)) :
    (w.map fun i k => A k i).prod = fun k => Kraus.evalWord (A k) w := by
  induction w with
  | nil => funext k; simp
  | cons i w ih => rw [List.map_cons, List.prod_cons, ih]; funext k; simp

private theorem span_range_letter_eq_top {A : (k : Fin r) → MPSTensor d (dim k)}
    (hA : WordTupleSpanTop A 1) :
    Submodule.span ℂ (Set.range fun i : Fin d => fun k => A k i) = ⊤ := by
  rw [eq_top_iff, ← hA]
  apply Submodule.span_mono
  rintro _ ⟨w, rfl⟩
  exact ⟨w 0, by funext k; simp [wordTuple, List.ofFn_succ]⟩

private theorem isUnit_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {u : Matrix n n ℂ} (hu : u ∈ Matrix.unitaryGroup n ℂ) : IsUnit u :=
  (Unitary.toUnits ⟨u, hu⟩).isUnit

private theorem mem_unitary_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr (by rw [RCLike.star_def, RCLike.conj_mul, hc]; simp)

private theorem smul_star_smul_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) : c • (star c • u) = u := by
  rw [smul_smul, Unitary.mul_star_self_of_mem (mem_unitary_of_norm_eq_one hc), one_smul]

variable {G : Type*} [Monoid G]

open scoped ComplexOrder in
/-- Symmetry up to a phase of a block-diagonal tensor whose blocks jointly span at one site
has phases that are powers of one unimodular scalar: the summed word traces of the blocks
rotated by \(U_g\) are \(c^{|w|}\) times those of the original blocks, with \(|c|=1\).
Source: arXiv:1010.3732, lines 440--445 and 655--657. -/
theorem exists_norm_eq_one_sum_trace_evalWord_rotatePhysical_eq_pow_mul
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w : List (Fin d),
      ∑ k, (Kraus.evalWord (rotatePhysical (U g) (A k)) w).trace =
        c ^ w.length * ∑ k, (Kraus.evalWord (A k) w).trace := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · exact ⟨1, by simp, fun w => by simp⟩
  set x : Fin d → ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := fun i k => A k i
    with hxdef
  set y : Fin d → ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
    fun i k => rotatePhysical (U g) (A k) i with hydef
  have hx : Submodule.span ℂ (Set.range x) = ⊤ := span_range_letter_eq_top hA
  have hy : Submodule.span ℂ (Set.range y) = ⊤ :=
    span_range_letter_eq_top (A := fun k => rotatePhysical (U g) (A k))
      ((wordTupleSpanTop_rotatePhysical_iff (U g) (isUnit_of_mem_unitaryGroup (hU g)) A 1).mpr
        hA)
  have hwx : ∀ w : List (Fin d), (w.map x).prod = fun k => Kraus.evalWord (A k) w :=
    list_prod_map_letter A
  have hwy : ∀ w : List (Fin d),
      (w.map y).prod = fun k => Kraus.evalWord (rotatePhysical (U g) (A k)) w :=
    list_prod_map_letter (fun k => rotatePhysical (U g) (A k))
  have hphase : ∀ N, ∃ c : ℂ, ∀ w : List (Fin d), w.length = N →
      blockTrace dim (w.map y).prod = c * blockTrace dim (w.map x).prod := by
    intro N
    obtain ⟨c, hc⟩ := hSymm g N
    refine ⟨c, fun w hw => ?_⟩
    subst hw
    have h := hc w.get
    have htw : twistedTensor (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U g =
        toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) (fun k => rotatePhysical (U g) (A k)) :=
      rotatePhysical_toTensorFromBlocks (U g) _ A
    rw [htw, mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum] at h
    rw [hwx, hwy, blockTrace_apply, blockTrace_apply]
    simpa [mpv, coeff, List.ofFn_get] using h
  obtain ⟨c₁, h₁⟩ := hphase 1
  obtain ⟨c₂, h₂⟩ := hphase 2
  obtain ⟨c₃, h₃⟩ := hphase 3
  have hpow := map_list_prod_eq_pow_mul_of_length_three (blockTrace dim)
    eq_zero_of_forall_blockTrace_mul_eq_zero (blockTrace_one_ne_zero hr) x y hx hy c₁ c₂ c₃
    (fun i => by simpa using h₁ [i] rfl) (fun i j => by simpa using h₂ [i, j] rfl)
    (fun i j k => by simpa [mul_assoc] using h₃ [i, j, k] rfl)
  refine ⟨c₁, ?_, fun w => by simpa [hwx, hwy, blockTrace_apply] using hpow w⟩
  -- the one-site traces form an eigenvector of `U g` with eigenvalue `c₁`
  set v : Fin d → ℂ := fun i => blockTrace dim (x i) with hvdef
  have hv : v ≠ 0 := by
    intro hv0
    apply blockTrace_one_ne_zero (dim := dim) hr
    have h := LinearMap.ext_on_range hx (f := blockTrace dim) (g := 0)
      (fun i => by simpa [v] using congrFun hv0 i)
    rw [h, LinearMap.zero_apply]
  have hUv : U g *ᵥ v = c₁ • v := by
    funext i
    have hi := h₁ [i] rfl
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hi
    rw [Pi.smul_apply, smul_eq_mul, ← hi]
    simp only [hydef, hvdef, hxdef, Matrix.mulVec, dotProduct, blockTrace_apply,
      rotatePhysical_apply, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hu : (U g)ᴴ * U g = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp (hU g)
  have hdot : star v ⬝ᵥ v = (star c₁ * c₁) * (star v ⬝ᵥ v) := by
    calc star v ⬝ᵥ v = star (U g *ᵥ v) ⬝ᵥ (U g *ᵥ v) := by
          rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
            ← Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, hu, Matrix.vecMul_one]
      _ = (star c₁ * c₁) * (star v ⬝ᵥ v) := by
          rw [hUv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
            mul_assoc]
  have hne : star v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
  have hcc : star c₁ * c₁ = 1 := mul_right_cancel₀ hne (hdot.symm.trans (one_mul _).symm)
  exact CStarRing.norm_of_mem_unitary (Unitary.mem_iff_star_mul_self.mpr hcc)

/-- Rotation by a rescaled physical matrix rescales every rotated letter. -/
private theorem rotatePhysical_smul_apply {D : ℕ} (a : ℂ) (u : Matrix (Fin d) (Fin d) ℂ)
    (B : MPSTensor d D) (i : Fin d) :
    rotatePhysical (a • u) B i = a • rotatePhysical u B i := by
  simp [rotatePhysical_apply, Finset.smul_sum, smul_smul]

/-- Rescaling a symmetry with phases \(c^N\) by \(\bar c\) gives a unitary physical matrix
whose rotation preserves all summed word traces. -/
private theorem rescaled_rotation_data (A : (k : Fin r) → MPSTensor d (dim k))
    {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ) {c : ℂ}
    (hc : ‖c‖ = 1)
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (rotatePhysical u (A k)) w).trace =
      c ^ w.length * ∑ k, (Kraus.evalWord (A k) w).trace) :
    star c • u ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      (∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
        ∑ k, (Kraus.evalWord (rotatePhysical (star c • u) (A k)) w).trace) ∧
      ∀ (k : Fin r) (i : Fin d),
        rotatePhysical u (A k) i = c • rotatePhysical (star c • u) (A k) i := by
  have hcu := mem_unitary_of_norm_eq_one hc
  have hstar : star c * c = 1 := (Unitary.mem_iff.mp hcu).1
  have hstar' : c * star c = 1 := (Unitary.mem_iff.mp hcu).2
  refine ⟨Unitary.smul_mem_of_mem (Unitary.star_mem hcu) hu, fun w => ?_, fun k i => ?_⟩
  · have hrot : ∀ k, rotatePhysical (star c • u) (A k) =
        fun i => star c • rotatePhysical u (A k) i :=
      fun k => funext fun i => rotatePhysical_smul_apply _ _ _ _
    simp only [hrot, Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul, ← Finset.mul_sum,
      hTr, ← mul_assoc, ← mul_pow, hstar, one_pow, one_mul]
  · rw [rotatePhysical_smul_apply, smul_smul, hstar', one_smul]

end WordTracePhase

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

/-- A physical rotation preserving all summed word traces of jointly spanning blocks
permutes the blocks up to gauge. -/
private theorem exists_perm_gauge_rotatePhysical_of_sum_trace_eq
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k)) (hA : WordTupleSpanTop A 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : IsUnit u)
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (rotatePhysical u (A k)) w).trace) :
    ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (X : ∀ k, GL (Fin (dim k)) ℂ),
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical u (A (σ k)) i) =
        (X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          ((X k)⁻¹ : GL (Fin (dim k)) ℂ) := by
  have hB : WordTupleSpanTop (fun k => rotatePhysical u (A k)) 1 :=
    (wordTupleSpanTop_rotatePhysical_iff u hu A 1).mpr hA
  obtain ⟨T, hT⟩ := exists_algEquiv_of_sum_trace_evalWord_eq hTr hA hB
  obtain ⟨σ, hdim, X, hX⟩ := algEquiv_pi_matrix_decomposition_apply T
  refine ⟨σ, hdim, X, fun k i => ?_⟩
  have h := hX (fun j => Kraus.evalWord (A j) [i]) k
  rw [hT [i], Matrix.coe_reindexAlgEquiv] at h
  simpa using h

/-- In the trace-preserving canonical normalization, the gauges of
`exists_perm_gauge_rotatePhysical_of_sum_trace_eq` for a unitary rotation are unitary. -/
private theorem exists_perm_unitary_rotatePhysical_of_sum_trace_eq
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (u : Matrix (Fin d) (Fin d) ℂ) (hU : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hTr : ∀ w : List (Fin d), ∑ k, (Kraus.evalWord (A k) w).trace =
      ∑ k, (Kraus.evalWord (rotatePhysical u (A k)) w).trace) :
    ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (∀ k, V k ∈ Matrix.unitaryGroup (Fin (dim k)) ℂ) ∧
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical u (A (σ k)) i) = V k * A k i * (V k)ᴴ := by
  obtain ⟨σ, hdim, X, hX⟩ :=
    exists_perm_gauge_rotatePhysical_of_sum_trace_eq A hA u (isUnit_of_mem_unitaryGroup hU) hTr
  have hu : u * uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  have hIrr : ∀ k, Kraus.IsIrreducibleFamily (A k) := fun k =>
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM (A k)
      (Kraus.injective_implies_irreducibleCP (A k) (isInjective_of_wordTupleSpanTop_one hA k))
  have hV : ∀ k, ∃ V : Matrix.unitaryGroup (Fin (dim k)) ℂ,
      ∀ i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical u (A (σ k)) i) =
        (V : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          (V : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)ᴴ := by
    intro k
    have hCleft := reindex_finCongr_transport (hdim k) (fun _ C => IsLeftCanonical C)
      (isLeftCanonical_rotatePhysical (A (σ k)) u hu (hTP (σ k)))
    have hCirr := reindex_finCongr_transport (hdim k) (fun _ C => Kraus.IsIrreducibleFamily C)
      (isIrreducibleTensor_rotatePhysical (A (σ k)) u hu (hIrr (σ k)))
    obtain ⟨V, -, hV⟩ :=
      exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible (X k) 1 one_ne_zero
        (fun i => by simpa only [one_smul] using hX k i) (hTP k) hCleft (hIrr k) hCirr
    exact ⟨V, fun i => by simpa only [one_smul] using hV i⟩
  choose V hV using hV
  exact ⟨σ, hdim, fun k => V k, fun k => (V k).property, hV⟩

variable {G : Type*} [Monoid G]

/-- A symmetry up to a phase of the matrix product vectors of a block-diagonal tensor
whose blocks jointly span at one site permutes the blocks: for a unimodular scalar \(c\),
the twist of the block \(\sigma(k)\) by \(U_g\) is \(c\) times a gauge transform of the
block \(k\). Source: arXiv:1010.3732, lines 652--660, for several normal blocks. -/
theorem exists_perm_gauge_rotatePhysical_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (X : ∀ k, GL (Fin (dim k)) ℂ),
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical (U g) (A (σ k)) i) =
        c • ((X k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) * A k i *
          ((X k)⁻¹ : GL (Fin (dim k)) ℂ)) := by
  obtain ⟨c, hc, hTr⟩ :=
    exists_norm_eq_one_sum_trace_evalWord_rotatePhysical_eq_pow_mul A hA U hU hSymm g
  obtain ⟨hu', hTr', hscale⟩ := rescaled_rotation_data A (hU g) hc hTr
  obtain ⟨σ, hdim, X, hX⟩ := exists_perm_gauge_rotatePhysical_of_sum_trace_eq A hA
    (star c • U g) (isUnit_of_mem_unitaryGroup hu') hTr'
  refine ⟨c, hc, σ, hdim, X, fun k i => ?_⟩
  rw [hscale, ← hX k i]
  simp [Matrix.reindex_apply, Matrix.submatrix_smul]

/-- In the trace-preserving canonical normalization of every block, the virtual gauges by
which a symmetry up to a phase permutes the blocks are unitary. Source: arXiv:1010.3732,
lines 652--660, for several normal blocks in the standard form
\(\operatorname{tr}_{\mathrm{left}}(P^\dagger P)=I\). -/
theorem exists_perm_unitary_rotatePhysical_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ (σ : Equiv.Perm (Fin r)) (hdim : ∀ k, dim (σ k) = dim k)
      (V : ∀ k, Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      (∀ k, V k ∈ Matrix.unitaryGroup (Fin (dim k)) ℂ) ∧
      ∀ k i, Matrix.reindex (finCongr (hdim k)) (finCongr (hdim k))
          (rotatePhysical (U g) (A (σ k)) i) = c • (V k * A k i * (V k)ᴴ) := by
  obtain ⟨c, hc, hTr⟩ :=
    exists_norm_eq_one_sum_trace_evalWord_rotatePhysical_eq_pow_mul A hA U hU hSymm g
  obtain ⟨hu', hTr', hscale⟩ := rescaled_rotation_data A (hU g) hc hTr
  obtain ⟨σ, hdim, V, hVU, hV⟩ :=
    exists_perm_unitary_rotatePhysical_of_sum_trace_eq A hA hTP (star c • U g) hu' hTr'
  refine ⟨c, hc, σ, hdim, V, hVU, fun k i => ?_⟩
  rw [hscale, ← hV k i]
  simp [Matrix.reindex_apply, Matrix.submatrix_smul]

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

/-- A symmetry up to a phase of a block-diagonal tensor in the trace-preserving canonical
normalization has a unitary virtual action on the joint physical map: \(U_gP=PX_g\).
Source: arXiv:1010.3732, lines 652--660, for several normal blocks. -/
theorem exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ ∧
      U g * blockPhysicalMatrix A = blockPhysicalMatrix A * X := by
  obtain ⟨c, hc, hTr⟩ :=
    exists_norm_eq_one_sum_trace_evalWord_rotatePhysical_eq_pow_mul A hA U hU hSymm g
  obtain ⟨hu', hTr', -⟩ := rescaled_rotation_data A (hU g) hc hTr
  obtain ⟨σ, hdim, V, hVU, hV⟩ :=
    exists_perm_unitary_rotatePhysical_of_sum_trace_eq A hA hTP (star c • U g) hu' hTr'
  have hcov := blockPhysicalMatrix_mul_blockVirtualAction A (star c • U g) σ hdim V hV
  have hcu := mem_unitary_of_norm_eq_one hc
  have hUg : U g = c • (star c • U g) := (smul_star_smul_of_norm_eq_one hc _).symm
  refine ⟨c • blockVirtualAction σ hdim V,
    Unitary.smul_mem_of_mem hcu (blockVirtualAction_mem_unitaryGroup σ hdim V hVU), ?_⟩
  rw [hUg, Matrix.smul_mul, hcov, Matrix.mul_smul]

/-- The positive polar factor of a block-diagonal tensor in trace-preserving canonical
normalization commutes with a symmetry up to a phase.
Source: arXiv:1010.3732, lines 660--676, for several normal blocks. -/
theorem commute_leftPolarPhysicalFactor_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    Commute (U g) (leftPolarPhysicalFactor A) := by
  obtain ⟨X, hX, hCov⟩ :=
    exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g
  exact commute_leftPolarPhysicalFactor_of_unitary_covariance A (U g) X (hU g) hX hCov

/-- The virtual unitary derived from a symmetry up to a phase of a block-diagonal tensor
intertwines the whole constructed isometric deformation.
Source: arXiv:1010.3732, lines 672--676, for several normal blocks. -/
theorem exists_isometricDeformationBlocks_unitary_covariance_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) :
    ∃ X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ,
      X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ ∧
      ∀ γ : unitInterval,
        U g * blockPhysicalMatrix (isometricDeformationBlocks A γ) =
          blockPhysicalMatrix (isometricDeformationBlocks A γ) * X := by
  obtain ⟨X, hX, hCov⟩ :=
    exists_blockPhysicalMatrix_unitary_covariance_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g
  exact ⟨X, hX, fun γ =>
    blockPhysicalMatrix_isometricDeformationBlocks_covariance A (U g) X (hU g) hX hCov γ⟩

/-- The `L`-fold on-site power of a rescaled matrix is the rescaled power. -/
private theorem onSiteTensorPow_smul (L : ℕ) (a : ℂ) (u : Matrix (Fin d) (Fin d) ℂ) :
    onSiteTensorPow L (a • u) = a ^ L • onSiteTensorPow L u := by
  ext σ τ
  simp [onSiteTensorPow_apply, Finset.prod_mul_distrib, Finset.prod_const]

/-- A symmetry up to a phase of a block-diagonal tensor whose blocks jointly span at one
site preserves every local MPS space of the tensor.
Source: arXiv:1010.3732, lines 672--676, for several normal blocks. -/
theorem groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (L : ℕ) :
    (groundSpaceES (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) L).map
      (Matrix.toEuclideanLin (onSiteTensorPow L (U g))) =
        groundSpaceES (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) L := by
  obtain ⟨c, hc, hTr⟩ :=
    exists_norm_eq_one_sum_trace_evalWord_rotatePhysical_eq_pow_mul A hA U hU hSymm g
  obtain ⟨hu', hTr', -⟩ := rescaled_rotation_data A (hU g) hc hTr
  obtain ⟨σ, hdim, X, hX⟩ := exists_perm_gauge_rotatePhysical_of_sum_trace_eq A hA
    (star c • U g) (isUnit_of_mem_unitaryGroup hu') hTr'
  have hUg : U g = c • (star c • U g) := (smul_star_smul_of_norm_eq_one hc _).symm
  have hc0 : c ^ L ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hc)
  rw [hUg, onSiteTensorPow_smul, map_smul, Submodule.map_smul _ _ _ hc0]
  have hblock : ∀ k, groundSpaceES (rotatePhysical (star c • U g) (A (σ k))) L =
      groundSpaceES (A k) L := by
    intro k
    have hre := reindex_finCongr_transport (hdim k)
      (fun _ C => groundSpaceES C L =
        groundSpaceES (rotatePhysical (star c • U g) (A (σ k))) L) rfl
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

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the canonical two-site parent projection
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) :
    Commute (parentInteractionES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2)
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) :=
  parentInteractionES_isometricDeformationBlocks_commute A (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g)
    (groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetricUpToPhase A hA U hU hSymm g 2) γ

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the inverse-conjugated positive
interaction along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformationInteractionES_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) :
    Commute (isometricDeformationInteractionES A γ).toLinearMap
      (Matrix.toEuclideanLin (onSiteTensorPow 2 (U g))) :=
  isometricDeformationInteractionES_commute A (U g) (hU g)
    (commute_leftPolarPhysicalFactor_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g)
    (groundSpaceES_toTensorFromBlocks_invariant_of_isOnSiteSymmetricUpToPhase A hA U hU hSymm g 2) γ

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the periodic canonical parent Hamiltonian
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_parentHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (parentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [periodicInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetricUpToPhase
        A hA hTP U hU hSymm g γ)

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the open canonical parent Hamiltonian
along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_openParentHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openParentHamiltonianES
      (toTensorFromBlocks (fun _ => 1) (isometricDeformationBlocks A γ)) 2 N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) := by
  simpa only [openInteractionHamiltonianES_parentInteractionES _
    (show 0 < (2 : ℕ) by decide)] using
    openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
      (parentInteractionES_isometricDeformationBlocks_commute_of_isOnSiteSymmetricUpToPhase
        A hA hTP U hU hSymm g γ)

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the periodic sum of inverse-conjugated
positive interactions along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_periodicInteractionHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (periodicInteractionHamiltonianES
      (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) :=
  periodicInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g γ)

/-- A symmetry up to a phase of a block-diagonal tensor in trace-preserving
canonical normalization persists in the open sum of inverse-conjugated
positive interactions along the constructed polar deformation.
Source: arXiv:1010.3732, lines 645--676, for several normal blocks. -/
theorem isometricDeformation_openInteractionHamiltonianES_commute_of_isOnSiteSymmetricUpToPhase
    [∀ k, NeZero (dim k)] (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : WordTupleSpanTop A 1) (hTP : ∀ k, ∑ i, (A k i)ᴴ * A k i = 1)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetricUpToPhase (toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) A) U)
    (g : G) (γ : unitInterval) {N : ℕ} (hN : 2 ≤ N) :
    Commute (openInteractionHamiltonianES
      (isometricDeformationInteractionES A γ).toLinearMap N)
      (Matrix.toEuclideanLin (onSiteTensorPow N (U g))) :=
  openInteractionHamiltonianES_commute_onSiteTensorPow _ (U g) hN
    (isometricDeformationInteractionES_commute_of_isOnSiteSymmetricUpToPhase
      A hA hTP U hU hSymm g γ)

end ParentHamiltonians

end MPSTensor

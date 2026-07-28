/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KoashiImoto.RecoveredConditionalDilation.Basic

/-!
# Ambient direct-sum action of a recovered conditional dilation

This module gives the coordinate equivalence and entrywise block calculation
for a pure-ancilla dilation acting on an ambient HJPW direct sum. Complementary
input blocks are required to vanish; no global recovery-channel equality is
asserted outside the joint support.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker

namespace Matrix

open RecoveredConditionalDilationInternal

/-- Reindex a dependent middle-system direct sum after adjoining a spectator
system and an output system.  Each block is ordered as the HJPW conditional
factor followed by the recovered common-output factor. -/
def RecoveredConditionalDilationInternal.recoveredTripartiteBlockEquiv
    {I A B C : Type*} {M D : I → Type*}
    (eB : ((i : I) × (M i × D i)) ≃ B) :
    ((i : I) × ((A × D i) × (M i × C))) ≃ A × (B × C) :=
  (Equiv.sigmaCongrRight fun i =>
      (Equiv.prodComm (A × D i) (M i × C)).trans
        (((Equiv.refl (M i × C)).prodCongr
          (Equiv.prodComm A (D i))).trans
            (Equiv.prodAssoc (M i × C) (D i) A).symm)) |>.trans
    (Equiv.sigmaProdDistrib (fun i => (M i × C) × D i) A).symm |>.trans
    ((dilationBlockEquiv eB).prodCongr (Equiv.refl A)) |>.trans
    (Equiv.prodComm (B × C) A)

@[simp]
theorem RecoveredConditionalDilationInternal.recoveredTripartiteBlockEquiv_apply
    {I A B C : Type*} {M D : I → Type*}
    (eB : ((i : I) × (M i × D i)) ≃ B)
    (i : I) (a : A) (d : D i) (m : M i) (c : C) :
    recoveredTripartiteBlockEquiv eB ⟨i, ((a, d), (m, c))⟩ =
      (a, (eB ⟨i, (m, d)⟩, c)) := by
  rfl

/-- The ambient matrix of a dependent direct sum of local dilation blocks. -/
def RecoveredConditionalDilationInternal.blockDilationUnitary
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ) :
    Matrix (Fin dB × (Fin dC × Fin r))
      (Fin dB × (Fin dC × Fin r)) ℂ :=
  let eD := dilationBlockEquiv (E := Fin dC × Fin r) eB
  Matrix.reindex eD eD
    (Matrix.blockDiagonal' fun s ↦
      Ulocal s ⊗ₖ
        (1 : Matrix (Fin (ambientRecoveredConditionalDim d s))
          (Fin (ambientRecoveredConditionalDim d s)) ℂ))

/-- Entrywise expansion of a rectangular Kraus map. -/
theorem RecoveredConditionalDilationInternal.rectangularKrausMap_apply_entry
    {I A B : Type*} [Fintype I] [Fintype A]
    (K : I → Matrix B A ℂ) (X : Matrix A A ℂ) (b b' : B) :
    rectangularKrausMap K X b b' =
      ∑ i, ∑ x, ∑ y, K i b x * X x y * star (K i b' y) := by
  simp only [rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- A fixed pure-ancilla recovery is the rectangular Kraus map obtained by
slicing its dilation isometry along the discarded environment coordinate. -/
theorem RecoveredConditionalDilationInternal.pureAncillaRecovery_eq_rectangularKrausMap
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ)
    (X : Matrix B B ℂ) :
    pureAncillaRecovery c₀ r₀ U X =
      rectangularKrausMap (fun i : R =>
        fun bc b => (U * fixedEnvEmbedding (S := B) (c₀, r₀))
          (bc.1, (bc.2, i)) b) X := by
  let K : R → Matrix (B × C) B ℂ := fun i bc b =>
    (U * fixedEnvEmbedding (S := B) (c₀, r₀))
      (bc.1, (bc.2, i)) b
  have hV : pureAncillaDilationIsometry c₀ r₀ U *
        (1 : Matrix B B ℂ) =
      stinespringVGen K * (1 : Matrix B B ℂ) := by
    rw [Matrix.mul_one, Matrix.mul_one]
    ext ⟨⟨b, c⟩, i⟩ x
    rfl
  have h := pureAncillaRecovery_eq_rectangularKrausMap_on_support
    c₀ r₀ U K (1 : Matrix B B ℂ) hV X
  simpa [K] using h

set_option maxHeartbeats 400000 in
-- The entrywise Kraus-family conjugation requires a larger reduction budget.
/-- Conjugating a block-coordinate pure-ancilla dilation by a system unitary
conjugates both its input and retained system-output coordinates. -/
theorem RecoveredConditionalDilationInternal.pureAncillaRecovery_physical_conjugation
    {B C R : Type*} [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (c₀ : C) (r₀ : R)
    (Q : Matrix B B ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup B ℂ)
    (U : Matrix (B × (C × R)) (B × (C × R)) ℂ)
    (X : Matrix B B ℂ) :
    let lift := Q ⊗ₖ (1 : Matrix (C × R) (C × R) ℂ)
    let Uphysical := lift * U * star lift
    star (Q ⊗ₖ (1 : Matrix C C ℂ)) *
        pureAncillaRecovery c₀ r₀ Uphysical X *
          (Q ⊗ₖ (1 : Matrix C C ℂ)) =
      pureAncillaRecovery c₀ r₀ U (star Q * X * Q) := by
  dsimp only
  rw [pureAncillaRecovery_eq_rectangularKrausMap,
    pureAncillaRecovery_eq_rectangularKrausMap]
  let J := fixedEnvEmbedding (S := B) (c₀, r₀)
  let lift := Q ⊗ₖ (1 : Matrix (C × R) (C × R) ℂ)
  let liftC := Q ⊗ₖ (1 : Matrix C C ℂ)
  let Kphysical : R → Matrix (B × C) B ℂ := fun i bc b =>
    ((lift * U * star lift) * J) (bc.1, (bc.2, i)) b
  let Kblocks : R → Matrix (B × C) B ℂ := fun i bc b =>
    (U * J) (bc.1, (bc.2, i)) b
  change star liftC * rectangularKrausMap Kphysical X * liftC =
    rectangularKrausMap Kblocks (star Q * X * Q)
  have hQright : Q * star Q = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hQ
  have hliftC : liftC ∈ Matrix.unitaryGroup (B × C) ℂ :=
    Matrix.kronecker_mem_unitary hQ (Submonoid.one_mem _)
  have hliftCleft : star liftC * liftC = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hliftC
  have hV : (lift * U * star lift) * J =
      lift * (U * J * star Q) := by
    have h := physicalDilation_mul_fixedEnvEmbedding_mul_support
      (c₀, r₀) Q hQ U (star Q)
    simpa only [lift, J, hQright, Matrix.mul_one] using h
  have hK (i : R) :
      Kphysical i = liftC * Kblocks i * star Q := by
    apply Matrix.ext
    rintro ⟨b, c⟩ b'
    change (lift * U * star lift * J) (b, (c, i)) b' =
      (liftC * Kblocks i * star Q) (b, c) b'
    rw [hV]
    rw [Matrix.mul_assoc liftC (Kblocks i) (star Q)]
    change rightOutputSlice (lift * (U * J * star Q)) (c, i) b b' =
      rightOutputSlice (liftC * (Kblocks i * star Q)) c b b'
    rw [rightOutputSlice_kronecker_one_mul,
      rightOutputSlice_kronecker_one_mul]
    rfl
  simp only [rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [hK]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose,
    star_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hliftCleft, Matrix.one_mul, Matrix.mul_one]

/-- A supported entry of the named ambient block dilation is the local
Stinespring entry tensored with the conditional identity. -/
@[simp] private theorem blockDilationUnitary_fixedEnv_apply_support
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (L : Fin r → ∀ j : Fin K,
      Matrix (Fin (m j) × Fin dC) (Fin (m j)) ℂ)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (hUlocal : ∀ j,
      Matrix.reindex (Equiv.prodAssoc (Fin (m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (m j))) (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding (S := Fin (m j)) (c₀, k₀))
    (j : Fin K)
    (u u' : Fin (ambientRecoveredCommonDim m (Sum.inr j)))
    (v v' : Fin (ambientRecoveredConditionalDim d (Sum.inr j)))
    (c : Fin dC) (i : Fin r) :
    (blockDilationUnitary eB Ulocal *
        fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
        (eB ⟨Sum.inr j, (u', v')⟩) =
      L i j (u, c) u' *
        (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v v' := by
  simpa [blockDilationUnitary] using
    blockDilation_fixedEnv_apply_support eB c₀ k₀ L Ulocal hUlocal
      j u v c i u' v'

/-- A supported output entry of the named block dilation vanishes on every
other supported input sector. -/
@[simp] private theorem blockDilationUnitary_fixedEnv_apply_support_ne
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    {j j' : Fin K} (hjj' : j ≠ j')
    (u : Fin (ambientRecoveredCommonDim m (Sum.inr j)))
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inr j)))
    (c : Fin dC) (i : Fin r)
    (u' : Fin (ambientRecoveredCommonDim m (Sum.inr j')))
    (v' : Fin (ambientRecoveredConditionalDim d (Sum.inr j'))) :
    (blockDilationUnitary eB Ulocal *
        fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
        (eB ⟨Sum.inr j', (u', v')⟩) = 0 := by
  simpa [blockDilationUnitary] using
    blockDilation_fixedEnv_apply_support_ne eB c₀ k₀ Ulocal hjj'
      u v c i u' v'

/-- A supported output entry of the named block dilation vanishes on a
complementary input. -/
@[simp] private theorem blockDilationUnitary_fixedEnv_apply_support_complement
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (j : Fin K)
    (u : Fin (ambientRecoveredCommonDim m (Sum.inr j)))
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inr j)))
    (c : Fin dC) (i : Fin r) (q : Fin z)
    (u' : Fin (ambientRecoveredCommonDim m (Sum.inl q)))
    (v' : Fin (ambientRecoveredConditionalDim d (Sum.inl q))) :
    (blockDilationUnitary eB Ulocal *
        fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
        (eB ⟨Sum.inl q, (u', v')⟩) = 0 := by
  simpa [blockDilationUnitary] using
    blockDilation_fixedEnv_apply_support_complement eB c₀ k₀ Ulocal
      j u v c i q u' v'

/-- A complementary output entry of the named block dilation vanishes on a
supported input. -/
@[simp] private theorem blockDilationUnitary_fixedEnv_apply_complement_support
    {z K dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (q : Fin z)
    (u : Fin (ambientRecoveredCommonDim m (Sum.inl q)))
    (v : Fin (ambientRecoveredConditionalDim d (Sum.inl q)))
    (c : Fin dC) (i : Fin r) (j : Fin K)
    (u' : Fin (ambientRecoveredCommonDim m (Sum.inr j)))
    (v' : Fin (ambientRecoveredConditionalDim d (Sum.inr j))) :
    (blockDilationUnitary eB Ulocal *
        fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
        (eB ⟨Sum.inl q, (u, v)⟩, (c, i))
        (eB ⟨Sum.inr j, (u', v')⟩) = 0 := by
  simpa [blockDilationUnitary] using
    blockDilation_fixedEnv_apply_complement_support eB c₀ k₀ Ulocal
      q u v c i j u' v'

/-- The ambient bipartite direct sum with zero complementary blocks. -/
def RecoveredConditionalDilationInternal.ambientBipartiteBlockMatrix
    {z K dA dB : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (σ : ∀ j : Fin K, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (ω : ∀ j : Fin K,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ) :
    Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ :=
  Matrix.reindex (recoveredBipartiteBlockEquiv eB)
    (recoveredBipartiteBlockEquiv eB)
    (Matrix.blockDiagonal' fun s => match s with
      | Sum.inl _ => 0
      | Sum.inr k => σ k ⊗ₖ ω k)

/-- The ambient tripartite direct sum in HJPW factor order, with zero
complementary blocks and supported blocks `ω_j ⊗ τ_j`. -/
def RecoveredConditionalDilationInternal.ambientTripartiteBlockMatrix
    {z K dA dB dC : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (ω : ∀ j : Fin K,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ)
    (τ : ∀ j : Fin K,
      Matrix (Fin (m j) × Fin dC) (Fin (m j) × Fin dC) ℂ) :
    Matrix (Fin dA × (Fin dB × Fin dC))
      (Fin dA × (Fin dB × Fin dC)) ℂ :=
  Matrix.reindex (recoveredTripartiteBlockEquiv eB)
    (recoveredTripartiteBlockEquiv eB)
    (Matrix.blockDiagonal' fun s => match s with
      | Sum.inl _ => 0
      | Sum.inr j => ω j ⊗ₖ τ j)

set_option linter.flexible false in
-- The four dependent-sector cases intentionally simplify to different goals.
/-- Taking an `A`-block of the ambient bipartite direct sum leaves a
middle-system direct sum with the corresponding conditional matrix entries. -/
theorem RecoveredConditionalDilationInternal.bipartiteBlock_ambientBipartiteBlockMatrix
    {z K dA dB : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (σ : ∀ j : Fin K, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (ω : ∀ j : Fin K,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ)
    (a a' : Fin dA) :
    bipartiteBlock (ambientBipartiteBlockMatrix eB σ ω) a a' =
      Matrix.reindex eB eB
        (Matrix.blockDiagonal' fun s => match s with
          | Sum.inl _ => 0
          | Sum.inr j => fun uv uv' =>
              σ j uv.1 uv'.1 * ω j (a, uv.2) (a', uv'.2)) := by
  apply Matrix.ext
  intro b b'
  rw [← eB.apply_symm_apply b, ← eB.apply_symm_apply b']
  generalize eB.symm b = x
  generalize eB.symm b' = y
  rcases x with ⟨s, u, v⟩
  rcases y with ⟨t, u', v'⟩
  rcases s with z | j <;> rcases t with z' | j' <;>
    simp [ambientBipartiteBlockMatrix, bipartiteBlock_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply, Matrix.kroneckerMap_apply]
  case inr.inr =>
    by_cases h : j = j'
    · subst j'
      simp
      exact Or.inl rfl
    · simp [h]

set_option linter.flexible false in
-- The four dependent-sector cases intentionally simplify to different goals.
set_option maxHeartbeats 400000 in
-- The entrywise direct-sum expansion requires a larger finite-sum reduction budget.
/-- A dependent direct sum of pure-ancilla dilation blocks acts sectorwise on
an ambient state whose complementary blocks vanish.  Supported blocks send
`σ_j ⊗ ω_j` to `ω_j ⊗ ℛ_j(σ_j)`; the factor swap is the HJPW ordering.

Only the supported Stinespring equations are assumed.  No action of the
resulting channel is asserted on a nonzero complementary input. -/
theorem RecoveredConditionalDilationInternal.blockDilation_fixedEnv_idTensorMap_blockDiagonal
    {z K dA dB dC r : ℕ} {m d : Fin K → ℕ}
    (eB : ((s : AmbientRecoveredBlockIndex z K) ×
      (Fin (ambientRecoveredCommonDim m s) ×
        Fin (ambientRecoveredConditionalDim d s))) ≃ Fin dB)
    (c₀ : Fin dC) (k₀ : Fin r)
    (L : Fin r → ∀ j : Fin K,
      Matrix (Fin (m j) × Fin dC) (Fin (m j)) ℂ)
    (Ulocal : ∀ s : AmbientRecoveredBlockIndex z K,
      Matrix
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r))
        (Fin (ambientRecoveredCommonDim m s) × (Fin dC × Fin r)) ℂ)
    (hUlocal : ∀ j,
      Matrix.reindex (Equiv.prodAssoc (Fin (m j)) (Fin dC) (Fin r))
          (Equiv.refl (Fin (m j))) (stinespringV (fun i ↦ L i j)) =
        (by simpa only [ambientRecoveredCommonDim] using Ulocal (Sum.inr j)) *
          fixedEnvEmbedding (S := Fin (m j)) (c₀, k₀))
    (σ : ∀ j : Fin K, Matrix (Fin (m j)) (Fin (m j)) ℂ)
    (ω : ∀ j : Fin K,
      Matrix (Fin dA × Fin (d j)) (Fin dA × Fin (d j)) ℂ) :
    idTensorMapLM (δ := Fin dA)
        (pureAncillaRecovery c₀ k₀ (blockDilationUnitary eB Ulocal))
        (ambientBipartiteBlockMatrix eB σ ω) =
      ambientTripartiteBlockMatrix eB ω
        (fun j => rectangularKrausMap (fun i => L i j) (σ j)) := by
  classical
  unfold ambientTripartiteBlockMatrix
  apply Matrix.ext
  rintro ⟨a, ⟨b, c⟩⟩ ⟨a', ⟨b', c'⟩⟩
  rw [← (recoveredTripartiteBlockEquiv eB).apply_symm_apply
    (a, (b, c)), ← (recoveredTripartiteBlockEquiv eB).apply_symm_apply
    (a', (b', c'))]
  generalize (recoveredTripartiteBlockEquiv eB).symm (a, (b, c)) = x
  generalize (recoveredTripartiteBlockEquiv eB).symm (a', (b', c')) = y
  rcases x with ⟨s, ⟨⟨a, v⟩, ⟨u, c⟩⟩⟩
  rcases y with ⟨t, ⟨⟨a', v'⟩, ⟨u', c'⟩⟩⟩
  simp only [recoveredTripartiteBlockEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  have hx : (recoveredTripartiteBlockEquiv eB).symm
      (a, (eB ⟨s, (u, v)⟩, c)) =
      ⟨s, ((a, v), (u, c))⟩ := by
    apply (recoveredTripartiteBlockEquiv eB).injective
    rw [(recoveredTripartiteBlockEquiv eB).apply_symm_apply]
    rfl
  have hy : (recoveredTripartiteBlockEquiv eB).symm
      (a', (eB ⟨t, (u', v')⟩, c')) =
      ⟨t, ((a', v'), (u', c'))⟩ := by
    apply (recoveredTripartiteBlockEquiv eB).injective
    rw [(recoveredTripartiteBlockEquiv eB).apply_symm_apply]
    rfl
  rw [hx, hy]
  rw [idTensorMapLM_apply, idTensorMap_apply,
    bipartiteBlock_ambientBipartiteBlockMatrix,
    pureAncillaRecovery_eq_rectangularKrausMap,
    rectangularKrausMap_apply_entry]
  rcases s with z | j <;> rcases t with z' | j'
  all_goals simp_rw [← eB.sum_comp, Fintype.sum_sigma,
    Fintype.sum_sum_type]
  all_goals simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.blockDiagonal'_apply,
    Matrix.zero_apply, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals simp
  case inl.inl | inl.inr | inr.inl =>
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    rw [blockDilationUnitary_fixedEnv_apply_complement_support]
    simp
  case inr.inr =>
    by_cases hj : j = j'
    · subst j'
      simp only [cast_eq]
      rw [rectangularKrausMap_apply_entry]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single j]
      · have hKleft
            (x : Fin (ambientRecoveredCommonDim m (Sum.inr j)) ×
              Fin (ambientRecoveredConditionalDim d (Sum.inr j))) :
            (blockDilationUnitary eB Ulocal *
                fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
                (eB ⟨Sum.inr j, (u, v)⟩, (c, i))
                (eB ⟨Sum.inr j, x⟩) =
              L i j (u, c) x.1 *
                (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v x.2 :=
          blockDilationUnitary_fixedEnv_apply_support
            eB c₀ k₀ L Ulocal hUlocal j u x.1 v x.2 c i
        have hKright
            (y : Fin (ambientRecoveredCommonDim m (Sum.inr j)) ×
              Fin (ambientRecoveredConditionalDim d (Sum.inr j))) :
            (blockDilationUnitary eB Ulocal *
                fixedEnvEmbedding (S := Fin dB) (c₀, k₀))
                (eB ⟨Sum.inr j, (u', v')⟩, (c', i))
                (eB ⟨Sum.inr j, y⟩) =
              L i j (u', c') y.1 *
                (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v' y.2 :=
          blockDilationUnitary_fixedEnv_apply_support
            eB c₀ k₀ L Ulocal hUlocal j u' y.1 v' y.2 c' i
        simp_rw [hKleft, hKright]
        have hOneLeft
            (q : Fin (ambientRecoveredConditionalDim d (Sum.inr j))) :
            (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v q =
              if v = q then 1 else 0 := by
          exact Matrix.one_apply
        have hOneRight
            (q : Fin (ambientRecoveredConditionalDim d (Sum.inr j))) :
            (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ) v' q =
              if v' = q then 1 else 0 := by
          exact Matrix.one_apply
        simp_rw [Fintype.sum_prod_type, hOneLeft, hOneRight]
        simp [apply_ite]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ac_rfl
      · intro k _ hkj
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro y _
        rw [blockDilationUnitary_fixedEnv_apply_support_ne eB c₀ k₀
          Ulocal (Ne.symm hkj)]
        simp
      · simp
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y _
      by_cases hjk : j = k
      · subst k
        rw [blockDilationUnitary_fixedEnv_apply_support_ne eB c₀ k₀
          Ulocal (Ne.symm hj)]
        simp
      · rw [blockDilationUnitary_fixedEnv_apply_support_ne eB c₀ k₀
          Ulocal hjk]
        simp


end Matrix

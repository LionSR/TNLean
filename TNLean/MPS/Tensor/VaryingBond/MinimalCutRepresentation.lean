/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.VaryingBond.MinimalCutRepresentationCuts
import TNLean.MPS.Tensor.VaryingBond.VaryingBondOBC
import TNLean.MPS.Tensor.VaryingBond.IsometricChain

/-!
# Exact open-boundary representation with minimal bonds

The matrices of coordinate slicing between successive coefficient column
spaces form an open-boundary chain. Composition of prefix evaluation maps
proves exact coefficient reconstruction. The bond dimension at every cut
is the rank of that physical coefficient flattening.

Choosing orthonormal bases of the same column spaces gives the successive Schmidt decompositions
of arXiv:quant-ph/0608197, lines 444--447: `OBCChainTensor.exists_coeff_eq_of_cutRank_le` is a
representation whose bond `k` is exactly the cut rank at `k` and in which every site except the
last satisfies `∑_i A_i^† A_i = 1` (every site, when the vector is normalized). This proves the
item "any state for which `max_m rank(ρ_m) ≤ D` can be written as a MPS of bond dimension `D`"
(lines 456--458) and, with `OBCChainTensor.cutRank_coeff_le`, the minimality of the resources in
the "recipe" of lines 1574--1577.

Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open ManyBody (interval cutMatrix cutRank RegionConfig ComplConfig)

open Matrix
open scoped BigOperators

namespace MPSPreparation

/-- The matrix of one restricted physical-coordinate slicing map in the chosen cut bases.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutSiteMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (k : ℕ) (i : Fin d) : Matrix (Fin (cutRank (interval N 0 k) ψ)) (Fin (cutRank (interval N 0
        (k + 1)) ψ)) ℂ :=
  LinearMap.toMatrix (B (k + 1)) (B k) (cutSlice ψ k i)

/-- Evaluation of a cut-space vector at the prefix of a global configuration.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def cutEvaluationMap {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ) (σ : Fin N → Fin d) (k : ℕ) :
    cutColumnSpace ψ k →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) (cutPrefixRestriction σ k)).comp (cutColumnSpace ψ k).subtype

/-- The coefficient row of prefix evaluation in the chosen cut basis.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutEvaluationMatrix {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (k : ℕ) : Matrix (Fin 1) (Fin (cutRank (interval N 0 k) ψ)) ℂ :=
  LinearMap.toMatrix (B k) (Module.Basis.singleton (Fin 1) ℂ) (cutEvaluationMap ψ σ k)

/-- A prefix evaluation coefficient is the corresponding cut-basis vector evaluated
at that prefix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_apply {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (k : ℕ) (a : Fin 1) (b : Fin (cutRank (interval N 0 k) ψ)) :
    cutEvaluationMatrix ψ B σ k a b = (B k b).val (cutPrefixRestriction σ k) := by
  rw [cutEvaluationMatrix, LinearMap.toMatrix_apply, Module.Basis.singleton_repr]
  rfl

/-- Consecutive prefix evaluations compose with physical-coordinate slicing.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMap_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (σ : Fin N → Fin d) (p : Fin N) :
    cutEvaluationMap ψ σ (p.val + 1) =
      (cutEvaluationMap ψ σ p.val).comp (cutSlice ψ p.val (σ p)) := by
  ext v
  exact (cutSlice_apply_restriction ψ σ p v).symm

/-- The matrix of prefix evaluation multiplies by the next site matrix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_step {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (σ : Fin N → Fin d) (p : Fin N) :
    cutEvaluationMatrix ψ B σ (p.val + 1) =
      cutEvaluationMatrix ψ B σ p.val * cutSiteMatrix ψ B p.val (σ p) := by
  change LinearMap.toMatrix (B (p.val + 1)) (Module.Basis.singleton (Fin 1) ℂ)
      (cutEvaluationMap ψ σ (p.val + 1)) = _
  rw [cutEvaluationMap_step]
  exact LinearMap.toMatrix_comp (B (p.val + 1)) (B p.val)
    (Module.Basis.singleton (Fin 1) ℂ) (cutEvaluationMap ψ σ p.val)
      (cutSlice ψ p.val (σ p))

/-- The square chain obtained by zero-padding the slicing matrices of a prefix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def cutPrefixChain {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (D k : ℕ) : MPSChainTensor d D k :=
  fun p i ↦ Matrix.zeroPad D (cutSiteMatrix ψ B p.val i)

/-- The padded prefix evaluation matrix is its initial matrix multiplied
by the ordered product of padded site matrices. This follows from composition
of linear maps, with no expansion over complete virtual paths.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutEvaluationMatrix_eq_initial_mul_eval {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hbound : ∀ k, k ≤ N → cutRank (interval N 0 k) ψ ≤ D) (σ : Fin N → Fin d)
    (k : ℕ) (hk : k ≤ N) :
    Matrix.zeroPad D (cutEvaluationMatrix ψ B σ k) =
      Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) *
        MPSChainTensor.eval (cutPrefixChain ψ B D k) (fun p ↦ σ (Fin.castLE hk p)) := by
  induction k with
  | zero => simp [MPSChainTensor.eval]
  | succ k ih =>
    have hk' : k ≤ N := by omega
    let p : Fin N := ⟨k, by omega⟩
    rw [MPSChainTensor.eval_succ']
    change Matrix.zeroPad D (cutEvaluationMatrix ψ B σ (k + 1)) =
      Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) *
        (MPSChainTensor.eval (cutPrefixChain ψ B D k) (fun q ↦ σ (Fin.castLE hk' q)) *
          Matrix.zeroPad D (cutSiteMatrix ψ B k (σ p)))
    have hstep := cutEvaluationMatrix_step ψ B σ p
    rw [hstep, Matrix.zeroPad_mul _ _ (hbound k hk'), ih hk', Matrix.mul_assoc]

/-- The initial evaluation row is the zero-coordinate basis vector when
the left endpoint cut basis is normalized to one.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initialCutEvaluation_row {d N D : ℕ} (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (σ : Fin N → Fin d) (hD : 0 < D) :
    (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0)) ⟨0, hD⟩ = basisVecZero hD := by
  have hentries : ∀ a b, cutEvaluationMatrix ψ B σ 0 a b = 1 := by
    intro a b
    rw [cutEvaluationMatrix_apply, hB0 b]
    rfl
  ext β
  simp [Matrix.zeroPad, (MPSPreparation.cutRank_zero_eq_one hψ), hentries, basisVecZero,
    Pi.single_apply, Fin.ext_iff]

/-- The normalized initial evaluation matrix preserves the zero-coordinate
row of every matrix.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem initialCutEvaluation_mul_apply {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (σ : Fin N → Fin d) (hD : 0 < D)
    (M : Matrix (Fin D) (Fin D) ℂ) (β : Fin D) :
    (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) * M) ⟨0, hD⟩ β = M ⟨0, hD⟩ β := by
  change (Matrix.zeroPad D (cutEvaluationMatrix ψ B σ 0) ⟨0, hD⟩) ⬝ᵥ
    (fun γ ↦ M γ β) = M ⟨0, hD⟩ β
  rw [initialCutEvaluation_row ψ hψ B hB0 σ hD]
  exact basisVecZero_dotProduct hD _

/-- The zero-coordinate entry of the padded site product equals the physical
coefficient when the two endpoint cut bases are fixed to one and to the full tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem cutPrefixChain_eval_entry {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hbound : ∀ k, k ≤ N → cutRank (interval N 0 k) ψ ≤ D) (σ : Fin N → Fin d) (hD : 0 < D) :
    MPSChainTensor.eval (cutPrefixChain ψ B D N) σ ⟨0, hD⟩ ⟨0, hD⟩ = ψ σ := by
  have hlast : Matrix.zeroPad D (cutEvaluationMatrix ψ B σ N) ⟨0, hD⟩ ⟨0, hD⟩ =
      ψ σ := by
    rw [Matrix.zeroPad_apply_of_lt _ (by simp) ((ManyBody.cutRank_pos (D := interval N 0 N) hψ))]
    rw [cutEvaluationMatrix_apply, hBN]
    exact fullCutVector_restriction ψ σ
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M ⟨0, hD⟩ ⟨0, hD⟩)
    (cutEvaluationMatrix_eq_initial_mul_eval ψ B hbound σ N (Nat.le_refl N))
  rw [hlast, initialCutEvaluation_mul_apply ψ hψ B hB0 σ hD] at h
  exact h.symm

/-- The open-boundary chain whose bond dimensions are the physical cut ranks
and whose sites are the restricted slicing maps in the chosen bases.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def minimalCutChain {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hbound : ∀ k : Fin (N + 1), cutRank (interval N 0 k.val) ψ ≤ D) : OBCChainTensor d D N where
  bondDim k := cutRank (interval N 0 k.val) ψ
  bondDim_le := hbound
  left_dim := (MPSPreparation.cutRank_zero_eq_one hψ)
  right_dim := (MPSPreparation.cutRank_self_eq_one hψ)
  tensor p i := cutSiteMatrix ψ B p.val i

/-- The chain of slicing matrices represents the full coefficient tensor exactly
when its endpoint bases are fixed to one and to that tensor.
Source: the minimal representation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem minimalCutChain_coeff {d N D : ℕ}
    (ψ : (Fin N → Fin d) → ℂ) (hψ : ψ ≠ 0)
    (B : ∀ k, Module.Basis (Fin (cutRank (interval N 0 k) ψ)) ℂ (cutColumnSpace ψ k))
    (hB0 : ∀ q, (B 0 q).val = 1) (hBN : ∀ q, (B N q).val = fullCutVector ψ)
    (hbound : ∀ k : Fin (N + 1), cutRank (interval N 0 k.val) ψ ≤ D) (σ : Fin N → Fin d) :
    (minimalCutChain ψ hψ B hbound).coeff σ = ψ σ := by
  rw [OBCChainTensor.coeff_eq_eval_zeroPad]
  change MPSChainTensor.eval (cutPrefixChain ψ B D N) σ
    ⟨0, (minimalCutChain ψ hψ B hbound).bondBound_pos⟩
    ⟨0, (minimalCutChain ψ hψ B hbound).bondBound_pos⟩ = ψ σ
  apply cutPrefixChain_eval_entry ψ hψ B hB0 hBN
  intro k hk
  exact hbound ⟨k, by omega⟩

end MPSPreparation

/-! ### Successive Schmidt decompositions -/

namespace MPSPreparation

open ManyBody (interval mem_interval)

variable {d N : ℕ} (ψ : (Fin N → Fin d) → ℂ)

/-- No site lies before the cut `0`. -/
private instance isEmpty_interval_zero : IsEmpty {v : Fin N // v ∈ interval N 0 0} :=
  ⟨fun v ↦ absurd (mem_interval.mp v.2).2 (Nat.not_lt_zero _)⟩

/-- The column space of the cut matrix at `k`, `MPSPreparation.cutColumnSpace`, read in the
Euclidean space of the left block. -/
private noncomputable def cutSpace (k : ℕ) : Submodule ℂ
    (EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k))) :=
  (cutColumnSpace ψ k).comap (WithLp.linearEquiv 2 ℂ _).toLinearMap

private theorem finrank_cutSpace (k : ℕ) :
    Module.finrank ℂ (cutSpace ψ k) = ManyBody.cutRank (interval N 0 k) ψ := by
  rw [cutSpace, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq,
    finrank_cutColumnSpace]

/-- The slicing map `MPSPreparation.cutSliceLinearMap` at the letter `i`, read in the Euclidean
spaces of the two left blocks. -/
private def sliceLast {k : ℕ} (i : Fin d) :
    EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1))) →ₗ[ℂ]
      EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ cutSliceLinearMap k i ∘ₗ
    (WithLp.linearEquiv 2 ℂ _).toLinearMap

/-- The column space at `k + 1`, restricted to a fixed last letter, lies in the column space at
`k`. -/
private theorem sliceLast_mem {k : ℕ} (i : Fin d)
    {w : EuclideanSpace ℂ (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)))}
    (hw : w ∈ cutSpace ψ (k + 1)) : sliceLast i w ∈ cutSpace ψ k :=
  cutSliceLinearMap_maps_columnSpace ψ k i ⟨_, hw, rfl⟩

/-- The orthonormal basis of the column space at `k`. -/
private noncomputable abbrev cutBasis (k : ℕ) := stdOrthonormalBasis ℂ (cutSpace ψ k)

/-- The site matrices of the successive Schmidt decompositions:
`A_k(i)_{ββ'} = ⟨e^{(k)}_β, e^{(k+1)}_{β'}(· i)⟩`. -/
private noncomputable def cutSite (k : ℕ) (i : Fin d) :
    Matrix (Fin (Module.finrank ℂ (cutSpace ψ k))) (Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
      ℂ :=
  fun β β' => inner ℂ (cutBasis ψ k β).1 (sliceLast i (cutBasis ψ (k + 1) β').1)

/-- Expansion of a basis vector at `k + 1` in the basis at `k`. -/
private theorem cutBasis_extendCutPrefix (k : ℕ) (i : Fin d)
    (β' : Fin (Module.finrank ℂ (cutSpace ψ (k + 1))))
    (σ : ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 k)) :
    (cutBasis ψ (k + 1) β').1 (extendCutPrefix k σ i) =
      ∑ β, (cutBasis ψ k β).1 σ * cutSite ψ k i β β' := by
  let x : cutSpace ψ k := ⟨sliceLast i (cutBasis ψ (k + 1) β').1,
    sliceLast_mem ψ i (cutBasis ψ (k + 1) β').2⟩
  have h := congrArg (fun w : cutSpace ψ k => w.1 σ) ((cutBasis ψ k).sum_repr' x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
  rw [WithLp.ofLp_sum, Finset.sum_apply] at h
  calc (cutBasis ψ (k + 1) β').1 (extendCutPrefix k σ i)
      = x.1 σ := rfl
    _ = _ := h.symm
    _ = _ := Finset.sum_congr rfl fun β _ => by simp [cutSite, x, mul_comm]

omit ψ in
private theorem sum_inner_sliceLast {k : ℕ} (hk : k < N)
    (a b : EuclideanSpace ℂ
      (ManyBody.RegionConfig (fun _ : Fin N ↦ Fin d) (interval N 0 (k + 1)))) :
    ∑ i, inner ℂ (sliceLast i a) (sliceLast i b) = inner ℂ a b := by
  simp only [PiLp.inner_apply]
  rw [← (extendCutPrefixEquiv hk).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The site matrices of the successive Schmidt decompositions before the last site satisfy
`∑_i A_i^† A_i = 1`. -/
private theorem sum_conjTranspose_mul_cutSite {k : ℕ} (hk : k < N) :
    ∑ i, (cutSite ψ k i)ᴴ * cutSite ψ k i = 1 := by
  ext β' β''
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hi : ∀ i, ∑ β, star (cutSite ψ k i β β') * cutSite ψ k i β β'' =
      inner ℂ (sliceLast i (cutBasis ψ (k + 1) β').1)
        (sliceLast i (cutBasis ψ (k + 1) β'').1) := by
    intro i
    let x' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β').2⟩
    let x'' : cutSpace ψ k := ⟨_, sliceLast_mem ψ i (cutBasis ψ (k + 1) β'').2⟩
    have h := (cutBasis ψ k).sum_inner_mul_inner x' x''
    rw [Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [cutSite, Submodule.coe_inner, RCLike.star_def, inner_conj_symm]
    rfl
  simp only [hi, sum_inner_sliceLast hk]
  rw [← Submodule.coe_inner, orthonormal_iff_ite.mp (cutBasis ψ (k + 1)).orthonormal,
    Matrix.one_apply]

variable {ψ}

private theorem finrank_cutSpace_zero (hψ : ψ ≠ 0) : Module.finrank ℂ (cutSpace ψ 0) = 1 :=
  (finrank_cutSpace ψ 0).trans (cutRank_zero_eq_one hψ)

/-- The value of the unit basis vector of the one-dimensional column space at the cut `0`. -/
private noncomputable def cutPhase (hψ : ψ ≠ 0) : ℂ :=
  (cutBasis ψ 0 ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩).1 default

private theorem star_cutPhase_mul_self (hψ : ψ ≠ 0) : star (cutPhase hψ) * cutPhase hψ = 1 := by
  have h := (orthonormal_iff_ite.mp (cutBasis ψ 0).orthonormal)
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
    ⟨0, by rw [finrank_cutSpace_zero hψ]; exact one_pos⟩
  simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, Fintype.sum_unique,
    RCLike.inner_apply] at h
  rw [cutPhase, mul_comm]
  exact h

/-- The open chain of the successive Schmidt decompositions of a nonzero vector, with bond `k`
the column space of the cut matrix at `k`. -/
private noncomputable def cutChain {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D) :
    OBCChainTensor d D (n + 1) where
  bondDim k := Module.finrank ℂ (cutSpace ψ k)
  bondDim_le k := (finrank_cutSpace ψ k).trans_le (hD k)
  left_dim := finrank_cutSpace_zero hψ
  right_dim := (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  tensor p i := cutSite ψ p i

/-- The prefix products of the chain of successive Schmidt decompositions are the basis vectors
of the column spaces, up to the phase at the cut `0`. -/
private theorem cutChain_prefix {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D)
    (σ : Fin (n + 1) → Fin d) :
    ∀ (k : ℕ) (hk : k ≤ n + 1) (γ : Fin D),
      (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk p)
          (σ (Fin.castLE hk p))).prod ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ =
        if h : γ.val < Module.finrank ℂ (cutSpace ψ k) then
          star (cutPhase hψ) * (cutBasis ψ k ⟨γ.val, h⟩).1 fun v => σ v.1
        else 0
  | 0, hk, γ => by
    have h1 := finrank_cutSpace_zero hψ
    rw [List.ofFn_zero, List.prod_nil]
    by_cases hγ : γ.val = 0
    · have hγ' : γ.val < Module.finrank ℂ (cutSpace ψ 0) := by omega
      rw [dite_eq_left hγ', show (⟨0, _⟩ : Fin D) = γ from Fin.ext hγ.symm, Matrix.one_apply_eq,
        ← star_cutPhase_mul_self hψ]
      congr 2
      have h0 : (⟨γ.val, hγ'⟩ : Fin (Module.finrank ℂ (cutSpace ψ 0))) = ⟨0, by omega⟩ :=
        Fin.ext hγ
      rw [h0, cutPhase]
      exact congrArg _ (Subsingleton.elim _ _)
    · rw [dite_eq_right (by omega), Matrix.one_apply_ne fun h => hγ (by rw [← h])]
  | k + 1, hk, γ' => by
    have ih := cutChain_prefix hψ hD σ k (by omega)
    rw [List.ofFn_succ', List.prod_concat, Matrix.mul_apply]
    have hσ : (fun v : {v // v ∈ interval (n + 1) 0 (k + 1)} => σ v.1) =
        extendCutPrefix k (fun v : {v // v ∈ interval (n + 1) 0 k} => σ v.1) (σ ⟨k, by omega⟩) := by
      funext v
      simp only [extendCutPrefix]
      split_ifs with h
      · rfl
      · exact congrArg σ (Fin.ext (by
          have := (mem_interval.mp v.2).2
          change v.1.val = k
          omega))
    have ih' : ∀ γ : Fin D, (List.ofFn fun p : Fin k => OBCChainTensor.zeroPad (cutChain hψ hD)
        (Fin.castLE hk p.castSucc) (σ (Fin.castLE hk p.castSucc))).prod
          ⟨0, (cutChain hψ hD).bondBound_pos⟩ γ = _ := ih
    simp only [ih']
    have hZ : ∀ x : Fin D, OBCChainTensor.zeroPad (cutChain hψ hD) (Fin.castLE hk (Fin.last k))
        (σ (Fin.castLE hk (Fin.last k))) x γ' =
          Matrix.zeroPad D (cutSite ψ k (σ ⟨k, by omega⟩)) x γ' := fun x => rfl
    simp only [hZ]
    split_ifs with hγ'
    · rw [hσ, cutBasis_extendCutPrefix, Finset.mul_sum, Fin.sum_castLE_extend_zero _
        ((finrank_cutSpace ψ k).trans_le (hD ⟨k, by omega⟩))]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rw [Matrix.zeroPad_apply_of_lt _ hx hγ', mul_assoc]
      · simp
    · refine Finset.sum_eq_zero fun x _ => ?_
      rw [Matrix.zeroPad_apply_eq_zero _ (fun h => hγ' h.2), mul_zero]

end MPSPreparation

namespace OBCChainTensor

open MPSPreparation
open ManyBody (interval mem_interval)

variable {d : ℕ}

/-- **Representation with the cut ranks as bond dimensions.** A nonzero vector on a chain of
positive length whose cut ranks are all at most `D` has an open-boundary representation with
common bound `D` whose bond `k` has dimension exactly the cut rank at `k`, and in which every
site except the last satisfies `∑_i A_i^† A_i = 1`; when the vector is normalized, the last site
satisfies it as well.

The construction is the successive Schmidt decompositions of arXiv:quant-ph/0608197,
lines 444--447, and proves the item "any state for which `max_m rank(ρ_m) ≤ D` can be written as
a MPS of bond dimension `D`" (lines 456--458); with `OBCChainTensor.cutRank_coeff_le` the bond
dimensions are the least possible at every cut simultaneously, the "minimal resources" of
lines 1574--1577. -/
theorem exists_coeff_eq_of_cutRank_le {D n : ℕ} {ψ : (Fin (n + 1) → Fin d) → ℂ} (hψ : ψ ≠ 0)
    (hD : ∀ k : Fin (n + 2), ManyBody.cutRank (interval (n + 1) 0 k) ψ ≤ D) :
    ∃ B : OBCChainTensor d D (n + 1), B.coeff = ψ ∧
      (∀ k, B.bondDim k = ManyBody.cutRank (interval (n + 1) 0 k) ψ) ∧
      (∀ p : Fin (n + 1), p ≠ Fin.last n → ∑ i, (B.tensor p i)ᴴ * B.tensor p i = 1) ∧
      (star ψ ⬝ᵥ ψ = 1 → ∑ i, (B.tensor (Fin.last n) i)ᴴ * B.tensor (Fin.last n) i = 1) := by
  classical
  -- The configurations of `n + 1` sites are the configurations of the full left block.
  let ρ : (Fin (n + 1) → Fin d) ≃
      ManyBody.RegionConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1)) :=
    { toFun := fun σ v => σ v.1
      invFun := fun x p => x ⟨p, mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : Module.finrank ℂ (cutSpace ψ (n + 1)) = 1 :=
    (finrank_cutSpace ψ (n + 1)).trans (cutRank_self_eq_one hψ)
  have h1 : 0 < Module.finrank ℂ (cutSpace ψ (n + 1)) := by omega
  let e := (cutBasis ψ (n + 1) ⟨0, h1⟩).1
  -- The coefficient of the chain of successive Schmidt decompositions.
  have hC : ∀ σ, (cutChain hψ hD).coeff σ = star (cutPhase hψ) * e (ρ σ) := fun σ => by
    have h := cutChain_prefix hψ hD σ (n + 1) le_rfl ⟨0, (cutChain hψ hD).bondBound_pos⟩
    rw [dite_eq_left h1] at h
    rw [coeff_eq_eval_zeroPad, MPSChainTensor.eval_eq_prod_ofFn]
    exact h
  -- The vector is a multiple of the unit vector spanning the column space at the cut `n + 1`.
  let τ₀ : ManyBody.ComplConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1)) :=
    fun v => absurd (mem_interval.mpr ⟨Nat.zero_le _, v.1.isLt⟩) v.2
  let ψ' : EuclideanSpace ℂ
      (ManyBody.RegionConfig (fun _ : Fin (n + 1) ↦ Fin d) (interval (n + 1) 0 (n + 1))) :=
    WithLp.toLp 2 fun σ =>
    ManyBody.cutMatrix (interval (n + 1) 0 (n + 1)) ψ σ τ₀
  have hmem : ψ' ∈ cutSpace ψ (n + 1) := Submodule.subset_span ⟨τ₀, rfl⟩
  have hρ : ∀ σ, ψ σ = ψ' (ρ σ) := fun σ => by
    change ψ σ = ψ ((ManyBody.cutEquiv _ (interval (n + 1) 0 (n + 1))).symm (ρ σ, τ₀))
    congr 1
    funext p
    exact (ManyBody.cutEquiv_symm_apply_mem (ρ σ) τ₀
      (mem_interval.mpr ⟨Nat.zero_le _, p.isLt⟩)).symm
  let c₀ : ℂ := inner ℂ e ψ'
  have hψσ : ∀ σ, ψ' σ = c₀ * e σ := fun σ => by
    have h := congrArg (fun w : cutSpace ψ (n + 1) => w.1 σ)
      ((cutBasis ψ (n + 1)).sum_repr' ⟨ψ', hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single ⟨0, h1⟩] at h
    · exact h.symm
    · intro β _ hβ
      exact absurd (Fin.ext (by have := β.isLt; omega)) hβ
    · simp
  let c : ℂ := cutPhase hψ * c₀
  refine ⟨(cutChain hψ hD).smulSite (Fin.last n) c, ?_, fun k => finrank_cutSpace ψ k,
    fun p hp => ?_, fun hn => ?_⟩
  · rw [coeff_smulSite]
    funext σ
    rw [Pi.smul_apply, hC, hρ, hψσ, smul_eq_mul]
    linear_combination (c₀ * e (ρ σ)) * star_cutPhase_mul_self hψ
  · change ∑ i, (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i)ᴴ *
      (if p = Fin.last n then c • cutSite ψ p i else cutSite ψ p i) = 1
    simp only [hp, ↓reduceIte]
    exact sum_conjTranspose_mul_cutSite ψ p.isLt
  · have he : ∑ σ, star (e (ρ σ)) * e (ρ σ) = 1 := by
      have h := (orthonormal_iff_ite.mp (cutBasis ψ (n + 1)).orthonormal) ⟨0, h1⟩ ⟨0, h1⟩
      simp only [↓reduceIte, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply] at h
      rw [← h]
      exact (ρ.sum_comp fun x => star (e x) * e x).trans
        (Finset.sum_congr rfl fun x _ => mul_comm _ _)
    have hcc : star c * c = 1 := by
      have hn' : star c₀ * c₀ = 1 := by
        rw [← hn, dotProduct]
        simp only [Pi.star_apply, hρ, hψσ, star_mul']
        rw [← mul_one (star c₀ * c₀), ← he, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
      simp only [c, star_mul']
      linear_combination (star c₀ * c₀) * star_cutPhase_mul_self hψ + hn'
    change ∑ i, (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i)ᴴ *
      (if Fin.last n = Fin.last n then c • cutSite ψ n i else cutSite ψ n i) = 1
    simp only [↓reduceIte, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← Finset.smul_sum, sum_conjTranspose_mul_cutSite ψ (Nat.lt_succ_self n)]
    rw [mul_comm, hcc, one_smul]

end OBCChainTensor

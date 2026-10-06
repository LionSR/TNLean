/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.SectorEncoder
import TNLean.MPS.Core.BlockSum

/-!
# Exact sector encoders through a fixed virtual space

The entire canonical periodic-sector encoder factors through the fixed virtual-pair
space of the unweighted direct sum. Its dimension is independent of the ring length.
This factorization keeps every logical column at once, rather than normalizing a chosen
linear combination of periodic states.

## Main results

* `MPSTensor.sectorEncoder_eq_polarIso_mul` factors the entire encoder through virtual pairs.
* `MPSTensor.injective_sectorColumnMatrix_of_isInjectiveOn` derives independence of the
  actual periodic columns from supported injectivity.
* `MPSPreparation.exists_isLocalCircuitOfDepth_sectorEncoder_exact` gives a genuine
  linear-depth physical unitary on all logical inputs simultaneously.

## References

* Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, equations (13)–(15) and discussion
  and outlook. The whole-encoder factorization is an additional coherent consequence.
-/

open Matrix MPSPreparation
open scoped BigOperators

namespace MPSTensor

variable {d D b : ℕ} {Dj : Fin b → ℕ}

/-- The blocked physical matrix with rows indexed by the original site configurations. -/
noncomputable def cfgPhysicalMatrix (A : MPSTensor d D) (N : ℕ) :
    Matrix (Cfg d N) (Fin D × Fin D) ℂ :=
  (physicalMatrix (blockTensor A N)).submatrix (decodeBlockEquiv d N).symm id

/-- In configuration coordinates the physical matrix is the product of the site tensors. -/
theorem cfgPhysicalMatrix_apply (A : MPSTensor d D) (N : ℕ) (s : Cfg d N)
    (p : Fin D × Fin D) :
    cfgPhysicalMatrix A N s p = Kraus.evalWord A (List.ofFn s) p.1 p.2 := by
  change blockTensor A N ((decodeBlockEquiv d N).symm s) p.1 p.2 = _
  rw [← MPSChainTensor.blockTensor_const, MPSChainTensor.blockTensor_decodeBlockEquiv_symm,
    MPSChainTensor.eval_const]

/-- Each virtual column selects the trace on one embedded sector. -/
noncomputable def sectorTraceSelector (ι : (j : Fin b) → Fin (Dj j) → Fin D) :
    Matrix (Fin D × Fin D) (Fin b) ℂ :=
  fun p j => ∑ a : Fin (Dj j), pairEmbedding (ι j) p (a, a)

/-- The actual periodic-sector matrix is the blocked unweighted direct sum applied to the
fixed family of virtual trace selectors. -/
theorem cfgPhysicalMatrix_mul_sectorTraceSelector
    (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a') {N : ℕ} (hN : N ≠ 0) :
    cfgPhysicalMatrix (blockSum A ι fun _ => 1) N * sectorTraceSelector ι =
      sectorColumnMatrix A N := by
  classical
  have hsector (j : Fin b) :
      physicalMatrix (blockTensor (blockSum A ι fun _ => 1) N) * pairEmbedding (ι j) =
        physicalMatrix (blockTensor (A j) N) := by
    rw [physicalMatrix_blockTensor_blockSum hι hdisj _ hN, Matrix.sum_mul]
    simp only [one_pow, one_smul, Matrix.mul_assoc]
    rw [Finset.sum_eq_single j]
    · rw [conjTranspose_pairEmbedding_mul_self (hι j), Matrix.mul_one]
    · intro i _ hij
      rw [conjTranspose_pairEmbedding_mul_eq_zero (hdisj i j hij), Matrix.mul_zero]
    · simp
  ext s j
  change (∑ p, cfgPhysicalMatrix (blockSum A ι fun _ => 1) N s p *
    ∑ a : Fin (Dj j), pairEmbedding (ι j) p (a, a)) = mpv (A j) s
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hentry (a : Fin (Dj j)) :
      (∑ p, cfgPhysicalMatrix (blockSum A ι fun _ => 1) N s p *
        pairEmbedding (ι j) p (a, a)) = cfgPhysicalMatrix (A j) N s (a, a) :=
    congrFun (congrFun (hsector j) ((decodeBlockEquiv d N).symm s)) (a, a)
  simp_rw [hentry, cfgPhysicalMatrix_apply]
  rfl

/-- A diagonal coordinate in one sector reads exactly that sector's logical coefficient. -/
theorem sectorTraceSelector_apply_diagonal
    (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a')
    (i j : Fin b) (a : Fin (Dj j)) :
    sectorTraceSelector ι (ι j a, ι j a) i = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst i
    simp [sectorTraceSelector, pairEmbedding_apply, Prod.mk.injEq, (hι j).eq_iff]
  · rw [ite_eq_right hij, sectorTraceSelector]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [pairEmbedding_apply, ite_eq_right ?_]
    intro h
    exact hdisj i j hij c a (congrArg Prod.fst h).symm

/-- The virtual trace selectors vanish outside the pairs belonging to one sector. -/
theorem sectorTraceSelector_eq_zero_of_notMem
    (ι : (j : Fin b) → Fin (Dj j) → Fin D) {p : Fin D × Fin D}
    (hp : p ∉ blockPairs ι) (j : Fin b) : sectorTraceSelector ι p j = 0 := by
  classical
  unfold sectorTraceSelector
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [pairEmbedding_apply, ite_eq_right ?_]
  intro h
  exact hp (mem_blockPairs.mpr ⟨j, a, a, h.symm⟩)

/-- Supported injectivity of the blocked direct sum already guarantees independence of
all actual periodic-sector columns, provided every sector has positive bond dimension. -/
theorem injective_sectorColumnMatrix_of_isInjectiveOn
    (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a')
    (hDj : ∀ j, 0 < Dj j) {N : ℕ} (hN : N ≠ 0)
    (hinj : IsInjectiveOn (blockTensor (blockSum A ι fun _ => 1) N)
      (blockPairs ι : Set (Fin D × Fin D))) :
    Function.Injective (sectorColumnMatrix A N).mulVec := by
  classical
  intro x y hxy
  let z := x - y
  have hv : sectorColumnMatrix A N *ᵥ z = 0 := by
    rw [show z = x - y from rfl, Matrix.mulVec_sub, hxy, sub_self]
  have hz : sectorTraceSelector ι *ᵥ z = 0 := by
    apply hinj.eq_zero_of_mulVec_eq_zero
    · intro p hp
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_eq_zero fun j _ => by
        rw [sectorTraceSelector_eq_zero_of_notMem ι hp j, zero_mul]
    · have hc : cfgPhysicalMatrix (blockSum A ι fun _ => 1) N *ᵥ
          (sectorTraceSelector ι *ᵥ z) = 0 := by
        rw [Matrix.mulVec_mulVec, cfgPhysicalMatrix_mul_sectorTraceSelector A ι hι hdisj hN]
        exact hv
      funext t
      have ht := congrFun hc (decodeBlockEquiv d N t)
      simpa only [cfgPhysicalMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, id_eq, Pi.zero_apply] using ht
  funext j
  let a : Fin (Dj j) := ⟨0, hDj j⟩
  have hj := congrFun hz (ι j a, ι j a)
  simp only [Matrix.mulVec, dotProduct, sectorTraceSelector_apply_diagonal ι hι hdisj,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Pi.zero_apply] at hj
  exact sub_eq_zero.mp hj

/-- The fixed-width virtual coefficient matrix for the complete periodic-sector family. -/
noncomputable def sectorCoefficientMatrix (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D) (N : ℕ) :
    Matrix (Fin D × Fin D) (Fin b) ℂ :=
  Matrix.polarPos (cfgPhysicalMatrix (blockSum A ι fun _ => 1) N) * sectorTraceSelector ι

/-- The canonical encoder factors exactly through a virtual-pair matrix of fixed row width
`D²`. The identity holds for all logical columns simultaneously. -/
theorem sectorEncoder_eq_polarIso_mul
    (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a') {N : ℕ} (hN : N ≠ 0) :
    sectorEncoder A N = Matrix.polarIso (cfgPhysicalMatrix (blockSum A ι fun _ => 1) N) *
      Matrix.polarIso (sectorCoefficientMatrix A ι N) := by
  let C := cfgPhysicalMatrix (blockSum A ι fun _ => 1) N
  let R := sectorCoefficientMatrix A ι N
  have hfactor : Matrix.polarIso C * R = sectorColumnMatrix A N := by
    rw [show R = Matrix.polarPos C * sectorTraceSelector ι from rfl,
      ← Matrix.mul_assoc, Matrix.polarIso_mul_polarPos]
    exact cfgPhysicalMatrix_mul_sectorTraceSelector A ι hι hdisj hN
  have hfix : (Matrix.polarIso C)ᴴ * Matrix.polarIso C * R = R := by
    rw [Matrix.conjTranspose_polarIso_mul_polarIso,
      show R = Matrix.polarPos C * sectorTraceSelector ι from rfl,
      ← Matrix.mul_assoc, Matrix.polarSupport_mul_polarPos]
  change Matrix.polarIso (sectorColumnMatrix A N) = _
  rw [← hfactor]
  exact Matrix.polarIso_mul_of_gram_eq
    (Matrix.gram_mul_eq_of_conjTranspose_mul_self_mul_eq hfix)

/-- Independent physical sector columns imply that the fixed-width virtual encoder is a
true isometry, even when the full blocked polar map is only a partial isometry. -/
theorem isIsometry_polarIso_sectorCoefficientMatrix
    (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D)
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a') {N : ℕ} (hN : N ≠ 0)
    (hinj : Function.Injective (sectorColumnMatrix A N).mulVec) :
    (Matrix.polarIso (sectorCoefficientMatrix A ι N)).IsIsometry := by
  apply Matrix.isIsometry_polarIso_of_injective
  intro x y hxy
  apply hinj
  have hfactor : Matrix.polarIso (cfgPhysicalMatrix (blockSum A ι fun _ => 1) N) *
      sectorCoefficientMatrix A ι N = sectorColumnMatrix A N := by
    rw [sectorCoefficientMatrix, ← Matrix.mul_assoc, Matrix.polarIso_mul_polarPos]
    exact cfgPhysicalMatrix_mul_sectorTraceSelector A ι hι hdisj hN
  rw [← hfactor, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

/-- The virtual polar encoder has no row outside the support of the blocked direct sum.
Only support of the actual blocked tensor is required. -/
theorem polarIso_sectorCoefficientMatrix_eq_zero_of_notMem
    (A : (j : Fin b) → MPSTensor d (Dj j))
    (ι : (j : Fin b) → Fin (Dj j) → Fin D) {N : ℕ} {S : Set (Fin D × Fin D)}
    (hinj : IsInjectiveOn (blockTensor (blockSum A ι fun _ => 1) N) S)
    {p : Fin D × Fin D} (hp : p ∉ S) (j : Fin b) :
    Matrix.polarIso (sectorCoefficientMatrix A ι N) p j = 0 := by
  classical
  let C := cfgPhysicalMatrix (blockSum A ι fun _ => 1) N
  let R := sectorCoefficientMatrix A ι N
  have hS : Matrix.polarSupport C = Matrix.diagonal fun p => if p ∈ S then 1 else 0 := by
    apply Matrix.polarSupport_eq_diagonal_of_support
    · intro s p hp
      exact hinj.1 _ p hp
    · intro x hx hzero
      apply hinj.eq_zero_of_mulVec_eq_zero hx
      funext t
      have ht := congrFun hzero (decodeBlockEquiv d N t)
      simpa only [C, cfgPhysicalMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, id_eq, Pi.zero_apply] using ht
  have hfix : Matrix.polarSupport C * R = R := by
    rw [show R = Matrix.polarPos C * sectorTraceSelector ι from rfl,
      ← Matrix.mul_assoc, Matrix.polarSupport_mul_polarPos]
  have hQ : Matrix.polarSupport C * Matrix.polarIso R = Matrix.polarIso R := by
    rw [Matrix.polarIso, ← Matrix.mul_assoc, hfix]
  have hrow := congrFun (congrFun hQ p) j
  rw [hS, Matrix.diagonal_mul, ite_eq_right hp, zero_mul] at hrow
  exact hrow.symm

/-- On one block, swapping the virtual pair orientation turns a coefficient column into the
pair vector expected by the coherent circuit. -/
theorem blockIsometryState_one_eq_polarIso_mulVec
    (A : MPSTensor d D) {N : ℕ} (hN : ∑ _ : Fin 1, N = N)
    (v : Fin D × Fin D → ℂ) :
    (fun s => blockIsometryState A (fun p => v p.swap) hN s) =
      Matrix.polarIso (cfgPhysicalMatrix A N) *ᵥ v := by
  classical
  have hsite : blockSite hN (0 : Fin 1) = id := by
    funext i
    apply Fin.ext
    simp [blockSite, blockOffset]
  have hblock (s : Cfg d N) :
      blockIndexEquiv d hN s (0 : Fin 1) = (decodeBlockEquiv d N).symm s := by
    rw [blockIndexEquiv_apply, hsite, Function.comp_id]
  funext s
  rw [blockIsometryState_apply]
  simp only [Fin.prod_univ_one, hblock, pairProductState]
  rw [cfgPhysicalMatrix, Matrix.polarIso_submatrix_equiv]
  change (∑ τ : Fin 1 → Fin (D * D),
    polarIsoMatrix (blockTensor A N) ((decodeBlockEquiv d N).symm s) (τ 0) *
      v ((finProdFinEquiv.symm (τ 0)).1, (finProdFinEquiv.symm (τ 0)).2)) = _
  rw [← (Equiv.funUnique (Fin 1) (Fin (D * D))).symm.sum_comp]
  change (∑ x : Fin (D * D),
    Matrix.polarIso (physicalMatrix (blockTensor A N)) ((decodeBlockEquiv d N).symm s)
      (virtualPairEquiv D x) * v (virtualPairEquiv D x)) = _
  exact (virtualPairEquiv D).sum_comp (fun p : Fin D × Fin D =>
    Matrix.polarIso (physicalMatrix (blockTensor A N)) ((decodeBlockEquiv d N).symm s) p * v p)

end MPSTensor

namespace MPSPreparation

open MPSTensor QuantumCircuit

variable {d D b r : ℕ} [NeZero d]

/-- One genuine nearest-neighbor unitary realizes the whole canonical sector encoder
exactly, with a depth linear in the physical ring length and a constant fixed before that
length and the tensor entries. The virtual normalization is performed in dimension `D²`.
Only pair support at the actual single block is used. -/
theorem exists_isLocalCircuitOfDepth_sectorEncoder_exact
    (hr : 2 ≤ r) {dig : Fin D → Cfg d r} (hdig : Function.Injective dig)
    {dig₀ : Fin b → Cfg d r} (hdig₀ : Function.Injective dig₀) (hD : 0 < D) :
    ∃ C : ℕ, ∀ {Dj : Fin b → ℕ} (A : (j : Fin b) → MPSTensor d (Dj j))
      (ι : (j : Fin b) → Fin (Dj j) → Fin D),
      (∀ j, Function.Injective (ι j)) →
      (∀ i j, i ≠ j → ∀ a a', ι i a ≠ ι j a') →
      (∀ j, 0 < Dj j) → ∀ (N : ℕ) [NeZero N] (hsize : 3 * r ≤ N),
      IsInjectiveOn (blockTensor (blockSum A ι fun _ => 1) N)
        (blockPairs ι : Set (Fin D × Fin D)) →
      ∃ (U : Matrix (Cfg d N) (Cfg d N) ℂ) (T : ℕ),
        IsLocalCircuitOfDepth U T ∧ T ≤ C * N ∧
        U * registerEncoder (ℓ := fun _ : Fin 1 => N) (by simp)
          (fun _ => by omega) dig₀ = sectorEncoder A N := by
  classical
  obtain ⟨C, hC⟩ := exists_isLocalCircuitOfDepth_registerCfg_of_pairProductState_supported
    hr hdig hdig₀ hD
  refine ⟨C, fun {Dj} A ι hι hdisj hDj N _ hsize hinj => ?_⟩
  let S := blockPairs ι
  have hV := injective_sectorColumnMatrix_of_isInjectiveOn A ι hι hdisj hDj (NeZero.ne N) hinj
  let Q := Matrix.polarIso (sectorCoefficientMatrix A ι N)
  let ω : Fin b → Fin D × Fin D → ℂ := fun j p => Q p.swap j
  have hQ : Q.IsIsometry :=
    isIsometry_polarIso_sectorCoefficientMatrix A ι hι hdisj (NeZero.ne N) hV
  have hω : ∀ i j, ∑ p, star (ω i p) * ω j p = if i = j then 1 else 0 := by
    intro i j
    calc
      (∑ p, star (ω i p) * ω j p) = ∑ p, star (Q p i) * Q p j :=
        (Equiv.prodComm (Fin D) (Fin D)).sum_comp (fun p => star (Q p i) * Q p j)
      _ = if i = j then 1 else 0 := by
        have h := congrFun (congrFun (show Qᴴ * Q = 1 from hQ) i) j
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  have hωS : ∀ j (c : Fin 1 → Fin D × Fin D), pairProductState (ω j) c ≠ 0 →
      ∀ k, c k ∈ S := by
    intro j c hc k
    rw [Subsingleton.elim k 0]
    by_contra hp
    apply hc
    have hz := polarIso_sectorCoefficientMatrix_eq_zero_of_notMem A ι hinj hp j
    have hrot : finRotate 1 0 = 0 := Subsingleton.elim _ _
    simpa only [ω, pairProductState, Fin.prod_univ_one, hrot, Prod.swap_prod_mk,
      Prod.mk.eta] using hz
  have hN : ∑ _ : Fin 1, N = N := by simp
  obtain ⟨U, T, hU, hT, hj⟩ := hC (blockSum A ι fun _ => 1) S ω hω
    (fun _ : Fin 1 => N) hN N hωS (fun _ => hsize) (fun _ => le_rfl) (fun _ => hinj)
  refine ⟨U, T, hU, hT, ?_⟩
  have heq := mul_registerEncoder_eq_blockIsometryEncoder hN
    (fun _ => by omega) dig₀ (blockSum A ι fun _ => 1) ω hj
  rw [heq]
  ext s j
  have hs := congrFun (blockIsometryState_one_eq_polarIso_mulVec
    (blockSum A ι fun _ => 1) hN (fun p => Q p j)) s
  change blockIsometryState (blockSum A ι fun _ => 1) (ω j) hN s = _
  rw [hs]
  change (Matrix.polarIso (cfgPhysicalMatrix (blockSum A ι fun _ => 1) N) * Q) s j = _
  exact congrFun (congrFun (sectorEncoder_eq_polarIso_mul A ι hι hdisj (NeZero.ne N)).symm s) j

end MPSPreparation

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence.Equivalence
import TNLean.MPS.MPU.Equivalence.IndexClassification
import TNLean.MPS.MPU.StandardForm.StandardFormInterpolation
import TNLean.MPS.MPU.CanonicalForm.MPUCanonicalForm
import TNLean.MPS.MPU.StandardForm.SourceFactorChoiceGates
import TNLean.MPS.MPU.Symmetry.Phases.TimeReversalSignInvariance
import TNLean.MPS.MPU.Index.Index
import TNLean.MPS.MPU.StandardForm.FundamentalTheoremGatesSupplied
import TNLean.MPS.MPU.Symmetry.Phases.ContinuousStandardFormPath

/-!
# The symmetry-preserving standard-form path criterion

Lemma `lem:equivalent-symmetry` of arXiv:1703.09188 (lines 1369--1376) states
that two MPUs described by simple tensors are strictly equivalent under a
symmetry `S` if and only if their standard-form unitaries are joined by
continuous families `u(p), v(p)` whose generated MPUs are invariant under `S`.
Strict equivalence under `S` is Definition `def:strictly-equivalent-symmetry`
(lines 1345--1354), `StrictlyEquivalentUnderSymmetry`.

This file proves the reverse direction for every blocking length `k`. The
tensors built from the gates form a continuous path of tensors on blocks of
`2k` sites. At each endpoint, the block of the given tensor and the tensor
built from its gates are standard forms with the same gates, and
interpolating their half factors joins them through tensors with the same
periodic operators (`TwoSiteStandardFormData.joinedIn_sameMPOSet_padBond`),
hence through invariant MPUs. For `k = 1`, with the lengths of `U^{(N)}`
counted on the two-spin standard-form chain
(`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`,
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`), this is the source's
reverse direction.

Conversely, a symmetric path of MPU tensors joining two simple tensors in
canonical form II, together with continuous gates for its blocks of `k`
sites whose ranks are fixed by the index, gives continuous gates for the
`k`-site blocks of the endpoints that generate MPUs invariant under the
symmetry blocked `2k` sites (`gatePath_of_symmetricPath`).

**Scope restriction (blocked symmetric path):** the proof of the forward
direction through Corollary `coruvSF` yields gates only after blocking `2k₀`
sites, `k₀ ≤ D⁴`, so the forward statement here is the blocked one; whether
the unblocked forward claim holds is open. The symmetry is imposed at positive
chain lengths. See `docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`.

## Main results

* `MPOTensor.strictlyEquivalentUnderSymmetry_reindexPhysical_of_gate_path`: the reverse
  direction for standard forms on pairs of sites, after a physical relabelling.
* `MPOTensor.strictlyEquivalentUnderSymmetry_blockTensor_of_gate_path`: the reverse
  direction after blocking `2k` sites.
* `MPOTensor.strictlyEquivalentUnderSymmetry_blockTwo_of_gate_path`: the reverse
  direction on the standard-form chain, with gates on pairs of original sites.
* `MPOTensor.gatePath_of_symmetricPath`: the forward direction from gate data along
  a symmetric path, as supplied by Corollary `coruvSF`.
* `MPOTensor.exists_gate_path_of_strictlyEquivalentUnderSymmetry`: the forward
  direction after blocking.
-/

open scoped Matrix

namespace MPOTensor

variable {d D D₁ D₂ ℓ r : ℕ}

/-- Physical relabelling depends continuously on the tensor. -/
theorem continuous_reindexPhysical {d' : ℕ} (e : Fin d' ≃ Fin d) :
    Continuous fun W : MPOTensor d D ↦ reindexPhysical e W :=
  continuous_pi fun ⟨i, j⟩ ↦ continuous_apply (e i, e j)

/-- Being an MPU and being invariant under a symmetry acting at positive lengths
depend only on the periodic operators at positive lengths. -/
theorem isMPU_and_isInvariant_of_mpo_eq {T : FiniteChainOperatorSymmetry d}
    (hpos : ∀ N ∈ T.applicable, 0 < N) {D' : ℕ} {X : MPOTensor d D} {Y : MPOTensor d D'}
    (h : ∀ N : ℕ, 0 < N → mpo X N = mpo Y N) (hY : IsMPU Y)
    (hYi : IsInvariantUnderSymmetry T Y) :
    IsMPU X ∧ IsInvariantUnderSymmetry T X := by
  refine ⟨fun N hN ↦ ?_, fun N hN ↦ ?_⟩
  · rw [h N (by omega)]
    exact hY N hN
  · rw [h N (hpos N hN)]
    exact hYi hN

/-- A path of tensors with the periodic operators of `W`, relabelled and padded,
is a path of symmetric MPU tensors when the relabelled `W` has the operators of
a symmetric MPU `Y`. -/
theorem joinedIn_symmetric_of_sameMPOSet {d' : ℕ} (e : Fin d' ≃ Fin d)
    {T : FiniteChainOperatorSymmetry d'} (hpos : ∀ N ∈ T.applicable, 0 < N)
    {D' E : ℕ} (hD : D ≤ D') {W a b : MPOTensor d D} (hab : JoinedIn (SameMPOSet W) a b)
    {Y : MPOTensor d' E} (hWY : ∀ N : ℕ, 0 < N → mpo (reindexPhysical e W) N = mpo Y N)
    (hY : IsMPU Y) (hYi : IsInvariantUnderSymmetry T Y) :
    JoinedIn {X : MPOTensor d' D' | IsMPU X ∧ IsInvariantUnderSymmetry T X}
      (reindexPhysical e (padBond a D' hD)) (reindexPhysical e (padBond b D' hD)) := by
  obtain ⟨γ, hγ⟩ := hab
  refine ⟨γ.map ((continuous_reindexPhysical e).comp (continuous_padBond D' hD)),
    fun t ↦ isMPU_and_isInvariant_of_mpo_eq hpos (fun N hN ↦ ?_) hY hYi⟩
  have : NeZero N := ⟨hN.ne'⟩
  simp only [Path.map_coe, Function.comp_apply]
  rw [mpo_reindexPhysical, mpo_padBond, hγ t N hN, ← mpo_reindexPhysical]
  exact hWY N hN

/-- **Reverse direction of the symmetry path criterion, for relabelled
standard forms.** Let `W₁, W₂` be tensors on pairs of sites with standard forms
whose gates `u(0), v(0)` and `u(1), v(1)` are joined by continuous families of
unitary gates, and relabel the physical index by `e`. If the relabelled MPU
generated by `u(p), v(p)` is invariant under `S` for every `p` and the
relabelled tensors are in canonical form, then they are strictly equivalent
under `S`.

Source: arXiv:1703.09188, Lemma `lem:equivalent-symmetry`, lines 1369--1376,
"if" direction, with Definition `def:strictly-equivalent-symmetry`
(lines 1345--1354). The symmetry is imposed at positive lengths only. -/
theorem strictlyEquivalentUnderSymmetry_reindexPhysical_of_gate_path {b d' : ℕ}
    (e : Fin d' ≃ Fin (b * b))
    {S : FiniteChainOperatorSymmetry d'} (hpos : ∀ N ∈ S.applicable, 0 < N)
    {W₁ : MPOTensor (b * b) D₁} {W₂ : MPOTensor (b * b) D₂}
    (hcf₁ : MPSTensor.IsMPUCanonicalForm (reindexPhysical e W₁).toMPSTensor)
    (hcf₂ : MPSTensor.IsMPUCanonicalForm (reindexPhysical e W₂).toMPSTensor)
    (u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin b × Fin b) ℂ)
    (v : unitInterval → Matrix (Fin b × Fin b) (Fin r × Fin ℓ) ℂ)
    (hu : Continuous u) (hv : Continuous v)
    (hu' : ∀ p, (u p).IsUnitaryBetween) (hv' : ∀ p, (v p).IsUnitaryBetween)
    (S₁ : TwoSiteStandardFormData W₁ (u 0) (v 0))
    (S₂ : TwoSiteStandardFormData W₂ (u 1) (v 1))
    (hinv : ∀ p, IsInvariantUnderSymmetry S
      (reindexPhysical e (standardFormTensorOfGates (u p) (v p)))) :
    StrictlyEquivalentUnderSymmetry S (reindexPhysical e W₁) (reindexPhysical e W₂) rfl := by
  have : NeZero b := ⟨S₁.phys_pos.ne'⟩
  have : NeZero ℓ := ⟨S₁.left_pos.ne'⟩
  have : NeZero r := ⟨S₁.right_pos.ne'⟩
  let G : unitInterval → MPOTensor (b * b) (b * r) := fun p ↦
    standardFormTensorOfGates (u p) (v p)
  let SG : ∀ p, TwoSiteStandardFormData (G p) (u p) (v p) := fun p ↦
    standardFormTensorOfGatesData _ _ (hu' p) (hv' p)
  have hGmpu : ∀ p, IsMPU (reindexPhysical e (G p)) := fun p ↦
    (isMPU_standardFormTensorOfGates _ _ (hu' p) (hv' p)).reindexPhysical e
  set D' := D₁ + b * r + D₂
  have hb₁ : D₁ + b * r ≤ D' := by omega
  have hb₂ : b * r + D₂ ≤ D' := by omega
  have hbr : b * r ≤ D' := by omega
  have hpad : ∀ {D₀ : ℕ} (W : MPOTensor (b * b) D₀) (h : D₀ ≤ D'),
      reindexPhysical e (padBond W D' h) = padBond (reindexPhysical e W) D' h :=
    fun _ _ ↦ rfl
  -- First leg: from `W₁` to the tensor of the gates at `0`.
  have hA := joinedIn_symmetric_of_sameMPOSet e hpos hb₁
    (S₁.joinedIn_sameMPOSet_padBond (SG 0)) (Y := reindexPhysical e (G 0))
    (fun N hN ↦ by
      have : NeZero N := ⟨hN.ne'⟩
      rw [mpo_reindexPhysical, mpo_padBond, S₁.mpo_eq_of_same_gates (SG 0) N hN,
        ← mpo_reindexPhysical])
    (hGmpu 0) (hinv 0)
  -- Last leg: from the tensor of the gates at `1` to `W₂`.
  have hC := joinedIn_symmetric_of_sameMPOSet e hpos hb₂
    ((SG 1).joinedIn_sameMPOSet_padBond S₂) (Y := reindexPhysical e (G 1))
    (fun N hN ↦ by
      have : NeZero N := ⟨hN.ne'⟩
      rw [mpo_reindexPhysical, mpo_padBond, ← mpo_reindexPhysical])
    (hGmpu 1) (hinv 1)
  -- Middle leg: the tensors of the gates along the path.
  have hB : JoinedIn {X : MPOTensor d' D' | IsMPU X ∧ IsInvariantUnderSymmetry S X}
      (reindexPhysical e (padBond (G 0) D' hbr)) (reindexPhysical e (padBond (G 1) D' hbr)) := by
    refine ⟨⟨⟨fun p ↦ reindexPhysical e (padBond (G p) D' hbr),
      (continuous_reindexPhysical e).comp ((continuous_padBond D' hbr).comp
        (continuous_standardFormTensorOfGates hu hv))⟩, rfl, rfl⟩, fun p ↦ ?_⟩
    refine isMPU_and_isInvariant_of_mpo_eq hpos (fun N hN ↦ ?_) (hGmpu p) (hinv p)
    have : NeZero N := ⟨hN.ne'⟩
    change mpo (reindexPhysical e (padBond (G p) D' hbr)) N = _
    rw [mpo_reindexPhysical, mpo_padBond, ← mpo_reindexPhysical]
  simp only [padBond_padBond] at hA hC
  rw [hpad] at hA
  rw [hpad W₂] at hC
  refine ⟨hcf₁, hcf₂, D', by omega, by omega, ?_⟩
  have hrefl : reindexPhysical (finCongr (rfl : d' = d')).symm
      (padBond (reindexPhysical e W₁) D' (by omega)) =
      padBond (reindexPhysical e W₁) D' (by omega) := by
    funext i j
    simp [reindexPhysical]
  rw [hrefl]
  exact hA.trans (hB.trans hC)

/-- **Reverse direction of the symmetry path criterion.** Let `𝒰₁, 𝒰₂` be
tensors in canonical form II, fix a blocking length `k`, and let
`u(p), v(p)` be continuous families of unitary gates such that `u(0), v(0)` are
standard-form gates of the two-site block of `𝒰₁` blocked `k` times, `u(1), v(1)`
those of `𝒰₂`, and the MPU generated by `u(p), v(p)` is invariant under the
symmetry `S` at every `p`. Then the blocks of `2k` sites of `𝒰₁` and `𝒰₂` are
strictly equivalent under the blocked symmetry.

For `k = 1` this is the reverse direction of Lemma `lem:equivalent-symmetry`
with lengths counted on the two-spin standard-form chain, see
`strictlyEquivalentUnderSymmetry_blockTwo_of_gate_path`.

Source: arXiv:1703.09188, Lemma `lem:equivalent-symmetry`, lines 1369--1376,
"if" direction, with Definition `def:strictly-equivalent-symmetry`
(lines 1345--1354) and the reading of standard forms in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`. The symmetry is
imposed at positive lengths only. -/
theorem strictlyEquivalentUnderSymmetry_blockTensor_of_gate_path
    {S : FiniteChainOperatorSymmetry d} (hpos : ∀ N ∈ S.applicable, 0 < N)
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂) {k : ℕ} (hk : 0 < k)
    (u : unitInterval → Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ)
    (v : unitInterval → Matrix (Fin (Kraus.blockPhysDim d k) ×
      Fin (Kraus.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ)
    (hu : Continuous u) (hv : Continuous v)
    (hu' : ∀ p, (u p).IsUnitaryBetween) (hv' : ∀ p, (v p).IsUnitaryBetween)
    (S₁ : TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₁ k)) (u 0) (v 0))
    (S₂ : TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₂ k)) (u 1) (v 1))
    (hinv : ∀ p, IsInvariantUnderSymmetry (S.block (2 * k))
      (reindexPhysical (twoSiteDirectBlockEquiv d k) (standardFormTensorOfGates (u p) (v p)))) :
    StrictlyEquivalentUnderSymmetry (S.block (2 * k))
      (blockTensor 𝒰₁ (2 * k)) (blockTensor 𝒰₂ (2 * k)) rfl := by
  have : NeZero d := h₁.neZero_phys
  have : NeZero (Kraus.blockPhysDim d (2 * k)) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (NeZero.ne d)⟩
  have hB₁ := reindexPhysical_blockTwo_blockTensor_two_mul 𝒰₁ k
  have hB₂ := reindexPhysical_blockTwo_blockTensor_two_mul 𝒰₂ k
  have h := strictlyEquivalentUnderSymmetry_reindexPhysical_of_gate_path
    (twoSiteDirectBlockEquiv d k) (fun N hN ↦ Nat.pos_of_mul_pos_right (hpos _ hN))
    (hB₁ ▸ (h₁.blockTensor (2 * k) (by omega)).isMPUCanonicalForm)
    (hB₂ ▸ (h₂.blockTensor (2 * k) (by omega)).isMPUCanonicalForm)
    u v hu hv hu' hv' S₁ S₂ hinv
  rwa [hB₁, hB₂] at h

/-- **The reverse direction of the symmetry path criterion on the standard-form
chain.** If continuous families of unitary gates join standard-form gates of
the two-site blocks of `𝒰₁` and `𝒰₂` through gates generating MPUs invariant
under `S` blocked two sites, then the two-site blocks of `𝒰₁` and `𝒰₂` are
strictly equivalent under the blocked symmetry. With the lengths of `U^{(N)}`
counted on the two-spin standard-form chain, as in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex` and
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`, this is the "if" direction
of the source lemma.

Source: arXiv:1703.09188, Lemma `lem:equivalent-symmetry`, lines 1369--1376,
"if" direction. -/
theorem strictlyEquivalentUnderSymmetry_blockTwo_of_gate_path
    {S : FiniteChainOperatorSymmetry d} (hpos : ∀ N ∈ S.applicable, 0 < N)
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : unitInterval → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : Continuous u) (hv : Continuous v)
    (hu' : ∀ p, (u p).IsUnitaryBetween) (hv' : ∀ p, (v p).IsUnitaryBetween)
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) (u 0) (v 0))
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) (u 1) (v 1))
    (hinv : ∀ p, IsInvariantUnderSymmetry (S.block 2)
      (reindexPhysical (twoSiteBlockEquiv d).symm (standardFormTensorOfGates (u p) (v p)))) :
    StrictlyEquivalentUnderSymmetry (S.block 2) (blockTensor 𝒰₁ 2) (blockTensor 𝒰₂ 2) rfl := by
  have hB : ∀ {D₀ : ℕ} (W : MPOTensor d D₀),
      reindexPhysical (twoSiteBlockEquiv d).symm (blockTwo W) = blockTensor W 2 := by
    intro D₀ W
    funext ⟨i, j⟩
    rw [blockTwo_eq_blockTensor_reindex]
    simp [reindexPhysical]
  have : NeZero d := h₁.neZero_phys
  have : NeZero (Kraus.blockPhysDim d 2) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (NeZero.ne d)⟩
  have h := strictlyEquivalentUnderSymmetry_reindexPhysical_of_gate_path
    (twoSiteBlockEquiv d).symm (fun N hN ↦ Nat.pos_of_mul_pos_right (hpos _ hN))
    ((hB 𝒰₁).symm ▸ (h₁.blockTensor 2 (by omega)).isMPUCanonicalForm)
    ((hB 𝒰₂).symm ▸ (h₂.blockTensor 2 (by omega)).isMPUCanonicalForm)
    u v hu hv hu' hv' S₁ S₂ hinv
  rwa [hB, hB] at h

/-- **Endpoint gates of the right ranks are standard-form gates of the block.**
Let `𝒰` be a simple tensor in canonical form II and `k ≥ 1`. If gates `u, v`
present the two-site block of some tensor `V` with the periodic operators of
the `k`-site block of `𝒰`, and the right rank of `u` matches the index of `𝒰`,
then `u, v` are also standard-form gates of the two-site block of the
`k`-site block of `𝒰` itself.

Source: arXiv:1703.09188, Theorem `FundamentalMPU` (lines 640--652) and the
index formula after `def:index` (lines 686--688). -/
theorem IsMPUCanonicalFormII.nonempty_twoSiteStandardFormData_blockTensor_of_index
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) (hs : IsMPUSimple U) {k : ℕ} (hk : 0 < k)
    {E : ℕ} {V : MPOTensor (Kraus.blockPhysDim d k) E}
    {u : Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : Matrix (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k))
      (Fin r × Fin ℓ) ℂ}
    (hV : ∀ N : ℕ, 0 < N → mpo V N = mpo (MPOTensor.blockTensor U k) N)
    (T : TwoSiteStandardFormData (MPOTensor.blockTwo V) u v)
    (hidx : hU.index = Real.logb 2 ((r : ℝ) / (d ^ k : ℕ))) :
    Nonempty (TwoSiteStandardFormData (MPOTensor.blockTwo (MPOTensor.blockTensor U k)) u v) := by
  have hK := hU.blockTensor k hk
  have hKs : IsMPUSimple (MPOTensor.blockTensor U k) := hs.blockTensor k hk
  let TK := hK.twoSiteStandardFormData hKs
  have : NeZero d := hU.neZero_phys
  have hdk : (0 : ℝ) < ((d ^ k : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (NeZero.pos d) k
  have hr : r = r[MPOTensor.blockTensor U k] := by
    have h := hidx.symm.trans (hU.index_eq_logb_rightRank_div hk hKs)
    have h' := Real.logb_injOn_pos (b := 2) (by norm_num)
      (div_pos (by exact_mod_cast T.right_pos) hdk)
      (div_pos (by exact_mod_cast TK.right_pos) hdk) h
    have : (r : ℝ) = r[MPOTensor.blockTensor U k] := by
      field_simp at h'
      exact h'
    exact_mod_cast this
  have hcard : ∀ {a b : ℕ} (w : Matrix (Fin a × Fin b)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ),
      w.IsUnitaryBetween → a * b =
        Kraus.blockPhysDim d k * Kraus.blockPhysDim d k := by
    intro a b w hw
    have h1 := Matrix.IsIsometry.card_le w hw.1
    have h2 := Matrix.IsCoisometry.card_le w hw.2
    simp only [Fintype.card_prod, Fintype.card_fin] at h1 h2
    omega
  have hℓ : ℓ = ℓ[MPOTensor.blockTensor U k] := by
    have h1 := hcard u T.u_unitary
    have h2 := hcard _ TK.u_unitary
    rw [hr] at h1
    exact Nat.eq_of_mul_eq_mul_right TK.right_pos (h1.trans h2.symm)
  subst hr
  subst hℓ
  obtain ⟨x, y, hu, hv⟩ := TK.exists_gate_gauges_of_mpo_eq T (fun N hN ↦
    (mpo_blockTwo_eq_of_mpo_eq hV N (by omega)).symm)
  rw [hu, hv]
  exact ⟨TK.ofGateGauges x y⟩

/-- **Forward direction of the symmetry path criterion, from gate data along a
path.** Let `𝒰₁, 𝒰₂` be simple tensors in canonical form II and `p ↦ γ(p)` a
continuous path of MPU tensors invariant under `S`, with the periodic operators
of `𝒰₁` at `0` and of `𝒰₂` at `1`. Suppose continuous gates `u(p), v(p)` on
blocks of `k` sites present, at every `p`, the two-site block of a tensor with
the operators of the `k`-site block of `γ(p)`, and that their right rank is
fixed by the index. Then `u(0), v(0)` and `u(1), v(1)` are standard-form gates
of the two-site blocks of the `k`-site blocks of `𝒰₁` and `𝒰₂`, the gates are
unitary, and the MPU generated by `u(p), v(p)` is invariant under the symmetry
blocked `2k` sites, for every `p`.

Source: arXiv:1703.09188, Lemma `lem:equivalent-symmetry`, lines 1369--1376,
"only if" direction, with the proof of Corollary `coruvSF` (lines 877--884)
supplying the gates. The symmetry is imposed at positive lengths only. -/
theorem gatePath_of_symmetricPath
    {S : FiniteChainOperatorSymmetry d} (hpos : ∀ N ∈ S.applicable, 0 < N)
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hs₁ : IsMPUSimple 𝒰₁) (hs₂ : IsMPUSimple 𝒰₂)
    {E : ℕ} {γ : unitInterval → MPOTensor d E} (hγ : Continuous γ)
    (hMPU : ∀ p, IsMPU (γ p)) (hinvγ : ∀ p, IsInvariantUnderSymmetry S (γ p))
    (hγ₀ : ∀ N : ℕ, 0 < N → mpo (γ 0) N = mpo 𝒰₁ N)
    (hγ₁ : ∀ N : ℕ, 0 < N → mpo (γ 1) N = mpo 𝒰₂ N)
    {k : ℕ} (hk : 0 < k)
    {u : unitInterval → Matrix (Fin ℓ × Fin r)
      (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ}
    {v : unitInterval → Matrix (Fin (Kraus.blockPhysDim d k) ×
      Fin (Kraus.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ}
    (hind : ∀ [NeZero d] [NeZero E], (hMPU 0).index =
      Real.logb 2 ((r : ℝ) / (Kraus.blockPhysDim d k : ℕ)))
    (hsf : ∀ p, ∃ (D' : ℕ) (V : MPOTensor (Kraus.blockPhysDim d k) D'),
      (∀ N : ℕ, 0 < N → mpo V N = mpo (blockTensor (γ p) k) N) ∧
        Nonempty (TwoSiteStandardFormData (blockTwo V) (u p) (v p))) :
    Nonempty (TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₁ k)) (u 0) (v 0)) ∧
      Nonempty (TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₂ k)) (u 1) (v 1)) ∧
      (∀ p, (u p).IsUnitaryBetween) ∧ (∀ p, (v p).IsUnitaryBetween) ∧
      ∀ p, IsInvariantUnderSymmetry (S.block (2 * k))
        (reindexPhysical (twoSiteDirectBlockEquiv d k)
          (standardFormTensorOfGates (u p) (v p))) := by
  have : NeZero d := h₁.neZero_phys
  have : NeZero E := (hMPU 0).neZero_bond
  have : NeZero (Kraus.blockPhysDim d k) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero _ (NeZero.ne d)⟩
  choose D' V hV hS using hsf
  have : NeZero ℓ := ⟨(hS 0).some.left_pos.ne'⟩
  have : NeZero r := ⟨(hS 0).some.right_pos.ne'⟩
  have hidx : (hMPU 0).index = Real.logb 2 ((r : ℝ) / (d ^ k : ℕ)) := by
    rw [hind, Kraus.blockPhysDim_eq_pow]
  -- The blocked operators of `γ` at the endpoints.
  have hblock : ∀ {D₀ : ℕ} {W : MPOTensor d D₀} (p : unitInterval),
      (∀ N : ℕ, 0 < N → mpo (γ p) N = mpo W N) →
      ∀ N : ℕ, 0 < N → mpo (V p) N = mpo (blockTensor W k) N := by
    intro D₀ W p h N hN
    rw [hV p N hN, mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex,
      h (N * k) (Nat.mul_pos hN hk)]
  refine ⟨h₁.nonempty_twoSiteStandardFormData_blockTensor_of_index hs₁ hk
      (hblock 0 hγ₀) (hS 0).some ?_,
    h₂.nonempty_twoSiteStandardFormData_blockTensor_of_index hs₂ hk
      (hblock 1 hγ₁) (hS 1).some ?_,
    fun p ↦ (hS p).some.u_unitary, fun p ↦ (hS p).some.v_unitary, fun p ↦ ?_⟩
  · rw [← (hMPU 0).index_eq_canonical_representative h₁ fun N hN ↦ (hγ₀ N hN).symm, hidx]
  · rw [← (hMPU 1).index_eq_canonical_representative h₂ fun N hN ↦ (hγ₁ N hN).symm,
      ← IsMPU.index_const_of_continuous hγ hMPU 0 1, hidx]
  · have hposB : ∀ N ∈ (S.block (2 * k)).applicable, 0 < N := fun N hN ↦
      Nat.pos_of_mul_pos_right (hpos _ hN)
    let T := (hS p).some
    let G := standardFormTensorOfGatesData (u p) (v p) T.u_unitary T.v_unitary
    refine (isMPU_and_isInvariant_of_mpo_eq hposB (fun N hN ↦ ?_)
      ((hMPU p).blockTensor (2 * k) (by omega)) ((hinvγ p).blockTensor (2 * k))).2
    rw [← reindexPhysical_blockTwo_blockTensor_two_mul, mpo_reindexPhysical,
      mpo_reindexPhysical, G.mpo_eq_of_same_gates T N hN,
      mpo_blockTwo_eq_of_mpo_eq (hV p) N hN]

/-- **Forward direction of the symmetry path criterion, after blocking.** Let
`𝒰₁, 𝒰₂` be simple tensors in canonical form II that are strictly equivalent
under a symmetry `S` imposed at positive lengths. Then for some block length
`k > 0` there are continuous families of unitary gates `u(p), v(p)` on blocks of
`k` sites such that `u(0), v(0)` and `u(1), v(1)` are standard-form gates of the
two-site blocks of the `k`-site blocks of `𝒰₁` and `𝒰₂`, and the MPU generated
by `u(p), v(p)` is invariant under `S` blocked `2k` sites for every `p`. The
printed forward direction asks for this with `k = 1`; see
`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`.

Source: arXiv:1703.09188, Lemma `lem:equivalent-symmetry`, lines 1369--1379,
"only if" direction, through Corollary `coruvSF` (lines 869--875). -/
theorem exists_gate_path_of_strictlyEquivalentUnderSymmetry
    {S : FiniteChainOperatorSymmetry d} (hpos : ∀ N ∈ S.applicable, 0 < N)
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hs₁ : IsMPUSimple 𝒰₁) (hs₂ : IsMPUSimple 𝒰₂)
    (h : StrictlyEquivalentUnderSymmetry S 𝒰₁ 𝒰₂ rfl) :
    ∃ k : ℕ, 0 < k ∧ ∃ (ℓ r : ℕ)
      (u : unitInterval → Matrix (Fin ℓ × Fin r)
        (Fin (Kraus.blockPhysDim d k) × Fin (Kraus.blockPhysDim d k)) ℂ)
      (v : unitInterval → Matrix (Fin (Kraus.blockPhysDim d k) ×
        Fin (Kraus.blockPhysDim d k)) (Fin r × Fin ℓ) ℂ),
      Continuous u ∧ Continuous v ∧
      (∀ p, (u p).IsUnitaryBetween) ∧ (∀ p, (v p).IsUnitaryBetween) ∧
      Nonempty (TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₁ k)) (u 0) (v 0)) ∧
      Nonempty (TwoSiteStandardFormData (blockTwo (blockTensor 𝒰₂ k)) (u 1) (v 1)) ∧
      ∀ p, IsInvariantUnderSymmetry (S.block (2 * k))
        (reindexPhysical (twoSiteDirectBlockEquiv d k)
          (standardFormTensorOfGates (u p) (v p))) := by
  have : NeZero d := h₁.neZero_phys
  obtain ⟨-, -, D', ha, hb, hJ⟩ := h
  let γ := hJ.somePath
  have hγmem := hJ.somePath_mem
  have hMPU : ∀ p, IsMPU (γ p) := fun p ↦ (hγmem p).1
  obtain ⟨k, hk, -, ℓ, r, u, v, hind, -, hu, hv, hsf⟩ :=
    IsMPU.exists_continuous_standardForm_of_path γ.continuous hMPU
  have hrefl : reindexPhysical (finCongr (rfl : d = d)).symm (padBond 𝒰₁ D' ha) =
      padBond 𝒰₁ D' ha := by
    funext i j
    simp [reindexPhysical]
  have hγ₀ : ∀ N : ℕ, 0 < N → mpo (γ 0) N = mpo 𝒰₁ N := fun N hN ↦ by
    have : NeZero N := ⟨hN.ne'⟩
    rw [γ.source, hrefl, mpo_padBond]
  have hγ₁ : ∀ N : ℕ, 0 < N → mpo (γ 1) N = mpo 𝒰₂ N := fun N hN ↦ by
    have : NeZero N := ⟨hN.ne'⟩
    rw [γ.target, mpo_padBond]
  obtain ⟨S₁, S₂, hu', hv', hinv⟩ := gatePath_of_symmetricPath hpos h₁ h₂ hs₁ hs₂
    γ.continuous hMPU (fun p ↦ (hγmem p).2) hγ₀ hγ₁ hk (fun {_ _} ↦ hind) hsf
  exact ⟨k, hk, ℓ, r, u, v, hu, hv, hu', hv', S₁, S₂, hinv⟩

end MPOTensor

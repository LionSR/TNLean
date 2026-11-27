/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.Blocking
import TNLean.MPS.Transfer.Irreducible.BlockingInfrastructure
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport

/-!
# Common blocked cyclic-sector families

**Auxiliary record.**  After period removal each nonzero-weight
block splits into cyclic sectors; the sectors from different blocks may
have different blocking lengths.  This file provides the common-reblocking
data that reblocks every sector to a single shared physical blocking length
so that all sectors can be compared in a uniform canonical form.

Blocking `extra` blocks of length `period` is blocking `p = period * extra` sites; the
blocked alphabets are identified by `nestedBlockEquiv`, built from
`Kraus.blockConfigEquiv`.

The structure and its derived theorems are intermediate constructions — they
record reindexing, flattening, and common-alphabet transport.  They are
not independent results of 1606.00608 or 2011.12127.
-/

open MPTensor

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPSTensor

variable {α : Type*} [Fintype α]

/-- Words of `p = m * e` letters read as `e` blocks of `m` letters. -/
noncomputable def nestedBlockEquiv (α : Type*) {p m e : ℕ} (h : p = m * e) :
    (Fin p → α) ≃ (Fin e → Fin m → α) :=
  (Equiv.arrowCongr (finCongr (h.trans (Nat.mul_comm m e))) (Equiv.refl α)).trans
    (Kraus.blockConfigEquiv α e m).symm

/-- Reading a word of `p = m * e` letters as `e` blocks of `m` letters, the iterated blocking
is the direct blocking. -/
theorem reindexPhysical_nestedBlockEquiv_block_block {D : ℕ} (A : MPTensor α (Fin D))
    {p m e : ℕ} (h : p = m * e) :
    Kraus.reindexPhysical (nestedBlockEquiv α h) (Kraus.block (Kraus.block A m) e) =
      Kraus.block A p := by
  subst h
  rw [← reindexPhysical_blockConfigEquiv_block]
  funext σ
  simp only [Kraus.reindexPhysical, nestedBlockEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply, Kraus.block_apply, Equiv.arrowCongr_apply, Equiv.refl_symm,
    Equiv.coe_refl, Function.comp_id]
  exact congrArg (Kraus.evalWord A) (List.ofFn_congr (Nat.mul_comm m e).symm _).symm

/-- **Internal record**: common reblocking data for the cyclic sectors of a finite
nonzero-weight block family.

After period removal, each original block is decomposed into cyclic sectors;
these are then reblocked so that every sector is expressed over one common
blocked physical alphabet.  The record bundles the period-removal lengths, the
additional positive blocking lengths, the primitive irreducible sector tensors,
and the MPV compatibility between the iterated block and the corresponding
unit-weight sum of reblocked cyclic sectors.

This is an auxiliary construction: the flattened common-sector family is derived
canonically from these data, and all attached theorems are properties of the
record's fields.  There is no theorem in CPSV that this record directly
instantiates; it is consumed by the normal canonical-form existence proof chain. -/
structure CommonBlockedCyclicSectorFamily {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPTensor α (Fin (dim k))) where
  /-- The common physical blocking length. -/
  p : ℕ
  /-- The common physical blocking length is positive. -/
  p_pos : 0 < p
  /-- The period-removal length of each original nonzero-weight block. -/
  period : Fin r → ℕ
  /-- Every period-removal length is positive. -/
  period_pos : ∀ k, 0 < period k
  /-- The later reblocking length applied after period removal. -/
  extra : Fin r → ℕ
  /-- Every later reblocking length is positive. -/
  extra_pos : ∀ k, 0 < extra k
  /-- The common length factors as period removal followed by later reblocking. -/
  p_eq_period_mul_extra : ∀ k, p = period k * extra k
  /-- Bond dimensions of the cyclic sector blocks before later reblocking. -/
  sectorDim : (k : Fin r) → Fin (period k) → ℕ
  /-- Cyclic sector blocks before later reblocking. -/
  sectorBlocks : (k : Fin r) → (s : Fin (period k)) →
    MPTensor (Fin (period k) → α) (Fin (sectorDim k s))
  /-- The sector blocks are trace-preserving before later reblocking. -/
  sector_tp : ∀ k s,
    ∑ i : Fin (period k) → α, (sectorBlocks k s i)ᴴ * sectorBlocks k s i = 1
  /-- Each period-blocked nonzero-weight block is represented by its unit-weight cyclic sectors. -/
  sector_same : ∀ k,
    SameMPV₂ (Kraus.block (blocks k) (period k))
      (toTensorFromBlocks (μ := fun _ : Fin (period k) => (1 : ℂ)) (sectorBlocks k))
  /-- The sector transfer maps are primitive before later reblocking. -/
  sector_primitive : ∀ k s, _root_.IsPrimitive (Kraus.transferMap (sectorBlocks k s))
  /-- The sector blocks are tensor-irreducible before later reblocking. -/
  sector_irreducible : ∀ k s, Kraus.IsIrreducibleFamily (sectorBlocks k s)
  /-- The sector bond dimensions are positive before later reblocking. -/
  sector_dim_pos : ∀ k s, 0 < sectorDim k s

namespace CommonBlockedCyclicSectorFamily

variable {r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPTensor α (Fin (dim k))}

/-- Decode a flattened common-sector index as an original block and a cyclic sector. -/
noncomputable def flatKey (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) : (k : Fin r) × Fin (F.period k) :=
  finSigmaFinEquiv.symm x

/-- The common-alphabet sector obtained by later reblocking one cyclic sector. -/
noncomputable def commonSectorBlock (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    MPTensor (Fin F.p → α) (Fin (F.sectorDim k s)) :=
  Kraus.reindexPhysical (nestedBlockEquiv α (F.p_eq_period_mul_extra k))
    (Kraus.block (F.sectorBlocks k s) (F.extra k))

/-- Bond dimensions of the derived flattened common-sector family. -/
noncomputable def commonFlatDim (F : CommonBlockedCyclicSectorFamily blocks) :
    Fin (∑ k : Fin r, F.period k) → ℕ :=
  fun x =>
    let y := F.flatKey x
    F.sectorDim y.1 y.2

/-- The derived flattened common-sector family, indexed by `Fin (∑ k, F.period k)`. -/
noncomputable def commonFlatBlocks (F : CommonBlockedCyclicSectorFamily blocks)
    (x : Fin (∑ k : Fin r, F.period k)) :
    MPTensor (Fin F.p → α) (Fin (F.commonFlatDim x)) :=
  let y := F.flatKey x
  show MPTensor (Fin F.p → α) (Fin (F.sectorDim y.1 y.2)) from
    F.commonSectorBlock y.1 y.2

/-- The common-alphabet sector tensor for one original nonzero-weight block. -/
noncomputable def commonSectorTensor (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) : MPTensor (Fin F.p → α) (Fin (∑ s : Fin (F.period k), F.sectorDim k s)) :=
  toTensorFromBlocks (μ := fun _ : Fin (F.period k) => (1 : ℂ))
    (fun s => F.commonSectorBlock k s)

/-- The derived flattened sector weights obtained from the original nonzero weights after
blocking by the common length. -/
noncomputable def commonFlatWeight (F : CommonBlockedCyclicSectorFamily blocks)
    (μ : Fin r → ℂ) : Fin (∑ k : Fin r, F.period k) → ℂ :=
  fun x => (μ (F.flatKey x).1) ^ F.p

/-- Each sector tensor in the common reblocked cyclic-sector family is trace-preserving,
has primitive transfer map, is tensor-irreducible, and has positive bond dimension. -/
theorem derived_properties (F : CommonBlockedCyclicSectorFamily blocks)
    (k : Fin r) (s : Fin (F.period k)) :
    (∑ i : Fin F.p → α, (F.commonSectorBlock k s i)ᴴ * F.commonSectorBlock k s i = 1) ∧
    _root_.IsPrimitive (Kraus.transferMap (F.commonSectorBlock k s)) ∧
    Kraus.IsIrreducibleFamily (F.commonSectorBlock k s) ∧
    0 < F.sectorDim k s := by
  have : NeZero (F.sectorDim k s) := ⟨Nat.ne_of_gt (F.sector_dim_pos k s)⟩
  obtain ⟨hTP, hPrim, hIrr⟩ := Kraus.tp_primitive_irreducible_extra_blocking
    (F.sectorBlocks k s) (F.sector_tp k s) (F.sector_primitive k s)
    (F.sector_irreducible k s) (F.extra_pos k)
  exact ⟨(Kraus.isTP_reindexPhysical_iff _ _).2 hTP,
    (isPrimitive_transferMap_reindexPhysical_equiv _ _).2 hPrim,
    (Kraus.isIrreducibleFamily_reindexPhysical_equiv _ _).2 hIrr, F.sector_dim_pos k s⟩

/-- The direct `p`-blocked tensor of one original block is represented by its common-alphabet
cyclic sectors. -/
private theorem block_sameMPV₂_commonSectorTensor
    (F : CommonBlockedCyclicSectorFamily blocks) (k : Fin r) :
    SameMPV₂ (Kraus.block (blocks k) F.p) (F.commonSectorTensor k) := by
  intro N σ
  have h := sameMPV₂_block_of_sameMPV₂_toTensorFromBlocks _ _ _ (F.sector_same k) (F.extra k)
    N (fun n => nestedBlockEquiv α (F.p_eq_period_mul_extra k) (σ n))
  rw [← reindexPhysical_nestedBlockEquiv_block_block (blocks k) (F.p_eq_period_mul_extra k)]
  simpa only [MPTensor.mpv_reindexPhysical, one_pow, commonSectorTensor, commonSectorBlock,
    mpv_toTensorFromBlocks_eq_sum] using h

/-- The nonzero-part decomposition of a weighted block sum $\bigoplus_k \mu_k B_k$
transports through the common-alphabet identification: the common-alphabet sectors
have the same nonzero-part decomposition as the direct $p$-blocked tensors. After
blocking by length $p$, the per-block scalar weights $\mu_k$ become $\mu_k^{p}$ since
each $B_k^{[p]}$ is a $p$-fold matrix product. -/
theorem reindexed_nonzero_part (F : CommonBlockedCyclicSectorFamily blocks) (μ : Fin r → ℂ) :
    SameMPV₂
      (toTensorFromBlocks (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => Kraus.block (blocks k) F.p))
      (toTensorFromBlocks (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) := by
  intro N σ
  let gSigma : ((k : Fin r) × Fin (F.period k)) → ℂ := fun y =>
    ((μ y.1) ^ F.p) ^ N * mpv (F.commonSectorBlock y.1 y.2) σ
  calc
    mpv (toTensorFromBlocks (μ := fun k : Fin r => (μ k) ^ F.p)
        (fun k => Kraus.block (blocks k) F.p)) σ
        = ∑ k : Fin r, ((μ k) ^ F.p) ^ N • mpv (Kraus.block (blocks k) F.p) σ :=
          mpv_toTensorFromBlocks_eq_sum _ _ σ
    _ = ∑ k : Fin r, ((μ k) ^ F.p) ^ N • mpv (F.commonSectorTensor k) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [F.block_sameMPV₂_commonSectorTensor k N σ]
    _ = ∑ k : Fin r, ∑ s : Fin (F.period k),
          ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [commonSectorTensor, mpv_toTensorFromBlocks_eq_sum]
          simp [smul_eq_mul, Finset.mul_sum]
    _ = ∑ y : ((k : Fin r) × Fin (F.period k)),
          ((μ y.1) ^ F.p) ^ N • mpv (F.commonSectorBlock y.1 y.2) σ :=
          (Fintype.sum_sigma'
            (fun k s => ((μ k) ^ F.p) ^ N • mpv (F.commonSectorBlock k s) σ)).symm
    _ = ∑ x : Fin (∑ k : Fin r, F.period k),
          (F.commonFlatWeight μ x) ^ N • mpv (F.commonFlatBlocks x) σ := by
          have h := (Equiv.sum_comp
            (finSigmaFinEquiv.symm :
              Fin (∑ k : Fin r, F.period k) ≃ ((k : Fin r) × Fin (F.period k)))
            gSigma).symm
          simp only [gSigma, commonFlatWeight, commonFlatBlocks, commonFlatDim, flatKey,
            smul_eq_mul] at h ⊢
          exact h
    _ = mpv (toTensorFromBlocks (μ := F.commonFlatWeight μ) (F.commonFlatBlocks)) σ :=
          (mpv_toTensorFromBlocks_eq_sum (F.commonFlatWeight μ) (F.commonFlatBlocks) σ).symm

end CommonBlockedCyclicSectorFamily

end MPSTensor

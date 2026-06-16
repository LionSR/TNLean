import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Core.Blocking

/-!
# MPS Symmetry Primitives

This module defines the symmetry-twisted tensor construction and proves its
functoriality, establishing the algebraic foundations for on-site symmetric MPS.

For an injective MPS tensor, on-site symmetry under a group representation
implies that each twisted tensor has the same matrix-product-vector family as
the original.  The single-block Fundamental Theorem then converts equality of
MPV families into a virtual gauge.

## Main definitions

* `MPSTensor.twistedTensor` : twist an MPS tensor by a group representation on the physical index
* `MPSTensor.IsOnSiteSymmetric` : predicate for on-site symmetry under a representation
* `MPSTensor.blockKronAction` : the on-site representation lifted to the blocked
  physical space by the Kronecker power of each group element's physical action

## Main results

* `MPSTensor.twistedTensor_one` : twisting by the identity is trivial
* `MPSTensor.twistedTensor_mul` : twisting is functorial (composition law)
* `MPSTensor.gaugeEquiv_twistedTensor_of_injective` :
  injective symmetric tensors have gauge-equivalent twists
* `MPSTensor.twistedTensor_blockTensor_comm` : twisting by `blockKronAction`
  commutes with physical blocking
* `MPSTensor.isOnSiteSymmetric_blockTensor` : on-site symmetry transfers to the
  blocked tensor under the Kronecker-power action

## References

* Pérez-García et al., *Matrix Product State Representations*, arXiv:0608197
* Pérez-García et al., *String order and symmetries in quantum spin lattices*,
  arXiv:0802.0447
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {G : Type*} [Monoid G] {d D : ℕ}

/-- Tensor twisted by physical action of `g ∈ G`.

If `U : G →* Matrix (Fin d) (Fin d) ℂ` is an on-site representation, then
`twistedTensor A U g` has components
`(twistedTensor A U g) i = ∑ j, U g i j • A j`. -/
noncomputable def twistedTensor (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) : MPSTensor d D :=
  fun i => ∑ j : Fin d, U g i j • A j

/-- `A` is on-site symmetric under `U` if each group twist has the same MPV as `A`. -/
def IsOnSiteSymmetric (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ g : G, SameMPV A (twistedTensor A U g)

/-- Twisting by the identity group element is trivial. -/
@[simp] lemma twistedTensor_one (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    twistedTensor A U 1 = A := by
  funext i
  simp [twistedTensor, Matrix.one_apply]

/-- Functoriality/composition law for twists:

twisting by `g * h` is the same as first twisting by `h` and then by `g`. -/
lemma twistedTensor_mul (A : MPSTensor d D)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g h : G) :
    twistedTensor A U (g * h) = twistedTensor (twistedTensor A U h) U g := by
  funext i
  calc
    twistedTensor A U (g * h) i
        = ∑ k : Fin d, (∑ j : Fin d, U g i j * U h j k) • A k := by
            simp [twistedTensor, Matrix.mul_apply]
    _ = ∑ k : Fin d, ∑ j : Fin d, (U g i j * U h j k) • A k := by
          simp_rw [Finset.sum_smul]
    _ = ∑ j : Fin d, ∑ k : Fin d, (U g i j * U h j k) • A k := Finset.sum_comm
    _ = twistedTensor (twistedTensor A U h) U g i := by
          simp [twistedTensor, Finset.smul_sum, smul_smul]

/-- If `A` is injective and on-site symmetric under `U`, then each twisted tensor is
gauge equivalent to `A`.

On-site symmetry supplies `SameMPV A (twistedTensor A U g)`, and
`sameMPV_iff_gaugeEquiv_of_injective` converts equal MPV families into
gauge equivalence for injective tensors. -/
theorem gaugeEquiv_twistedTensor_of_injective
    (A : MPSTensor d D) (hA : IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∀ g : G, GaugeEquiv A (twistedTensor A U g) := by
  intro g
  exact (sameMPV_iff_gaugeEquiv_of_injective hA).1 (hSymm g)

/-! ### The Kronecker-power physical action through blocking

For a physical-index operator, the blocked operator `blockKron` acts on the
blocked physical index by the entrywise product over the decoded sites.  The
following definitions and lemmas package this lift as a group action and show
that twisting by it commutes with physical blocking. -/

/-- The on-site representation lifted to the blocked physical space by the
Kronecker power of each group element's physical action. -/
noncomputable def blockKronAction (L : ℕ)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    G →* Matrix (Fin (blockPhysDim d L)) (Fin (blockPhysDim d L)) ℂ where
  toFun g := blockKron L (U g)
  map_one' := by rw [map_one, blockKron_one]
  map_mul' g h := by rw [map_mul, blockKron_mul]

@[simp] lemma blockKronAction_apply (L : ℕ)
    (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    blockKronAction L U g = blockKron L (U g) := rfl

/-- Word evaluation of a twisted tensor expands over the intermediate word: for a
length-`L` index function `b`,
`evalWord (twistedTensor A U g) (List.ofFn b) =
  ∑ v, (∏ k, (U g) (b k) (v k)) • evalWord A (List.ofFn v)`. -/
lemma evalWord_twistedTensor_ofFn
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) :
    ∀ {L : ℕ} (b : Fin L → Fin d),
      evalWord (twistedTensor A U g) (List.ofFn b) =
        ∑ v : Fin L → Fin d,
          (∏ k : Fin L, (U g) (b k) (v k)) • evalWord A (List.ofFn v) := by
  classical
  intro L
  induction L with
  | zero =>
    intro b
    simp only [List.ofFn_zero, evalWord_nil]
    rw [Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
  | succ L ih =>
    intro b
    rw [List.ofFn_succ, evalWord_cons, twistedTensor, ih (fun i => b i.succ)]
    -- Head sum times tail sum; distribute and reindex over `Fin.cons`.
    rw [Finset.sum_mul]
    -- Reindex the sum over `Fin (L+1) → Fin d` via `Fin.consEquiv`.
    rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => Fin d)).sum_comp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    -- Evaluate the consed word and the product over `Fin (L+1)`.
    have heval : evalWord A (List.ofFn ((Fin.consEquiv fun _ : Fin (L + 1) => Fin d) (a, w)))
        = A a * evalWord A (List.ofFn w) := by
      simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, evalWord_cons,
        Fin.cons_succ]
    rw [heval]
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ,
      Matrix.mul_smul, smul_smul]

/-- Twisting by `blockKronAction` agrees with blocking the twisted tensor:
`twistedTensor (blockTensor A L) (blockKronAction L U) g = blockTensor
(twistedTensor A U g) L`. -/
lemma twistedTensor_blockTensor_comm
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (g : G) (L : ℕ) :
    twistedTensor (blockTensor A L) (blockKronAction L U) g =
      blockTensor (twistedTensor A U g) L := by
  classical
  funext I
  rw [twistedTensor]
  simp only [blockKronAction_apply, blockKron, blockTensor, wordOfBlock]
  rw [evalWord_twistedTensor_ofFn A U g (decodeBlock d L I)]
  -- Reindex the sum over words by the blocked index.
  rw [← (decodeBlockEquiv d L).sum_comp]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  simp [decodeBlockEquiv_apply]

/-- On-site symmetry transfers to the blocked tensor under the Kronecker-power
action: if `A` is on-site symmetric under `U`, then `blockTensor A L` is on-site
symmetric under `blockKronAction L U`.  Blocking preserves the underlying matrix
product vector family, so no injectivity of `A` is needed. -/
theorem isOnSiteSymmetric_blockTensor
    (A : MPSTensor d D) (U : G →* Matrix (Fin d) (Fin d) ℂ) (L : ℕ)
    (hSymm : IsOnSiteSymmetric A U) :
    IsOnSiteSymmetric (blockTensor A L) (blockKronAction L U) := by
  intro g
  rw [twistedTensor_blockTensor_comm]
  exact (hSymm g).blockTensor L

end MPSTensor

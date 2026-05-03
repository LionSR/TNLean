/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.BNT.Basic
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Vertical canonical form for MPO tensors

This file introduces a block-decomposed version of the vertical canonical-form
structure used in the MPDO analysis of arXiv:1606.00608, Section 4.4.

The paper's Proposition IV.12 writes the tensor, after a local isometry on the
physical indices, as a direct sum
`⊕_α μ_α ⊗ M_α`, where the `μ_α` are positive diagonal matrices and the
`M_α` form a basis of normal tensors (BNT). The current repository formalization
uses canonical-form and BNT data with scalar block weights. We therefore
encode the paper's diagonal matrices by **flattening** each diagonal entry of
`μ_α` into a repeated positive scalar weight attached to the same block `M_α`.

The resulting predicate `IsVerticalCF` should be read as a repository-friendly
surrogate for the paper's vertical canonical form.

## Main definitions

* `diagonalTensor`:
  the MPS tensor `i ↦ M i i` extracted from the diagonal MPO entries.
* `verticalTransferMap`:
  the transfer map of `diagonalTensor`, i.e. `E_vert(X) = Σ_i M^{ii} X (M^{ii})†`.
* `HorizontalCFData` / `IsHorizontalCF`:
  lightweight horizontal canonical-form data for an MPO, expressed via the
  doubled-index MPS tensor `M.toMPSTensor`.
* `IsVerticalCF`:
  a flattened positive-weight BNT decomposition for `diagonalTensor M`.
* `blockwise_insert_eq_of_mpv_agree`:
  Lemma L from the paper's appendix, proved here using the block-injective
  canonical-form (biCF) field of `HorizontalCFData`.

The full Proposition IV.12 / Proposition 4.13 bridge from horizontal to vertical
canonical form is deferred to a follow-up PR: its blueprint entry
`thm:vertical_cf_of_horizontal_cf` is marked `\notready`, and the corresponding
Lean statement will be introduced together with its proof rather than as an
empty placeholder.

## Module location

The MPO/MPDO/LPDO foundations introduced by issue #235 live under `TNLean/MPS/MPDO/`
(imported as layer 3b in `TNLean.lean`) rather than as a top-level `TNLean/MPDO/`
namespace: they sit on top of the `MPSTensor` framework from `TNLean/MPS/`, so
the MPS-scoped location matches the existing layering.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Proposition IV.12 and the auxiliary Lemma L in the appendix
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A "first-site insertion" on an MPS tensor. The resulting local tensor is the
one obtained by contracting the physical index with `Y` at a single site. -/
noncomputable def insertedTensor
    (Y : Matrix (Fin d) (Fin d) ℂ) (A : MPSTensor d D) : MPSTensor d D :=
  fun i => ∑ j : Fin d, Y i j • A j

/-- Coefficient-level formulation of "acting with `Y` on the first spin" of an
MPV. This is the hypothesis used in the paper's Lemma L. -/
def FirstSiteActionAgree (A : MPSTensor d D)
    (Y Z : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (N : ℕ) (σ : Fin (N + 1) → Fin d),
    ∑ i : Fin d, Y (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ)) =
      ∑ i : Fin d, Z (σ 0) i * MPSTensor.mpv A (Fin.cons i (σ ∘ Fin.succ))

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- The diagonal MPS tensor extracted from an MPO by restricting to equal ket
and bra indices. This is the tensor whose transfer map is the "vertical"
transfer map used in the MPDO vertical-canonical-form discussion. -/
def diagonalTensor (M : MPOTensor d D) : MPSTensor d D :=
  fun i => M i i

@[simp] lemma diagonalTensor_apply (M : MPOTensor d D) (i : Fin d) :
    diagonalTensor M i = M i i :=
  rfl

/-- The vertical transfer map of an MPO tensor:
`E_vert(X) = Σ_i M^{ii} X (M^{ii})†`. -/
noncomputable def verticalTransferMap (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  MPSTensor.transferMap (diagonalTensor M)

lemma verticalTransferMap_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    verticalTransferMap M X = ∑ i : Fin d, M i i * X * (M i i)ᴴ := by
  simp [verticalTransferMap, diagonalTensor, MPSTensor.transferMap_apply]

/-- Lightweight horizontal canonical-form data for a family of blocks.

This is the fragment of the full canonical-form data needed for the MPDO
vertical-canonical-form interface in this file: injective blocks, the
left-canonical normalization, nonzero block weights, and block-injective
canonical form (biCF). -/
structure HorizontalCFData {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) : Prop where
  /-- Each block is algebraically injective. -/
  block_injective : ∀ k, MPSTensor.IsInjective (A k)
  /-- Each block is left-canonical. -/
  left_canonical : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1
  /-- No block weight vanishes. -/
  weight_ne_zero : ∀ k, μ k ≠ 0
  /-- **Block-injective canonical form** (biCF): there is a blocking length `L`
  such that the trace pairing against length-`L` block products is faithful
  across all blocks simultaneously. Concretely, if a tuple of block matrices
  `Δ k : Matrix (Fin (dim k)) (Fin (dim k)) ℂ` pairs to zero against every
  length-`L` block-diagonal product, then each `Δ k` vanishes individually.

  This is the block-decomposed surrogate for [Cirac--Perez-Garcia--Schuch--Verstraete 2017], Proposition IV.3
  (arXiv:1606.00608, "`propblockinj`"): after blocking at most `3 D^5` spins,
  where `D` denotes the bond dimension in the paper (in this block-decomposed
  setting one may take `D` to be a global bound such as `⨆ k, dim k`),
  any tensor in CF is in biCF, which is what the paper's Lemma L invokes to
  separate blockwise contributions.

  *Current repository status.* `TNLean/MPS/MPDO/BiCFDerivation.lean` now provides
  several exact routes to this field: from a full finite-length tuple-span
  witness (`WordTupleSpanTop`), from the abstract selector data
  (`PropBlockInjective`), and from the more concrete linear-independence criterion
  `wordEntryFamily`. What is still open is to derive one of those finite-length
  witnesses from the remaining canonical-form/BNT data alone, i.e. the actual
  Proposition IV.3 theorem from [Cirac--Perez-Garcia--Schuch--Verstraete 2017]. -/
  biCF : ∃ L : ℕ, ∀ (Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
    (∀ w : Fin L → Fin d,
        (∑ k : Fin r, Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w))) = 0) →
    ∀ k, Δ k = 0

/-- Horizontal canonical form for an MPO tensor, expressed via a canonical-form
decomposition of the doubled-index MPS tensor `M.toMPSTensor`. -/
def IsHorizontalCF (M : MPOTensor d D) : Prop :=
  ∃ (r : ℕ) (dim : Fin r → ℕ) (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor (d * d) (dim k)),
    HorizontalCFData (d := d * d) μ A ∧
      MPSTensor.SameMPV₂ M.toMPSTensor
        (MPSTensor.toTensorFromBlocks (d := d * d) (μ := μ) A)

/-- The multiplicity-expanded block dimensions corresponding to a family of
positive diagonal weights. -/
def verticalCopyDim {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ) :
    Fin (∑ α : Fin g, mult α) → ℕ :=
  fun q => dim ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded block family obtained by repeating the same BNT
block across all diagonal entries of its positive weight matrix. -/
def verticalCopyBlocks {g : ℕ} (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    (q : Fin (∑ α : Fin g, mult α)) → MPSTensor d (verticalCopyDim dim mult q) :=
  fun q => A ((finSigmaFinEquiv.symm q).1)

/-- The multiplicity-expanded scalar weights obtained by flattening the
positive diagonal matrices from the paper's vertical decomposition. -/
def verticalCopyWeights {g : ℕ} (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ) :
    Fin (∑ α : Fin g, mult α) → ℂ :=
  fun q =>
    let p := finSigmaFinEquiv.symm q
    ω p.1 p.2

/-- The flattened repeated tensor corresponding to the paper's
`⊕_α μ_α ⊗ M_α` block structure. -/
noncomputable def verticalAssembledTensor {g : ℕ}
    (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)) :
    MPSTensor d (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) :=
  MPSTensor.toTensorFromBlocks
    (μ := verticalCopyWeights mult ω)
    (A := verticalCopyBlocks dim mult A)

/-- A Lean-friendly version of the paper's vertical canonical form:

there is a basis of normal tensors `A α`, together with positive scalar weights
obtained by flattening the positive diagonal matrices `μ_α`, such that the
diagonal MPO tensor `diagonalTensor M` generates the same MPV family as the
flattened repeated tensor built from those blocks. -/
def IsVerticalCF (M : MPOTensor d D) : Prop :=
  ∃ (g : ℕ) (dim : Fin g → ℕ) (mult : Fin g → ℕ)
    (ω : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor d (dim α)),
    (∀ α q, (0 : ℂ) < ω α q) ∧
      MPSTensor.IsBNT (verticalAssembledTensor dim mult ω A) g dim A ∧
      MPSTensor.SameMPV₂ (diagonalTensor M) (verticalAssembledTensor dim mult ω A)

/-- **Lemma L** (arXiv:1606.00608, appendix): if two operators act identically
on the first site of every MPV generated by a canonical-form tensor, then their
insertions agree blockwise.

This is the precise blockwise statement needed in the proof of Proposition
IV.12. The intended proof follows the paper: use block separation for the
canonical-form decomposition together with the nonvanishing of the Newton-Girard
sums of the block weights. -/
theorem blockwise_insert_eq_of_mpv_agree
    {r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : HorizontalCFData (d := d) μ A)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hAct :
      MPSTensor.FirstSiteActionAgree
        (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A) Y Z) :
    ∀ k, MPSTensor.insertedTensor Y (A k) = MPSTensor.insertedTensor Z (A k) := by
  -- Obtain the biCF blocking length `L`.
  obtain ⟨L, hL⟩ := hCF.biCF
  intro k₀
  funext s
  -- Candidate witness for biCF: the blockwise difference weighted by `(μ k)^(L+1)`.
  set Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ := fun k =>
    (μ k) ^ (L + 1) • (MPSTensor.insertedTensor Y (A k) s -
      MPSTensor.insertedTensor Z (A k) s)
  -- Show that `Δ` pairs to zero against every length-`L` block word, so biCF forces `Δ = 0`.
  have hΔzero : ∀ k, Δ k = 0 := by
    refine hL Δ (fun w => ?_)
    -- Specialize `hAct` at `σ := Fin.cons s w` (which has length `L + 1`).
    have hA := hAct L (Fin.cons s w)
    -- Simplify `σ 0 = s` and `Fin.cons i (σ ∘ Fin.succ) = Fin.cons i w`.
    have hsimp : ∀ i : Fin d,
        (Fin.cons i ((Fin.cons s w : Fin (L + 1) → Fin d) ∘ Fin.succ) :
            Fin (L + 1) → Fin d) = Fin.cons i w :=
      fun i => by simp [Function.comp_def, Fin.cons_succ]
    simp only [Fin.cons_zero, hsimp] at hA
    -- Rewriter: for any `W`, expand the MPV pairing on the LHS of `hA` into a
    -- blockwise trace pairing against `insertedTensor W (A k) s`.
    have htrans : ∀ W : Matrix (Fin d) (Fin d) ℂ,
        ∑ i : Fin d, W s i *
            MPSTensor.mpv
              (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A)
              (Fin.cons i w : Fin (L + 1) → Fin d) =
          ∑ k : Fin r, Matrix.trace
            ((μ k) ^ (L + 1) • MPSTensor.insertedTensor W (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) := by
      intro W
      -- Expand the assembled-tensor MPV block-by-block and fold
      -- `mpv (A k) (Fin.cons i w)` into `trace (A k i * evalWord (A k) (List.ofFn w))`.
      have hExp : ∀ i : Fin d,
          MPSTensor.mpv
              (MPSTensor.toTensorFromBlocks (d := d) (μ := μ) A)
              (Fin.cons i w : Fin (L + 1) → Fin d) =
            ∑ k : Fin r, (μ k) ^ (L + 1) *
              Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)) := by
        intro i
        rw [MPSTensor.mpv_toTensorFromBlocks_eq_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hof : List.ofFn (Fin.cons i w : Fin (L + 1) → Fin d)
            = i :: List.ofFn w := by
          simp [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
        simp only [smul_eq_mul, MPSTensor.mpv, MPSTensor.coeff, hof,
          MPSTensor.evalWord_cons]
      simp_rw [hExp, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      calc ∑ i : Fin d, W s i *
                ((μ k) ^ (L + 1) *
                  Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)))
            = (μ k) ^ (L + 1) * ∑ i : Fin d, W s i *
                Matrix.trace (A k i * MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by ring
        _   = (μ k) ^ (L + 1) * ∑ i : Fin d, Matrix.trace
                ((W s i • A k i) * MPSTensor.evalWord (A k) (List.ofFn w)) := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                (∑ i : Fin d, (W s i • A k i) *
                    MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Matrix.trace_sum]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                ((∑ i : Fin d, W s i • A k i) *
                  MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Finset.sum_mul]
        _   = (μ k) ^ (L + 1) * Matrix.trace
                (MPSTensor.insertedTensor W (A k) s *
                  MPSTensor.evalWord (A k) (List.ofFn w)) := rfl
        _   = Matrix.trace ((μ k) ^ (L + 1) •
                MPSTensor.insertedTensor W (A k) s *
                MPSTensor.evalWord (A k) (List.ofFn w)) := by
              rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    -- Apply `htrans` to both sides of `hA`.
    rw [htrans Y, htrans Z] at hA
    -- Rewrite each `Δ k * E_k` trace as the difference of the `Y` and `Z` versions.
    have hsubtr : ∀ k : Fin r,
        Matrix.trace (Δ k * MPSTensor.evalWord (A k) (List.ofFn w)) =
          Matrix.trace ((μ k) ^ (L + 1) •
              MPSTensor.insertedTensor Y (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) -
            Matrix.trace ((μ k) ^ (L + 1) •
              MPSTensor.insertedTensor Z (A k) s *
              MPSTensor.evalWord (A k) (List.ofFn w)) := by
      intro k
      change Matrix.trace
          (((μ k) ^ (L + 1) • (MPSTensor.insertedTensor Y (A k) s -
              MPSTensor.insertedTensor Z (A k) s)) *
            MPSTensor.evalWord (A k) (List.ofFn w)) = _
      rw [smul_sub, sub_mul, Matrix.trace_sub]
    simp_rw [hsubtr]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hA
  -- From `Δ k₀ = 0` and `(μ k₀)^(L+1) ≠ 0`, conclude the pointwise equality.
  have hk := hΔzero k₀
  have hμne : (μ k₀) ^ (L + 1) ≠ 0 := pow_ne_zero _ (hCF.weight_ne_zero k₀)
  have hdiff : MPSTensor.insertedTensor Y (A k₀) s -
      MPSTensor.insertedTensor Z (A k₀) s = 0 :=
    (smul_eq_zero.mp hk).resolve_left hμne
  exact sub_eq_zero.mp hdiff

-- The full bridge `verticalCF_of_horizontalCF` (Proposition IV.12 / Proposition 4.13
-- of arXiv:1606.00608) — every MPDO in horizontal canonical form is in vertical
-- canonical form — is tracked by the blueprint entry
-- `thm:vertical_cf_of_horizontal_cf` (currently `\notready`) and will be added
-- as a theorem in a follow-up PR together with its proof. See the RFP/MPDO 3/5
-- milestone in issue #235 for the forward plan.

end MPOTensor

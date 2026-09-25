/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.ZeroCorrelationExamples
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Core.PhysicalIndexMixing
import TNLean.MPS.ParentHamiltonian.GroundSpace
import TNLean.MPS.RFP.Defs
import TNLean.Algebra.MatrixCyclicPathSum
import TNLean.Algebra.ProjectiveRepresentation

/-!
# Cluster state: the review tensor and the controlled-`Z` construction

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127),
Appendix A, "The cluster state", `Papers/2011.12127/TN-Review-main.tex`
lines 2364–2369: the one-dimensional cluster state is an MPS with
`A⁰ = |0)(+|`, `A¹ = |1)(-|`, which can be derived from the construction of the
cluster state by controlled-`Z` gates between nearest neighbours acting on
`|+⟩^{⊗N}`.
Review: arXiv:2011.12127, Appendix A, "The cluster state".
The review cites Raussendorf–Briegel (arXiv:quant-ph/0010033,
`References/quant-ph_0010033/source/qcfinal.tex` lines 48–64: an Ising-type
nearest-neighbour interaction applied to `|+⟩^{⊗N}`) and Verstraete–Cirac
(arXiv:quant-ph/0311130, `References/quant-ph_0311130/source/cluster.tex`
lines 298–312: the cluster state as a valence-bond state with bonds
`|H⟩ = |00⟩ + |01⟩ + |10⟩ - |11⟩` and site maps
`P = |0'⟩⟨00…0| + |1'⟩⟨11…1|`).

**Formalized here.** The review tensor, exactly as printed; its periodic
matrix product vector at every positive length `N` equals
`(∏ⱼ CZ_{j,j+1}) |+⟩^{⊗N}` on the ring, with no further scalar (the review's
normalization makes the vector a unit vector); the Verstraete–Cirac
valence-bond tensor `|s)(s|H` has periodic vector `∏ⱼ H_{sⱼ s_{j+1}}`, the
contracted valence-bond coefficient, and is `√2` times the review tensor; and the review tensor is
gauge equivalent, through the Hadamard gauge, to the representative
`clusterTensor` of `TNLean.MPS.Examples.Cluster`, which is its transpose. The
following results are transferred to the review tensor: failure of one-site
injectivity, injectivity after blocking two sites, normality, the `Z₂ × Z₂`
on-site symmetry of the two-site blocking, the projective virtual action
carrying the non-trivial factor system `clusterOmega`, string order, and zero
correlation length of the two-site blocking.

Ring convention: the controlled-`Z` product runs over the `N` cyclic bonds
`(j, j + 1 mod N)`. For `N ≥ 3` these are the `N` distinct nearest-neighbour
bonds of the ring. For `N = 2` the two factors `CZ_{0,1} CZ_{1,0}` cancel, and
the vector is `|+⟩^{⊗2}`. For `N = 1` the single factor `CZ_{0,0}` acts as the
Pauli `Z`, and the vector is `|-⟩`. These are the values the trace formula gives.

## Main definitions
* `clusterTensorRMP` : the review tensor `A⁰ = |0)(+|`, `A¹ = |1)(-|`
* `clusterTensorVBS` : the Verstraete–Cirac valence-bond tensor `|s)(s|H`
* `controlledZ`, `clusterCZRing`, `plusProductState` : the ring of
  controlled-`Z` gates and the product state `|+⟩^{⊗N}`
* `clusterBlockedRMP` : the two-site blocking of the review tensor
* `clusterProjRepRMP` : the virtual projective action of `Z₂ × Z₂` on the
  bond space of the blocked review tensor

## Main results
* `clusterTensorRMP_mpv_eq_clusterCZRing` : the controlled-`Z` construction
* `clusterTensorVBS_mpv_eq_prod` : the valence-bond tensor gives the contracted
  valence-bond coefficient `∏ⱼ H_{sⱼ s_{j+1}}`
* `clusterTensorVBS_eq_smul` : the valence-bond tensor is `√2` times the review
  tensor
* `clusterTensorRMP_eq_transpose`,
  `clusterTensor_gaugeEquiv_clusterTensorRMP` : the bridges to `clusterTensor`
* `clusterTensorRMP_isNormal`, `clusterBlockedRMP_isInjective`,
  `clusterBlockedRMP_isOnSiteSymmetric_Z2Z2`,
  `clusterBlockedRMP_twist_intertwine`, `clusterBlockedRMP_hasStringOrder`,
  `clusterBlockedRMP_isZCL` : the transferred results

## References
- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*
- [arXiv:quant-ph/0010033](https://arxiv.org/abs/quant-ph/0010033) --
  Raussendorf, Briegel, *A one-way quantum computer*
- [arXiv:quant-ph/0311130](https://arxiv.org/abs/quant-ph/0311130) --
  Verstraete, Cirac, *Valence bond solids for quantum computation*
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The review tensor -/

/-- Source: arXiv:2011.12127, Appendix A, "The cluster state",
`Papers/2011.12127/TN-Review-main.tex` lines 2364–2367: the cluster-state tensor
`A⁰ = |0)(+|`, `A¹ = |1)(-|`, where `|±⟩ = (|0⟩ ± |1⟩)/√2`.

* `A⁰ = |0)(+| = (1/√2) · !![1, 1; 0, 0]`
* `A¹ = |1)(-| = (1/√2) · !![0, 0; 1, -1]` -/
def clusterTensorRMP : MPSTensor 2 2 := fun i =>
  match i with
  | 0 => (↑(1 / Real.sqrt 2) : ℂ) • !![1, 1; 0, 0]
  | 1 => (↑(1 / Real.sqrt 2) : ℂ) • !![0, 0; 1, -1]

/-- Entry formula for the review tensor: `(Aˢ)_{αβ} = δ_{αs} (-1)^{sβ}/√2`,
the matrix entries of `|s)(h_s|` with `h₀ = +`, `h₁ = -`. -/
lemma clusterTensorRMP_apply (s α β : Fin 2) :
    clusterTensorRMP s α β =
      if α = s then (↑(1 / Real.sqrt 2) : ℂ) * (-1 : ℂ) ^ ((s : ℕ) * (β : ℕ)) else 0 := by
  fin_cases s <;> fin_cases α <;> fin_cases β <;> simp [clusterTensorRMP]

/-! ### The valence-bond derivation -/

/-- Source: arXiv:quant-ph/0311130, `References/quant-ph_0311130/source/cluster.tex`
lines 298–312: the cluster state as a valence-bond state, with (unnormalized)
bonds `|H⟩ = |00⟩ + |01⟩ + |10⟩ - |11⟩` and site maps `|0'⟩⟨00| + |1'⟩⟨11|`.
The site map identifies both virtual qubits with the physical one, which
suggests the tensor `Aˢ = |s)(s| H` with `H = !![1, 1; 1, -1]` defined here;
`clusterTensorVBS_mpv_eq_prod` proves that its periodic vector is the contracted
valence-bond coefficient `∏ⱼ H_{sⱼ s_{j+1}}`. -/
def clusterTensorVBS : MPSTensor 2 2 := fun s =>
  Matrix.single s s (1 : ℂ) * !![1, 1; 1, -1]

/-- Bridge: the valence-bond tensor of arXiv:quant-ph/0311130 (lines 298–312) is
`√2` times the review tensor of arXiv:2011.12127 (lines 2364–2367); the review
normalizes the bond `|H⟩` to a unit vector. -/
theorem clusterTensorVBS_eq_smul (s : Fin 2) :
    clusterTensorVBS s = (Real.sqrt 2 : ℂ) • clusterTensorRMP s := by
  fin_cases s <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [clusterTensorVBS, clusterTensorRMP, Matrix.mul_apply, Matrix.single_apply]

/-- Entry formula for the valence-bond tensor: `(Aˢ)_{αβ} = δ_{αs} H_{sβ}`. -/
lemma clusterTensorVBS_apply (s α β : Fin 2) :
    clusterTensorVBS s α β =
      if α = s then (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) s β else 0 := by
  fin_cases s <;> fin_cases α <;> fin_cases β <;>
    simp [clusterTensorVBS, Matrix.mul_apply, Matrix.single_apply]

/-- Source: arXiv:quant-ph/0311130, `References/quant-ph_0311130/source/cluster.tex`
lines 298–312: contracting the bond `|H⟩` on every nearest-neighbour pair of a
ring of `N ≥ 1` sites with the site maps `|0'⟩⟨00| + |1'⟩⟨11|` gives the
coefficient `∏ⱼ ⟨sⱼ s_{j+1}|H⟩ = ∏ⱼ H_{sⱼ s_{j+1}}`, indices mod `N`. This is
the periodic vector of the valence-bond tensor:
`tr ∏ⱼ |sⱼ)(sⱼ| H = ∏ⱼ H_{sⱼ s_{j+1}}`. -/
theorem clusterTensorVBS_mpv_eq_prod {N : ℕ} (hN : 0 < N) (s : Fin N → Fin 2) :
    mpv clusterTensorVBS s =
      ∏ j : Fin N, (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) (s j) (s (finRotate N j)) := by
  obtain ⟨L, rfl⟩ : ∃ L, N = L + 1 := ⟨N - 1, by omega⟩
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod, Matrix.trace_ofFn_prod_eq_sum_cyclic,
    Finset.sum_eq_single s]
  · exact Finset.prod_congr rfl fun n _ => by simp [clusterTensorVBS_apply]
  · intro t _ hts
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hts
    exact Finset.prod_eq_zero (Finset.mem_univ n) (by simp [clusterTensorVBS_apply, hn])
  · intro h
    exact absurd (Finset.mem_univ s) h

/-! ### The controlled-`Z` construction -/

/-- The controlled-`Z` gate between sites `a` and `b` of an `N`-qubit chain,
acting on coefficient vectors: the coefficient of `|s⟩` is multiplied by
`(-1)^{s_a s_b}`. For `a = b` this is the Pauli `Z` on site `a`. -/
def controlledZ {N : ℕ} (a b : Fin N) : NSiteSpace 2 N →ₗ[ℂ] NSiteSpace 2 N where
  toFun v s := (-1 : ℂ) ^ ((s a : ℕ) * (s b : ℕ)) * v s
  map_add' v w := by
    ext s
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma controlledZ_apply {N : ℕ} (a b : Fin N) (v : NSiteSpace 2 N)
    (s : Fin N → Fin 2) :
    controlledZ a b v s = (-1 : ℂ) ^ ((s a : ℕ) * (s b : ℕ)) * v s := rfl

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2369:
controlled-`Z` gates between nearest neighbours, here on the ring of `N` sites,
one gate on each cyclic bond `(j, j + 1 mod N)`. -/
def clusterCZRing (N : ℕ) : Module.End ℂ (NSiteSpace 2 N) :=
  (List.ofFn fun j : Fin N => controlledZ j (finRotate N j)).prod

/-- Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2369:
the product state `|+⟩^{⊗N}`, whose coefficient on every basis vector is
`∏ⱼ ⟨sⱼ|+⟩ = (1/√2)^N`. -/
def plusProductState (N : ℕ) : NSiteSpace 2 N :=
  fun _ => ∏ _j : Fin N, (↑(1 / Real.sqrt 2) : ℂ)

private lemma list_prod_controlledZ_apply {N : ℕ} (l : List (Fin N × Fin N))
    (v : NSiteSpace 2 N) (s : Fin N → Fin 2) :
    (l.map fun p => controlledZ p.1 p.2).prod v s =
      (l.map fun p => (-1 : ℂ) ^ ((s p.1 : ℕ) * (s p.2 : ℕ))).prod * v s := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, controlledZ_apply, ih]
      ring

/-- The ring of controlled-`Z` gates multiplies the coefficient of `|s⟩` by
`∏ⱼ (-1)^{sⱼ s_{j+1}}`, indices mod `N`. -/
theorem clusterCZRing_apply {N : ℕ} (v : NSiteSpace 2 N) (s : Fin N → Fin 2) :
    clusterCZRing N v s =
      (∏ j : Fin N, (-1 : ℂ) ^ ((s j : ℕ) * (s (finRotate N j) : ℕ))) * v s := by
  have h : clusterCZRing N =
      ((List.ofFn fun j : Fin N => (j, finRotate N j)).map
        fun p => controlledZ p.1 p.2).prod := by
    rw [List.map_ofFn]; rfl
  rw [h, list_prod_controlledZ_apply, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Source: arXiv:2011.12127, Appendix A, "The cluster state",
`Papers/2011.12127/TN-Review-main.tex` lines 2364–2369: the review tensor
generates the cluster state obtained by acting with controlled-`Z` gates between
nearest neighbours on `|+⟩^{⊗N}`. On the ring of `N ≥ 1` sites the periodic
vector `tr(A^{s₁} ⋯ A^{s_N})` equals `(∏ⱼ CZ_{j,j+1}) |+⟩^{⊗N}` exactly, a unit
vector; the conventions at `N = 1, 2` are those of `clusterCZRing` (see the
module docstring). At `N = 0` the trace is the bond dimension `2`, so the
statement is for positive lengths. -/
theorem clusterTensorRMP_mpv_eq_clusterCZRing {N : ℕ} (hN : 0 < N)
    (s : Fin N → Fin 2) :
    mpv clusterTensorRMP s = clusterCZRing N (plusProductState N) s := by
  obtain ⟨L, rfl⟩ : ∃ L, N = L + 1 := ⟨N - 1, by omega⟩
  rw [mpv_eq, coeff_eq, evalWord_ofFn_eq_prod, Matrix.trace_ofFn_prod_eq_sum_cyclic,
    Finset.sum_eq_single s, clusterCZRing_apply, plusProductState,
    ← Finset.prod_mul_distrib]
  · refine Finset.prod_congr rfl fun n _ => ?_
    simp [clusterTensorRMP_apply, mul_comm]
  · intro t _ hts
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hts
    exact Finset.prod_eq_zero (Finset.mem_univ n) (by simp [clusterTensorRMP_apply, hn])
  · intro h
    exact absurd (Finset.mem_univ s) h

/-! ### Bridges to the representative `clusterTensor` -/

/-- Bridge: the review tensor is the transpose of `clusterTensor`, the
representative used in `TNLean.MPS.Examples.Cluster`. -/
theorem clusterTensorRMP_eq_transpose (i : Fin 2) :
    clusterTensorRMP i = (clusterTensor i)ᵀ := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [clusterTensorRMP, clusterTensor]

/-- The unnormalized Hadamard matrix `!![1, 1; 1, -1]` as a virtual gauge. -/
private def hadamardGauge : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 1, -1] (by norm_num [Matrix.det_fin_two])

private lemma hadamardGauge_val :
    (hadamardGauge : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 1; 1, -1] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma hadamardGauge_inv_val :
    ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1 / 2, 1 / 2; 1 / 2, -1 / 2] := by
  rw [Matrix.GeneralLinearGroup.coe_inv, hadamardGauge_val]
  refine Matrix.inv_eq_right_inv ?_
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

private lemma clusterTensorRMP_eq_gauge (i : Fin 2) :
    clusterTensorRMP i =
      (hadamardGauge : Matrix (Fin 2) (Fin 2) ℂ) * clusterTensor i *
        ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [hadamardGauge_val, hadamardGauge_inv_val]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [clusterTensorRMP, clusterTensor, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Bridge: the review tensor is the Hadamard conjugate of `clusterTensor`:
`Aˢ_RMP = H Aˢ H⁻¹` with `H = !![1, 1; 1, -1]`, since `H|+⟩ = √2|0⟩` and
`H|-⟩ = √2|1⟩`. Every gauge-invariant result about `clusterTensor` (its matrix
product vectors, stabilizers and parent Hamiltonians) therefore holds for the
review tensor. -/
theorem clusterTensor_gaugeEquiv_clusterTensorRMP :
    GaugeEquiv clusterTensor clusterTensorRMP :=
  ⟨hadamardGauge, clusterTensorRMP_eq_gauge⟩

/-- The review tensor and `clusterTensor` generate the same matrix product
vectors at every length. -/
theorem clusterTensor_sameMPV_clusterTensorRMP : SameMPV clusterTensor clusterTensorRMP :=
  clusterTensor_gaugeEquiv_clusterTensorRMP.sameMPV

/-! ### Injectivity and normality -/

/-- The review tensor is not injective at one site. -/
theorem clusterTensorRMP_not_isInjective : ¬ Kraus.IsInjective clusterTensorRMP :=
  fun h => cluster_not_isInjective
    (isInjective_of_gaugeEquiv h clusterTensor_gaugeEquiv_clusterTensorRMP.symm)

/-- The review tensor is injective after blocking two sites. -/
theorem clusterTensorRMP_isNBlkInjective_two : Kraus.IsNBlkInjective clusterTensorRMP 2 :=
  isNBlkInjective_of_gaugeEquiv cluster_isNBlkInjective_two
    clusterTensor_gaugeEquiv_clusterTensorRMP

/-- The review tensor is normal. -/
theorem clusterTensorRMP_isNormal : Kraus.IsNormal clusterTensorRMP :=
  ⟨2, Nat.zero_lt_succ 1, clusterTensorRMP_isNBlkInjective_two⟩

/-! ### The two-site blocking -/

private lemma blockPhysDim_two_two : blockPhysDim 2 2 = 4 := by
  simp [blockPhysDim_eq_pow]

/-- The length-`2` blocking of the review tensor, presented on `Fin 4` in the
same little-endian order as `clusterBlocked`. -/
def clusterBlockedRMP : MPSTensor 4 2 :=
  fun i => blockTensor clusterTensorRMP 2 (Fin.cast blockPhysDim_two_two.symm i)

private lemma clusterBlockedRMP_eq_gauge (i : Fin 4) :
    clusterBlockedRMP i =
      (hadamardGauge : Matrix (Fin 2) (Fin 2) ℂ) * clusterBlocked i *
        ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
  evalWord_gauge hadamardGauge clusterTensorRMP_eq_gauge _

/-- Bridge: the blocked review tensor is the Hadamard conjugate of
`clusterBlocked`. -/
theorem clusterBlocked_gaugeEquiv_clusterBlockedRMP :
    GaugeEquiv clusterBlocked clusterBlockedRMP :=
  ⟨hadamardGauge, clusterBlockedRMP_eq_gauge⟩

/-- The blocked letter `A⁰A⁰ = (1/√2)|0)(+|`. -/
@[simp] lemma clusterBlockedRMP_zero :
    clusterBlockedRMP 0 = (1 / 2 : ℂ) • !![1, 1; 0, 0] := by
  rw [clusterBlockedRMP_eq_gauge, hadamardGauge_val, hadamardGauge_inv_val, clusterBlocked_zero]
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The blocked letter `A¹A⁰ = (1/√2)|1)(+|`. -/
@[simp] lemma clusterBlockedRMP_one :
    clusterBlockedRMP 1 = (1 / 2 : ℂ) • !![0, 0; 1, 1] := by
  rw [clusterBlockedRMP_eq_gauge, hadamardGauge_val, hadamardGauge_inv_val, clusterBlocked_one]
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The blocked letter `A⁰A¹ = (1/√2)|0)(-|`. -/
@[simp] lemma clusterBlockedRMP_two :
    clusterBlockedRMP 2 = (1 / 2 : ℂ) • !![1, -1; 0, 0] := by
  rw [clusterBlockedRMP_eq_gauge, hadamardGauge_val, hadamardGauge_inv_val, clusterBlocked_two]
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The blocked letter `A¹A¹ = -(1/√2)|1)(-|`. -/
@[simp] lemma clusterBlockedRMP_three :
    clusterBlockedRMP 3 = (1 / 2 : ℂ) • !![0, 0; -1, 1] := by
  rw [clusterBlockedRMP_eq_gauge, hadamardGauge_val, hadamardGauge_inv_val, clusterBlocked_three]
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The blocked review tensor is injective. -/
theorem clusterBlockedRMP_isInjective : Kraus.IsInjective clusterBlockedRMP :=
  isInjective_of_gaugeEquiv clusterBlocked_isInjective clusterBlocked_gaugeEquiv_clusterBlockedRMP

/-! ### `Z₂ × Z₂` symmetry and its projective virtual action -/

/-- The blocked review tensor is on-site symmetric under the `Z₂ × Z₂` action
by `σx ⊗ I` and `I ⊗ σx`. -/
theorem clusterBlockedRMP_isOnSiteSymmetric_Z2Z2 :
    IsOnSiteSymmetric clusterBlockedRMP clusterZ2Z2Action := by
  intro g N σ
  have hB := clusterBlocked_gaugeEquiv_clusterBlockedRMP
  have htw : GaugeEquiv (twistedTensor clusterBlocked clusterZ2Z2Action g)
      (twistedTensor clusterBlockedRMP clusterZ2Z2Action g) :=
    hB.sum_smul (clusterZ2Z2Action g)
  rw [← hB.sameMPV N σ, cluster_isOnSiteSymmetric_Z2Z2 g N σ, htw.sameMPV N σ]

/-- The virtual action on the bond space of the blocked review tensor: the
Hadamard conjugate `H V(g) H⁻¹` of the virtual action `clusterRepX` of
`clusterBlocked`. Since `H σz H⁻¹ = σx` and `H σx H⁻¹ = σz`, it sends
`(1,0) ↦ σx`, `(0,1) ↦ σz`, `(1,1) ↦ σx σz`. -/
def clusterRepXRMP (g : Multiplicative (ZMod 2 × ZMod 2)) : GL (Fin 2) ℂ :=
  hadamardGauge * clusterRepX g * hadamardGauge⁻¹

open TNLean.Algebra in
/-- The virtual action of the blocked review tensor is a projective
representation with the cluster factor system `clusterOmega`, whose class is
non-trivial (`cluster_isNontrivialSPT`); it is the Hadamard conjugate of
`clusterProjRep`. -/
def clusterProjRepRMP : ProjectiveRepresentation (D := 2) clusterOmega where
  X := clusterRepXRMP
  map_mul' g h := by
    simp only [clusterRepXRMP, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (clusterRepX g : Matrix (Fin 2) (Fin 2) ℂ),
      show ((clusterRepX g : Matrix (Fin 2) (Fin 2) ℂ) * clusterRepX h) = _ from
        clusterProjRep.map_mul' g h]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rfl

/-- The twist of the blocked review tensor is the Hadamard conjugate of the
twist of `clusterBlocked`. -/
private lemma clusterBlockedRMP_twist_eq_gauge (g : Multiplicative (ZMod 2 × ZMod 2))
    (i : Fin 4) :
    twistedTensor clusterBlockedRMP clusterZ2Z2Action g i =
      (hadamardGauge : Matrix (Fin 2) (Fin 2) ℂ) *
        twistedTensor clusterBlocked clusterZ2Z2Action g i *
        ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [twistedTensor, clusterBlockedRMP_eq_gauge, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- The virtual action `clusterProjRepRMP` implements the on-site symmetry of the
blocked review tensor: for every group element `g` and blocked letter `i`,
`(twist by g of A)ᵢ · V(g) = V(g) · Aᵢ`. This is the Hadamard conjugate of
`clusterBlocked_twist_intertwine`. -/
theorem clusterBlockedRMP_twist_intertwine (g : Multiplicative (ZMod 2 × ZMod 2))
    (i : Fin 4) :
    twistedTensor clusterBlockedRMP clusterZ2Z2Action g i *
        (clusterProjRepRMP.X g : Matrix (Fin 2) (Fin 2) ℂ) =
      (clusterProjRepRMP.X g : Matrix (Fin 2) (Fin 2) ℂ) * clusterBlockedRMP i := by
  have h := clusterBlocked_twist_intertwine g i
  change _ * ((clusterRepXRMP g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    ((clusterRepXRMP g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * _
  change _ * ((clusterRepX g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
    ((clusterRepX g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * _ at h
  rw [clusterBlockedRMP_twist_eq_gauge, clusterBlockedRMP_eq_gauge]
  simp only [clusterRepXRMP, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  rw [← mul_assoc (twistedTensor clusterBlocked clusterZ2Z2Action g i), h, mul_assoc]

/-! ### String order and zero correlation length -/

section StringOrder

open scoped ComplexOrder MatrixOrder

/-- The Hadamard matrix is real symmetric. -/
private lemma hadamard_conjTranspose :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![1, 1; 1, -1] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp

/-- The inverse Hadamard matrix is real symmetric. -/
private lemma hadamard_inv_conjTranspose :
    (!![1 / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      !![1 / 2, 1 / 2; 1 / 2, -1 / 2] := by
  ext a b; fin_cases a <;> fin_cases b <;> simp

/-- The blocked review transfer map is unital: by gauge covariance it is
`H E(H⁻¹ H⁻¹ᴴ) Hᴴ = H E(1/2) Hᴴ = (1/2) H Hᴴ = 1`, where `E` is the unital
transfer map of `clusterBlocked`. -/
private theorem clusterBlockedRMP_transferMap_one :
    Kraus.transferMap clusterBlockedRMP 1 = 1 := by
  have hB : clusterBlockedRMP = fun i => (hadamardGauge : Matrix (Fin 2) (Fin 2) ℂ) *
      clusterBlocked i * ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    funext clusterBlockedRMP_eq_gauge
  have hin : (!![1 / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℂ) * 1 *
      (!![1 / 2, 1 / 2; 1 / 2, -1 / 2] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (1 / 2 : ℂ) • 1 := by
    rw [hadamard_inv_conjTranspose]
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hB, Matrix.coe_units_inv hadamardGauge, Kraus.transferMap_gauge_conj,
    ← Matrix.coe_units_inv, hadamardGauge_inv_val, hin, map_smul,
    clusterBlocked_transferMap_one, hadamardGauge_val, hadamard_conjTranspose]
  ext a b; fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The maximally mixed state `Λ = 1/2` is a fixed point of the adjoint blocked
review transfer map: since `H` is real symmetric, the adjoint letters are the
`H⁻¹`-conjugates of those of `clusterBlocked`, and gauge covariance gives
`H⁻¹ E†(H Λ H) H⁻¹ = H⁻¹ E†(1) H⁻¹ = H⁻¹ H⁻¹ = Λ`. -/
private theorem clusterBlockedRMP_adjoint_fixes_maximallyMixed :
    Kraus.transferMap (fun i => (clusterBlockedRMP i)ᴴ) ((1 / 2 : ℂ) • 1) =
      (1 / 2 : ℂ) • 1 := by
  have hB : (fun i => (clusterBlockedRMP i)ᴴ) = fun i =>
      ((hadamardGauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * (clusterBlocked i)ᴴ *
        ((hadamardGauge⁻¹⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext i
    rw [clusterBlockedRMP_eq_gauge, inv_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hadamardGauge_val, hadamardGauge_inv_val,
      hadamard_conjTranspose, hadamard_inv_conjTranspose, mul_assoc]
  have hin : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) * ((1 / 2 : ℂ) • 1) *
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (2 : ℂ) • ((1 / 2 : ℂ) • 1) := by
    rw [hadamard_conjTranspose]
    ext a b; fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hB, Matrix.coe_units_inv hadamardGauge⁻¹, Kraus.transferMap_gauge_conj,
    ← Matrix.coe_units_inv, inv_inv, hadamardGauge_val, hin, map_smul,
    clusterBlocked_adjoint_fixes_maximallyMixed, hadamardGauge_inv_val,
    hadamard_inv_conjTranspose]
  ext a b; fin_cases a <;> fin_cases b <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The blocked review tensor has string order under every element of its
`Z₂ × Z₂` symmetry, with the maximally mixed boundary state. -/
theorem clusterBlockedRMP_hasStringOrder (g : Multiplicative (ZMod 2 × ZMod 2)) :
    HasStringOrder clusterBlockedRMP (clusterZ2Z2Action g)
      ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) :=
  hasStringOrder_of_symmetric_injective clusterBlockedRMP clusterBlockedRMP_isInjective
    clusterZ2Z2Action clusterBlockedRMP_isOnSiteSymmetric_Z2Z2 clusterZ2Z2Action_unitary g
    ((1 / 2 : ℂ) • 1) (Matrix.PosDef.smul_one (by norm_num))
    (by rw [Matrix.trace_smul_one]; norm_num)
    clusterBlockedRMP_adjoint_fixes_maximallyMixed clusterBlockedRMP_transferMap_one

end StringOrder

/-- The blocked review tensor has zero correlation length. -/
theorem clusterBlockedRMP_isZCL : IsZCL clusterBlockedRMP :=
  (zcl_iff_idempotent_transfer _).mpr
    (clusterBlocked_gaugeEquiv_clusterBlockedRMP.isTransferIdempotent_iff.mp
      ((zcl_iff_idempotent_transfer _).mp clusterBlocked_isZCL))

end MPSTensor

end

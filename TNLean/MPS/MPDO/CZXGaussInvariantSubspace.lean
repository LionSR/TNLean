/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MonomialFixedSubspace
import TNLean.MPS.MPDO.CZXGaussCircuitTuple
import TNLean.MPS.MPDO.EmbedLocalOperatorMonomial
import TNLean.MPS.MPDO.GaussProjectorPlacement

/-!
# The gauge-invariant subspace of the displayed CZX circuit tuple

For the displayed CZX circuit tuple
$R^{\mathrm{CZX}}=(\mathrm{id},\mathrm{id},w,\tilde\lambda)$ on a periodic
chain of $N$ blocked sites, each carrying two matter qubits and one gauge
qubit, the common $+1$ eigenspace $\mathcal V_N(R^{\mathrm{CZX}})$ of the
placed Gauss projectors $\widetilde P_j$ has dimension $2^N$ for every
$N\geq3$. This is a new theorem answering, for this one displayed tuple, the
question of arXiv:2502.20257, lines 5198--5204, on the growth of the
gauge-invariant subspace.

A computational-basis configuration of the chain is
$s=(m^{(1)}_k,m^{(2)}_k,g_k)_{k\in\mathbb Z/N}$. The placed Gauss operator
$G_j$ is monomial: its permutation part $\sigma_j$ flips $m^{(1)}_j$,
$m^{(2)}_j$, $g_j$, and $g_{j+1}$, and its phase is $i^{q_j(s)}$ with the
local phase table. The labels

$p_k(s)=m^{(1)}_k+m^{(2)}_k$, $b_k(s)=g_k+m^{(1)}_k+m^{(1)}_{k-1}$

are invariant under every $\sigma_j$, and the fiber
$S_{p,b}$ over each $(p,b)\in\mathbb F_2^N\times\mathbb F_2^N$ is one free
transitive orbit of $\mathbb F_2^N$, parametrized by $\gamma=m^{(1)}$. The
neighboring holonomy identity reads
$(G_jG_{j+1})^2\ket{s}=(-1)^{b_{j+1}(s)}\ket{s}$.
By the monomial fixed-space criterion, a fiber contributes one dimension exactly
when $b=0$, and there are $2^N$ such fibers.

The theorem concerns the displayed circuit tuple acting through the local
Gauss operator. It does not identify this tuple with a member of the full
physical completion class of the CZX defect data, which would require the
three defect domains and maps not supplied by the displayed matrices.
-/

noncomputable section

open Matrix

namespace MPOTensor.CZX

/-! ### Chain configurations in bits -/

/-- The bits $((m^{(1)},m^{(2)}),g)$ of one blocked site. -/
abbrev Site : Type := (ZMod 2 × ZMod 2) × ZMod 2

/-- The enumerated site index of the placed Gauss projector, decoded into the two
matter bits and the gauge bit. -/
def siteDecode : Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2))) ≃ Site :=
  (Fintype.equivFin (Fin 4 × Multiplicative (ZMod 2))).symm.trans
    (siteBits.prodCongr Multiplicative.toAdd)

@[simp]
theorem siteDecode_equivFin (i : Fin 4) (a : Multiplicative (ZMod 2)) :
    siteDecode (Fintype.equivFin (Fin 4 × Multiplicative (ZMod 2)) (i, a)) =
      (siteBits i, Multiplicative.toAdd a) := by
  simp [siteDecode]

/-- A chain configuration decoded site by site. -/
def chainDecode (N : ℕ) :
    (Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) ≃ (Fin N → Site) :=
  Equiv.piCongrRight fun _ ↦ siteDecode

@[simp]
theorem chainDecode_apply (N : ℕ)
    (t : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) (k : Fin N) :
    chainDecode N t k = siteDecode (t k) :=
  rfl

variable {N : ℕ} [NeZero N]

/-- The bits flipped by the bond-`j` Gauss operator: $m^{(1)}_j$, $m^{(2)}_j$,
$g_j$, and $g_{j+1}$. -/
def flipPattern (j : Fin N) : Fin N → Site :=
  Pi.single j ((1, 1), 1) + Pi.single (j + 1) ((0, 0), 1)

/-- The permutation part $\sigma_j$ of the bond-`j` Gauss operator on chain
configurations. -/
def chainFlip (j : Fin N) : Equiv.Perm (Fin N → Site) :=
  Equiv.addRight (flipPattern j)

@[simp]
theorem chainFlip_apply (j : Fin N) (s : Fin N → Site) : chainFlip j s = s + flipPattern j :=
  rfl

theorem succ_ne_self (hN : 2 ≤ N) (j : Fin N) : j + 1 ≠ j := by
  intro h
  have h1 := add_eq_left.mp h
  rw [Fin.one_eq_zero_iff] at h1
  omega

theorem succ_succ_ne_self (hN : 3 ≤ N) (j : Fin N) : j + 1 + 1 ≠ j := by
  intro h
  rw [add_assoc] at h
  have h1 := congrArg Fin.val (add_eq_left.mp h)
  rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < N),
    Nat.mod_eq_of_lt (by omega : 1 + 1 < N)] at h1
  omega

theorem flipPattern_apply_self (hN : 2 ≤ N) (j : Fin N) : flipPattern j j = ((1, 1), 1) := by
  simp [flipPattern, (succ_ne_self hN j).symm]

theorem flipPattern_apply_succ (hN : 2 ≤ N) (j : Fin N) :
    flipPattern j (j + 1) = ((0, 0), 1) := by
  simp [flipPattern, succ_ne_self hN j]

theorem flipPattern_apply_of_ne (j k : Fin N) (hk : k ≠ j) (hk1 : k ≠ j + 1) :
    flipPattern j k = 0 := by
  simp [flipPattern, hk, hk1]

/-- The phase exponent $q_j(s)$ of the bond-`j` Gauss operator, read from the
matter bits $(m^{(1)}_j,m^{(2)}_j,m^{(1)}_{j+1},m^{(2)}_{j+1})$ and the gauge bits
$(g_j,g_{j+1})$ through the local phase table. -/
def bondExponent (j : Fin N) (s : Fin N → Site) : ZMod 4 :=
  phaseExponent ![(s j).1.1, (s j).1.2, (s (j + 1)).1.1, (s (j + 1)).1.2] (s j).2 (s (j + 1)).2

/-- The label $b_k(s)=g_k+m^{(1)}_k+m^{(1)}_{k-1}$. -/
def bLabel (k : Fin N) (s : Fin N → Site) : ZMod 2 :=
  (s k).2 + (s k).1.1 + (s (k - 1)).1.1

/-- The label $p_k(s)=m^{(1)}_k+m^{(2)}_k$. -/
def pLabel (k : Fin N) (s : Fin N → Site) : ZMod 2 :=
  (s k).1.1 + (s k).1.2

/-! ### Involution and neighboring holonomy -/

/-- Every bond Gauss operator is an involution: the phase exponents along an edge
and back add to zero. -/
theorem bondExponent_add_bondExponent_chainFlip (hN : 2 ≤ N) (j : Fin N) (s : Fin N → Site) :
    bondExponent j s + bondExponent j (chainFlip j s) = 0 := by
  simp only [bondExponent, chainFlip_apply, Pi.add_apply, flipPattern_apply_self hN,
    flipPattern_apply_succ hN, Prod.fst_add, Prod.snd_add]
  generalize_decide (s j).1.1, (s j).1.2, (s j).2, (s (j + 1)).1.1, (s (j + 1)).1.2,
    (s (j + 1)).2

/-- **Neighboring holonomy.** Transporting around the square spanned by the bonds
`j` and `j + 1` accumulates the phase $(-1)^{b_{j+1}(s)}$; in exponents,
$q_j(s)+q_{j+1}(\sigma_js)=q_{j+1}(s)+q_j(\sigma_{j+1}s)+2b_{j+1}(s)\pmod4$. -/
theorem bondExponent_holonomy (hN : 3 ≤ N) (j : Fin N) (s : Fin N → Site) :
    bondExponent j s + bondExponent (j + 1) (chainFlip j s) =
      bondExponent (j + 1) s + bondExponent j (chainFlip (j + 1) s) +
        2 * ((bLabel (j + 1) s).val : ZMod 4) := by
  have h2 : 2 ≤ N := by omega
  have hj1 : j + 1 ≠ j := succ_ne_self h2 j
  have hj2 : j + 1 + 1 ≠ j := succ_succ_ne_self hN j
  have hj2' : j + 1 + 1 ≠ j + 1 := succ_ne_self h2 (j + 1)
  have hsub : j + 1 - 1 = j := add_sub_cancel_right j 1
  simp only [bondExponent, bLabel, chainFlip_apply, Pi.add_apply, flipPattern_apply_self h2,
    flipPattern_apply_succ h2, flipPattern_apply_of_ne j (j + 1 + 1) hj2 hj2',
    flipPattern_apply_of_ne (j + 1) j hj1.symm hj2.symm, hsub, Prod.fst_add, Prod.snd_add,
    add_zero]
  generalize_decide (s j).1.1, (s j).1.2, (s j).2, (s (j + 1)).1.1, (s (j + 1)).1.2,
    (s (j + 1)).2, (s (j + 1 + 1)).1.1, (s (j + 1 + 1)).1.2, (s (j + 1 + 1)).2

/-- Bond operators on disjoint windows do not see each other's flips. -/
theorem bondExponent_chainFlip_of_disjoint (j k : Fin N) (hkj : k ≠ j) (hkj1 : k ≠ j + 1)
    (hk1j : k + 1 ≠ j) (s : Fin N → Site) :
    bondExponent j (chainFlip k s) = bondExponent j s := by
  have hk1j1 : k + 1 ≠ j + 1 := fun h ↦ hkj (add_right_cancel h)
  simp only [bondExponent, chainFlip_apply, Pi.add_apply,
    flipPattern_apply_of_ne k j hkj.symm hk1j.symm,
    flipPattern_apply_of_ne k (j + 1) hkj1.symm hk1j1.symm, add_zero]

/-! ### Orbit classification by the affine labels -/

/-- The fiber coordinates $((p,b),\gamma)$ of a chain configuration: given the
labels $p,b\in\mathbb F_2^N$ and the free bits $\gamma=m^{(1)}$, the
configuration is reconstructed by $m^{(2)}_k=p_k+m^{(1)}_k$ and
$g_k=b_k+m^{(1)}_k+m^{(1)}_{k-1}$. -/
def fiberEquiv (N : ℕ) [NeZero N] :
    ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2) ≃ (Fin N → Site) where
  toFun x k := ((x.2 k, x.1.1 k + x.2 k), x.1.2 k + x.2 k + x.2 (k - 1))
  invFun s := ((fun k ↦ (s k).1.1 + (s k).1.2, fun k ↦ (s k).2 + (s k).1.1 + (s (k - 1)).1.1),
    fun k ↦ (s k).1.1)
  left_inv x := by
    obtain ⟨⟨p, b⟩, γ⟩ := x
    refine Prod.ext (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)) (funext fun k ↦ ?_)
    · simp only
      generalize_decide γ k, p k
    · simp only
      generalize_decide γ k, γ (k - 1), b k
    · rfl
  right_inv s := by
    funext k
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · simp only
      generalize_decide (s k).1.1, (s k).1.2
    · simp only
      generalize_decide (s k).1.1, (s (k - 1)).1.1, (s k).2

@[simp]
theorem fiberEquiv_apply (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2))
    (k : Fin N) :
    fiberEquiv N x k = ((x.2 k, x.1.1 k + x.2 k), x.1.2 k + x.2 k + x.2 (k - 1)) :=
  rfl

/-- The label $p$ of a configuration in fiber coordinates. -/
theorem pLabel_fiberEquiv (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2))
    (k : Fin N) :
    pLabel k (fiberEquiv N x) = x.1.1 k := by
  simp only [pLabel, fiberEquiv_apply]
  generalize_decide x.2 k, x.1.1 k

/-- The label $b$ of a configuration in fiber coordinates. -/
theorem bLabel_fiberEquiv (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2))
    (k : Fin N) :
    bLabel k (fiberEquiv N x) = x.1.2 k := by
  simp only [bLabel, fiberEquiv_apply]
  generalize_decide x.2 k, x.2 (k - 1), x.1.2 k

/-- **Permutation-orbit classification.** In fiber coordinates the bond-`j` move
flips the free bit $\gamma_j$ and leaves the labels $(p,b)$ unchanged. -/
theorem chainFlip_fiberEquiv (hN : 2 ≤ N) (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    chainFlip j (fiberEquiv N (pb, γ)) = fiberEquiv N (pb, γ + Pi.single j 1) := by
  funext k
  simp only [chainFlip_apply, Pi.add_apply, fiberEquiv_apply, flipPattern, Pi.single_apply,
    sub_eq_iff_eq_add]
  by_cases hkj : k = j
  · subst hkj
    simp [(succ_ne_self hN k).symm]
    constructor <;> ring
  · by_cases hkj1 : k = j + 1
    · subst hkj1
      simp [hkj]
      ring
    · simp [hkj, hkj1]

/-- The phases of the bond Gauss operators in fiber coordinates. -/
def fiberPhase (j : Fin N) (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2)) :
    ℂ :=
  iPow (bondExponent j (fiberEquiv N x))

theorem fiberPhase_mul_fiberPhase_flip (hN : 2 ≤ N) (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    fiberPhase j (pb, γ) * fiberPhase j (pb, γ + Pi.single j 1) = 1 := by
  rw [fiberPhase, fiberPhase, ← chainFlip_fiberEquiv hN, ← iPow_add,
    bondExponent_add_bondExponent_chainFlip hN, iPow_zero]

/-- The bond-`j` phase in fiber coordinates is unchanged by a flip on a disjoint
bond. -/
theorem fiberPhase_flip_of_disjoint (hN : 2 ≤ N) (j k : Fin N) (hkj : k ≠ j)
    (hkj1 : k ≠ j + 1) (hk1j : k + 1 ≠ j) (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2))
    (γ : Fin N → ZMod 2) :
    fiberPhase j (pb, γ + Pi.single k 1) = fiberPhase j (pb, γ) := by
  rw [fiberPhase, fiberPhase, ← chainFlip_fiberEquiv hN,
    bondExponent_chainFlip_of_disjoint j k hkj hkj1 hk1j]

/-- The neighboring holonomy in fiber coordinates: around the square spanned by
the bonds `j` and `j + 1` the phases differ by $(-1)^{b_{j+1}}$. -/
theorem fiberPhase_holonomy (hN : 3 ≤ N) (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    fiberPhase j (pb, γ) * fiberPhase (j + 1) (pb, γ + Pi.single j 1) =
      fiberPhase (j + 1) (pb, γ) * fiberPhase j (pb, γ + Pi.single (j + 1) 1) *
        (-1) ^ (pb.2 (j + 1)).val := by
  have h2 : 2 ≤ N := by omega
  rw [fiberPhase, fiberPhase, fiberPhase, fiberPhase, ← chainFlip_fiberEquiv h2,
    ← chainFlip_fiberEquiv h2, ← iPow_add, ← iPow_add, bondExponent_holonomy hN j, iPow_add,
    iPow_two_mul_val, bLabel_fiberEquiv]

theorem fiberPhase_ne_zero (j : Fin N)
    (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2)) : fiberPhase j x ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

/-- **Fixed spaces on the orbit fibers.** The phases have trivial holonomy on the
fiber over $(p,b)$ exactly when $b=0$. -/
theorem trivialHolonomy_fiberPhase_iff (hN : 3 ≤ N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) :
    TNLean.Algebra.TrivialHolonomy fiberPhase pb ↔ pb.2 = 0 := by
  have h2 : 2 ≤ N := by omega
  constructor
  · intro h
    funext k
    have hk := h (k - 1) (k - 1 + 1) 0
    have hhol := fiberPhase_holonomy hN (k - 1) pb 0
    rw [sub_add_cancel] at hk hhol
    rw [hhol, mul_comm, mul_eq_right₀ (mul_ne_zero (fiberPhase_ne_zero _ _)
      (fiberPhase_ne_zero _ _))] at hk
    rcases TNLean.Algebra.zmod_two_eq_zero_or_one (pb.2 k) with h0 | h1
    · exact h0
    · rw [h1, show ((1 : ZMod 2)).val = 1 from rfl] at hk
      exfalso
      norm_num at hk
  · intro hb j k γ
    by_cases hkj : k = j
    · subst hkj
      rfl
    · by_cases hkj1 : k = j + 1
      · subst hkj1
        rw [fiberPhase_holonomy hN j, hb]
        simp
      · by_cases hjk1 : j = k + 1
        · subst hjk1
          rw [fiberPhase_holonomy hN k, hb]
          simp
        · rw [fiberPhase_flip_of_disjoint h2 j k hkj hkj1 (Ne.symm hjk1),
            fiberPhase_flip_of_disjoint h2 k j (Ne.symm hkj) hjk1 (Ne.symm hkj1),
            mul_comm]

/-! ### The placed Gauss operators of the circuit tuple -/

/-- The coordinate identification of the local Gauss operator with the two-site
chain window. -/
abbrev windowCoordinates :=
  gaussLocalCoordinateEquiv 4 (Multiplicative (ZMod 2))

/-- The local Gauss operator $G$ of the circuit tuple placed on the bond
$(j,j+1)$ of the periodic chain; this is the operator $G_j$ whose common fixed
space is $\mathcal V_N(R^{\mathrm{CZX}})$. -/
def placedGaussOperator (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    ChainOperator (Fintype.card (Fin 4 × Multiplicative (ZMod 2))) N :=
  embedLocalOperator 2 N hN j
    (Matrix.reindexAlgEquiv ℂ ℂ windowCoordinates
      (TNLean.Algebra.gaussOperator circuitTuple gen))

theorem sum_multiplicative_zmod_two {M : Type*} [AddCommMonoid M]
    (f : Multiplicative (ZMod 2) → M) :
    ∑ g : Multiplicative (ZMod 2), f g = f 1 + f gen := by
  have huniv : (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, gen} := by decide
  rw [huniv, Finset.sum_pair (by decide)]

/-- For $\mathbb Z_2$ the local Gauss projector is $P=(\mathrm{id}+G)/2$. -/
theorem gaussProjector_circuitTuple :
    TNLean.Algebra.gaussProjector circuitTuple =
      (2 : ℂ)⁻¹ • (1 + TNLean.Algebra.gaussOperator circuitTuple gen) := by
  rw [TNLean.Algebra.gaussProjector_eq_average, sum_multiplicative_zmod_two,
    TNLean.Algebra.gaussOperator_one, show Fintype.card (Multiplicative (ZMod 2)) = 2 by decide]
  push_cast
  rfl

/-- The placed Gauss projector is $\widetilde P_j=(\mathrm{id}+G_j)/2$. -/
theorem placedGaussProjector_circuitTuple (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    placedGaussProjector 4 (Multiplicative (ZMod 2)) N hN j circuitTuple =
      (2 : ℂ)⁻¹ • (1 + placedGaussOperator N hN j) := by
  rw [placedGaussProjector, gaussWindowProjector, gaussProjector_circuitTuple, map_smul, map_add,
    map_one, placedGaussOperator]
  change embedLocalOperatorAlgHom 2 N hN j _ = _
  rw [map_smul, map_add, map_one]
  rfl

/-- A vector is fixed by $(\mathrm{id}+G)/2$ exactly when it is fixed by $G$. -/
theorem inv_two_smul_add_mulVec_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    ((2 : ℂ)⁻¹ • (1 + A)) *ᵥ v = v ↔ A *ᵥ v = v := by
  rw [smul_mulVec, add_mulVec, one_mulVec, inv_smul_eq_iff₀ two_ne_zero, two_smul]
  exact add_left_cancel_iff

/-- The common fixed subspace of the placed Gauss projectors is the common fixed
subspace of the placed Gauss operators $G_j$: this is the description of
$\mathcal V_N(R^{\mathrm{CZX}})$ as the common fixed space of the translated
bond operators. -/
theorem commonFixedSubmodule_placedGaussProjector_circuitTuple (N : ℕ) (hN : 2 ≤ N) :
    LinearMap.commonFixedSubmodule (fun j : Fin N ↦
        toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) N hN j circuitTuple)) =
      LinearMap.commonFixedSubmodule fun j : Fin N ↦ toLin' (placedGaussOperator N hN j) := by
  ext v
  simp only [LinearMap.mem_commonFixedSubmodule_iff, toLin'_apply,
    placedGaussProjector_circuitTuple, inv_two_smul_add_mulVec_eq_iff]

/-- The placed Gauss operator in monomial form: its permutation acts on the two-site
window by $\sigma$ and its phase is read off the window. -/
theorem placedGaussOperator_eq_monomial (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    placedGaussOperator N hN j =
      monomial
        (windowPerm 2 hN j (windowCoordinates.symm.trans (localPerm.trans windowCoordinates)))
        fun t ↦ localPhase (windowCoordinates.symm (MPSTensor.extractWindow 2 j t)) := by
  rw [placedGaussOperator, gaussOperator_circuitTuple_gen, Matrix.coe_reindexAlgEquiv,
    reindex_monomial, embedLocalOperator_monomial]
  rfl

theorem siteBits_eq_localBits_zero (m : Fin 2 → Fin 4) :
    siteBits (m 0) = (localBits m 0, localBits m 1) :=
  rfl

theorem siteBits_eq_localBits_one (m : Fin 2 → Fin 4) :
    siteBits (m 1) = (localBits m 2, localBits m 3) :=
  rfl

theorem barFlip_apply_zero (x : Fin 4 → ZMod 2) : barFlip x 0 = x 0 + 1 := by
  simp [barFlip_apply]

theorem barFlip_apply_one (x : Fin 4 → ZMod 2) : barFlip x 1 = x 1 + 1 := by
  simp [barFlip_apply]

theorem barFlip_apply_two (x : Fin 4 → ZMod 2) : barFlip x 2 = x 2 := by
  simp [barFlip_apply]

theorem barFlip_apply_three (x : Fin 4 → ZMod 2) : barFlip x 3 = x 3 := by
  simp [barFlip_apply]

theorem toAdd_mul_gen_inv (a : Multiplicative (ZMod 2)) :
    Multiplicative.toAdd (a * gen⁻¹) = Multiplicative.toAdd a + 1 := by
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd]
  rfl

theorem toAdd_gen_mul (a : Multiplicative (ZMod 2)) :
    Multiplicative.toAdd (gen * a) = Multiplicative.toAdd a + 1 := by
  rw [toAdd_mul, toAdd_ofAdd, add_comm]

theorem gaussLegAction_fst {G : Type*} [Group G] (g : G) (l : G × G) :
    (TNLean.Algebra.gaussLegAction g l).1 = l.1 * g⁻¹ :=
  rfl

theorem gaussLegAction_snd {G : Type*} [Group G] (g : G) (l : G × G) :
    (TNLean.Algebra.gaussLegAction g l).2 = g * l.2 :=
  rfl

/-- Decoding the two-site window at `j` of a chain configuration. -/
theorem chainDecode_window (hN : 2 ≤ N) (j : Fin N)
    (t : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :
    let y := windowCoordinates.symm (MPSTensor.extractWindow 2 j t)
    chainDecode N t j = (siteBits (y.1 0), Multiplicative.toAdd y.2.1) ∧
      chainDecode N t (j + 1) = (siteBits (y.1 1), Multiplicative.toAdd y.2.2) := by
  intro y
  have hκ : windowCoordinates y = MPSTensor.extractWindow 2 j t := Equiv.apply_symm_apply _ _
  rw [extractWindow_two hN] at hκ
  have h0 := congrFun hκ 0
  have h1 := congrFun hκ 1
  rw [gaussLocalCoordinateEquiv_apply_zero] at h0
  rw [gaussLocalCoordinateEquiv_apply_one] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
  rw [chainDecode_apply, chainDecode_apply, ← h0, ← h1, siteDecode_equivFin,
    siteDecode_equivFin]
  exact ⟨rfl, rfl⟩

/-- The permutation part of the placed Gauss operator is the bond flip in bit
coordinates. -/
theorem chainDecode_windowPerm (hN : 2 ≤ N) (j : Fin N)
    (t : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :
    chainDecode N
        (windowPerm 2 hN j (windowCoordinates.symm.trans (localPerm.trans windowCoordinates)) t) =
      chainFlip j (chainDecode N t) := by
  obtain ⟨hj, hj1⟩ := chainDecode_window hN j t
  set y := windowCoordinates.symm (MPSTensor.extractWindow 2 j t) with hy
  funext k
  rw [chainDecode_apply, windowPerm_apply, replaceWindow_two_apply hN, chainFlip_apply,
    Pi.add_apply, Equiv.trans_apply, Equiv.trans_apply, ← hy]
  by_cases hkj : k = j
  · subst hkj
    rw [ite_eq_left rfl, gaussLocalCoordinateEquiv_apply_zero, siteDecode_equivFin,
      flipPattern_apply_self hN, hj]
    simp only [localPerm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      gaussLegAction_fst, siteBits_eq_localBits_zero, localBits_matterBarFlip,
      barFlip_apply_zero, barFlip_apply_one, toAdd_mul_gen_inv, Prod.mk_add_mk]
  · by_cases hkj1 : k = j + 1
    · subst hkj1
      rw [ite_eq_right hkj, ite_eq_left rfl, gaussLocalCoordinateEquiv_apply_one,
        siteDecode_equivFin, flipPattern_apply_succ hN, hj1]
      simp only [localPerm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
        gaussLegAction_snd, siteBits_eq_localBits_one, localBits_matterBarFlip,
        barFlip_apply_two, barFlip_apply_three, toAdd_gen_mul, Prod.mk_add_mk, add_zero]
    · rw [ite_eq_right hkj, ite_eq_right hkj1, flipPattern_apply_of_ne j k hkj hkj1, add_zero,
        chainDecode_apply]

/-- The phase of the placed Gauss operator is the bond phase in bit coordinates. -/
theorem localPhase_window (hN : 2 ≤ N) (j : Fin N)
    (t : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :
    localPhase (windowCoordinates.symm (MPSTensor.extractWindow 2 j t)) =
      iPow (bondExponent j (chainDecode N t)) := by
  obtain ⟨hj, hj1⟩ := chainDecode_window hN j t
  rw [localPhase, bondExponent, hj, hj1]
  rfl

/-- The fiber coordinates of a chain configuration. -/
def fiberCoordinates (N : ℕ) [NeZero N] :
    ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2) ≃
      (Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :=
  (fiberEquiv N).trans (chainDecode N).symm

/-- In fiber coordinates the placed Gauss operator on bond `j` is the monomial
operator with the coordinate flip $\gamma\mapsto\gamma+e_j$ and the phase
$i^{q_j}$. -/
theorem placedGaussOperator_eq_reindex (N : ℕ) [NeZero N] (hN : 2 ≤ N) (j : Fin N) :
    placedGaussOperator N hN j =
      reindex (fiberCoordinates N) (fiberCoordinates N)
        (monomial (TNLean.Algebra.fiberFlip j) (fiberPhase j)) := by
  rw [placedGaussOperator_eq_monomial, reindex_monomial]
  congr 1
  · ext t : 1
    apply (chainDecode N).injective
    rw [chainDecode_windowPerm hN]
    simp only [Equiv.trans_apply, fiberCoordinates, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
    generalize hx : (fiberEquiv N).symm (chainDecode N t) = x
    rw [Equiv.symm_apply_eq] at hx
    obtain ⟨pb, γ⟩ := x
    rw [hx, TNLean.Algebra.fiberFlip_apply, chainFlip_fiberEquiv hN]
  · funext t
    rw [localPhase_window hN, Function.comp_apply, fiberPhase, fiberCoordinates,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-! ### The exact dimension -/

/-- **Exact dimension of the gauge-invariant subspace for the displayed CZX circuit
tuple.** On a periodic chain of $N\geq3$ blocked sites, the common $+1$
eigenspace $\mathcal V_N(R^{\mathrm{CZX}})$ of the placed Gauss projectors of the
displayed circuit tuple $R^{\mathrm{CZX}}=(\mathrm{id},\mathrm{id},w,\tilde\lambda)$
has dimension $2^N$. This new result addresses the growth question posed in
arXiv:2502.20257, lines 5198--5204.

The proof classifies the orbits of the bond flips by the labels $(p,b)$, applies
the monomial fixed-space criterion, and uses the neighboring holonomy to show
that exactly the fibers with $b=0$ carry a fixed vector.

This theorem concerns the displayed circuit tuple only. It does not assert that
the tuple belongs to the full physical completion class of the CZX defect
data. -/
theorem finrank_commonFixedSubmodule_placedGaussProjector_circuitTuple (N : ℕ) (hN : 3 ≤ N) :
    Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j : Fin N ↦
      toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) N (by omega) j circuitTuple)) =
      2 ^ N := by
  have : NeZero N := ⟨by omega⟩
  have h2 : 2 ≤ N := by omega
  rw [commonFixedSubmodule_placedGaussProjector_circuitTuple N h2]
  have hop : (fun j : Fin N ↦ toLin' (placedGaussOperator N h2 j)) =
      fun j ↦ toLin' (reindex (fiberCoordinates N) (fiberCoordinates N)
        (monomial (TNLean.Algebra.fiberFlip j) (fiberPhase j))) :=
    funext fun j ↦ by rw [placedGaussOperator_eq_reindex N h2 j]
  rw [hop, TNLean.Algebra.finrank_commonFixedSubmodule_reindex (fiberCoordinates N)
    (fun j ↦ monomial (TNLean.Algebra.fiberFlip j) (fiberPhase j)),
    TNLean.Algebra.finrank_commonFixedSubmodule_monomial_fiberFlip fiberPhase
      (fun j s ↦ by
        obtain ⟨pb, γ⟩ := s
        rw [TNLean.Algebra.fiberFlip_apply]
        exact fiberPhase_mul_fiberPhase_flip h2 j pb γ)]
  let hequiv : {x : (Fin N → ZMod 2) × (Fin N → ZMod 2) //
      TNLean.Algebra.TrivialHolonomy fiberPhase x} ≃ (Fin N → ZMod 2) :=
    { toFun := fun x ↦ x.1.1
      invFun := fun p ↦ ⟨(p, 0), (trivialHolonomy_fiberPhase_iff hN (p, 0)).mpr rfl⟩
      left_inv := fun x ↦ by
        obtain ⟨⟨p, b⟩, h⟩ := x
        have hb : b = 0 := (trivialHolonomy_fiberPhase_iff hN (p, b)).mp h
        subst hb
        rfl
      right_inv := fun p ↦ rfl }
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_pi_const, ZMod.card]

end MPOTensor.CZX

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXGaussInvariantSubspace

/-!
# A second displayed circuit tuple and its gauge-invariant subspace at three and four sites

The CZX model of arXiv:2502.20257, lines 4503--5183, supplies the fusion
operators $w$ and $\tilde\lambda$ and, through them, the displayed circuit tuple
$R^{\mathrm{CZX}}=(\mathrm{id},\mathrm{id},w,\tilde\lambda)$. Only the $(1,1)$
defect domain and map are supplied there, so the displayed matrices do not
determine a four-sector completion. Replacing the $(1,1)$ block by a second
matrix with the same prescribed action on the supplied defect subspace produces
a second displayed tuple.

Let $R_\star$ be the diagonal unitary on the four matter qubits of two
neighboring blocked sites determined by the phase polynomial

$R_\star\ket{x}=(-1)^{r_\star(x)}\ket{x}$,
$r_\star(x)=x_1+x_3+x_0x_1+x_0x_3+x_1x_2+x_2x_3$,

equivalently $R_\star=Z_1Z_3\,\mathrm{CZ}_{01}\mathrm{CZ}_{03}\mathrm{CZ}_{12}
\mathrm{CZ}_{23}$. The prescribed $(1,1)$ defect subspace is spanned by
$\ket{0011}$ and $\ket{1100}$, and $r_\star(0011)=r_\star(1100)=0$, so $R_\star$
fixes that subspace pointwise. The second displayed tuple is

$R^\star=(U^\star_{0,0},U^\star_{0,1},U^\star_{1,0},U^\star_{1,1})
=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$,

which has the same prescribed action as $R^{\mathrm{CZX}}$ on the supplied
defect subspace. Its nontrivial local Gauss operator has the same permutation
part as that of $R^{\mathrm{CZX}}$ and differs only by phases in the $(0,0)$ and
$(1,1)$ gauge sectors.

This file computes the dimension of the common $+1$ eigenspace
$\mathcal V_N(R^\star)$ of the placed Gauss projectors of $R^\star$ at two
system sizes:

$\dim\mathcal V_3(R^\star)=14$, $\dim\mathcal V_4(R^\star)=36$.

The route is the orbit and holonomy reduction of the first displayed tuple. The
bond flips have the same orbits, the fibers are again indexed by the affine
labels $(p,b)\in\mathbb F_2^N\times\mathbb F_2^N$, and the neighboring holonomy
around the square spanned by the bonds $j$ and $j+1$ is
$(-1)^{c_j(p,b)}$ with

$c_j(p,b)=b_{j+1}(1+p_j+p_{j+1})+b_{j+2}(p_{j+1}+p_{j+2})$.

A fiber therefore contributes one dimension exactly when $c_j(p,b)=0$ for every
$j$, and the dimension is the number of pairs $(p,b)$ satisfying those $N$
equations. At $N=3$ and $N=4$ that finite count is $14$ and $36$.

**Scope of the two dimension theorems.** They are certificates at two system
sizes. They must not be promoted to an asymptotic statement, and no growth law
may be extrapolated from them; two system sizes are two system sizes. They
assert nothing about the physical completion class of the CZX defect data,
because the other three defect domains and maps are not supplied by the
displayed matrices, and they give no value for the minimum or the maximum of
the dimension over completions. The comparison with
`MPOTensor.CZX.finrank_commonFixedSubmodule_placedGaussProjector_circuitTuple`,
whose values are $8$ and $16$ at the same two sizes, exhibits dependence of the
dimension on the displayed circuit data at those two sizes only.

The question addressed is that of arXiv:2502.20257, lines 5198--5204.
-/

noncomputable section

open Matrix Complex

namespace MPOTensor.CZX

/-! ### The diagonal unitary of the second displayed tuple -/

/-- The phase polynomial
$r_\star(x)=x_1+x_3+x_0x_1+x_0x_3+x_1x_2+x_2x_3$ of the diagonal unitary
$R_\star$. -/
def rStarExponent (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 1 + x 3 + x 0 * x 1 + x 0 * x 3 + x 1 * x 2 + x 2 * x 3

/-- The diagonal unitary
$R_\star=Z_1Z_3\,\mathrm{CZ}_{01}\mathrm{CZ}_{03}\mathrm{CZ}_{12}
\mathrm{CZ}_{23}$ on the four matter qubits of two neighboring blocked sites,
built from the elementary gates of the CZX model (arXiv:2502.20257, lines
4503--5183). -/
def rStar : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  pauliZ 1 * pauliZ 3 * controlledZ 0 1 * controlledZ 0 3 * controlledZ 1 2 * controlledZ 2 3

/-- The phase table of $R_\star$: $R_\star\ket{x}=(-1)^{r_\star(x)}\ket{x}$. -/
theorem rStar_eq : rStar = monomial 1 fun x ↦ (-1) ^ (rStarExponent x).val := by
  simp only [rStar, pauliZ, controlledZ, monomial_mul_monomial, Equiv.Perm.coe_one, id_eq,
    mul_one]
  congr 1
  funext x
  rw [rStarExponent, neg_one_pow_val_add, neg_one_pow_val_add, neg_one_pow_val_add,
    neg_one_pow_val_add, neg_one_pow_val_add]

/-- The phase polynomial vanishes at $0011$. -/
theorem rStarExponent_zero_zero_one_one : rStarExponent ![0, 0, 1, 1] = 0 := by decide

/-- The phase polynomial vanishes at $1100$. -/
theorem rStarExponent_one_one_zero_zero : rStarExponent ![1, 1, 0, 0] = 0 := by decide

/-- **The prescribed defect subspace is fixed pointwise.** Every vector supported
on $\{\ket{0011},\ket{1100}\}$, the prescribed $(1,1)$ defect subspace of the CZX
model, is fixed by $R_\star$. -/
theorem rStar_mulVec_eq_self {v : (Fin 4 → ZMod 2) → ℂ}
    (hv : ∀ x, x ≠ ![0, 0, 1, 1] → x ≠ ![1, 1, 0, 0] → v x = 0) : rStar *ᵥ v = v := by
  rw [rStar_eq, monomial_mulVec]
  funext t
  change (-1 : ℂ) ^ (rStarExponent t).val * v t = v t
  by_cases h1 : t = ![0, 0, 1, 1]
  · rw [h1, rStarExponent_zero_zero_one_one]
    simp
  · by_cases h2 : t = ![1, 1, 0, 0]
    · rw [h2, rStarExponent_one_one_zero_zero]
      simp
    · rw [hv t h1 h2, mul_zero]

/-- The modified fusion operator $\tilde\lambda R_\star$ of the second displayed
tuple. -/
def tildeLambdaStar : Matrix (Fin 4 → ZMod 2) (Fin 4 → ZMod 2) ℂ :=
  tildeLambda * rStar

/-- The phase table of $\tilde\lambda R_\star$:
$\tilde\lambda R_\star\ket{x}=-i(-1)^{f(x)+r_\star(x)}\ket{\overline x}$. -/
theorem tildeLambdaStar_eq :
    tildeLambdaStar =
      monomial barFlip fun x ↦ -I * (-1) ^ (fExponent x + rStarExponent x).val := by
  rw [tildeLambdaStar, tildeLambda_eq, rStar_eq, monomial_mul_monomial, mul_one]
  congr 1
  funext x
  rw [Equiv.Perm.coe_one, id_eq, neg_one_pow_val_add]
  ring

theorem tildeLambdaStar_mem_unitaryGroup :
    matterMatrix tildeLambdaStar ∈ Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ := by
  rw [tildeLambdaStar_eq, matterMatrix_monomial]
  refine monomial_mem_unitaryGroup _ _ fun s ↦ ?_
  have hstar :
      star (-I * (-1 : ℂ) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val) =
        I * (-1) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val := by
    simp
  rw [Function.comp_apply, hstar]
  calc I * (-1 : ℂ) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val *
        (-I * (-1) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val)
      = -(I * I) * ((-1) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val *
          (-1) ^ (fExponent (localBits s) + rStarExponent (localBits s)).val) := by ring
    _ = 1 := by
        rw [I_mul_I, ← mul_pow]
        simp

/-- The second displayed circuit tuple
$R^\star=(U^\star_{0,0},U^\star_{0,1},U^\star_{1,0},U^\star_{1,1})
=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$, indexed by the ordered pair
of gauge labels in $\mathbb Z_2$ with $e\leftrightarrow0$ and
$g\leftrightarrow1$.

Since $R_\star$ fixes the prescribed $(1,1)$ defect subspace pointwise, this
tuple has the same prescribed action there as the first displayed tuple.
Whether either tuple belongs to the full physical completion class of the CZX
defect data is not asserted; the source supplies only the $(1,1)$ defect domain
and map. -/
def circuitTupleStar (a b : Multiplicative (ZMod 2)) : Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ :=
  if Multiplicative.toAdd a = 0 then 1
  else if Multiplicative.toAdd b = 0 then ⟨matterMatrix w, w_mem_unitaryGroup⟩
  else ⟨matterMatrix tildeLambdaStar, tildeLambdaStar_mem_unitaryGroup⟩

@[simp]
theorem circuitTupleStar_one (b : Multiplicative (ZMod 2)) : circuitTupleStar 1 b = 1 := by
  simp [circuitTupleStar]

@[simp]
theorem circuitTupleStar_gen_one :
    (circuitTupleStar gen 1 : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) = matterMatrix w := by
  simp [circuitTupleStar]

@[simp]
theorem circuitTupleStar_gen_gen :
    (circuitTupleStar gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) =
      matterMatrix tildeLambdaStar := by
  simp [circuitTupleStar]

/-! ### The local Gauss operator of the second displayed tuple -/

/-- The phase polynomial on the flipped argument:
$r_\star(\overline x)=r_\star(x)+x_0+x_1+x_2+x_3$. -/
theorem rStarExponent_barFlip (x : Fin 4 → ZMod 2) :
    rStarExponent (barFlip x) = rStarExponent x + x 0 + x 1 + x 2 + x 3 := by
  simp only [rStarExponent, barFlip_apply, Pi.add_apply, Pi.single_apply]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, add_zero]
  generalize_decide x 0, x 1, x 2, x 3

/-- The correction that $R_\star$ adds to the local phase table of the first
displayed tuple. It vanishes in the $(0,1)$ and $(1,0)$ gauge sectors, equals
$r_\star(x)$ in the $(1,1)$ sector, and equals
$r_\star(\overline x)=r_\star(x)+x_0+x_1+x_2+x_3$ in the $(0,0)$ sector. -/
def starDefect (x : Fin 4 → ZMod 2) (a a' : ZMod 2) : ZMod 2 :=
  if a = 0 then (if a' = 0 then rStarExponent x + x 0 + x 1 + x 2 + x 3 else 0)
  else (if a' = 0 then 0 else rStarExponent x)

/-- The phase table $q^\star(s)$ of the local Gauss operator of the second
displayed tuple: the table of the first displayed tuple corrected by
$2\,\delta_\star$ modulo $4$. -/
def phaseExponentStar (x : Fin 4 → ZMod 2) (a a' : ZMod 2) : ZMod 4 :=
  phaseExponent x a a' + 2 * ((starDefect x a a').val : ZMod 4)

theorem phaseExponentStar_zero_zero (x : Fin 4 → ZMod 2) :
    phaseExponentStar x 0 0 =
      3 + 2 * ((eExponent x).val : ZMod 4) + 2 * ((rStarExponent (barFlip x)).val : ZMod 4) := by
  rw [rStarExponent_barFlip]
  simp only [phaseExponentStar, starDefect, phaseExponent, uExponent, eExponent, rStarExponent,
    ↓reduceIte]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponentStar_zero_one (x : Fin 4 → ZMod 2) :
    phaseExponentStar x 0 1 = 2 + 2 * ((fExponent x).val : ZMod 4) := by
  simp only [phaseExponentStar, starDefect, phaseExponent, uExponent, fExponent, ↓reduceIte,
    one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponentStar_one_zero (x : Fin 4 → ZMod 2) :
    phaseExponentStar x 1 0 = 2 * ((eExponent x).val : ZMod 4) := by
  simp only [phaseExponentStar, starDefect, phaseExponent, uExponent, eExponent, ↓reduceIte,
    one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

theorem phaseExponentStar_one_one (x : Fin 4 → ZMod 2) :
    phaseExponentStar x 1 1 =
      3 + 2 * ((fExponent x).val : ZMod 4) + 2 * ((rStarExponent x).val : ZMod 4) := by
  simp only [phaseExponentStar, starDefect, phaseExponent, uExponent, fExponent, rStarExponent,
    ↓reduceIte, one_ne_zero]
  generalize_decide x 0, x 1, x 2, x 3

/-- The phase $i^{q^\star(s)}$ of the local Gauss operator of the second displayed
tuple. -/
def localPhaseStar (s : (Fin 2 → Fin 4) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ℂ :=
  iPow (phaseExponentStar (localBits s.1) (Multiplicative.toAdd s.2.1)
    (Multiplicative.toAdd s.2.2))

/-- **Local monomial action of the second tuple's Gauss operator.** Substituting
the second displayed circuit tuple into the local Gauss operator gives the
monomial operator $G^\star\ket{s}=i^{q^\star(s)}\ket{\sigma(s)}$ with the same
permutation part $\sigma(s)=(\overline x,a+1,a'+1)$ as the first displayed
tuple. -/
theorem gaussOperator_circuitTupleStar_gen :
    TNLean.Algebra.gaussOperator circuitTupleStar gen = monomial localPerm localPhaseStar := by
  let σ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → Equiv.Perm (Fin 2 → Fin 4) :=
    fun a _ ↦ if Multiplicative.toAdd a = 0 then 1 else matterBarFlip
  let φ : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) → (Fin 2 → Fin 4) → ℂ :=
    fun a b ↦ if Multiplicative.toAdd a = 0 then fun _ ↦ 1
      else if Multiplicative.toAdd b = 0 then fun i ↦ (-1) ^ (eExponent (localBits i)).val
      else fun i ↦ -I * (-1) ^ (fExponent (localBits i) + rStarExponent (localBits i)).val
  have hR : ∀ a b, (circuitTupleStar a b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) =
      monomial (σ a b) (φ a b) := by
    intro a b
    rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
      rcases MPSTensor.zmod2_cases b with rfl | rfl
    · simp [σ, φ, monomial_one]
    · simp [σ, φ, monomial_one]
    · simp only [circuitTupleStar_gen_one, w_eq, matterMatrix_monomial, σ, φ, toAdd_ofAdd,
        one_ne_zero, ↓reduceIte, toAdd_one]
      rfl
    · simp only [circuitTupleStar_gen_gen, tildeLambdaStar_eq, matterMatrix_monomial, σ, φ,
        toAdd_ofAdd, one_ne_zero, ↓reduceIte]
      rfl
  rw [TNLean.Algebra.gaussOperator_eq_monomial circuitTupleStar σ φ hR gen]
  congr 1
  · ext ⟨i, a, b⟩ : 1
    rcases MPSTensor.zmod2_cases a with rfl | rfl
    · simp [σ, localPerm, gen_inv, matterBarFlip_symm]
    · simp [σ, localPerm]
      rfl
  · funext ⟨i, a, b⟩
    simp only [TNLean.Algebra.gaussMonomialPhase, localPhaseStar, σ, φ,
      TNLean.Algebra.gaussLegAction_apply]
    rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
      rcases MPSTensor.zmod2_cases b with rfl | rfl
    · simp [gen_inv, matterBarFlip_symm, fExponent_barFlip, phaseExponentStar_zero_zero,
        iPow_add, iPow_two_mul_cast, neg_one_pow_val_add,
        show ((1 : ZMod 2)).val = 1 from rfl]
      ring
    · simp [gen_inv, gen_mul_gen, matterBarFlip_symm, eExponent_barFlip,
        phaseExponentStar_zero_one, iPow_add, iPow_two_mul_cast, neg_one_pow_val_add,
        show ((1 : ZMod 2)).val = 1 from rfl]
    · simp [gen_inv, gen_mul_gen, phaseExponentStar_one_zero, iPow_two_mul_cast]
    · simp [gen_inv, gen_mul_gen, phaseExponentStar_one_one, iPow_add, iPow_two_mul_cast,
        neg_one_pow_val_add]
      ring

/-! ### Bond phases, involution, and neighboring holonomy -/

variable {N : ℕ} [NeZero N]

/-- The phase exponent $q^\star_j(s)$ of the bond-`j` Gauss operator of the second
displayed tuple. -/
def bondExponentStar (j : Fin N) (s : Fin N → Site) : ZMod 4 :=
  phaseExponentStar ![(s j).1.1, (s j).1.2, (s (j + 1)).1.1, (s (j + 1)).1.2] (s j).2
    (s (j + 1)).2

/-- The holonomy label
$c_j(s)=b_{j+1}(1+p_j+p_{j+1})+b_{j+2}(p_{j+1}+p_{j+2})$ of the second displayed
tuple. -/
def starHolonomyLabel (j : Fin N) (s : Fin N → Site) : ZMod 2 :=
  bLabel (j + 1) s * (1 + pLabel j s + pLabel (j + 1) s) +
    bLabel (j + 1 + 1) s * (pLabel (j + 1) s + pLabel (j + 1 + 1) s)

/-- Every bond Gauss operator of the second displayed tuple is an involution. -/
theorem bondExponentStar_add_bondExponentStar_chainFlip (hN : 2 ≤ N) (j : Fin N)
    (s : Fin N → Site) :
    bondExponentStar j s + bondExponentStar j (chainFlip j s) = 0 := by
  simp only [bondExponentStar, chainFlip_apply, Pi.add_apply, flipPattern_apply_self hN,
    flipPattern_apply_succ hN, Prod.fst_add, Prod.snd_add]
  generalize_decide (s j).1.1, (s j).1.2, (s j).2, (s (j + 1)).1.1, (s (j + 1)).1.2,
    (s (j + 1)).2

/-- **Neighboring holonomy for the second displayed tuple.** Transporting around
the square spanned by the bonds `j` and `j + 1` accumulates the phase
$(-1)^{c_j(s)}$. -/
theorem bondExponentStar_holonomy (hN : 3 ≤ N) (j : Fin N) (s : Fin N → Site) :
    bondExponentStar j s + bondExponentStar (j + 1) (chainFlip j s) =
      bondExponentStar (j + 1) s + bondExponentStar j (chainFlip (j + 1) s) +
        2 * ((starHolonomyLabel j s).val : ZMod 4) := by
  have h2 : 2 ≤ N := by omega
  have hj1 : j + 1 ≠ j := succ_ne_self h2 j
  have hj2 : j + 1 + 1 ≠ j := succ_succ_ne_self hN j
  have hj2' : j + 1 + 1 ≠ j + 1 := succ_ne_self h2 (j + 1)
  have hsub : j + 1 - 1 = j := add_sub_cancel_right j 1
  have hsub2 : j + 1 + 1 - 1 = j + 1 := add_sub_cancel_right (j + 1) 1
  simp only [bondExponentStar, starHolonomyLabel, bLabel, pLabel, chainFlip_apply, Pi.add_apply,
    flipPattern_apply_self h2, flipPattern_apply_succ h2,
    flipPattern_apply_of_ne j (j + 1 + 1) hj2 hj2',
    flipPattern_apply_of_ne (j + 1) j hj1.symm hj2.symm, hsub, hsub2, Prod.fst_add, Prod.snd_add,
    add_zero]
  generalize_decide (s j).1.1, (s j).1.2, (s j).2, (s (j + 1)).1.1, (s (j + 1)).1.2,
    (s (j + 1)).2, (s (j + 1 + 1)).1.1, (s (j + 1 + 1)).1.2, (s (j + 1 + 1)).2

/-- Bond operators of the second displayed tuple on disjoint windows do not see
each other's flips. -/
theorem bondExponentStar_chainFlip_of_disjoint (j k : Fin N) (hkj : k ≠ j) (hkj1 : k ≠ j + 1)
    (hk1j : k + 1 ≠ j) (s : Fin N → Site) :
    bondExponentStar j (chainFlip k s) = bondExponentStar j s := by
  have hk1j1 : k + 1 ≠ j + 1 := fun h ↦ hkj (add_right_cancel h)
  simp only [bondExponentStar, chainFlip_apply, Pi.add_apply,
    flipPattern_apply_of_ne k j hkj.symm hk1j.symm,
    flipPattern_apply_of_ne k (j + 1) hkj1.symm hk1j1.symm, add_zero]

/-! ### The holonomy condition on the orbit fibers -/

/-- The holonomy label of the second displayed tuple in fiber coordinates:
$c_j(p,b)=b_{j+1}(1+p_j+p_{j+1})+b_{j+2}(p_{j+1}+p_{j+2})$. -/
def starFiberLabel (j : Fin N) (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) : ZMod 2 :=
  pb.2 (j + 1) * (1 + pb.1 j + pb.1 (j + 1)) +
    pb.2 (j + 1 + 1) * (pb.1 (j + 1) + pb.1 (j + 1 + 1))

theorem starHolonomyLabel_fiberEquiv (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    starHolonomyLabel j (fiberEquiv N (pb, γ)) = starFiberLabel j pb := by
  simp only [starHolonomyLabel, starFiberLabel, bLabel_fiberEquiv, pLabel_fiberEquiv]

/-- The phases of the bond Gauss operators of the second displayed tuple in fiber
coordinates. -/
def fiberPhaseStar (j : Fin N) (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2)) :
    ℂ :=
  iPow (bondExponentStar j (fiberEquiv N x))

theorem fiberPhaseStar_mul_fiberPhaseStar_flip (hN : 2 ≤ N) (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    fiberPhaseStar j (pb, γ) * fiberPhaseStar j (pb, γ + Pi.single j 1) = 1 := by
  rw [fiberPhaseStar, fiberPhaseStar, ← chainFlip_fiberEquiv hN, ← iPow_add,
    bondExponentStar_add_bondExponentStar_chainFlip hN, iPow_zero]

theorem fiberPhaseStar_flip_of_disjoint (hN : 2 ≤ N) (j k : Fin N) (hkj : k ≠ j)
    (hkj1 : k ≠ j + 1) (hk1j : k + 1 ≠ j) (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2))
    (γ : Fin N → ZMod 2) :
    fiberPhaseStar j (pb, γ + Pi.single k 1) = fiberPhaseStar j (pb, γ) := by
  rw [fiberPhaseStar, fiberPhaseStar, ← chainFlip_fiberEquiv hN,
    bondExponentStar_chainFlip_of_disjoint j k hkj hkj1 hk1j]

/-- The neighboring holonomy of the second displayed tuple in fiber coordinates:
around the square spanned by the bonds `j` and `j + 1` the phases differ by
$(-1)^{c_j(p,b)}$. -/
theorem fiberPhaseStar_holonomy (hN : 3 ≤ N) (j : Fin N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) (γ : Fin N → ZMod 2) :
    fiberPhaseStar j (pb, γ) * fiberPhaseStar (j + 1) (pb, γ + Pi.single j 1) =
      fiberPhaseStar (j + 1) (pb, γ) * fiberPhaseStar j (pb, γ + Pi.single (j + 1) 1) *
        (-1) ^ (starFiberLabel j pb).val := by
  have h2 : 2 ≤ N := by omega
  rw [fiberPhaseStar, fiberPhaseStar, fiberPhaseStar, fiberPhaseStar, ← chainFlip_fiberEquiv h2,
    ← chainFlip_fiberEquiv h2, ← iPow_add, ← iPow_add, bondExponentStar_holonomy hN j, iPow_add,
    iPow_two_mul_val, starHolonomyLabel_fiberEquiv]

theorem fiberPhaseStar_ne_zero (j : Fin N)
    (x : ((Fin N → ZMod 2) × (Fin N → ZMod 2)) × (Fin N → ZMod 2)) : fiberPhaseStar j x ≠ 0 :=
  pow_ne_zero _ Complex.I_ne_zero

/-- **Fixed spaces on the orbit fibers for the second displayed tuple.** The phases
have trivial holonomy on the fiber over $(p,b)$ exactly when $c_j(p,b)=0$ for
every bond `j`. -/
theorem isTrivialHolonomy_fiberPhaseStar_iff (hN : 3 ≤ N)
    (pb : (Fin N → ZMod 2) × (Fin N → ZMod 2)) :
    TNLean.Algebra.IsTrivialHolonomy fiberPhaseStar pb ↔ ∀ j : Fin N, starFiberLabel j pb = 0 := by
  have h2 : 2 ≤ N := by omega
  constructor
  · intro h j
    have hk := h j (j + 1) 0
    have hhol := fiberPhaseStar_holonomy hN j pb 0
    rw [hhol, mul_comm, mul_eq_right₀ (mul_ne_zero (fiberPhaseStar_ne_zero _ _)
      (fiberPhaseStar_ne_zero _ _))] at hk
    rcases TNLean.Algebra.zmod_two_eq_zero_or_one (starFiberLabel j pb) with h0 | h1
    · exact h0
    · rw [h1, show ((1 : ZMod 2)).val = 1 from rfl] at hk
      exfalso
      norm_num at hk
  · intro hc j k γ
    by_cases hkj : k = j
    · subst hkj
      rfl
    · by_cases hkj1 : k = j + 1
      · subst hkj1
        rw [fiberPhaseStar_holonomy hN j, hc j]
        simp
      · by_cases hjk1 : j = k + 1
        · subst hjk1
          rw [fiberPhaseStar_holonomy hN k, hc k]
          simp
        · rw [fiberPhaseStar_flip_of_disjoint h2 j k hkj hkj1 (Ne.symm hjk1),
            fiberPhaseStar_flip_of_disjoint h2 k j (Ne.symm hkj) hjk1 (Ne.symm hkj1),
            mul_comm]

/-! ### The placed Gauss operators of the second displayed tuple -/

/-- The local Gauss operator $G^\star$ of the second displayed tuple placed on the
bond $(j,j+1)$ of the periodic chain. -/
def placedGaussOperatorStar (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    ChainOperator (Fintype.card (Fin 4 × Multiplicative (ZMod 2))) N :=
  embedLocalOperator 2 N hN j
    (Matrix.reindexAlgEquiv ℂ ℂ windowCoordinates
      (TNLean.Algebra.gaussOperator circuitTupleStar gen))

/-- For $\mathbb Z_2$ the local Gauss projector of the second displayed tuple is
$P^\star=(\mathrm{id}+G^\star)/2$. -/
theorem gaussProjector_circuitTupleStar :
    TNLean.Algebra.gaussProjector circuitTupleStar =
      (2 : ℂ)⁻¹ • (1 + TNLean.Algebra.gaussOperator circuitTupleStar gen) := by
  rw [TNLean.Algebra.gaussProjector_eq_average, sum_multiplicative_zmod_two,
    TNLean.Algebra.gaussOperator_one, show Fintype.card (Multiplicative (ZMod 2)) = 2 by decide]
  push_cast
  rfl

/-- The placed Gauss projector of the second displayed tuple is
$\widetilde P^\star_j=(\mathrm{id}+G^\star_j)/2$. -/
theorem placedGaussProjector_circuitTupleStar (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    placedGaussProjector 4 (Multiplicative (ZMod 2)) N hN j circuitTupleStar =
      (2 : ℂ)⁻¹ • (1 + placedGaussOperatorStar N hN j) := by
  rw [placedGaussProjector, gaussWindowProjector, gaussProjector_circuitTupleStar, map_smul,
    map_add, map_one, placedGaussOperatorStar]
  change embedLocalOperatorAlgHom 2 N hN j _ = _
  rw [map_smul, map_add, map_one]
  rfl

/-- The common fixed subspace of the placed Gauss projectors of the second
displayed tuple is the common fixed subspace of the placed Gauss operators
$G^\star_j$. -/
theorem commonFixedSubmodule_placedGaussProjector_circuitTupleStar (N : ℕ) (hN : 2 ≤ N) :
    LinearMap.commonFixedSubmodule (fun j : Fin N ↦
        toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) N hN j circuitTupleStar)) =
      LinearMap.commonFixedSubmodule fun j : Fin N ↦ toLin' (placedGaussOperatorStar N hN j) := by
  ext v
  simp only [LinearMap.mem_commonFixedSubmodule_iff, toLin'_apply,
    placedGaussProjector_circuitTupleStar, inv_two_smul_add_mulVec_eq_iff]

/-- The placed Gauss operator of the second displayed tuple in monomial form. -/
theorem placedGaussOperatorStar_eq_monomial (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    placedGaussOperatorStar N hN j =
      monomial
        (windowPerm 2 hN j (windowCoordinates.symm.trans (localPerm.trans windowCoordinates)))
        fun t ↦ localPhaseStar (windowCoordinates.symm (MPSTensor.extractWindow 2 j t)) := by
  rw [placedGaussOperatorStar, gaussOperator_circuitTupleStar_gen, Matrix.coe_reindexAlgEquiv,
    reindex_monomial, embedLocalOperator_monomial]
  rfl

/-- The phase of the placed Gauss operator of the second displayed tuple is the
bond phase in bit coordinates. -/
theorem localPhaseStar_window (hN : 2 ≤ N) (j : Fin N)
    (t : Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) :
    localPhaseStar (windowCoordinates.symm (MPSTensor.extractWindow 2 j t)) =
      iPow (bondExponentStar j (chainDecode N t)) := by
  obtain ⟨hj, hj1⟩ := chainDecode_window hN j t
  rw [localPhaseStar, bondExponentStar, hj, hj1]
  rfl

/-- In fiber coordinates the placed Gauss operator of the second displayed tuple on
bond `j` is the monomial operator with the coordinate flip
$\gamma\mapsto\gamma+e_j$ and the phase $i^{q^\star_j}$. -/
theorem placedGaussOperatorStar_eq_reindex (N : ℕ) [NeZero N] (hN : 2 ≤ N) (j : Fin N) :
    placedGaussOperatorStar N hN j =
      reindex (fiberCoordinates N) (fiberCoordinates N)
        (monomial (TNLean.Algebra.fiberFlip j) (fiberPhaseStar j)) := by
  rw [placedGaussOperatorStar_eq_monomial, reindex_monomial]
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
    rw [localPhaseStar_window hN, Function.comp_apply, fiberPhaseStar, fiberCoordinates,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-! ### The finite enumeration and the two certificates -/

/-- **Reduction of the dimension to a finite count.** On a periodic chain of
$N\geq3$ blocked sites, the dimension of the common $+1$ eigenspace
$\mathcal V_N(R^\star)$ of the placed Gauss projectors of the second displayed
circuit tuple is the number of pairs $(p,b)\in\mathbb F_2^N\times\mathbb F_2^N$
satisfying $c_j(p,b)=0$ for every bond `j`.

This is a reduction, not a dimension formula: it replaces a computation on a
space of dimension $8^N$ by a count over $4^N$ label pairs. -/
theorem finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar (N : ℕ) [NeZero N]
    (hN : 3 ≤ N) :
    Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j : Fin N ↦
      toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) N (by omega) j
        circuitTupleStar)) =
      Nat.card {pb : (Fin N → ZMod 2) × (Fin N → ZMod 2) //
        ∀ j : Fin N, starFiberLabel j pb = 0} := by
  have h2 : 2 ≤ N := by omega
  rw [commonFixedSubmodule_placedGaussProjector_circuitTupleStar N h2]
  have hop : (fun j : Fin N ↦ toLin' (placedGaussOperatorStar N h2 j)) =
      fun j ↦ toLin' (reindex (fiberCoordinates N) (fiberCoordinates N)
        (monomial (TNLean.Algebra.fiberFlip j) (fiberPhaseStar j))) :=
    funext fun j ↦ by rw [placedGaussOperatorStar_eq_reindex N h2 j]
  rw [hop, TNLean.Algebra.finrank_commonFixedSubmodule_reindex (fiberCoordinates N)
    (fun j ↦ monomial (TNLean.Algebra.fiberFlip j) (fiberPhaseStar j)),
    TNLean.Algebra.finrank_commonFixedSubmodule_monomial_fiberFlip fiberPhaseStar
      (fun j s ↦ by
        obtain ⟨pb, γ⟩ := s
        rw [TNLean.Algebra.fiberFlip_apply]
        exact fiberPhaseStar_mul_fiberPhaseStar_flip h2 j pb γ)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun pb ↦ isTrivialHolonomy_fiberPhaseStar_iff hN pb)

/-- **Certificate at three sites.** On a periodic chain of three blocked sites the
common $+1$ eigenspace of the placed Gauss projectors of the second displayed
circuit tuple $R^\star=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$ has
dimension $14$.

The value is obtained by counting the $64$ label pairs
$(p,b)\in\mathbb F_2^3\times\mathbb F_2^3$ that satisfy the three holonomy
equations $c_j(p,b)=0$.

This is a certificate at one system size. It carries no asymptotic content, no
growth law may be extrapolated from it, it asserts nothing about the physical
completion class of the CZX defect data, and it gives no value for the minimum
or the maximum of the dimension over completions. -/
theorem finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar_three :
    Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j : Fin 3 ↦
      toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) 3 (by omega) j
        circuitTupleStar)) = 14 := by
  rw [finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar 3 (by omega),
    Nat.card_eq_fintype_card]
  decide

/-- **Certificate at four sites.** On a periodic chain of four blocked sites the
common $+1$ eigenspace of the placed Gauss projectors of the second displayed
circuit tuple $R^\star=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$ has
dimension $36$.

The value is obtained by counting the $256$ label pairs
$(p,b)\in\mathbb F_2^4\times\mathbb F_2^4$ that satisfy the four holonomy
equations $c_j(p,b)=0$.

This is a certificate at one system size. It carries no asymptotic content, no
growth law may be extrapolated from it, it asserts nothing about the physical
completion class of the CZX defect data, and it gives no value for the minimum
or the maximum of the dimension over completions. -/
theorem finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar_four :
    Module.finrank ℂ (LinearMap.commonFixedSubmodule fun j : Fin 4 ↦
      toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) 4 (by omega) j
        circuitTupleStar)) = 36 := by
  rw [finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar 4 (by omega),
    Nat.card_eq_fintype_card]
  decide

end MPOTensor.CZX

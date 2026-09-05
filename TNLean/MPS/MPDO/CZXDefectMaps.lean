/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import TNLean.Algebra.UnitaryCompletionClass
import TNLean.MPS.MPDO.CZXGaussCircuitTuple

/-!
# The CZX defect domains and prescribed defect maps

The modified-fusion lemma of FBC25 (arXiv:2502.20257, lines 4215--4254)
attaches to every ordered pair $(a,b)$ of gauge labels and every injective
block $x$ the two-site defect vector $v(a,b,x)=a[bx]\otimes b[x]$, the left
defect $a[bx]$ tensored with the right defect $b[x]$, and prescribes a unitary
$\tilde\lambda_{a,b}$ on the two-site matter space with
$\tilde\lambda_{a,b}v(a,b,x)=v(e,ab,x)$. For the CZX model of
arXiv:2502.20257, lines 4503--5183, the source displays the injective blocks,
the action tensors, and the single-site evaluations, but not the eight
two-site vectors, so their values, the four defect domains they span, and the
four prescribed maps are derived by finite contraction of the displayed
tensors in `docs/paper-gaps/fbc25_czx_defect_domains.tex`. This file carries
that derived data.

One blocked site carries two matter qubits and the four qubits of two
neighboring blocked sites are numbered $0,1$ on the left site and $2,3$ on the
right, matching `MPOTensor.CZX.localBits`. With $e\leftrightarrow0$ and
$g\leftrightarrow1$, the single-site defects are $e[x]=\ket{xx}$,
$g[0]=\ket{00}$, and $g[1]=-i\ket{11}$ (arXiv:2502.20257, lines 4800--4859),
whence

$v(e,e,0)=\ket{0000}$, $v(e,e,1)=\ket{1111}$,
$v(e,g,0)=\ket{1100}$, $v(e,g,1)=-i\ket{0011}$,
$v(g,e,0)=\ket{0000}$, $v(g,e,1)=-i\ket{1111}$,
$v(g,g,0)=-i\ket{1100}$, $v(g,g,1)=-i\ket{0011}$.

The four defect domains are therefore $\mathcal K_{e,e}=\mathcal K_{g,e}=
\mathcal L_0=\operatorname{span}\{\ket{0000},\ket{1111}\}$ and
$\mathcal K_{e,g}=\mathcal K_{g,g}=\mathcal L_1=
\operatorname{span}\{\ket{1100},\ket{0011}\}$, two orthogonal planes, and the
prescribed map $D_{a,b}$ is the partial isometry
$\sum_x\ket{v(e,ab,x)}\bra{v(a,b,x)}$ carrying $v(a,b,x)$ to $v(e,ab,x)$. It
is built from the defect vectors themselves, not from the displayed circuits
$w$ and $\tilde\lambda$ of `MPOTensor.CZX.w` and
`MPOTensor.CZX.tildeLambda`.

## Non-goals

* No claim that the displayed circuit tuple `MPOTensor.CZX.circuitTuple` is a
  completion of these prescribed maps.
* No general defect theory: no movement operators, no $L$-symbols, no
  associator, and no reconstruction of the domains from general fusion data.
* No dimension, minimum, or maximum statement about the gauge-invariant
  subspace of any completion.
-/

noncomputable section

namespace MPOTensor.CZX

open Matrix Complex

/-! ### Computational basis vectors of one and two blocked sites -/

/-- The computational basis vector $\ket{m_0m_1}$ of one blocked site, whose
two matter qubits are read off by `MPOTensor.CZX.siteBits`. -/
def siteKet (m₀ m₁ : ZMod 2) : Fin 4 → ℂ :=
  Pi.single (siteBits.symm (m₀, m₁)) 1

/-- The computational basis vector $\ket{x_0x_1x_2x_3}$ of the two-site matter
space, with the qubits $0,1$ on the left blocked site and $2,3$ on the right
one, as read off by `MPOTensor.CZX.localBits`. -/
def matterKet (x : Fin 4 → ZMod 2) : (Fin 2 → Fin 4) → ℂ :=
  Pi.single (localBits.symm x) 1

/-- The two-site vector obtained from a vector on the left blocked site and a
vector on the right blocked site, in that order. This is the contraction of
two neighboring defect tensors of FBC25 (arXiv:2502.20257, lines 4234--4245),
whose virtual bond has dimension one. -/
def twoSiteTensor (u v : Fin 4 → ℂ) : (Fin 2 → Fin 4) → ℂ :=
  fun i ↦ u (i 0) * v (i 1)

theorem twoSiteTensor_smul_left (c : ℂ) (u v : Fin 4 → ℂ) :
    twoSiteTensor (c • u) v = c • twoSiteTensor u v := by
  funext i
  simp only [twoSiteTensor, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem twoSiteTensor_smul_right (c : ℂ) (u v : Fin 4 → ℂ) :
    twoSiteTensor u (c • v) = c • twoSiteTensor u v := by
  funext i
  simp only [twoSiteTensor, Pi.smul_apply, smul_eq_mul]
  ring

/-- Tensoring two computational basis vectors of one blocked site gives the
computational basis vector of the two-site matter space whose first two bits
are those of the left site. -/
theorem twoSiteTensor_siteKet (m₀ m₁ m₂ m₃ : ZMod 2) :
    twoSiteTensor (siteKet m₀ m₁) (siteKet m₂ m₃) = matterKet ![m₀, m₁, m₂, m₃] := by
  have hsymm : localBits.symm ![m₀, m₁, m₂, m₃] =
      ![siteBits.symm (m₀, m₁), siteBits.symm (m₂, m₃)] := rfl
  have hcons : (∀ i : Fin 2 → Fin 4,
      (i = ![siteBits.symm (m₀, m₁), siteBits.symm (m₂, m₃)]) ↔
        (i 0 = siteBits.symm (m₀, m₁) ∧ i 1 = siteBits.symm (m₂, m₃))) := by
    intro i
    rw [funext_iff, Fin.forall_fin_two]
    simp
  funext i
  simp only [twoSiteTensor, siteKet, matterKet, hsymm, Pi.single_apply, hcons i]
  by_cases h₀ : i 0 = siteBits.symm (m₀, m₁) <;>
    by_cases h₁ : i 1 = siteBits.symm (m₂, m₃) <;> simp [h₀, h₁]

/-- Distinct computational basis vectors of the two-site matter space are
orthogonal, and each has unit length. -/
theorem star_matterKet_dotProduct_matterKet (x y : Fin 4 → ZMod 2) :
    star (matterKet x) ⬝ᵥ matterKet y = if x = y then 1 else 0 := by
  have hstar : star (matterKet x) = matterKet x := by
    funext i
    simp [matterKet, Pi.single_apply, apply_ite (star : ℂ → ℂ)]
  rw [hstar]
  simp only [matterKet, single_dotProduct, one_mul, Pi.single_apply, Equiv.apply_eq_iff_eq]

/-! ### The single-site defect vectors -/

/-- The identity defect $e[x]=\ket{xx}$: the injective block $x$ of the
once-blocked GHZ state (arXiv:2502.20257, lines 4660--4670), which the source
draws as a plain block circle wherever a fused identity defect occurs
(arXiv:2502.20257, lines 4889--5066). Derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def identityDefect (x : ZMod 2) : Fin 4 → ℂ :=
  siteKet x x

/-- The domain-wall defect $g[x]$ of arXiv:2502.20257, lines 2831--2845,
evaluated for the CZX model: $g[0]=\ket{00}$ and $g[1]=-i\ket{11}$
(arXiv:2502.20257, lines 4800--4859). Derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def flipDefect (x : ZMod 2) : Fin 4 → ℂ :=
  (if x = 1 then -I else 1) • siteKet x x

/-- The single-site defect $e[0]=\ket{00}$. -/
theorem identityDefect_zero : identityDefect 0 = siteKet 0 0 := rfl

/-- The single-site defect $e[1]=\ket{11}$. -/
theorem identityDefect_one : identityDefect 1 = siteKet 1 1 := rfl

/-- The single-site defect $g[0]=\ket{00}$ (arXiv:2502.20257, lines
4800--4859). -/
theorem flipDefect_zero : flipDefect 0 = siteKet 0 0 := by
  simp +decide [flipDefect]

/-- The single-site defect $g[1]=-i\ket{11}$ (arXiv:2502.20257, lines
4800--4859). -/
theorem flipDefect_one : flipDefect 1 = (-I) • siteKet 1 1 := by
  simp [flipDefect]

/-- The single-site defect attached to the gauge label $a$ and the injective
block $x$: the identity defect for $a=e$ and the domain-wall defect for
$a=g$. -/
def siteDefect (a : Multiplicative (ZMod 2)) (x : ZMod 2) : Fin 4 → ℂ :=
  if Multiplicative.toAdd a = 0 then identityDefect x else flipDefect x

theorem siteDefect_one (x : ZMod 2) : siteDefect 1 x = identityDefect x := by
  simp [siteDefect]

theorem siteDefect_gen (x : ZMod 2) : siteDefect gen x = flipDefect x := by
  simp +decide [siteDefect]

/-! ### The two-site defect vectors -/

/-- The two-site defect vector $v(a,b,x)=a[bx]\otimes b[x]$ of the
modified-fusion lemma of FBC25 (arXiv:2502.20257, lines 4215--4254), the left
defect $a[bx]$ tensored with the right defect $b[x]$ in that order
(arXiv:2502.20257, lines 4234--4245). Its CZX values are derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def defectVector (a b : Multiplicative (ZMod 2)) (x : ZMod 2) : (Fin 2 → Fin 4) → ℂ :=
  twoSiteTensor (siteDefect a (Multiplicative.toAdd b + x)) (siteDefect b x)

/-- $v(e,e,x)=e[x]\otimes e[x]$. -/
theorem defectVector_one_one (x : ZMod 2) :
    defectVector 1 1 x = twoSiteTensor (identityDefect x) (identityDefect x) := by
  simp [defectVector, siteDefect_one]

/-- $v(e,g,x)=e[1+x]\otimes g[x]$. -/
theorem defectVector_one_gen (x : ZMod 2) :
    defectVector 1 gen x = twoSiteTensor (identityDefect (1 + x)) (flipDefect x) := by
  simp +decide [defectVector, siteDefect_one, siteDefect_gen]

/-- $v(g,e,x)=g[x]\otimes e[x]$. -/
theorem defectVector_gen_one (x : ZMod 2) :
    defectVector gen 1 x = twoSiteTensor (flipDefect x) (identityDefect x) := by
  simp +decide [defectVector, siteDefect_one, siteDefect_gen]

/-- $v(g,g,x)=g[1+x]\otimes g[x]$. -/
theorem defectVector_gen_gen (x : ZMod 2) :
    defectVector gen gen x = twoSiteTensor (flipDefect (1 + x)) (flipDefect x) := by
  simp +decide [defectVector, siteDefect_gen]

/-- $v(e,e,0)=\ket{0000}$. -/
theorem defectVector_one_one_zero : defectVector 1 1 0 = matterKet ![0, 0, 0, 0] := by
  rw [defectVector_one_one, identityDefect_zero, twoSiteTensor_siteKet]

/-- $v(e,e,1)=\ket{1111}$. -/
theorem defectVector_one_one_one : defectVector 1 1 1 = matterKet ![1, 1, 1, 1] := by
  rw [defectVector_one_one, identityDefect_one, twoSiteTensor_siteKet]

/-- $v(e,g,0)=\ket{1100}$. -/
theorem defectVector_one_gen_zero : defectVector 1 gen 0 = matterKet ![1, 1, 0, 0] := by
  rw [defectVector_one_gen, add_zero, identityDefect_one, flipDefect_zero,
    twoSiteTensor_siteKet]

/-- $v(e,g,1)=-i\ket{0011}$. -/
theorem defectVector_one_gen_one : defectVector 1 gen 1 = (-I) • matterKet ![0, 0, 1, 1] := by
  rw [defectVector_one_gen, MPSTensor.zmod2_one_add_one, identityDefect_zero, flipDefect_one,
    twoSiteTensor_smul_right, twoSiteTensor_siteKet]

/-- $v(g,e,0)=\ket{0000}$. -/
theorem defectVector_gen_one_zero : defectVector gen 1 0 = matterKet ![0, 0, 0, 0] := by
  rw [defectVector_gen_one, identityDefect_zero, flipDefect_zero, twoSiteTensor_siteKet]

/-- $v(g,e,1)=-i\ket{1111}$. -/
theorem defectVector_gen_one_one : defectVector gen 1 1 = (-I) • matterKet ![1, 1, 1, 1] := by
  rw [defectVector_gen_one, identityDefect_one, flipDefect_one, twoSiteTensor_smul_left,
    twoSiteTensor_siteKet]

/-- $v(g,g,0)=-i\ket{1100}$. -/
theorem defectVector_gen_gen_zero : defectVector gen gen 0 = (-I) • matterKet ![1, 1, 0, 0] := by
  rw [defectVector_gen_gen, add_zero, flipDefect_one, flipDefect_zero, twoSiteTensor_smul_left,
    twoSiteTensor_siteKet]

/-- $v(g,g,1)=-i\ket{0011}$. -/
theorem defectVector_gen_gen_one : defectVector gen gen 1 = (-I) • matterKet ![0, 0, 1, 1] := by
  rw [defectVector_gen_gen, MPSTensor.zmod2_one_add_one, flipDefect_zero, flipDefect_one,
    twoSiteTensor_smul_right, twoSiteTensor_siteKet]

/-- For every label pair the two defect vectors form an orthonormal pair, the
orthogonality required by the modified-fusion lemma of FBC25
(arXiv:2502.20257, lines 4215--4254). -/
theorem star_defectVector_dotProduct_defectVector (a b : Multiplicative (ZMod 2))
    (x y : ZMod 2) :
    star (defectVector a b y) ⬝ᵥ defectVector a b x = if x = y then 1 else 0 := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
    rcases MPSTensor.zmod2_cases b with rfl | rfl <;>
    rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl <;>
      rcases TNLean.Algebra.zmod_two_eq_zero_or_one y with rfl | rfl <;>
        simp +decide [defectVector_one_one_zero, defectVector_one_one_one,
          defectVector_one_gen_zero, defectVector_one_gen_one, defectVector_gen_one_zero,
          defectVector_gen_one_one, defectVector_gen_gen_zero, defectVector_gen_gen_one,
          star_smul, smul_dotProduct, dotProduct_smul,
          star_matterKet_dotProduct_matterKet, Complex.I_mul_I]

/-! ### The defect domains -/

/-- The even target $\mathcal L_0=\operatorname{span}\{\ket{0000},\ket{1111}\}$,
the support of the defect pair with product label $e$. Its two spanning vectors
are the values of $v(e,e,x)$ derived from the tensors of arXiv:2502.20257,
lines 4660--4694 and 4800--4859, in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def evenTarget : Submodule ℂ ((Fin 2 → Fin 4) → ℂ) :=
  Submodule.span ℂ {matterKet ![0, 0, 0, 0], matterKet ![1, 1, 1, 1]}

/-- The odd target $\mathcal L_1=\operatorname{span}\{\ket{1100},\ket{0011}\}$,
the support of the defect pair with product label $g$. Its two spanning vectors
are the values of $v(e,g,x)$ derived from the tensors of arXiv:2502.20257,
lines 4660--4694 and 4800--4859, in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def oddTarget : Submodule ℂ ((Fin 2 → Fin 4) → ℂ) :=
  Submodule.span ℂ {matterKet ![1, 1, 0, 0], matterKet ![0, 0, 1, 1]}

/-- The defect domain $\mathcal K_{a,b}=\operatorname{span}\{v(a,b,x):x\}$ on
which the modified-fusion lemma of FBC25 (arXiv:2502.20257, lines 4215--4254)
constrains the fusion operator of the label pair $(a,b)$. Derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def defectDomain (a b : Multiplicative (ZMod 2)) : Submodule ℂ ((Fin 2 → Fin 4) → ℂ) :=
  Submodule.span ℂ {defectVector a b 0, defectVector a b 1}

/-- Rescaling the first generator of a plane by a nonzero scalar leaves the
plane unchanged. -/
theorem span_pair_smul_left {u v : (Fin 2 → Fin 4) → ℂ} {c : ℂ} (hc : c ≠ 0) :
    Submodule.span ℂ {c • u, v} = Submodule.span ℂ {u, v} := by
  rw [Submodule.span_insert, Submodule.span_insert,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

/-- Rescaling the second generator of a plane by a nonzero scalar leaves the
plane unchanged. -/
theorem span_pair_smul_right {u v : (Fin 2 → Fin 4) → ℂ} {c : ℂ} (hc : c ≠ 0) :
    Submodule.span ℂ {u, c • v} = Submodule.span ℂ {u, v} := by
  rw [Submodule.span_insert, Submodule.span_insert,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

/-- $\mathcal K_{e,e}=\mathcal L_0$. -/
theorem defectDomain_one_one : defectDomain 1 1 = evenTarget := by
  rw [defectDomain, defectVector_one_one_zero, defectVector_one_one_one, evenTarget]

/-- $\mathcal K_{g,e}=\mathcal L_0$. -/
theorem defectDomain_gen_one : defectDomain gen 1 = evenTarget := by
  rw [defectDomain, defectVector_gen_one_zero, defectVector_gen_one_one,
    span_pair_smul_right (neg_ne_zero.mpr I_ne_zero), evenTarget]

/-- $\mathcal K_{e,g}=\mathcal L_1$. -/
theorem defectDomain_one_gen : defectDomain 1 gen = oddTarget := by
  rw [defectDomain, defectVector_one_gen_zero, defectVector_one_gen_one,
    span_pair_smul_right (neg_ne_zero.mpr I_ne_zero), oddTarget]

/-- $\mathcal K_{g,g}=\mathcal L_1$. -/
theorem defectDomain_gen_gen : defectDomain gen gen = oddTarget := by
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
  rw [defectDomain, defectVector_gen_gen_zero, defectVector_gen_gen_one,
    span_pair_smul_left hI, span_pair_smul_right hI, oddTarget]

/-- The defect domain depends only on the right label: it is the even target
for $b=e$ and the odd target for $b=g$. -/
theorem defectDomain_eq (a b : Multiplicative (ZMod 2)) :
    defectDomain a b = if Multiplicative.toAdd b = 0 then evenTarget else oddTarget := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
    rcases MPSTensor.zmod2_cases b with rfl | rfl <;>
    simp +decide [defectDomain_one_one, defectDomain_one_gen, defectDomain_gen_one,
      defectDomain_gen_gen]

/-- The even and odd targets are orthogonal. -/
theorem star_dotProduct_eq_zero_of_mem_evenTarget_of_mem_oddTarget
    {ξ η : (Fin 2 → Fin 4) → ℂ} (hξ : ξ ∈ evenTarget) (hη : η ∈ oddTarget) :
    star ξ ⬝ᵥ η = 0 := by
  rw [evenTarget, Submodule.mem_span_pair] at hξ
  rw [oddTarget, Submodule.mem_span_pair] at hη
  obtain ⟨s, t, rfl⟩ := hξ
  obtain ⟨p, q, rfl⟩ := hη
  simp +decide [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, star_matterKet_dotProduct_matterKet]

/-- Two distinct computational basis vectors of the two-site matter space are
linearly independent. -/
theorem linearIndependent_matterKet_pair {x y : Fin 4 → ZMod 2} (hxy : x ≠ y) :
    LinearIndependent ℂ ![matterKet x, matterKet y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrArg (fun v ↦ star (matterKet x) ⬝ᵥ v) hst
    simpa [dotProduct_add, dotProduct_smul, star_matterKet_dotProduct_matterKet, hxy] using h
  · have h := congrArg (fun v ↦ star (matterKet y) ⬝ᵥ v) hst
    simpa [dotProduct_add, dotProduct_smul, star_matterKet_dotProduct_matterKet,
      Ne.symm hxy] using h

theorem finrank_evenTarget : Module.finrank ℂ evenTarget = 2 := by
  have hli : LinearIndependent ℂ ![matterKet ![0, 0, 0, 0], matterKet ![1, 1, 1, 1]] :=
    linearIndependent_matterKet_pair (by decide)
  have hrange : Set.range ![matterKet ![0, 0, 0, 0], matterKet ![1, 1, 1, 1]] =
      {matterKet ![0, 0, 0, 0], matterKet ![1, 1, 1, 1]} :=
    Matrix.range_cons_cons_empty _ _ _
  rw [evenTarget, ← hrange, finrank_span_eq_card hli]
  simp

theorem finrank_oddTarget : Module.finrank ℂ oddTarget = 2 := by
  have hli : LinearIndependent ℂ ![matterKet ![1, 1, 0, 0], matterKet ![0, 0, 1, 1]] :=
    linearIndependent_matterKet_pair (by decide)
  have hrange : Set.range ![matterKet ![1, 1, 0, 0], matterKet ![0, 0, 1, 1]] =
      {matterKet ![1, 1, 0, 0], matterKet ![0, 0, 1, 1]} :=
    Matrix.range_cons_cons_empty _ _ _
  rw [oddTarget, ← hrange, finrank_span_eq_card hli]
  simp

/-- Every CZX defect domain is a plane. -/
theorem finrank_defectDomain (a b : Multiplicative (ZMod 2)) :
    Module.finrank ℂ (defectDomain a b) = 2 := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl <;>
    rcases MPSTensor.zmod2_cases b with rfl | rfl
  · rw [defectDomain_one_one]
    exact finrank_evenTarget
  · rw [defectDomain_one_gen]
    exact finrank_oddTarget
  · rw [defectDomain_gen_one]
    exact finrank_evenTarget
  · rw [defectDomain_gen_gen]
    exact finrank_oddTarget

/-! ### The prescribed defect maps -/

/-- The prescribed defect map
$D_{a,b}=\sum_x\ket{v(e,ab,x)}\bra{v(a,b,x)}$ of the modified-fusion lemma of
FBC25 (arXiv:2502.20257, lines 4215--4254), the partial isometry carrying
$v(a,b,x)$ to $v(e,ab,x)$. It is assembled from the defect vectors derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`, not from the displayed
circuits of arXiv:2502.20257, lines 4860--5013 and 5179--5183. -/
def prescribedMap (a b : Multiplicative (ZMod 2)) :
    Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ :=
  vecMulVec (defectVector 1 (a * b) 0) (star (defectVector a b 0)) +
    vecMulVec (defectVector 1 (a * b) 1) (star (defectVector a b 1))

/-- `Matrix.vecMulVec_mulVec` with the scalar of the commutative field ℂ in
place of its opposite. -/
theorem vecMulVec_mulVec_eq_smul (u v w : (Fin 2 → Fin 4) → ℂ) :
    vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  rw [Matrix.vecMulVec_mulVec]
  funext i
  simp [MulOpposite.smul_eq_mul_unop, mul_comm]

theorem star_prescribedMap (a b : Multiplicative (ZMod 2)) :
    star (prescribedMap a b) =
      vecMulVec (defectVector a b 0) (star (defectVector 1 (a * b) 0)) +
        vecMulVec (defectVector a b 1) (star (defectVector 1 (a * b) 1)) := by
  simp [prescribedMap, Matrix.star_eq_conjTranspose, conjTranspose_vecMulVec]

/-- The prescribed map carries each defect vector of its label pair to the
defect vector of the product label, which is the prescription
$\tilde\lambda_{a,b}v(a,b,x)=v(e,ab,x)$ of FBC25 (arXiv:2502.20257, lines
4215--4254). -/
theorem prescribedMap_mulVec_defectVector (a b : Multiplicative (ZMod 2)) (x : ZMod 2) :
    prescribedMap a b *ᵥ defectVector a b x = defectVector 1 (a * b) x := by
  rw [prescribedMap, add_mulVec, vecMulVec_mulVec_eq_smul, vecMulVec_mulVec_eq_smul,
    star_defectVector_dotProduct_defectVector, star_defectVector_dotProduct_defectVector]
  rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl <;> simp +decide

theorem star_prescribedMap_mulVec_defectVector (a b : Multiplicative (ZMod 2)) (x : ZMod 2) :
    star (prescribedMap a b) *ᵥ defectVector 1 (a * b) x = defectVector a b x := by
  rw [star_prescribedMap, add_mulVec, vecMulVec_mulVec_eq_smul, vecMulVec_mulVec_eq_smul,
    star_defectVector_dotProduct_defectVector, star_defectVector_dotProduct_defectVector]
  rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl <;> simp +decide

theorem starMul_prescribedMap_mulVec_defectVector (a b : Multiplicative (ZMod 2))
    (x : ZMod 2) :
    (star (prescribedMap a b) * prescribedMap a b) *ᵥ defectVector a b x =
      defectVector a b x := by
  rw [← Matrix.mulVec_mulVec, prescribedMap_mulVec_defectVector,
    star_prescribedMap_mulVec_defectVector]

/-- The prescribed map is an isometry on its defect domain. -/
theorem isometry_on_defectDomain (a b : Multiplicative (ZMod 2)) :
    ∀ ξ ∈ defectDomain a b,
      (star (prescribedMap a b) * prescribedMap a b) *ᵥ ξ = ξ := by
  intro ξ hξ
  rw [defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [mulVec_add, mulVec_smul, mulVec_smul, starMul_prescribedMap_mulVec_defectVector,
    starMul_prescribedMap_mulVec_defectVector]

/-- The prescribed map carries its defect domain into the domain of the
product label. -/
theorem prescribedMap_mem_defectDomain (a b : Multiplicative (ZMod 2)) :
    ∀ ξ ∈ defectDomain a b, prescribedMap a b *ᵥ ξ ∈ defectDomain 1 (a * b) := by
  intro ξ hξ
  rw [defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [mulVec_add, mulVec_smul, mulVec_smul, prescribedMap_mulVec_defectVector,
    prescribedMap_mulVec_defectVector]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-! ### The prescribed maps in the computational basis -/

/-- $D_{e,e}$ is the identity on the even target. -/
theorem prescribedMap_one_one_mulVec (ξ : (Fin 2 → Fin 4) → ℂ) (hξ : ξ ∈ evenTarget) :
    prescribedMap 1 1 *ᵥ ξ = ξ := by
  rw [← defectDomain_one_one, defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [mulVec_add, mulVec_smul, mulVec_smul, prescribedMap_mulVec_defectVector,
    prescribedMap_mulVec_defectVector, mul_one]

/-- $D_{e,g}$ is the identity on the odd target. -/
theorem prescribedMap_one_gen_mulVec (ξ : (Fin 2 → Fin 4) → ℂ) (hξ : ξ ∈ oddTarget) :
    prescribedMap 1 gen *ᵥ ξ = ξ := by
  rw [← defectDomain_one_gen, defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [mulVec_add, mulVec_smul, mulVec_smul, prescribedMap_mulVec_defectVector,
    prescribedMap_mulVec_defectVector, one_mul]

/-- $D_{g,e}\ket{0000}=\ket{1100}$. -/
theorem prescribedMap_gen_one_mulVec_zero :
    prescribedMap gen 1 *ᵥ matterKet ![0, 0, 0, 0] = matterKet ![1, 1, 0, 0] := by
  have h := prescribedMap_mulVec_defectVector gen 1 0
  rwa [defectVector_gen_one_zero, mul_one, defectVector_one_gen_zero] at h

/-- $D_{g,e}\ket{1111}=\ket{0011}$. -/
theorem prescribedMap_gen_one_mulVec_one :
    prescribedMap gen 1 *ᵥ matterKet ![1, 1, 1, 1] = matterKet ![0, 0, 1, 1] := by
  have h := prescribedMap_mulVec_defectVector gen 1 1
  rw [defectVector_gen_one_one, mul_one, defectVector_one_gen_one, mulVec_smul] at h
  have h' := congrArg (fun v ↦ (I : ℂ) • v) h
  simpa [smul_smul, Complex.I_mul_I] using h'

/-- $D_{g,g}\ket{1100}=i\ket{0000}$. -/
theorem prescribedMap_gen_gen_mulVec_zero :
    prescribedMap gen gen *ᵥ matterKet ![1, 1, 0, 0] = I • matterKet ![0, 0, 0, 0] := by
  have h := prescribedMap_mulVec_defectVector gen gen 0
  rw [defectVector_gen_gen_zero, gen_mul_gen, defectVector_one_one_zero, mulVec_smul] at h
  have h' := congrArg (fun v ↦ (I : ℂ) • v) h
  simpa [smul_smul, Complex.I_mul_I] using h'

/-- $D_{g,g}\ket{0011}=i\ket{1111}$. -/
theorem prescribedMap_gen_gen_mulVec_one :
    prescribedMap gen gen *ᵥ matterKet ![0, 0, 1, 1] = I • matterKet ![1, 1, 1, 1] := by
  have h := prescribedMap_mulVec_defectVector gen gen 1
  rw [defectVector_gen_gen_one, gen_mul_gen, defectVector_one_one_one, mulVec_smul] at h
  have h' := congrArg (fun v ↦ (I : ℂ) • v) h
  simpa [smul_smul, Complex.I_mul_I] using h'

/-! ### The prescribed defect maps of the CZX model -/

/-- The prescribed defect maps of the CZX model: the four defect domains and
the four prescribed defect maps derived from the tensors displayed in FBC25
(arXiv:2502.20257, lines 4503--5183) in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
def defectMaps : TNLean.Algebra.DefectMaps (Multiplicative (ZMod 2)) (Fin 2 → Fin 4) where
  domain := defectDomain
  prescribed := prescribedMap
  isometry_on_domain := isometry_on_defectDomain

@[simp]
theorem defectMaps_domain (a b : Multiplicative (ZMod 2)) :
    defectMaps.domain a b = defectDomain a b := rfl

@[simp]
theorem defectMaps_prescribed (a b : Multiplicative (ZMod 2)) :
    defectMaps.prescribed a b = prescribedMap a b := rfl

end MPOTensor.CZX

end

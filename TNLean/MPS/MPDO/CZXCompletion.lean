/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CZXDefectMaps
import TNLean.MPS.MPDO.CZXGaussInvariantSubspace
import TNLean.MPS.MPDO.CZXSecondTupleCertificate
import TNLean.MPS.MPDO.GaugeInvariantSubspace

/-!
# The displayed CZX tuples are completions, and the supremum over their class

The displayed CZX circuit tuple
$R^{\mathrm{CZX}}=(\mathrm{id},\mathrm{id},w,\tilde\lambda)$ of
arXiv:2502.20257, lines 4503--5183, restricted to the four defect domains of
the CZX model, is exactly the family of prescribed defect maps: the four
displayed operators satisfy the eight fusion identities

$\mathrm{id}\,v(e,b,x)=v(e,b,x)$ for both labels $b$ and both blocks $x$,
$w\,v(g,e,0)=v(e,g,0)$, $w\,v(g,e,1)=v(e,g,1)$,
$\tilde\lambda\,v(g,g,0)=v(e,e,0)$, $\tilde\lambda\,v(g,g,1)=v(e,e,1)$,

which are the prescription $\tilde\lambda_{a,b}v(a,b,x)=v(e,ab,x)$ of the
modified-fusion lemma of FBC25 (arXiv:2502.20257, lines 4215--4254). Since the
two defect vectors of a label pair span its defect domain, the tuple belongs to
the full completion class of the CZX prescribed defect maps. Combined with the
exact dimension $2^N$ of the gauge-invariant subspace of that tuple, the
supremum of the gauge-invariant dimension over the whole completion class is at
least $2^N$ for every $N\geq3$.

The four displayed operators are read on the computational basis through the
phase tables $w\ket{x}=(-1)^{e(x)}\ket{\overline x}$ and
$\tilde\lambda\ket{x}=-i(-1)^{f(x)}\ket{\overline x}$ of
`MPOTensor.CZX.w_eq` and `MPOTensor.CZX.tildeLambda_eq`, evaluated at the four
computational basis states $\ket{0000}$, $\ket{1111}$, $\ket{1100}$, and
$\ket{0011}$ that carry the eight defect vectors, giving
$w\ket{0000}=\ket{1100}$, $w\ket{1111}=\ket{0011}$,
$\tilde\lambda\ket{1100}=i\ket{0000}$, and
$\tilde\lambda\ket{0011}=i\ket{1111}$.

The defect domains and prescribed maps are derived from the displayed tensors
in `docs/paper-gaps/fbc25_czx_defect_domains.tex`, whose section "The displayed
fusion operators restrict to the prescribed maps" contains the same eight
identities in mathematical form.

The second displayed tuple
$R^\star=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$ of the same source
passage is a completion as well. Its first three operators are those of
$R^{\mathrm{CZX}}$, and the diagonal factor $R_\star$ fixes the plane
$\operatorname{span}\{\ket{1100},\ket{0011}\}$ pointwise, which is the defect
domain of the label pair $(g,g)$, so the fourth operator has the prescribed
action there too. Its gauge-invariant dimensions $14$ at three sites and $36$
at four sites are therefore values of the dimension on the completion class,
and each bounds the supremum over the class from below at that chain length.

## What is and is not claimed

The two memberships and the lower bounds are unconditional. They settle what
the earlier development left undecided: the displayed matrices alone do not
exhibit a tuple as a member of a full completion class, since the source
displays only the defect map of the pair $(g,g)$, and the dimension theorems
are each stated for one displayed tuple in isolation. The defect maps derived
from the displayed tensors supply what is missing, and the theorems here make
the identification.

Nothing is claimed here about the minimum of the gauge-invariant dimension over
the completion class, about the exact value of its supremum, or about which
completion attains that supremum. Those are questions about this completion
class, not questions the source raises; they are tracked in the development.
Nor is anything claimed about the behaviour of the dimension as the chain
length grows, which is the question the source leaves open
(arXiv:2502.20257, lines 5198--5204).
-/

noncomputable section

namespace MPOTensor.CZX

open Matrix Complex

/-! ### Monomial operators on computational basis vectors -/

/-- A monomial four-qubit operator transported to the two-site matter space
sends a computational basis vector to a phase times the permuted computational
basis vector. -/
theorem matterMatrix_monomial_mulVec_matterKet (σ : Equiv.Perm (Fin 4 → ZMod 2))
    (φ : (Fin 4 → ZMod 2) → ℂ) (x : Fin 4 → ZMod 2) :
    matterMatrix (monomial σ φ) *ᵥ matterKet x = φ x • matterKet (σ x) := by
  rw [matterMatrix_monomial, matterKet, monomial_mulVec_single]
  simp [matterKet]

/-- The movement operator on a computational basis vector:
$w\ket{x}=(-1)^{e(x)}\ket{\overline x}$ transported to the two-site matter
space. -/
theorem matterMatrix_w_mulVec_matterKet (x : Fin 4 → ZMod 2) :
    matterMatrix w *ᵥ matterKet x =
      ((-1 : ℂ) ^ (eExponent x).val) • matterKet (barFlip x) := by
  rw [w_eq, matterMatrix_monomial_mulVec_matterKet]

/-- The modified fusion operator on a computational basis vector:
$\tilde\lambda\ket{x}=-i(-1)^{f(x)}\ket{\overline x}$ transported to the
two-site matter space. -/
theorem matterMatrix_tildeLambda_mulVec_matterKet (x : Fin 4 → ZMod 2) :
    matterMatrix tildeLambda *ᵥ matterKet x =
      (-I * (-1 : ℂ) ^ (fExponent x).val) • matterKet (barFlip x) := by
  rw [tildeLambda_eq, matterMatrix_monomial_mulVec_matterKet]

/-- $w\ket{0000}=\ket{1100}$. -/
theorem matterMatrix_w_mulVec_matterKet_zero :
    matterMatrix w *ᵥ matterKet ![0, 0, 0, 0] = matterKet ![1, 1, 0, 0] := by
  have hperm : barFlip ![0, 0, 0, 0] = ![1, 1, 0, 0] := by decide
  have hphase : eExponent ![0, 0, 0, 0] = 0 := by decide
  rw [matterMatrix_w_mulVec_matterKet, hperm, hphase]
  simp

/-- $w\ket{1111}=\ket{0011}$. -/
theorem matterMatrix_w_mulVec_matterKet_one :
    matterMatrix w *ᵥ matterKet ![1, 1, 1, 1] = matterKet ![0, 0, 1, 1] := by
  have hperm : barFlip ![1, 1, 1, 1] = ![0, 0, 1, 1] := by decide
  have hphase : eExponent ![1, 1, 1, 1] = 0 := by decide
  rw [matterMatrix_w_mulVec_matterKet, hperm, hphase]
  simp

/-- $\tilde\lambda\ket{1100}=i\ket{0000}$. -/
theorem matterMatrix_tildeLambda_mulVec_matterKet_zero :
    matterMatrix tildeLambda *ᵥ matterKet ![1, 1, 0, 0] = I • matterKet ![0, 0, 0, 0] := by
  have hperm : barFlip ![1, 1, 0, 0] = ![0, 0, 0, 0] := by decide
  have hphase : fExponent ![1, 1, 0, 0] = 1 := by decide
  rw [matterMatrix_tildeLambda_mulVec_matterKet, hperm, hphase]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]

/-- $\tilde\lambda\ket{0011}=i\ket{1111}$. -/
theorem matterMatrix_tildeLambda_mulVec_matterKet_one :
    matterMatrix tildeLambda *ᵥ matterKet ![0, 0, 1, 1] = I • matterKet ![1, 1, 1, 1] := by
  have hperm : barFlip ![0, 0, 1, 1] = ![1, 1, 1, 1] := by decide
  have hphase : fExponent ![0, 0, 1, 1] = 1 := by decide
  rw [matterMatrix_tildeLambda_mulVec_matterKet, hperm, hphase]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]

/-! ### The eight fusion identities of the displayed tuple -/

/-- The four trivial fusion identities: for the left label $e$ the displayed
operator is the identity, and the defect vector of $(e,b)$ is already the
defect vector of the product label. These are the trivial cases
$\lambda^R_{e,e}=\lambda^R_{e,g}=\mathrm{id}$ of arXiv:2502.20257, lines
3331--3340. -/
theorem circuitTuple_one_mulVec_defectVector (b : Multiplicative (ZMod 2)) (x : ZMod 2) :
    (circuitTuple 1 b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ defectVector 1 b x =
      defectVector 1 (1 * b) x := by
  rw [circuitTuple_one, one_mul]
  simp

/-- The first movement identity $w\,v(g,e,0)=v(e,g,0)$ of arXiv:2502.20257,
lines 4889--4988, derived in `docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
theorem circuitTuple_gen_one_mulVec_defectVector_zero :
    (circuitTuple gen 1 : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ defectVector gen 1 0 =
      defectVector 1 gen 0 := by
  rw [circuitTuple_gen_one, defectVector_gen_one_zero, matterMatrix_w_mulVec_matterKet_zero,
    defectVector_one_gen_zero]

/-- The second movement identity $w\,v(g,e,1)=v(e,g,1)$ of arXiv:2502.20257,
lines 4889--4988, derived in `docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
theorem circuitTuple_gen_one_mulVec_defectVector_one :
    (circuitTuple gen 1 : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ defectVector gen 1 1 =
      defectVector 1 gen 1 := by
  rw [circuitTuple_gen_one, defectVector_gen_one_one, mulVec_smul,
    matterMatrix_w_mulVec_matterKet_one, defectVector_one_gen_one]

/-- The first modified fusion identity $\tilde\lambda\,v(g,g,0)=v(e,e,0)$,
the modification $\tilde\lambda^R_{g,g}=\lambda^R_{g,g}Z_1$ of
arXiv:2502.20257, lines 5179--5183, applied to the defect vector; derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
theorem circuitTuple_gen_gen_mulVec_defectVector_zero :
    (circuitTuple gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ
        defectVector gen gen 0 =
      defectVector 1 1 0 := by
  rw [circuitTuple_gen_gen, defectVector_gen_gen_zero, mulVec_smul,
    matterMatrix_tildeLambda_mulVec_matterKet_zero, defectVector_one_one_zero, smul_smul,
    neg_mul, I_mul_I, neg_neg, one_smul]

/-- The second modified fusion identity $\tilde\lambda\,v(g,g,1)=v(e,e,1)$,
the modification $\tilde\lambda^R_{g,g}=\lambda^R_{g,g}Z_1$ of
arXiv:2502.20257, lines 5179--5183, applied to the defect vector; derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
theorem circuitTuple_gen_gen_mulVec_defectVector_one :
    (circuitTuple gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ
        defectVector gen gen 1 =
      defectVector 1 1 1 := by
  rw [circuitTuple_gen_gen, defectVector_gen_gen_one, mulVec_smul,
    matterMatrix_tildeLambda_mulVec_matterKet_one, defectVector_one_one_one, smul_smul,
    neg_mul, I_mul_I, neg_neg, one_smul]

/-- Every displayed operator carries every defect vector of its label pair to
the defect vector of the product label, which is the prescription
$\tilde\lambda_{a,b}v(a,b,x)=v(e,ab,x)$ of the modified-fusion lemma of FBC25
(arXiv:2502.20257, lines 4215--4254). -/
theorem circuitTuple_mulVec_defectVector (a b : Multiplicative (ZMod 2)) (x : ZMod 2) :
    (circuitTuple a b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ defectVector a b x =
      defectVector 1 (a * b) x := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl
  · exact circuitTuple_one_mulVec_defectVector b x
  · rcases MPSTensor.zmod2_cases b with rfl | rfl
    · rw [mul_one]
      rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl
      · exact circuitTuple_gen_one_mulVec_defectVector_zero
      · exact circuitTuple_gen_one_mulVec_defectVector_one
    · rw [gen_mul_gen]
      rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl
      · exact circuitTuple_gen_gen_mulVec_defectVector_zero
      · exact circuitTuple_gen_gen_mulVec_defectVector_one

/-! ### Membership in the full completion class -/

/-- **The displayed CZX circuit tuple is a completion.** The four displayed
operators $(\mathrm{id},\mathrm{id},w,\tilde\lambda)$ of arXiv:2502.20257,
lines 4503--5183, agree on every defect domain with the prescribed defect map
of that label pair.

This is unconditional: it replaces the reservation recorded in the docstrings
of `MPOTensor.CZX.circuitTuple` and
`MPOTensor.CZX.finrank_commonFixedSubmodule_placedGaussProjector_circuitTuple`,
where the identification of the displayed tuple with a member of a full
physical completion class was withheld pending the four defect domains and
maps. Those are supplied by `MPOTensor.CZX.defectMaps`, derived from the
displayed tensors in `docs/paper-gaps/fbc25_czx_defect_domains.tex`. -/
theorem isCompletion_circuitTuple : defectMaps.IsCompletion circuitTuple := by
  intro a b ξ hξ
  rw [defectMaps_domain, defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [defectMaps_prescribed, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
    mulVec_smul, circuitTuple_mulVec_defectVector, circuitTuple_mulVec_defectVector,
    prescribedMap_mulVec_defectVector, prescribedMap_mulVec_defectVector]

/-- The displayed CZX circuit tuple belongs to the full completion class of the
CZX prescribed defect maps. -/
theorem circuitTuple_mem_completionClass : circuitTuple ∈ defectMaps.completionClass :=
  defectMaps.mem_completionClass_iff.mpr isCompletion_circuitTuple

/-! ### A lower bound on the supremum over the completion class -/

/-- The gauge-invariant dimensions of the members of the CZX completion class
are bounded above by the dimension of the whole chain space, so their supremum
is finite. Attainment of the supremum by a particular completion is not
asserted. -/
theorem bddAbove_range_finrank_gaugeInvariantSubspace (N : ℕ) (hN : 2 ≤ N) :
    BddAbove (Set.range fun R ↦ ⨆ _ : R ∈ defectMaps.completionClass,
      Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) N hN R)) := by
  refine ⟨Module.finrank ℂ
    ((Fin N → Fin (Fintype.card (Fin 4 × Multiplicative (ZMod 2)))) → ℂ), ?_⟩
  rintro _ ⟨R, rfl⟩
  exact ciSup_le' fun _ ↦ Submodule.finrank_le _

/-- The gauge-invariant dimension of any member of the CZX completion class is
at most the supremum of that dimension over the class. -/
theorem finrank_gaugeInvariantSubspace_le_iSup_completionClass {N : ℕ} (hN : 2 ≤ N)
    {R : Multiplicative (ZMod 2) → Multiplicative (ZMod 2) →
      Matrix.unitaryGroup (Fin 2 → Fin 4) ℂ} (hR : R ∈ defectMaps.completionClass) :
    Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) N hN R) ≤
      ⨆ S ∈ defectMaps.completionClass,
        Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) N hN S) := by
  refine le_ciSup_of_le (bddAbove_range_finrank_gaugeInvariantSubspace N hN) R ?_
  rw [ciSup_pos hR]

/-- **The supremum of the gauge-invariant dimension over the CZX completion
class is at least $2^N$.** On a periodic chain of $N\geq3$ blocked sites, the
displayed circuit tuple lies in the completion class of the CZX prescribed
defect maps and its gauge-invariant subspace has dimension $2^N$, so the
supremum over the class is at least $2^N$.

This is unconditional, where the same bound was previously available only
conditionally on the displayed tuple being a completion. It claims nothing
about the minimum of the dimension over the class, nothing about the exact
value of the supremum, and nothing about which completion attains it; those are
questions about this completion class rather than questions the source raises.
Nor does it claim anything about the behaviour of the dimension in the chain
length, which is the question the source leaves open (arXiv:2502.20257, lines
5198--5204). The defect domains and maps entering the class are derived in
`docs/paper-gaps/fbc25_czx_defect_domains.tex`.

The dimension of the gauge-invariant subspace of the displayed tuple is the one
computed in `MPOTensor.CZX.finrank_gaugeInvariantSubspace_circuitTuple`. -/
theorem two_pow_le_iSup_finrank_gaugeInvariantSubspace_completionClass {N : ℕ} (hN : 3 ≤ N) :
    2 ^ N ≤ ⨆ R ∈ defectMaps.completionClass,
      Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) N
        (Nat.le_of_succ_le hN) R) := by
  rw [← finrank_gaugeInvariantSubspace_circuitTuple N hN]
  exact finrank_gaugeInvariantSubspace_le_iSup_completionClass (Nat.le_of_succ_le hN)
    circuitTuple_mem_completionClass

/-! ### The second displayed tuple is a completion -/

/-- $\tilde\lambda R_\star\ket{1100}=i\ket{0000}$: the diagonal factor
$R_\star$ acts trivially on $\ket{1100}$, so the modified fusion operator of the
second displayed tuple has the same value there as that of the first. -/
theorem matterMatrix_tildeLambdaStar_mulVec_matterKet_zero :
    matterMatrix tildeLambdaStar *ᵥ matterKet ![1, 1, 0, 0] = I • matterKet ![0, 0, 0, 0] := by
  have hperm : barFlip ![1, 1, 0, 0] = ![0, 0, 0, 0] := by decide
  have hphase : fExponent ![1, 1, 0, 0] + rStarExponent ![1, 1, 0, 0] = 1 := by decide
  rw [tildeLambdaStar_eq, matterMatrix_monomial_mulVec_matterKet, hperm, hphase]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]

/-- $\tilde\lambda R_\star\ket{0011}=i\ket{1111}$. -/
theorem matterMatrix_tildeLambdaStar_mulVec_matterKet_one :
    matterMatrix tildeLambdaStar *ᵥ matterKet ![0, 0, 1, 1] = I • matterKet ![1, 1, 1, 1] := by
  have hperm : barFlip ![0, 0, 1, 1] = ![1, 1, 1, 1] := by decide
  have hphase : fExponent ![0, 0, 1, 1] + rStarExponent ![0, 0, 1, 1] = 1 := by decide
  rw [tildeLambdaStar_eq, matterMatrix_monomial_mulVec_matterKet, hperm, hphase]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]

/-- The first modified fusion identity of the second displayed tuple,
$\tilde\lambda R_\star\,v(g,g,0)=v(e,e,0)$. -/
theorem circuitTupleStar_gen_gen_mulVec_defectVector_zero :
    (circuitTupleStar gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ
        defectVector gen gen 0 =
      defectVector 1 1 0 := by
  rw [circuitTupleStar_gen_gen, defectVector_gen_gen_zero, mulVec_smul,
    matterMatrix_tildeLambdaStar_mulVec_matterKet_zero, defectVector_one_one_zero, smul_smul,
    neg_mul, I_mul_I, neg_neg, one_smul]

/-- The second modified fusion identity of the second displayed tuple,
$\tilde\lambda R_\star\,v(g,g,1)=v(e,e,1)$. -/
theorem circuitTupleStar_gen_gen_mulVec_defectVector_one :
    (circuitTupleStar gen gen : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ
        defectVector gen gen 1 =
      defectVector 1 1 1 := by
  rw [circuitTupleStar_gen_gen, defectVector_gen_gen_one, mulVec_smul,
    matterMatrix_tildeLambdaStar_mulVec_matterKet_one, defectVector_one_one_one, smul_smul,
    neg_mul, I_mul_I, neg_neg, one_smul]

/-- Every operator of the second displayed tuple carries every defect vector of
its label pair to the defect vector of the product label. The three operators
other than the one of the pair $(g,g)$ are those of the first displayed
tuple. -/
theorem circuitTupleStar_mulVec_defectVector (a b : Multiplicative (ZMod 2)) (x : ZMod 2) :
    (circuitTupleStar a b : Matrix (Fin 2 → Fin 4) (Fin 2 → Fin 4) ℂ) *ᵥ defectVector a b x =
      defectVector 1 (a * b) x := by
  rcases MPSTensor.zmod2_cases a with rfl | rfl
  · rw [circuitTupleStar_one, one_mul]
    simp
  · rcases MPSTensor.zmod2_cases b with rfl | rfl
    · rw [circuitTupleStar_gen_one, ← circuitTuple_gen_one]
      exact circuitTuple_mulVec_defectVector gen 1 x
    · rw [gen_mul_gen]
      rcases TNLean.Algebra.zmod_two_eq_zero_or_one x with rfl | rfl
      · exact circuitTupleStar_gen_gen_mulVec_defectVector_zero
      · exact circuitTupleStar_gen_gen_mulVec_defectVector_one

/-- **The second displayed CZX circuit tuple is a completion.** The tuple
$R^\star=(\mathrm{id},\mathrm{id},w,\tilde\lambda R_\star)$ of arXiv:2502.20257,
lines 4503--5183, agrees on every defect domain with the prescribed defect map
of that label pair. Its first three operators are those of the first displayed
tuple, and the diagonal factor $R_\star$ fixes the defect domain of the pair
$(g,g)$ pointwise. -/
theorem isCompletion_circuitTupleStar : defectMaps.IsCompletion circuitTupleStar := by
  intro a b ξ hξ
  rw [defectMaps_domain, defectDomain, Submodule.mem_span_pair] at hξ
  obtain ⟨s, t, rfl⟩ := hξ
  rw [defectMaps_prescribed, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
    mulVec_smul, circuitTupleStar_mulVec_defectVector, circuitTupleStar_mulVec_defectVector,
    prescribedMap_mulVec_defectVector, prescribedMap_mulVec_defectVector]

/-- The second displayed CZX circuit tuple belongs to the full completion class
of the CZX prescribed defect maps. -/
theorem circuitTupleStar_mem_completionClass :
    circuitTupleStar ∈ defectMaps.completionClass :=
  defectMaps.mem_completionClass_iff.mpr isCompletion_circuitTupleStar

/-! ### Two further values of the dimension on the completion class -/

/-- The gauge-invariant subspace of the second displayed tuple has dimension
$14$ at three sites. This is the certificate of
`MPOTensor.CZX.finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar_three`
in the spelling of `MPOTensor.gaugeInvariantSubspace`; the two spellings of the
subspace are definitionally equal. -/
theorem finrank_gaugeInvariantSubspace_circuitTupleStar_three :
    Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 3 (by omega)
      circuitTupleStar) = 14 := by
  have hsubspace : gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 3 (by omega)
      circuitTupleStar =
      LinearMap.commonFixedSubmodule fun j : Fin 3 ↦
        toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) 3 (by omega) j
          circuitTupleStar) := by
    simp only [gaugeInvariantSubspace, Matrix.toLin'_apply']
  rw [hsubspace]
  exact finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar_three

/-- The gauge-invariant subspace of the second displayed tuple has dimension
$36$ at four sites. -/
theorem finrank_gaugeInvariantSubspace_circuitTupleStar_four :
    Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 4 (by omega)
      circuitTupleStar) = 36 := by
  have hsubspace : gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 4 (by omega)
      circuitTupleStar =
      LinearMap.commonFixedSubmodule fun j : Fin 4 ↦
        toLin' (placedGaussProjector 4 (Multiplicative (ZMod 2)) 4 (by omega) j
          circuitTupleStar) := by
    simp only [gaugeInvariantSubspace, Matrix.toLin'_apply']
  rw [hsubspace]
  exact finrank_commonFixedSubmodule_placedGaussProjector_circuitTupleStar_four

/-- **A second value on the class at three sites.** The second displayed tuple
lies in the completion class and its gauge-invariant subspace has dimension
$14$ at three blocked sites, so the supremum over the class is at least $14$
there. Together with the value $8=2^3$ of the first displayed tuple this
exhibits two different values of the dimension on the class at one chain
length. Nothing follows about the minimum, the exact supremum, or which
completion attains it. -/
theorem fourteen_le_iSup_finrank_gaugeInvariantSubspace_completionClass :
    14 ≤ ⨆ R ∈ defectMaps.completionClass,
      Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 3 (by omega) R) := by
  rw [← finrank_gaugeInvariantSubspace_circuitTupleStar_three]
  exact finrank_gaugeInvariantSubspace_le_iSup_completionClass (by omega)
    circuitTupleStar_mem_completionClass

/-- **A second value on the class at four sites.** The second displayed tuple
lies in the completion class and its gauge-invariant subspace has dimension
$36$ at four blocked sites, so the supremum over the class is at least $36$
there. Nothing follows about the minimum, the exact supremum, which completion
attains it, or the behaviour of any of these in the chain length. -/
theorem thirtySix_le_iSup_finrank_gaugeInvariantSubspace_completionClass :
    36 ≤ ⨆ R ∈ defectMaps.completionClass,
      Module.finrank ℂ (gaugeInvariantSubspace 4 (Multiplicative (ZMod 2)) 4 (by omega) R) := by
  rw [← finrank_gaugeInvariantSubspace_circuitTupleStar_four]
  exact finrank_gaugeInvariantSubspace_le_iSup_completionClass (by omega)
    circuitTupleStar_mem_completionClass

end MPOTensor.CZX

end

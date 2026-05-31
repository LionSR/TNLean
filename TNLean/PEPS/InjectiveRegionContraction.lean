import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Data.Complex.Basic

/-!
# Contraction chain for the union of injective PEPS regions

This file records the linear-algebra kernel argument in the proof that the
union of two injective PEPS regions is injective.

For two regions $A$ and $B$, write the four parts as
$P_0=A\setminus B$, $P_1=A\cap B$, $P_2=B\setminus A$, and
$P_3=(A\cup B)^c$. The source proof starts with a boundary tensor $X$ on
$P_3$ satisfying $\mathcal C_{\{0,1,2\}}(X)=0$. Injectivity of
$A=P_0\cup P_1$, contraction with the tensor over $P_1$, and injectivity of
$B=P_1\cup P_2$ give the chain
$\mathcal C_{\{0,1,2\}}(X)=0 \Rightarrow \mathcal C_{\{2\}}(X)=0
\Rightarrow \mathcal C_{\{1,2\}}(X)=0 \Rightarrow X=0$.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Lemma lem:injective_union](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

/-- The three contraction maps used in the proof that $A\cup B$ is injective.

Here `K` is the boundary space for the outside region
$P_3=(A\cup B)^c$. The three maps are the contractions
$\mathcal C_{\{0,1,2\}}$, $\mathcal C_{\{2\}}$, and
$\mathcal C_{\{1,2\}}$ which occur in the source proof.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1324--1404 of `Papers/1804.04964/paper_normal.tex`. -/
structure InjectiveUnionContractionMaps
    (K E012 E2 E12 : Type*) [AddCommGroup K] [Module ℂ K]
    [AddCommGroup E012] [Module ℂ E012] [AddCommGroup E2] [Module ℂ E2]
    [AddCommGroup E12] [Module ℂ E12] where
  /-- The contraction $\mathcal C_{\{0,1,2\}}$ over the three inside pieces. -/
  contraction012 : K →ₗ[ℂ] E012
  /-- The contraction $\mathcal C_{\{2\}}$ remaining after the inverse for $A$. -/
  contraction2 : K →ₗ[ℂ] E2
  /-- The contraction $\mathcal C_{\{1,2\}}$ after reinserting the overlap piece. -/
  contraction12 : K →ₗ[ℂ] E12

/-- The contraction-chain data used in the proof that $A\cup B$ is injective.

This extends `InjectiveUnionContractionMaps` by the three implications obtained
from the left inverses for the two injective regions and from reinserting the
overlap tensor.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1324--1404 of `Papers/1804.04964/paper_normal.tex`. -/
structure InjectiveUnionContractionChain
    (K E012 E2 E12 : Type*) [AddCommGroup K] [Module ℂ K]
    [AddCommGroup E012] [Module ℂ E012] [AddCommGroup E2] [Module ℂ E2]
    [AddCommGroup E12] [Module ℂ E12] extends
    InjectiveUnionContractionMaps K E012 E2 E12 where
  /-- The inverse for $A=P_0\cup P_1$ sends
  $\mathcal C_{\{0,1,2\}}(X)=0$ to $\mathcal C_{\{2\}}(X)=0$. -/
  left_inverse_A_zero : ∀ X : K, contraction012 X = 0 → contraction2 X = 0
  /-- Contracting with the tensor over $P_1=A\cap B$ sends
  $\mathcal C_{\{2\}}(X)=0$ to $\mathcal C_{\{1,2\}}(X)=0$. -/
  insert_overlap_zero : ∀ X : K, contraction2 X = 0 → contraction12 X = 0
  /-- The inverse for $B=P_1\cup P_2$ sends
  $\mathcal C_{\{1,2\}}(X)=0$ to $X=0$. -/
  left_inverse_B_zero : ∀ X : K, contraction12 X = 0 → X = 0

namespace InjectiveUnionContractionChain

variable {K E012 E2 E12 : Type*} [AddCommGroup K] [Module ℂ K]
variable [AddCommGroup E012] [Module ℂ E012] [AddCommGroup E2] [Module ℂ E2]
variable [AddCommGroup E12] [Module ℂ E12]

/-- The contraction chain gives a zero kernel for
$\mathcal C_{\{0,1,2\}}$.

Source: arXiv:1804.04964, Section 3, Lemma lem:injective_union, lines
1324--1404. The proof is exactly the displayed implication chain
$\mathcal C_{\{0,1,2\}}(X)=0 \Rightarrow \mathcal C_{\{2\}}(X)=0
\Rightarrow \mathcal C_{\{1,2\}}(X)=0 \Rightarrow X=0$. -/
theorem union_contraction_ker_eq_bot
    (c : InjectiveUnionContractionChain K E012 E2 E12) :
    LinearMap.ker c.contraction012 = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro X hX
  exact c.left_inverse_B_zero X
    (c.insert_overlap_zero X (c.left_inverse_A_zero X hX))

/-- Equivalently, the contraction $\mathcal C_{\{0,1,2\}}$ is injective. -/
theorem union_contraction_injective
    (c : InjectiveUnionContractionChain K E012 E2 E12) :
    Function.Injective c.contraction012 :=
  LinearMap.ker_eq_bot.mp c.union_contraction_ker_eq_bot

end InjectiveUnionContractionChain

end PEPS
end TNLean

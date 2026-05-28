import TNLean.PEPS.InjectiveRegion
import TNLean.PEPS.VirtualInsertion

/-!
# Singleton blocked regions for PEPS

This file records the one-vertex base case of the PEPS blocking argument. For
a singleton region, blocking performs no contraction: the blocked tensor is the
original local tensor at that vertex.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3](https://arxiv.org/abs/1804.04964)
- `Papers/1804.04964/paper_normal.tex`, lines 981--1009.
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Physical configurations of the singleton blocked region $\{v\}$.

For a one-vertex region, the blocked physical space is the original physical
space at that vertex.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
abbrev SingletonRegionPhysicalConfig (_v : V) : Type :=
  Fin d

/-- The tensor family obtained by blocking the singleton region $\{v\}$.

For a one-vertex block, no contraction occurs: the blocked tensor is the
original local tensor at $v$.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
def singletonRegionTensorFamily (A : Tensor G d) (v : V) :
    LocalVirtualConfig A v → SingletonRegionPhysicalConfig (d := d) v → ℂ :=
  A.component v

/-- Injectivity of the singleton blocked-region tensor.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
def SingletonRegionTensorInjective (A : Tensor G d) (v : V) : Prop :=
  LinearIndependent ℂ (singletonRegionTensorFamily (G := G) A v)

omit [Fintype V] in
/-- Vertex injectivity is exactly injectivity of every singleton blocked tensor.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem IsVertexInjective.singletonRegionTensorInjective {A : Tensor G d}
    (hA : IsVertexInjective A) (v : V) :
    SingletonRegionTensorInjective (G := G) A v := by
  simpa [SingletonRegionTensorInjective, singletonRegionTensorFamily] using hA v

/-- Compatibility between the concrete singleton blocked tensor and an abstract
region-injectivity predicate.

The abstract injectivity predicate $\kappa$ is used for finite blocked
regions in the normal PEPS proof. This comparison records the one-vertex base
case: if the concrete singleton blocked tensor is injective, then the
corresponding singleton region is injective for $\kappa$.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
structure SingletonRegionInjectivityComparison
    (κ : RegionInjectivityData V) (A : Tensor G d) : Prop where
  /-- Injectivity of the concrete singleton tensor gives injectivity of the
  singleton region in the abstract predicate. -/
  singleton_region_injective :
    ∀ v : V, SingletonRegionTensorInjective (G := G) A v → κ.IsInjective {v}

/-- Compatibility between vertex injectivity and singleton blocked-region
injectivity.

For a one-vertex region, the blocked tensor is the original local tensor. The
source proof in arXiv:1804.04964, Section 3, uses this as the base case before
applying closure of injectivity under contractions. This proposition records,
for every vertex $v$, the implication
$A\text{ vertex-injective}\Longrightarrow\kappa(\{v\})$.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
structure SingletonRegionInjectivityFromVertexInjectivity
    (κ : RegionInjectivityData V) (A : Tensor G d) : Prop where
  /-- Vertex injectivity gives injectivity of the singleton blocked region
  $\{v\}$. -/
  singleton_injective : IsVertexInjective A → ∀ v : V, κ.IsInjective {v}

namespace SingletonRegionInjectivityFromVertexInjectivity

omit [Fintype V] in
/-- The concrete singleton-tensor comparison supplies the singleton base case
of the source contraction step.

Source: arXiv:1804.04964, Section 3;
`Papers/1804.04964/paper_normal.tex`, lines 981--1009. -/
theorem ofSingletonComparison
    {κ : RegionInjectivityData V} {A : Tensor G d}
    (hComparison :
      SingletonRegionInjectivityComparison (G := G) (d := d) κ A) :
    SingletonRegionInjectivityFromVertexInjectivity (G := G) (d := d) κ A where
  singleton_injective hA v :=
    hComparison.singleton_region_injective v (hA.singletonRegionTensorInjective v)

end SingletonRegionInjectivityFromVertexInjectivity

end PEPS
end TNLean

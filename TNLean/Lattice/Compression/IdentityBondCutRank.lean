/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WholeGroupNetwork
import TNLean.Lattice.Compression.DistributedOperatorContraction
import TNLean.Lattice.Compression.DependentNetworkColumn
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Cut ranks of heterogeneous identity-bond networks

Across a partition of the vertices, contract the internal edge labels separately on each
side. The remaining common index has one coordinate for each labelled crossing edge, of
that edge's own alphabet. The two partial contractions factor the coefficient matrix, so
its rank is at most the product of the crossing alphabet sizes.

The construction uses the existing identity-network contraction and existing partial
contractions. Physical alphabets may vary from vertex to vertex. Parallel edges retain
their labels; a self edge remains internal. No norm, injectivity or nonempty-alphabet
hypothesis is used. In particular the factorization does not pass through the larger space
of two independent endpoint labels on every cut edge.

The final two results apply to the actual product-basis columns of the distributed
operator contraction. They fix the input index in its existing local tensor, retaining
its actual tagged star and sample links, local sums, and identity bond matrices.

Source: the one-dimensional note, Part II, proof of Theorem B, the product-basis column
and crossing-link contraction in `part2b_mps_protocol.tex`, lines 587–604; polynomial-PEPS
manuscript, Lemma 8.1 `lem:columns`, `07-assembly.tex`, lines 67–94. The finite-coordinate
factorization is the one already proved in `WholeGroup.flattening_contraction`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace TNLean.Lattice.DependentBondNetwork

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {tail head : E → V} {D : E → Type*} [∀ e, Fintype (D e)]
    [∀ e, DecidableEq (D e)] {P : V → Type*}

/-- The actual identity-bond coefficient matrix factors through one label per crossing edge.
The factors are the existing literal sums over the two internal edge families.
Source: the one-dimensional note, Part II, proof of Theorem B, lines 597–604. -/
theorem flattening_network_one_eq_mul
    (A : (v : V) → LocalConfig tail head D v → P v → ℂ) (S : Finset V) :
    WholeGroup.flattening (network tail head D A (fun _ ↦ 1)) S =
      WholeGroup.bipartitionLeft (WholeGroup.ofLocalTensors A) S *
        (WholeGroup.bipartitionRight (WholeGroup.ofLocalTensors A) S)ᵀ := by
  have h : network tail head D A (fun _ ↦ 1) =
      WholeGroup.contraction (WholeGroup.ofLocalTensors A) :=
    funext (WholeGroup.network_one_eq_contraction A)
  rw [h]
  exact WholeGroup.flattening_contraction (WholeGroup.ofLocalTensors A) S

/-- The cut rank of an identity-bond network is at most the product of the actual crossing
alphabet sizes. The alphabet of each tagged crossing edge occurs once.
Source: the one-dimensional note, Part II, proof of Theorem B, lines 597–604. -/
theorem rank_flattening_network_one_le [∀ v, Fintype (P v)]
    (A : (v : V) → LocalConfig tail head D v → P v → ℂ) (S : Finset V) :
    (WholeGroup.flattening (network tail head D A (fun _ ↦ 1)) S).rank ≤
      ∏ e : {e // WholeGroup.IsLink tail head S Sᶜ e}, Fintype.card (D e) := by
  rw [flattening_network_one_eq_mul]
  calc
    _ ≤ (WholeGroup.bipartitionLeft (WholeGroup.ofLocalTensors A) S).rank :=
      Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card ((e : {e // WholeGroup.IsLink tail head S Sᶜ e}) → D e) :=
      Matrix.rank_le_card_width _
    _ = _ := Fintype.card_pi

end TNLean.Lattice.DependentBondNetwork

namespace TNLean.Lattice.Compression.DistributedOperatorContraction

open TNLean.Lattice.DependentBondNetwork

variable {Party Gate : Type*} [Fintype Party] [DecidableEq Party] [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset Party) (root : Gate → Party)
    (hroot : ∀ g ∈ gates, root g ∈ participants g)
    (Label : Gate → Type) [∀ g, Fintype (Label g)] (k : ℕ)
    {Out In : Party → Type*}

open Classical in
/-- Fixing the actual input column gives explicit cut factors on the same tagged links.
The displayed local tensor is the existing input-fixed endpoint tensor, not new network data.
Source: polynomial-PEPS Lemma 8.1, `07-assembly.tex`, lines 91–93, and the
one-dimensional note, Part II, proof of Theorem B, lines 587–604. -/
theorem flattening_contractedOperator_column_eq_mul
    (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (z : (p : Party) → In p) (S : Finset Party) :
    let A := fixInput (src gates participants root) (tgt gates participants root)
      (alphabet gates participants root Label k)
      (endpointTensor gates participants root hroot Label k c T) z
    WholeGroup.flattening (fun x ↦ contractedOperator gates participants root hroot Label k c T x z)
        S =
      WholeGroup.bipartitionLeft (WholeGroup.ofLocalTensors A) S *
        (WholeGroup.bipartitionRight (WholeGroup.ofLocalTensors A) S)ᵀ := by
  dsimp only
  have h : (fun x ↦ contractedOperator gates participants root hroot Label k c T x z) =
      network (src gates participants root) (tgt gates participants root)
        (alphabet gates participants root Label k)
        (fixInput (src gates participants root) (tgt gates participants root)
          (alphabet gates participants root Label k)
          (endpointTensor gates participants root hroot Label k c T) z) (fun _ ↦ 1) := rfl
  rw [h]
  exact flattening_network_one_eq_mul _ S

open Classical in
/-- Every actual product-basis column has cut rank bounded by the product of the alphabets
of its tagged crossing star and sample links, with no change in physical dimensions.
Source: the one-dimensional note, Part II, proof of Theorem B, lines 587–604. -/
theorem rank_flattening_contractedOperator_column_le [∀ p, Fintype (Out p)]
    (c : (g : Gate) → Label g → ℂ)
    (T : (p : Party) → GateLabelsAt gates participants Label p →
      (SampleAt gates participants p → Fin k) → Matrix (Out p) (In p) ℂ)
    (z : (p : Party) → In p) (S : Finset Party) :
    (WholeGroup.flattening
      (fun x ↦ contractedOperator gates participants root hroot Label k c T x z) S).rank ≤
      ∏ e : {e : Link gates participants root //
        WholeGroup.IsLink (src gates participants root) (tgt gates participants root) S Sᶜ e},
        Fintype.card (alphabet gates participants root Label k e) := by
  change (WholeGroup.flattening
    (network (src gates participants root) (tgt gates participants root)
      (alphabet gates participants root Label k)
      (fixInput (src gates participants root) (tgt gates participants root)
        (alphabet gates participants root Label k)
        (endpointTensor gates participants root hroot Label k c T) z) (fun _ ↦ 1)) S).rank ≤ _
  exact rank_flattening_network_one_le _ S

end TNLean.Lattice.Compression.DistributedOperatorContraction

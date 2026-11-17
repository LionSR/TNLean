/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct
import TNLean.Circuit.SiteOperators
import QICLean.Circuit.Gate.Controlled

/-!
# Controlled single-site operations

On a finite set of sites `ι`, the operation "apply `u` at the site `t` when the sites of `S`
are in the configuration `c`" is `C(p, U) = p U + (1 - p)`, where `p` is the projection onto
the configurations agreeing with `c` on `S` and `U = u` at `t`. This file develops the algebra
of these operations used to write a unitary on a constant number of sites as a product of
two-site gates: the controlled operators on a finite set of sites, with their supports and
unitarity. The projections and single-site operators they are built from are in
`TNLean.Circuit.SiteOperators`. The identities of controlled elements in any ring, among them
the commutator identity `QuantumCircuit.ctrlElem_commutator` that lowers the number of control
sites by one, are in `QICLean.Circuit.Gate.Controlled`.

The decomposition of gates acting on a constant number of sites into two-site gates is the
step "can be further expressed with a low-depth circuit of local gates" of arXiv:2307.01696
(caption of Fig. 1 and paragraph "The sequential-RG circuit").
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

/-! ### Controlled operators on sites -/

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The controlled operator: `u` at the site `t` when the sites of `S` are in the configuration
`c`, the identity otherwise.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
noncomputable def ctrlOp (S : Finset ι) (c : ι → Fin d) (t : ι)
    (u : Matrix (Fin d) (Fin d) ℂ) : Matrix (ι → Fin d) (ι → Fin d) ℂ :=
  ctrlElem (ctrlProj S c) (siteOp t u)

@[simp] theorem ctrlOp_empty (c : ι → Fin d) (t : ι) (u : Matrix (Fin d) (Fin d) ℂ) :
    ctrlOp ∅ c t u = siteOp t u := by
  simp [ctrlOp, ctrlElem]

theorem ctrlOp_mul {S : Finset ι} {t : ι} (ht : t ∉ S) (c : ι → Fin d)
    (u v : Matrix (Fin d) (Fin d) ℂ) : ctrlOp S c t u * ctrlOp S c t v = ctrlOp S c t (u * v) := by
  rw [ctrlOp, ctrlOp, ctrlElem_mul (isIdempotentElem_ctrlProj S c)
    (commute_ctrlProj_siteOp ht c u), siteOp_mul, ctrlOp]

theorem ctrlOp_one (S : Finset ι) (c : ι → Fin d) (t : ι) : ctrlOp S c t 1 = 1 := by
  rw [ctrlOp, siteOp_one, ctrlElem_one]

theorem ctrlOp_star {S : Finset ι} {t : ι} (ht : t ∉ S) (c : ι → Fin d)
    (u : Matrix (Fin d) (Fin d) ℂ) : star (ctrlOp S c t u) = ctrlOp S c t (star u) := by
  have hc := commute_ctrlProj_siteOp ht c u
  have hp : star (ctrlProj S c) = ctrlProj S c := ctrlProj_conjTranspose S c
  rw [ctrlOp, ctrlOp, ctrlElem, ctrlElem, star_add, star_mul, star_sub, star_one, hp,
    siteOp_star, (commute_ctrlProj_siteOp ht c (star u)).eq]

theorem ctrlOp_mem_unitary {S : Finset ι} {t : ι} (ht : t ∉ S) (c : ι → Fin d)
    {u : Matrix (Fin d) (Fin d) ℂ} (hu : u ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ctrlOp S c t u ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ) := by
  rw [Unitary.mem_iff] at hu ⊢
  rw [ctrlOp_star ht, ctrlOp_mul ht, ctrlOp_mul ht, hu.1, hu.2, ctrlOp_one]
  exact ⟨rfl, rfl⟩

theorem ctrlOp_mem_supportedOperators (S : Finset ι) (c : ι → Fin d) (t : ι)
    (u : Matrix (Fin d) (Fin d) ℂ) :
    ctrlOp S c t u ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (insert t S) := by
  have hp := ManyBody.supportedOperators_mono (Finset.subset_insert t S)
    (ctrlProj_mem_supportedOperators (d := d) S c)
  have hs := ManyBody.supportedOperators_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self t S))
    (siteOp_mem_supportedOperators (d := d) t u)
  exact add_mem (mul_mem hp hs)
    (sub_mem (one_mem (ManyBody.supportedOperators _ _)) hp)

/-- **Controlled commutator on the sites.** Removing one control site `s` from the controls of
a commutator `v w v† w†` at the site `t`. -/
theorem ctrlOp_insert_commutator {S : Finset ι} {s t : ι} (ht : t ∉ S)
    (hst : s ≠ t) (c : ι → Fin d) {v w : Matrix (Fin d) (Fin d) ℂ}
    (hv : v ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hw : w ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    ctrlOp (insert s S) c t (v * w * star v * star w) =
      ctrlOp S c t v * ctrlOp {s} c t w * ctrlOp S c t (star v) * ctrlOp {s} c t (star w) := by
  have hts : t ∉ ({s} : Finset ι) := by simpa using Ne.symm hst
  rw [ctrlOp, ctrlProj_insert, ← siteOp_mul, ← siteOp_mul, ← siteOp_mul, ctrlOp, ctrlOp, ctrlOp,
    ctrlOp]
  refine (ctrlElem_commutator (isIdempotentElem_ctrlProj S c) (isIdempotentElem_ctrlProj {s} c)
    (commute_ctrlProj S {s} c c) (commute_ctrlProj_siteOp ht c v)
    (commute_ctrlProj_siteOp ht c w)
    (commute_ctrlProj_siteOp hts c v) (commute_ctrlProj_siteOp hts c _)
    (commute_ctrlProj_siteOp hts c w) ?_ ?_).symm
  · rw [siteOp_mul, Unitary.mul_star_self_of_mem hv, siteOp_one]
  · rw [siteOp_mul, Unitary.mul_star_self_of_mem hw, siteOp_one]

end QuantumCircuit

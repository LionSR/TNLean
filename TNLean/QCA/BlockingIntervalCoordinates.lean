/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.QuasiLocalBlocking
import TNLean.QCA.QuasiLocalInterval

/-!
# Consecutive interval coordinates under site blocking

Grouping \(L>0\) consecutive sites expands the integer interval
\([a,a+N)\) into \([aL,(a+N)L)\). The finite observable coordinates
are transported by decoding each blocked spin in increasing residue order.
Consequently, quasi-local blocking sends an interval observable to the
expanded interval observable, with both matrix indices reindexed by the
existing blocked-configuration equivalence.

The finite-coordinate identities require only \(L>0\). The quasi-local
identity also assumes a positive physical dimension. Negative interval starts
and empty intervals are included.

Source: CPGSV17, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320,
site grouping and the induced observable-algebra equivalence; Nachtergaele,
arXiv:cond-mat/9410110, Section 3, the consecutive-interval convention.
-/

namespace SpinChain

/-- Expanding a consecutive blocked interval multiplies its start and
length by the block length. This includes negative starts and empty intervals.
Source: CPGSV17, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
theorem expandedRegion_intervalRegion (L : ℕ) [NeZero L] (a : ℤ) (N : ℕ) :
    expandedRegion L (intervalRegion a N) = intervalRegion (a * L) (N * L) := by
  ext z
  simp only [mem_expandedRegion, intervalRegion, Finset.mem_Ico, Int.divModEquiv_apply]
  have hL : 0 < (L : ℤ) := by exact_mod_cast NeZero.pos L
  rw [Int.le_ediv_iff_mul_le hL, Int.ediv_lt_iff_lt_mul hL]
  simp [Nat.cast_mul, add_mul]

private theorem intervalConfigEquiv_blocking_symm (d L : ℕ) [NeZero L]
    (a : ℤ) (N : ℕ)
    (hs : expandedRegion L (intervalRegion a N) ⊆ intervalRegion (a * L) (N * L))
    (σ : Fin (N * L) → Fin d) :
    (intervalConfigEquiv (MPSTensor.blockPhysDim d L) a N).symm
      ((Config.blocking d L (intervalRegion a N)).symm
        (Config.restrict hs (intervalConfigEquiv d (a * L) (N * L) σ))) =
      (MPSTensor.blockedConfigEquiv d N L).symm σ := by
  funext i
  change (MPSTensor.decodeBlockEquiv d L).symm
      (fun r => Config.restrict hs (intervalConfigEquiv d (a * L) (N * L) σ)
        ((blockSiteEquiv L (intervalRegion a N)).symm (intervalSiteEquiv a N i, r))) =
    (MPSTensor.decodeBlockEquiv d L).symm
      (fun r => σ (finProdFinEquiv (i, r)))
  apply congrArg (MPSTensor.decodeBlockEquiv d L).symm
  funext r
  change σ _ = σ _
  apply congrArg σ
  apply Fin.ext
  change (((a + i.val) * L + r.val - a * L).toNat) = r.val + L * i.val
  have hsite : (a + i.val) * (L : ℤ) + r.val - a * L =
      ((r.val + L * i.val : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hsite, Int.toNat_natCast]

/-- In consecutive matrix coordinates, finite blocking reindexes both
indices by the blocked-configuration equivalence. The local inclusion
transports across the equality of the two interval regions.
Source: CPGSV17, arXiv:1703.09188, Appendix, lines 2308 and 2313--2320. -/
theorem intervalCoordinates_localBlocking (d L : ℕ) [NeZero L] (a : ℤ) (N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d L))
      (Fin N → Fin (MPSTensor.blockPhysDim d L)) ℂ) :
    intervalCoordinates d (a * L) (N * L)
      (localInclusion (expandedRegion_intervalRegion L a N).le
        (localBlocking d L (intervalRegion a N)
          ((intervalCoordinates (MPSTensor.blockPhysDim d L) a N).symm X))) =
      Matrix.reindex (MPSTensor.blockedConfigEquiv d N L)
        (MPSTensor.blockedConfigEquiv d N L) X := by
  ext σ τ
  have hcomp :
      (Config.splitEquiv (expandedRegion_intervalRegion L a N).le
        (intervalConfigEquiv d (a * L) (N * L) σ)).2 =
      (Config.splitEquiv (expandedRegion_intervalRegion L a N).le
        (intervalConfigEquiv d (a * L) (N * L) τ)).2 := by
    funext z
    have hz := Finset.mem_sdiff.mp z.2
    exact (hz.2 ((expandedRegion_intervalRegion L a N).ge hz.1)).elim
  simp only [intervalCoordinates_apply, localInclusion_apply, localBlocking_apply,
    hcomp, ite_true, mul_one]
  change X ((intervalConfigEquiv (MPSTensor.blockPhysDim d L) a N).symm _)
    ((intervalConfigEquiv (MPSTensor.blockPhysDim d L) a N).symm _) =
      X ((MPSTensor.blockedConfigEquiv d N L).symm σ)
        ((MPSTensor.blockedConfigEquiv d N L).symm τ)
  rw [intervalConfigEquiv_blocking_symm, intervalConfigEquiv_blocking_symm]

/-- Quasi-local blocking sends an interval observable to its expanded
interval observable, with both matrix indices reindexed in the consecutive
block order. Source: CPGSV17, arXiv:1703.09188, Appendix,
lines 2308 and 2313--2320. -/
theorem quasiLocalBlocking_quasiLocalIntervalObservable (d L : ℕ)
    [NeZero d] [NeZero L] (a : ℤ) (N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d L))
      (Fin N → Fin (MPSTensor.blockPhysDim d L)) ℂ) :
    quasiLocalBlocking d L
        (quasiLocalIntervalObservable (MPSTensor.blockPhysDim d L) a N X) =
      quasiLocalIntervalObservable d (a * L) (N * L)
        (Matrix.reindex (MPSTensor.blockedConfigEquiv d N L)
          (MPSTensor.blockedConfigEquiv d N L) X) := by
  rw [quasiLocalIntervalObservable_apply, quasiLocalBlocking_quasiLocalObservable,
    ← quasiLocalObservable_localInclusion d (expandedRegion_intervalRegion L a N).le]
  rw [quasiLocalIntervalObservable_apply]
  apply congrArg (quasiLocalObservable d (intervalRegion (a * L) (N * L)))
  apply (intervalCoordinates d (a * L) (N * L)).injective
  change intervalCoordinates d (a * L) (N * L) _ =
    intervalCoordinates d (a * L) (N * L) _
  rw [intervalCoordinates_localBlocking, StarAlgEquiv.apply_symm_apply]

end SpinChain

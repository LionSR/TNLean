# Zero-reference circuit helper slice — 2026-10-29

Issue: #9881, ledger S2. Baseline: main
`152f3c81984a0d25599471bf700ecc967e13777f`.

## Current census and deletion criterion

The default `scripts/zero_reference_scan.py --json` scan, with the fixed-point
pass enabled and attributed declarations/Archive excluded, reports 33
candidates at this baseline. The issue's 103-candidate list is a historical
snapshot; several of its directory waves are already integrated.

The scan is a candidate list, not a deletion verdict. This slice removes only
three un-attributed structural helpers with no use outside their own extent.
Exact-name searches cover production and Archive Lean, Blueprint, docs,
scripts, Notes and Papers. No source label, Blueprint tag, declaration attribute
or instance use names any of them. Their individual statements carry no paper
citation and are not the source-facing bounds highlighted by their modules.

| Removed declaration | Former role | Retained mathematical surface |
|---|---|---|
| `QuantumCircuit.bondNeighbourhood_mono` | Set-inclusion adapter for the one-step bond neighbourhood | `bondNeighbourhood`, `mem_bondNeighbourhood`, `subset_bondNeighbourhood`, and the light-cone bounds for the ring, open chain and graph |
| `QuantumCircuit.lightCone_mono_radius` | Iterates the one-step inclusion to compare radii | `lightCone`, `lightCone_subset_succ` and all geometric light-cone conclusions; the one-step inclusion is live in `Circuit/Channel/Layer.lean` |
| `TNLean.Lattice.PartyCircuit.PartyChain.length_effectParties` | Recursive count accessor for the endpoint-party list | `effectParties`, `toEffectChain`, the register identities and source-preparation bounds; the list itself remains used by party restrictions and Blueprint `ch24_peps_pair_effects.tex` |

The slice removes exactly 19 production Lean lines. Rerunning the same fixed-point
scan on the edited tree reports 30 candidates. All 48 remaining declarations
in the two edited Lean files retain their exact source signatures.

No definition, instance, automation attribute, terminal worked example or
source-cited theorem is removed. No compatibility alias is retained for a
consumer-free helper under TNLean's local API-removal convention.

## Work intentionally retained

The other candidates include terminal example calculations and source-facing
amplification results. Their lack of call sites alone does not justify
deleting them. The Hastings/low-energy helpers are also left for a separate
check against the concurrent source-completion contributions. This slice does
not declare the residue cleared or the tracking issue completed.

## Verification boundary

This is source-only work. The removed names have no surviving production or
Blueprint references. Every remaining declaration signature in the two edited
Lean files is unchanged. No modules are added or deleted, so import
aggregators do not change. `git diff --check` passes. The user explicitly
requested no local Lean compilation; elaboration and integration remain
pending in the draft PR. No persistent Lean fixtures are added.

# PEPS new-pin resource checkpoint

The existing queue (PID 85524, original session 38476) ran without restart
and stopped at its 1 GiB boundary after ActualTransportEstimates passed.
119 additional modules passed build and strict, 5 passed previously: 124/591.
467 remain unverified; exact disjoint sets and hashes are in summary.json.
HoneycombCluster additionally passed but is outside the original 591 manifest.
Earlier reports incorrectly counted it inside: 125/591 and 466 remaining are
superseded by this exact-set audit. The original queue had 586, not 585, entries.
No production edits were made. Evidence commits change audits only.

The initial path-sorted Approximation aggregator was intentionally interrupted
to prioritize concrete owners in import order. That event is preserved in the
ledger and raw logs, not counted as a compilation failure. No unresolved
compilation failure occurred in this queue. Old-pin failures remain historical
and are not relabelled as successes.

CI 44326484230 build job 134879110163 remains in progress. gh cannot retrieve
its running log, and the direct log endpoint returned Forbidden. Checkout SHA,
BASE_SHA, PR_HEAD_SHA and actual first parent remain unknown. Successful checkout
steps, the known synthetic tree, and REST's dynamically updated base do not prove
those values. No CI rerun was requested.

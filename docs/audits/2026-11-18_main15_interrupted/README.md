# Preserved pre-new-pin validation checkpoint

Source head: 9a440ee87474b5564ed26c297c7f63e0ab81aeac, based on e06a33e5.
Three local DG interval-open fixes: 2c1ac009c, 2a6ca0769, 9a440ee87.
Five targets passed build and strict. DGConstantNodeTreeApproximation failed
on unresolved interval; its attempted fourth fix did not land. Nine targets
were not started. No process remained at recovery. Original logs and ledger
are preserved, including failed attempts. No successful new-pin validation
is claimed; QICLean was pinned to 1af32a2. Main subsequently landed #10903,
so those source fixes must be deduplicated by exact content during integration.
The editing_seconds field originated in the driver and does not measure total
human/model reasoning time; individual tool-edit timestamps are recorded separately.

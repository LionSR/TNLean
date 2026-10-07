# Current integrated encoder verification

The compiler ran at local integration revision
`8602b340cfe0b3b73bad634a06b75f9dd6b20049`. The current encoder ledger names
public revision `d92310cca4f63cf1c2b0c91936e538f80288b48c` to identify its
unchanged source. `identity.json` independently compares the production
module, consumers, guards, and raw audit driver at both revisions and the
original author checkpoint. This is equality of those four files, not of
the entire repository trees or execution environments.

`checks.json` retains the actual integrated commands and outcomes. The nine
successful logs include the aggregate builds, strict adapter and encoder
checks, and independent raw reports for all three adapter and twenty-two
encoder declarations. The active encoder ledger uses its aggregate build,
encoder consumer and guard checks, and raw encoder audit. All twenty-two
raw reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`.

The original encoder ledger is archived at
`../historical/author-checkpoint-ledger.json`, with exact copies of its four
successful command logs, verification index, and README. Every preexisting
encoder evidence file remains unchanged at its original path. The identity
record preserves their hashes and the original-to-retained manifest mapping.
Only manifest log destinations were normalized; all nine new logs are unchanged.

The adapter ledger still identifies local revision
`61f76928032b1eef7417ae9d79dda93796019eb6`. Its three records are unchanged.
A local full provenance pass therefore does not establish a public-only CI
pass: migration of those three references to an authorized published source
remains pending. No files or commits were published during this migration.

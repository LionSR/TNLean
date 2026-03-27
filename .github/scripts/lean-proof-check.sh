#!/usr/bin/env bash
# lean-proof-check.sh — Detect proof cheating patterns in Lean 4 files
#
# Scans for: sorry/admit, kernel bypasses, axiom smuggling,
# placeholder tactics, suspicious options, and unsafe primitives.
#
# Usage:
#   ./lean-proof-check.sh [file-or-directory...]
#   Default: scans TNLean/ from the repo root.
#
# Exit codes:
#   0 — no issues found
#   1 — issues detected (details on stdout in markdown)

set -euo pipefail

# --- Configuration -----------------------------------------------------------

# Paths to scan (default: TNLean/)
TARGETS=("${@:-TNLean/}")

# Temp working files
REPORT=$(mktemp)
FOUND_ISSUES=0

trap 'rm -f "$REPORT"' EXIT

# --- Helpers ------------------------------------------------------------------

# grep_pattern FILE_GLOB PATTERN LABEL SEVERITY EXPLANATION
#   Searches TARGETS for PATTERN in *.lean files.
#   Appends matches to $REPORT in markdown format.
check_pattern() {
  local pattern="$1"
  local label="$2"
  local severity="$3"   # blocker | warning | info
  local explanation="$4"

  local matches
  matches=$(grep -rnE --include='*.lean' "$pattern" "${TARGETS[@]}" 2>/dev/null || true)

  if [[ -n "$matches" ]]; then
    FOUND_ISSUES=1
    local count
    count=$(echo "$matches" | wc -l)
    {
      echo ""
      echo "### ${severity^^}: ${label} (${count} occurrence(s))"
      echo ""
      echo "> ${explanation}"
      echo ""
      echo '```'
      echo "$matches"
      echo '```'
    } >> "$REPORT"
  fi
}

# --- Tier 1: Direct Proof Holes (BLOCKER) ------------------------------------

# Match `sorry` used as an actual tactic (not just mentioned in comments/docs).
# Pattern: line contains `sorry` as a word AND is not a pure comment line (-- ...)
# and does not look like a documentation reference (sorry-free, no sorry, etc.)
check_pattern \
  '^\s*sorry\b|:=.*\bsorry\b|\bby\b.*\bsorry\b|·\s*sorry|;\s*sorry|\bexact\s+sorry' \
  'sorry usage (tactic/term)' \
  'blocker' \
  '`sorry` axiomatically closes any proof goal. Every `sorry` must be resolved before merging.'

check_pattern \
  '^\s*admit\b|:=.*\badmit\b|\bby\b.*\badmit\b|·\s*admit' \
  'admit usage' \
  'blocker' \
  '`admit` is a tactic alias for `sorry`. Must be removed before merging.'

# --- Tier 2: Kernel / Type System Bypasses (BLOCKER) -------------------------

check_pattern \
  '\bnative_decide\b' \
  'native_decide' \
  'blocker' \
  '`native_decide` uses native code evaluation that bypasses the kernel. It can be unsound and is banned in Mathlib. Use `decide` or provide an explicit proof instead.'

check_pattern \
  '\bunsafeCast\b|\bunsafeCoerce\b' \
  'unsafeCast / unsafeCoerce' \
  'blocker' \
  'Unsafe casts bypass the type checker entirely and can fabricate any proof. Never use in proof code.'

check_pattern \
  '\blcProof\b' \
  'lcProof' \
  'blocker' \
  '`lcProof` is a low-level primitive that fabricates proof terms. It can prove `False`. Must not appear in proof code.'

check_pattern \
  '\bofReduceBool\b|\bofReduceNat\b' \
  'ofReduceBool / ofReduceNat' \
  'blocker' \
  'Kernel reduction primitives that can be exploited for unsound proofs. Requires careful review.'

check_pattern \
  '\bimplemented_by\b|\bimplementedBy\b' \
  'implemented_by' \
  'warning' \
  '`implemented_by` replaces a function implementation with native code. Can make the runtime behavior diverge from the proven specification.'

# --- Tier 3: Axiom Smuggling (BLOCKER) ---------------------------------------

check_pattern \
  '^\s*axiom\s+' \
  'Custom axiom declarations' \
  'blocker' \
  'Custom `axiom` declarations introduce unproven assumptions that could be inconsistent. Each axiom must be explicitly justified.'

check_pattern \
  '^\s*constant\s+.*:\s*Prop' \
  'Constant Prop declarations' \
  'blocker' \
  'Declaring a `constant` of type `Prop` is equivalent to introducing an axiom. Must be justified or replaced with a proof.'

check_pattern \
  '^\s*opaque\s+.*:\s*Prop' \
  'Opaque Prop declarations' \
  'warning' \
  '`opaque` declarations of type `Prop` hide unproven assumptions. Review carefully.'

# --- Tier 4: Placeholder / Scaffolding Tactics (WARNING) ---------------------

check_pattern \
  '\bexact\?\b|\bapply\?\b|\bsuggest\b|\blibrary_search\b' \
  'Search tactics left in code' \
  'warning' \
  'Search/suggestion tactics (`exact?`, `apply?`, `library_search`) are development aids. Replace with the concrete tactic they suggest.'

check_pattern \
  '^\s*#check\s|\s#eval\s|\s#print\s' \
  'Debug commands (#check, #eval, #print)' \
  'info' \
  'Debug commands should be removed from final proof files.'

check_pattern \
  '\bdbg_trace\b' \
  'dbg_trace' \
  'warning' \
  '`dbg_trace` is a debug aid that should be removed from final proofs.'

check_pattern \
  '\bstop\b' \
  'stop command' \
  'warning' \
  '`stop` halts elaboration — typically used during development. Remove before merging.'

# --- Tier 5: Suspicious Options (WARNING) ------------------------------------

check_pattern \
  'set_option\s+maxHeartbeats\s+0\b' \
  'maxHeartbeats disabled' \
  'warning' \
  '`set_option maxHeartbeats 0` disables the timeout. This can hide non-terminating proofs. Use a finite bound.'

check_pattern \
  'set_option\s+maxHeartbeats\s+[0-9]{7,}' \
  'Extremely high maxHeartbeats' \
  'warning' \
  'Heartbeat limits above 10 million suggest a proof may be inefficient or non-terminating.'

check_pattern \
  'set_option\s+maxRecDepth\s+[0-9]{5,}' \
  'Extremely high maxRecDepth' \
  'info' \
  'Very high recursion depth limits may hide structural issues in proofs.'

# --- Tier 6: Unsafe definitions in proof context (WARNING) -------------------

check_pattern \
  '^\s*unsafe\s+def\b' \
  'unsafe def' \
  'warning' \
  '`unsafe def` bypasses Lean safety checks. Should not be used in proof-relevant code.'

check_pattern \
  '^\s*partial\s+def\b' \
  'partial def' \
  'warning' \
  '`partial def` does not require termination proof. If used to build proof terms, it can be unsound.'

# --- Tier 7: Nonterminal simp / omega abuse (INFO) ---------------------------

check_pattern \
  '\bsorry\b.*\bTODO\b|\bTODO\b.*\bsorry\b' \
  'sorry with TODO marker' \
  'info' \
  'Marked as known TODO — track these for completion.'

# --- Output -------------------------------------------------------------------

if [[ "$FOUND_ISSUES" -eq 0 ]]; then
  echo "## Lean Proof Integrity Check -- All Clear"
  echo ""
  echo "No proof cheating patterns detected."
  exit 0
else
  echo "## Lean Proof Integrity Check -- Issues Found"
  echo ""
  echo "The following proof integrity issues were detected in Lean files."
  echo "Blockers **must** be resolved before merging."
  cat "$REPORT"
  echo ""
  echo "---"
  echo "*Generated by lean-proof-check.sh*"
  exit 1
fi

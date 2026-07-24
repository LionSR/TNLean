#!/usr/bin/env bash
# Gate for the kernel language stage: the seven contract fixtures pin their
# record streams, and every sugar spelling proves byte-identical events
# against its kernel expansion.  Sources: tests/tenkz/kernel/.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KERNEL="$REPO/tests/tenkz/kernel"
GOLDEN="$KERNEL/golden.sha256"
MODE=${1:---check}

WORK="$(mktemp -d "${TMPDIR:-/tmp}/tenkz-kernel.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
cp "$KERNEL"/k_*.tex "$WORK"/
cp "$KERNEL"/regression/r_*.tex "$WORK"/
cp "$KERNEL"/sugar/s*_*.tex "$WORK"/

compile() {
  ( cd "$WORK" &&
    TEXINPUTS="$REPO/tex/tenkz//:" \
      timeout 120 xelatex -interaction=nonstopmode -halt-on-error "$1" \
      >"$WORK/$1.transcript" 2>&1 ) || {
    echo "FAIL: $1 did not compile" >&2
    tail -20 "$WORK/$1.transcript" >&2
    exit 1
  }
}

for tex in "$WORK"/*.tex; do
  compile "$(basename "$tex")"
done

atom_count=$(grep -c '^atom|' "$WORK/r_explicit_at.tnlog")
[ "$atom_count" -eq 2 ] || {
  echo "FAIL: explicit at= did not suppress population of its claimed cell" >&2
  exit 1
}
grep -Fq '|addr=(1,1)|kind=tn|populated=ket' "$WORK/r_explicit_at.tnlog" || {
  echo "FAIL: the unclaimed cell was not populated" >&2
  exit 1
}
grep -Fq '|name=cup-1-2|origin=cup|' "$WORK/r_cup.tnlog" || {
  echo "FAIL: cup policy did not derive the adjacent-row cup-1-2 record" >&2
  exit 1
}
grep -Fq '|name=bond-1-1-1-2|origin=grid|' "$WORK/k_blocking.tnlog" || {
  echo "FAIL: bonds=grid did not materialize the adjacent WIRE record" >&2
  exit 1
}
grep -Fq '|name=wrap-1|origin=trace|row=1|' "$WORK/k_twoshift.tnlog" || {
  echo "FAIL: trace policy did not derive the per-row wrap-1 record" >&2
  exit 1
}
if grep -Eq 'name=(wrap|cup)-(west|east|north|south)' \
    "$WORK/k_twoshift.tnlog" "$WORK/r_cup.tnlog"; then
  echo "FAIL: a side-level closure survived normalization" >&2
  exit 1
fi
wide_atom_count=$(grep -c '^atom|' "$WORK/r_wide_chain.tnlog")
[ "$wide_atom_count" -eq 2 ] || {
  echo "FAIL: a chain-positioned wide atom did not claim its full span" >&2
  exit 1
}
grep -Fq '|name=P|ports=n:physical|skin=box' \
    "$WORK/r_declare_atom.tnlog" || {
  echo "FAIL: an identifier atom declaration did not mint a typed command" >&2
  exit 1
}
grep -Fq '|name=M|ports=w:virtual,e:virtual|skin=ring' \
    "$WORK/r_declare_atom.tnlog" || {
  echo "FAIL: a control-sequence atom declaration did not mint a typed command" >&2
  exit 1
}
grep -Fq '|name=trace-1-2|origin=trace|' "$WORK/r_cell_policy.tnlog" || {
  echo "FAIL: trace= cell policy did not materialize a closure wire" >&2
  exit 1
}
if ! grep -Fq '|face=upper|' "$WORK/r_cell_policy.tnlog" ||
   ! grep -Fq '|origin=open|to-open=s' "$WORK/r_cell_policy.tnlog"; then
  echo "FAIL: open= cell policy did not materialize its upper open leg" >&2
  exit 1
fi
if ! grep -Fq '|face=lower|from-open=n|' "$WORK/r_cell_policy.tnlog"; then
  echo "FAIL: open= cell policy did not materialize its lower open leg" >&2
  exit 1
fi
physical_trace_count=$(
  grep -c '|mode=physical|name=trace-physical-' "$WORK/r_cell_policy.tnlog"
)
[ "$physical_trace_count" -eq 3 ] || {
  echo "FAIL: trace=physical did not materialize one closure per column" >&2
  exit 1
}
grep -Fq '|from=' "$WORK/r_spaced_wire.tnlog" || {
  echo "FAIL: whitespace before positional wire ends changed wire arity" >&2
  exit 1
}
if grep -Fq '|origin=grid|' "$WORK/r_sealed_void.tnlog"; then
  echo "FAIL: a sealed void retained an incident generated grid bond" >&2
  exit 1
fi
replaced_bond_count=$(
  grep -c '|name=bond-1-2-2-2|origin=grid|' "$WORK/r_cell_policy.tnlog"
)
[ "$replaced_bond_count" -eq 1 ] || {
  echo "FAIL: trace/open cell policies did not replace their grid bonds" >&2
  exit 1
}

negative="$KERNEL/negative/n_diagonal_port.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error "$negative" \
       >"$WORK/n_diagonal_port.transcript" 2>&1 ); then
  echo "FAIL: a diagonal atom port was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-ADDRESS]' "$WORK/n_diagonal_port.transcript" || {
  echo "FAIL: the diagonal-port rejection lacked TKZ-LANG-ADDRESS" >&2
  tail -20 "$WORK/n_diagonal_port.transcript" >&2
  exit 1
}

signature_negative="$KERNEL/negative/n_signature_mismatch.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$signature_negative" >"$WORK/n_signature_mismatch.transcript" 2>&1 ); then
  echo "FAIL: unequal panel signatures were accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-SIGNATURE]' "$WORK/n_signature_mismatch.transcript" || {
  echo "FAIL: signature mismatch lacked TKZ-EQ-SIGNATURE" >&2
  exit 1
}
grep -Fq 'result=mismatch' "$WORK/n_signature_mismatch.tnlog" || {
  echo "FAIL: signature mismatch was not recorded before the hard error" >&2
  exit 1
}
if grep -Fq 'result=equal' "$WORK/n_signature_mismatch.tnlog"; then
  echo "FAIL: signature mismatch emitted a false equal verdict" >&2
  exit 1
fi

for sugar_negative in \
  n_malformed_sugar \
  n_malformed_surface \
  n_malformed_cluster \
  n_malformed_ring
do
  source="$KERNEL/negative/$sugar_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$sugar_negative.transcript" 2>&1 ); then
    echo "FAIL: malformed sugar in $sugar_negative was accepted" >&2
    exit 1
  fi
  grep -Fq '[TKZ-LANG-SUGAR]' "$WORK/$sugar_negative.transcript" || {
    echo "FAIL: $sugar_negative lacked TKZ-LANG-SUGAR" >&2
    exit 1
  }
done
echo "PASS: thirteen review regressions hold"

fail=0
for pair in s1 s2 s3 s4 s5 s6 s7 s8; do
  if ! cmp -s "$WORK/${pair}_sugar.tnlog" "$WORK/${pair}_kernel.tnlog"; then
    echo "FAIL: sugar pair $pair diverges from its kernel expansion" >&2
    diff "$WORK/${pair}_sugar.tnlog" "$WORK/${pair}_kernel.tnlog" >&2 || true
    fail=1
  fi
done
[ "$fail" -eq 0 ] && echo "PASS: 8 sugar spellings byte-identical to their expansions"

CURRENT="$WORK/current.sha256"
( cd "$WORK"
  for log in k_*.tnlog; do
    python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), "", sys.argv[1])' "$log"
  done | LC_ALL=C sort -k2
) >"$CURRENT"

if [ "$MODE" = "--snapshot" ]; then
  cp "$CURRENT" "$GOLDEN"
  echo "PASS: froze $(wc -l <"$GOLDEN" | tr -d ' ') kernel record streams"
  exit "$fail"
fi
if ! diff -u "$GOLDEN" "$CURRENT"; then
  echo "FAIL: kernel record streams diverged from their pins" >&2
  exit 1
fi
echo "PASS: $(wc -l <"$GOLDEN" | tr -d ' ') kernel record streams byte-identical"
exit "$fail"

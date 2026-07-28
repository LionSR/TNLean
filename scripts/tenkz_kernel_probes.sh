#!/usr/bin/env bash
# Gate for the kernel language stage: the seven contract fixtures pin their
# record streams, and every sugar spelling proves byte-identical events
# against its kernel expansion.  Sources: tests/tenkz/kernel/.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
KERNEL="$REPO/tests/tenkz/kernel"
GOLDEN="$KERNEL/golden.sha256"
PIXEL_GOLDEN="$KERNEL/golden-pixels.sha256"
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

atom_count=$(grep -c '^atom|' "$WORK/r_explicit_at.tnlog" || true)
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
grep -Fq '|name=cup-west-1-2|origin=cup|' "$WORK/r_cup_both.tnlog" || {
  echo "FAIL: west/east cup policies did not mint a distinct west name" >&2
  exit 1
}
grep -Fq '|name=cup-east-1-2|origin=cup|' "$WORK/r_cup_both.tnlog" || {
  echo "FAIL: west/east cup policies did not mint a distinct east name" >&2
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
wide_atom_count=$(grep -c '^atom|' "$WORK/r_wide_chain.tnlog" || true)
[ "$wide_atom_count" -eq 2 ] || {
  echo "FAIL: a chain-positioned wide atom did not claim its full span" >&2
  exit 1
}
if grep -Fq '|name=bond-1-1-1-2|origin=grid|' \
    "$WORK/r_wide_chain.tnlog"; then
  echo "FAIL: a wide atom received an internal horizontal grid bond" >&2
  exit 1
fi
grep -Fq '|name=bond-1-2-1-3|origin=grid|' \
  "$WORK/r_wide_chain.tnlog" || {
  echo "FAIL: a wide atom lost its external horizontal grid bond" >&2
  exit 1
}
grep -Fq '|addr=(1,3)|kind=tn|label=N|name=N' \
  "$WORK/r_wide_chain.tnlog" || {
  echo "FAIL: chain placement after a wide atom reused its claimed span" >&2
  exit 1
}
if grep -Fq '|name=bond-1-1-2-1|origin=grid|' \
    "$WORK/r_tall_grid.tnlog"; then
  echo "FAIL: a multi-wire atom received an internal vertical grid bond" >&2
  exit 1
fi
grep -Fq '|name=bond-1-1-1-2|origin=grid|' \
  "$WORK/r_tall_grid.tnlog" || {
  echo "FAIL: a multi-wire atom lost its external horizontal grid bond" >&2
  exit 1
}
grep -Fq '|addr=(3,1)|kind=tn|label=B|name=B' \
  "$WORK/r_tall_grid.tnlog" || {
  echo "FAIL: a new row did not advance past a multi-wire atom" >&2
  exit 1
}
for false_field in closed conjugate outline; do
  if grep -Fq "|$false_field=" "$WORK/r_false_flags.tnlog"; then
    echo "FAIL: $false_field=false enabled or materialized the flag" >&2
    exit 1
  fi
done
grep -Fq '|name=wrap-west-1|origin=trace|row=1|side=west' \
  "$WORK/r_one_sided_trace.tnlog" || {
  echo "FAIL: west=trace did not materialize its first closure wire" >&2
  exit 1
}
grep -Fq '|name=wrap-west-2|origin=trace|row=2|side=west' \
  "$WORK/r_one_sided_trace.tnlog" || {
  echo "FAIL: west=trace did not materialize one closure per row" >&2
  exit 1
}
grep -Fq '|col=1|kind=index|name=wrap-north-col-1|origin=trace|side=north' \
  "$WORK/r_one_sided_trace.tnlog" || {
  echo "FAIL: north=trace did not materialize its first closure wire" >&2
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
  grep -c '|mode=physical|name=trace-physical-' "$WORK/r_cell_policy.tnlog" ||
    true
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
if grep -Fq '|physical=none|' "$WORK/r_physical_policy.tnlog"; then
  echo "FAIL: physical=none materialized a physical port" >&2
  exit 1
fi
grep -Fq '|name=C|physical=up' "$WORK/r_physical_policy.tnlog" || {
  echo "FAIL: physical=up did not reach the carrying frame atom" >&2
  exit 1
}
grep -Fq '|name=V|' "$WORK/r_physical_policy.tnlog" || {
  echo "FAIL: the sealed-void atom disappeared from the model" >&2
  exit 1
}
if grep -F '|name=V|' "$WORK/r_physical_policy.tnlog" |
   grep -Fq '|physical='; then
  echo "FAIL: physical policy reached a sealed void" >&2
  exit 1
fi
grep -Fq '|cluster-of=C|' "$WORK/r_physical_policy.tnlog" || {
  echo "FAIL: the cluster sub-atom disappeared from the model" >&2
  exit 1
}
if grep -F '|cluster-of=C|' "$WORK/r_physical_policy.tnlog" |
   grep -Fq '|physical='; then
  echo "FAIL: physical policy reached a cluster sub-atom" >&2
  exit 1
fi
grep -Fq '|weight=bundle=3' "$WORK/r_bundle_weight.tnlog" || {
  echo "FAIL: bundle arity was not preserved in the wire record" >&2
  exit 1
}
replaced_bond_count=$(
  grep -c '|name=bond-1-2-2-2|origin=grid|' "$WORK/r_cell_policy.tnlog" ||
    true
)
[ "$replaced_bond_count" -eq 1 ] || {
  echo "FAIL: trace/open cell policies did not replace their grid bonds" >&2
  exit 1
}

selector_log="$WORK/r_selector_normalization.tnlog"
canonical_three_count=$(
  grep -Fc '|form=enclosure|members=atom-1,atom-2,atom-3' "$selector_log" ||
    true
)
[ "$canonical_three_count" -eq 2 ] || {
  echo "FAIL: range/list selectors did not share one canonical membership" >&2
  exit 1
}
grep -Fq '|form=enclosure|members=atom-2' "$selector_log" || {
  echo "FAIL: a single-address selector did not normalize to its atom" >&2
  exit 1
}
grep -Fq '|form=enclosure|members=atom-6,atom-7,atom-8,atom-9' \
    "$selector_log" || {
  echo "FAIL: a named cluster did not normalize to its generated members" >&2
  exit 1
}
if grep -Fq '|target=' "$selector_log"; then
  echo "FAIL: an author selector survived model normalization" >&2
  exit 1
fi
grep -Fq 'TENKZ-HULL-LABEL-USES=1' "$WORK/r_hull_live.tex.transcript" || {
  echo "FAIL: live hull measurement evaluated an author label more than once" >&2
  exit 1
}
grep -Fq 'TENKZ-HULL-BOX-POOL=1' "$WORK/r_hull_live.tex.transcript" || {
  echo "FAIL: live hull boxes were not reused across pictures" >&2
  exit 1
}
skin_pairing_count=$(
  grep -c '^wire.*|origin=skin|' "$WORK/k_skin_pairings.tnlog" || true
)
[ "$skin_pairing_count" -eq 16 ] || {
  echo "FAIL: declared skin pairings were not materialized as WIRE records" >&2
  exit 1
}
grep -Eq \
  '^wire.*\|host=atom-1\|.*\|name=skin-atom-1-3\|origin=skin\|species=cool' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: a slotted skin WIRE lost its host, name, or species" >&2
  exit 1
}
command -v pdftoppm >/dev/null 2>&1 || {
  echo "FAIL: kernel pixel gate requires pdftoppm" >&2
  exit 1
}
for pixel_fixture in k_skin_pairings r_hull_live r_ink_semantics; do
  if ! pdftoppm -singlefile -png -r 300 \
      "$WORK/$pixel_fixture.pdf" "$WORK/$pixel_fixture" >/dev/null 2>&1; then
    echo "FAIL: $pixel_fixture fixture could not be rasterized" >&2
    exit 1
  fi
  [ -f "$WORK/$pixel_fixture.png" ] || {
    echo "FAIL: $pixel_fixture rasterizer produced no PNG" >&2
    exit 1
  }
done
grep -Eq '^atom.*\|size=s\|.*\|species=warm($|\|)' \
  "$WORK/r_ink_semantics.tnlog" || {
  echo "FAIL: small warm atom semantics were not recorded" >&2
  exit 1
}
grep -Fq '|dir=to|' "$WORK/r_ink_semantics.tnlog" || {
  echo "FAIL: forward direction semantics were not recorded" >&2
  exit 1
}
grep -Fq '|dir=from|' "$WORK/r_ink_semantics.tnlog" || {
  echo "FAIL: reverse direction semantics were not recorded" >&2
  exit 1
}
grep -Eq '^mark.*\|form=enclosure\|.*\|species=warm($|\|)' \
  "$WORK/r_ink_semantics.tnlog" || {
  echo "FAIL: mark species semantics were not recorded" >&2
  exit 1
}
grep -Eq '^atom.*\|skin=dots\|species=gamma($|\|)' \
  "$WORK/r_ink_semantics.tnlog" || {
  echo "FAIL: ellipsis species semantics were not recorded" >&2
  exit 1
}
cluster_species_count=$(
  grep -Ec '^atom.*\|cluster-of=quad\|.*\|species=leaf($|\|)' \
    "$WORK/r_ink_semantics.tnlog" || true
)
[ "$cluster_species_count" -eq 4 ] || {
  echo "FAIL: cluster species semantics did not reach all four child dots" >&2
  exit 1
}
PIXEL_CURRENT="$WORK/current-pixels.sha256"
# This is intentionally an exact-toolchain pixel pin.  After an approved
# XeTeX, Poppler, or font update, inspect the full-resolution render and run
# this script with --snapshot to accept the new raster.
python3 -c \
  'import hashlib,sys
for path in sys.argv[1:]:
    data = open(path, "rb").read()
    print(hashlib.sha256(data).hexdigest(), "", path.rsplit("/", 1)[-1])' \
  "$WORK/k_skin_pairings.png" "$WORK/r_hull_live.png" \
  "$WORK/r_ink_semantics.png" >"$PIXEL_CURRENT"

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

selector_negative="$KERNEL/negative/n_selector_mixed.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$selector_negative" >"$WORK/n_selector_mixed.transcript" 2>&1 ); then
  echo "FAIL: a mixed atom/wire selector was accepted" >&2
  exit 1
fi
selector_kind_count=$(
  grep -Fc '[TKZ-KERNEL-SELECTOR-KIND]' \
    "$WORK/n_selector_mixed.transcript" || true
)
[ "$selector_kind_count" -eq 1 ] || {
  echo "FAIL: mixed selector did not emit exactly one selector diagnostic" >&2
  exit 1
}
if [ -f "$WORK/n_selector_mixed.tnlog" ] &&
   grep -Fq '|members=' "$WORK/n_selector_mixed.tnlog"; then
  echo "FAIL: a rejected mixed selector retained partial membership" >&2
  exit 1
fi
rm -f "$WORK"/n_selector_mixed.{aux,log,pdf,tnlog}
( cd "$WORK" &&
  TEXINPUTS="$REPO/tex/tenkz//:" \
    timeout 120 xelatex -interaction=nonstopmode \
    "$selector_negative" >"$WORK/n_selector_mixed.recovery.transcript" 2>&1
) || true
[ -f "$WORK/n_selector_mixed.pdf" ] || {
  echo "FAIL: rejected selector did not survive TeX error recovery" >&2
  exit 1
}
if grep -Eq 'TeX capacity exceeded|q_no_value|Emergency stop' \
    "$WORK/n_selector_mixed.recovery.transcript"; then
  echo "FAIL: rejected selector leaked missing membership into rendering" >&2
  exit 1
fi

missing_onwire="$KERNEL/negative/n_missing_onwire.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$missing_onwire" >"$WORK/n_missing_onwire.transcript" 2>&1 ); then
  echo "FAIL: an on-wire address accepted a missing wire" >&2
  exit 1
fi
grep -Fq '[TKZ-KERNEL-RENDER-ONWIRE]' \
    "$WORK/n_missing_onwire.transcript" || {
  echo "FAIL: missing on-wire name lacked TKZ-KERNEL-RENDER-ONWIRE" >&2
  tail -20 "$WORK/n_missing_onwire.transcript" >&2
  exit 1
}

addr_cycle="$KERNEL/negative/n_addr_cycle.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$addr_cycle" >"$WORK/n_addr_cycle.transcript" 2>&1 ); then
  echo "FAIL: a cyclic address dependency was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-ADDR-CYCLE]' "$WORK/n_addr_cycle.transcript" || {
  echo "FAIL: cyclic address dependency lacked TKZ-ADDR-CYCLE" >&2
  tail -20 "$WORK/n_addr_cycle.transcript" >&2
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

prose_negative="$KERNEL/negative/n_prose_signature.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$prose_negative" >"$WORK/n_prose_signature.transcript" 2>&1 ); then
  echo "FAIL: checked prose panel was accepted as a diagram" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-SIGNATURE]' "$WORK/n_prose_signature.transcript" || {
  echo "FAIL: checked prose rejection lacked TKZ-EQ-SIGNATURE" >&2
  exit 1
}
grep -Fq 'result=mismatch|reason=prose' "$WORK/n_prose_signature.tnlog" || {
  echo "FAIL: checked prose mismatch was not recorded before the hard error" >&2
  exit 1
}

cluster_negative="$KERNEL/negative/n_unnamed_cluster.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$cluster_negative" >"$WORK/n_unnamed_cluster.transcript" 2>&1 ); then
  echo "FAIL: an unnamed cluster was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-CLUSTER-NAME]' "$WORK/n_unnamed_cluster.transcript" || {
  echo "FAIL: unnamed cluster rejection lacked TKZ-LANG-CLUSTER-NAME" >&2
  exit 1
}

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

physical_negative="$KERNEL/negative/n_malformed_physical.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$physical_negative" >"$WORK/n_malformed_physical.transcript" 2>&1 ); then
  echo "FAIL: malformed physical sugar was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-CHOICE]' "$WORK/n_malformed_physical.transcript" || {
  echo "FAIL: malformed physical rejection lacked TKZ-LANG-CHOICE" >&2
  exit 1
}
grep -Fq '(record picture)' "$WORK/n_malformed_physical.transcript" || {
  echo "FAIL: malformed physical rejection dropped its record context" >&2
  exit 1
}

for strict_negative in \
  n_strict_sandwich \
  n_strict_role \
  n_strict_tnbond \
  n_strict_tnprose
do
  source="$KERNEL/negative/$strict_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$strict_negative.transcript" 2>&1 ); then
    echo "FAIL: $strict_negative survived strict mode" >&2
    exit 1
  fi
  grep -Fq '[TKZ-LANG-STRICT]' "$WORK/$strict_negative.transcript" || {
    echo "FAIL: $strict_negative lacked TKZ-LANG-STRICT" >&2
    exit 1
  }
done

for contract_negative in \
  n_one_end_wire \
  n_malformed_via \
  n_malformed_cross \
  n_malformed_mark_target \
  n_noncell_leg
do
  source="$KERNEL/negative/$contract_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$contract_negative.transcript" 2>&1 ); then
    echo "FAIL: $contract_negative was accepted" >&2
    exit 1
  fi
  expected='[TKZ-LANG-ADDRESS]'
  [ "$contract_negative" = n_one_end_wire ] &&
    expected='[TKZ-LANG-WIRE-ARITY]'
  grep -Fq "$expected" "$WORK/$contract_negative.transcript" || {
    echo "FAIL: $contract_negative lacked $expected" >&2
    exit 1
  }
done
grep -Eq '\(node addr-[0-9]+\)' "$WORK/n_noncell_leg.transcript" || {
  echo "FAIL: the non-cell leg rejection dropped its node context" >&2
  exit 1
}

occupied_negative="$KERNEL/negative/n_occupied_span.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$occupied_negative" >"$WORK/n_occupied_span.transcript" 2>&1 ); then
  echo "FAIL: overlapping atom spans were accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-OCCUPANCY]' "$WORK/n_occupied_span.transcript" || {
  echo "FAIL: overlapping atom spans lacked TKZ-LANG-OCCUPANCY" >&2
  exit 1
}

picture_check_negative="$KERNEL/negative/n_picture_check.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$picture_check_negative" >"$WORK/n_picture_check.transcript" 2>&1 ); then
  echo "FAIL: picture-scoped check= was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-CHECK-SCOPE]' "$WORK/n_picture_check.transcript" || {
  echo "FAIL: picture-scoped check= lacked TKZ-EQ-CHECK-SCOPE" >&2
  exit 1
}

for span_negative in n_nonpositive_span n_nonnumeric_span; do
  source="$KERNEL/negative/$span_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$span_negative.transcript" 2>&1 ); then
    echo "FAIL: invalid atom span in $span_negative was accepted" >&2
    exit 1
  fi
  grep -Fq '[TKZ-ATOM-POSITIVE-INTEGER]' \
    "$WORK/$span_negative.transcript" || {
    echo "FAIL: $span_negative lacked TKZ-ATOM-POSITIVE-INTEGER" >&2
    exit 1
  }
done

skin_slot_negative="$KERNEL/negative/n_skin_pairing_slot.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_slot_negative" >"$WORK/n_skin_pairing_slot.transcript" 2>&1 ); then
  echo "FAIL: an out-of-range skin pairing slot was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-SKIN-PAIRING-SLOT]' \
  "$WORK/n_skin_pairing_slot.transcript" || {
  echo "FAIL: an out-of-range skin pairing lacked TKZ-SKIN-PAIRING-SLOT" >&2
  exit 1
}

weight_negative="$KERNEL/negative/n_malformed_weight.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$weight_negative" >"$WORK/n_malformed_weight.transcript" 2>&1 ); then
  echo "FAIL: malformed bundle arity was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-CHOICE]' "$WORK/n_malformed_weight.transcript" || {
  echo "FAIL: malformed bundle arity lacked TKZ-LANG-CHOICE" >&2
  exit 1
}
grep -Fq '(record wire-1)' "$WORK/n_malformed_weight.transcript" || {
  echo "FAIL: malformed bundle arity dropped its record context" >&2
  exit 1
}

bundle_signature="$KERNEL/negative/n_bundle_signature.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$bundle_signature" >"$WORK/n_bundle_signature.transcript" 2>&1 ); then
  echo "FAIL: bundle arity was ignored by the signature audit" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-SIGNATURE]' "$WORK/n_bundle_signature.transcript" || {
  echo "FAIL: bundle signature mismatch lacked TKZ-EQ-SIGNATURE" >&2
  exit 1
}
grep -Fq 'result=mismatch' "$WORK/n_bundle_signature.tnlog" || {
  echo "FAIL: bundle signature mismatch was not recorded" >&2
  exit 1
}

grep -Fq 'result=equal|modulo=bundles' "$WORK/r_bundle_modulo.tnlog" || {
  echo "FAIL: bundle regrouping did not pass modulo bundles" >&2
  exit 1
}

bundle_modulo_negative="$KERNEL/negative/n_bundle_modulo_mismatch.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$bundle_modulo_negative" \
       >"$WORK/n_bundle_modulo_mismatch.transcript" 2>&1 ); then
  echo "FAIL: wrong bundle multiplicity passed modulo bundles" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-SIGNATURE]' \
  "$WORK/n_bundle_modulo_mismatch.transcript" || {
  echo "FAIL: bundle modulo mismatch lacked TKZ-EQ-SIGNATURE" >&2
  exit 1
}
grep -Fq 'result=mismatch|modulo=bundles' \
  "$WORK/n_bundle_modulo_mismatch.tnlog" || {
  echo "FAIL: bundle modulo mismatch was not recorded" >&2
  exit 1
}

for arity_negative in n_missing_relation n_dangling_relation; do
  source="$KERNEL/negative/$arity_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$arity_negative.transcript" 2>&1 ); then
    echo "FAIL: malformed equation $arity_negative was accepted" >&2
    exit 1
  fi
  grep -Fq '[TKZ-EQ-ARITY]' "$WORK/$arity_negative.transcript" || {
    echo "FAIL: $arity_negative lacked TKZ-EQ-ARITY" >&2
    exit 1
  }
  grep -Fq 'result=malformed|reason=relation-count' \
    "$WORK/$arity_negative.tnlog" || {
    echo "FAIL: $arity_negative did not record its relation-count failure" >&2
    exit 1
  }
done

off_count=$(grep -c 'result=off' "$WORK/r_multiple_off.tnlog" || true)
[ "$off_count" -eq 2 ] || {
  echo "FAIL: multiple equation opt-outs did not each emit an event" >&2
  exit 1
}
grep -Fq 'check|relation=1|result=off|reason=first' \
  "$WORK/r_multiple_off.tnlog" || {
  echo "FAIL: the first equation opt-out was not preserved" >&2
  exit 1
}
grep -Fq 'check|relation=3|result=off|reason=third' \
  "$WORK/r_multiple_off.tnlog" || {
  echo "FAIL: the later equation opt-out was silently dropped" >&2
  exit 1
}
echo "PASS: fifty review regressions hold"

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
  cp "$PIXEL_CURRENT" "$PIXEL_GOLDEN"
  echo "PASS: froze $(wc -l <"$GOLDEN" | tr -d ' ') kernel record streams"
  echo "PASS: froze kernel pixel baselines"
  exit "$fail"
fi
if ! diff -u "$GOLDEN" "$CURRENT"; then
  echo "FAIL: kernel record streams diverged from their pins" >&2
  exit 1
fi
echo "PASS: $(wc -l <"$GOLDEN" | tr -d ' ') kernel record streams byte-identical"
if ! diff -u "$PIXEL_GOLDEN" "$PIXEL_CURRENT"; then
  echo "FAIL: kernel pixels diverged from their pins" >&2
  exit 1
fi
echo "PASS: kernel pixels byte-identical"
exit "$fail"

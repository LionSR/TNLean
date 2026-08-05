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
for side in west east; do
  grep -Eq "^atom\|.*\|node=.*\|skin=ring" "$WORK/r_cup_label.tnlog" || {
    echo "FAIL: the labelled cup minted no bead on its bend" >&2
    exit 1
  }
  grep -Fq "|name=cup-$side-1-2|origin=cup|" "$WORK/r_cup_label.tnlog" || {
    echo "FAIL: the labelled cup lost the $side bend it stands on" >&2
    exit 1
  }
done
labelled_cup_beads=$(grep -c '^atom|.*|skin=ring' "$WORK/r_cup_label.tnlog" \
  || true)
[ "$labelled_cup_beads" -eq 4 ] || {
  echo "FAIL: labelled cups minted $labelled_cup_beads beads, expected 4" >&2
  exit 1
}
for members in \
  'members=atom-2,atom-3,atom-4' \
  'members=atom-1,atom-2,atom-3,atom-4,atom-5,atom-6'; do
  grep -F '|form=bracket|' "$WORK/r_mark_bracket_range.tnlog" |
    grep -Fq "|$members" || {
    echo "FAIL: a bracket over a cell range resolved no membership" >&2
    exit 1
  }
done
grep -Fq '|name=bond-1-1-1-2|origin=grid|' "$WORK/k_blocking.tnlog" || {
  echo "FAIL: bonds=grid did not materialize the adjacent WIRE record" >&2
  exit 1
}
[ "$(grep -c '|origin=open|' \
      "$WORK/r_plane_open_perimeter.tnlog" || true)" -eq 12 ] || {
  echo "FAIL: four open plane sides did not materialize 12 perimeter wires" >&2
  exit 1
}
[ "$(grep -c '|origin=grid|' \
      "$WORK/r_plane_open_perimeter.tnlog" || true)" -eq 12 ] || {
  echo "FAIL: the open 3x3 plane did not retain 12 interior grid bonds" >&2
  exit 1
}
for side in west east north south; do
  [ "$(grep -F '|origin=open|' "$WORK/r_plane_open_perimeter.tnlog" | \
        grep -c "|side=$side|" || true)" -eq 3 ] || {
    echo "FAIL: plane side $side did not own three open wires" >&2
    exit 1
  }
done
open_perimeter=$(grep -F '|origin=open|' \
  "$WORK/r_plane_open_perimeter.tnlog")
[ "$(printf '%s\n' "$open_perimeter" | \
      grep -Ec '\|(from|to)=addr-[0-9]+' || true)" -eq 12 ] || {
  echo "FAIL: a plane-side opening lost its boundary-cell endpoint" >&2
  exit 1
}
[ "$(printf '%s\n' "$open_perimeter" | \
      grep -Ec '\|(from|to)-open=[nesw](\||$)' || true)" -eq 12 ] || {
  echo "FAIL: a plane-side opening lost its exterior endpoint" >&2
  exit 1
}
grep -Fxq \
  'kernel-boundary|signature=open:e, open:e, open:e, open:n, open:n, open:n, open:s, open:s, open:s, open:w, open:w, open:w' \
  "$WORK/r_plane_open_perimeter.tnlog" || {
  echo "FAIL: the open 3x3 plane did not expose its twelve perimeter indices" >&2
  exit 1
}
if grep -Fq '|origin=port-open|' \
    "$WORK/r_plane_open_perimeter.tnlog"; then
  echo "FAIL: explicit open sides left duplicate typed-port stubs" >&2
  exit 1
fi
grep -Fq '|name=wrap-1|origin=trace|row=1|' "$WORK/k_twoshift.tnlog" || {
  echo "FAIL: trace policy did not derive the per-row wrap-1 record" >&2
  exit 1
}
grep -Fq '|origin=trace|' "$WORK/r_closure_typed_ports.tnlog" || {
  echo "FAIL: typed-port trace closure emitted no trace record" >&2
  exit 1
}
grep -Fq '|origin=cup|' "$WORK/r_closure_typed_ports.tnlog" || {
  echo "FAIL: typed-port cup closure emitted no cup record" >&2
  exit 1
}
if grep -Fq '|origin=port-open|' "$WORK/r_closure_typed_ports.tnlog"; then
  echo "FAIL: trace/cup closure left duplicate typed-port stubs" >&2
  exit 1
fi
if grep -Fq '|origin=port-open|' "$WORK/r_closure_implicit_virtual.tnlog"; then
  echo "FAIL: implicit closure endpoints grew open-port stubs" >&2
  exit 1
fi
grep -Fq 'stringbead|id=cup-1-2|t=0.5' "$WORK/r_onwire_cup_arc.tnlog" || {
  echo "FAIL: a place on a generated cup was not measured along the cup" >&2
  exit 1
}
if grep -Fq 'stringbead|id=run|' "$WORK/r_onwire_cup_arc.tnlog"; then
  echo "FAIL: a straight run stopped dividing its own run" >&2
  exit 1
fi
awk -F'|' '
  /^picture\|id=k2\|/ { exit }
  /^glyph-geometry\|/ {
    for (i = 1; i <= NF; i++) {
      split($i, kv, "=")
      if (kv[1] == "xmin") lo = kv[2] + 0
      if (kv[1] == "xmax") hi = kv[2] + 0
    }
    if (n == 1) east = prev
    else if (n > 1 && prev > east) east = prev
    prev = hi
    centre = (lo + hi) / 2
    n++
  }
  END { exit !(n > 1 && centre > east) }
' "$WORK/r_onwire_cup_arc.tnlog" || {
  echo "FAIL: the operator on the cup stands on the chord, not the arc" >&2
  exit 1
}
chain_ports=$(awk '/^picture\|id=k2\|/ { exit } /^wire\|.*origin=port-open/' \
  "$WORK/r_ports_chain_placed.tnlog" | sed 's/|from=addr-[0-9]*//')
at_ports=$(awk '/^picture\|id=k2\|/ { seen = 1 }
  seen && /^wire\|.*origin=port-open/' \
  "$WORK/r_ports_chain_placed.tnlog" | sed 's/|from=addr-[0-9]*//')
[ -n "$chain_ports" ] && [ "$chain_ports" = "$at_ports" ] || {
  echo "FAIL: chain-placed and at-placed atoms declared different ports" >&2
  exit 1
}
[ "$(grep -Fc 'kernel-boundary|signature=phys:n, phys:n, phys:s, phys:s' \
      "$WORK/r_ports_chain_placed.tnlog" || true)" -eq 2 ] || {
  echo "FAIL: the two placements reached different open physical boundaries" >&2
  exit 1
}
chain_pairing=$(awk '/^picture\|id=k2\|/ { exit } /^wire\|/' \
  "$WORK/r_skin_pairing_chain_placed.tnlog" | sed 's/addr-[0-9]*/addr/g')
at_pairing=$(awk '/^picture\|id=k2\|/ { seen = 1 }
  seen && /^wire\|/' \
  "$WORK/r_skin_pairing_chain_placed.tnlog" | sed 's/addr-[0-9]*/addr/g')
[ -n "$chain_pairing" ] && [ "$chain_pairing" = "$at_pairing" ] || {
  echo "FAIL: a declared skin's pairings differ between the two placements" >&2
  exit 1
}
[ "$(grep -Fc \
      'kernel-boundary|signature=open:e, open:w, phys:n, phys:n, phys:s, phys:s' \
      "$WORK/r_skin_pairing_chain_placed.tnlog" || true)" -eq 2 ] || {
  echo "FAIL: a chained pairing carrier reached a different boundary" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=phys:n' \
    "$WORK/r_port_physical_open.tnlog" || {
  echo "FAIL: physical port type did not reach its explicit open boundary" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=phys:n' \
    "$WORK/r_cell_policy_typed_ports.tnlog" || {
  echo "FAIL: matching physical-open policy lost its physical boundary" >&2
  exit 1
}
grep -Fxq 'kernel-boundary|signature=phys:n, phys:s' \
    "$WORK/r_planes_transverse_open.tnlog" || {
  echo "FAIL: bilayer transverse opens did not reach the boundary signature" >&2
  exit 1
}
grep -Fq '|port-type=physical|to-open-type=physical|to-open=up' \
    "$WORK/r_planes_transverse_open.tnlog" || {
  echo "FAIL: the ket member's transverse open lost its physical typing" >&2
  exit 1
}
grep -Fq '|port-type=physical|to-open-type=physical|to-open=down' \
    "$WORK/r_planes_transverse_open.tnlog" || {
  echo "FAIL: the bra member's transverse open lost its physical typing" >&2
  exit 1
}
for bearing in e n w s; do
  grep -Eq "^wire\|.*\|dir=to\|.*\|kind=index\|.*\|port-type=physical\|.*\|to-open=$bearing\$" \
      "$WORK/r_physical_dir.tnlog" || {
    echo "FAIL: directed physical open end lost its typed record bearing $bearing" >&2
    exit 1
  }
done
# The direction mark rides the leg's daylight, so it inks on every bearing:
# the fixture's own assertions place each barb between the silhouette it
# leaves and the free tip, whichever end of the leg is the open one.
for bearing in e n w s; do
  grep -Eq "^wire\|.*\|dir=to\|.*\|kind=index\|.*\|to-open=$bearing\$" \
      "$WORK/r_dir_open_bearings.tnlog" || {
    echo "FAIL: the departing open leg lost bearing $bearing" >&2
    exit 1
  }
  grep -Eq "^wire\|.*\|dir=to\|from-open=$bearing\|kind=index\|.*\|to=addr-" \
      "$WORK/r_dir_open_bearings.tnlog" || {
    echo "FAIL: the arriving open leg lost bearing $bearing" >&2
    exit 1
  }
done
# A wire declares its stroke; the absent key and solid= are the same rail.
for spelling in dashed dotted; do
  [ "$(grep -c "|stroke=$spelling|" "$WORK/r_wire_stroke.tnlog" || true)" \
      -eq 2 ] || {
    echo "FAIL: the $spelling rail count changed" >&2
    exit 1
  }
done
grep -Eq '^wire\|.*\|name=plain\|to=addr-' "$WORK/r_wire_stroke.tnlog" || {
  echo "FAIL: an undeclared rail acquired a stroke field" >&2
  exit 1
}
grep -Fq '|name=said|stroke=solid|' "$WORK/r_wire_stroke.tnlog" || {
  echo "FAIL: the solid spelling lost its recorded default" >&2
  exit 1
}
grep -Eq '^wire\|.*dir=to\|.*kind=index\|.*name=inner\|.*port-type=physical\|to=addr-' \
    "$WORK/r_physical_dir.tnlog" || {
  echo "FAIL: internal directed physical contraction lost its typed record" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=phys:e:to, phys:n:to, phys:s:to, phys:w:to' \
    "$WORK/r_physical_dir.tnlog" || {
  echo "FAIL: directed physical open ends lost their oriented boundary" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=phys:n:from' \
    "$WORK/r_physical_dir.tnlog" || {
  echo "FAIL: the entering physical open end lost its oriented boundary" >&2
  exit 1
}
physical_dir_boundaries=$(grep -c '^kernel-boundary|' \
  "$WORK/r_physical_dir.tnlog" || true)
[ "$physical_dir_boundaries" -eq 3 ] || {
  echo "FAIL: the directed physical fixture changed its picture count" >&2
  exit 1
}
awk -F'signature=' '/^kernel-boundary\|/ { print $2 }' \
    "$WORK/r_physical_dir.tnlog" | sed -n '2p' | grep -q '^$' || {
  echo "FAIL: an internal directed physical contraction left a boundary entry" >&2
  exit 1
}
grep -Fq \
    '|cross=over at crossing of open-arc and port-open-1|' \
    "$WORK/r_route_open_all_arc.tnlog" || {
  echo "FAIL: bare open all-side route omitted its traversed port" >&2
  exit 1
}
grep -Fq \
    'stringcross|under=port-open-1|over=open-arc|hits=1' \
    "$WORK/r_route_open_all_arc.tnlog" || {
  echo "FAIL: bare open all-side route did not meet its traversed port" >&2
  exit 1
}
if ! grep -F 'name=north-route' "$WORK/r_route_noncell_port.tnlog" |
     grep -Fq 'cross=over at crossing of north-route and port-open-1'; then
  echo "FAIL: a midpoint carrier was omitted from its routed crossing set" >&2
  exit 1
fi
grep -Fq \
    'stringcross|under=port-open-1|over=north-route|hits=1' \
    "$WORK/r_route_noncell_port.tnlog" || {
  echo "FAIL: a midpoint carrier port did not reach its routed crossing" >&2
  exit 1
}
if ! grep -F 'name=onwire-route' "$WORK/r_route_noncell_port.tnlog" |
     grep -Fq 'cross=over at crossing of onwire-route and port-open-1'; then
  echo "FAIL: an on-wire carrier was omitted from its routed crossing set" >&2
  exit 1
fi
grep -Fq \
    'stringcross|under=port-open-1|over=onwire-route|hits=1' \
    "$WORK/r_route_noncell_port.tnlog" || {
  echo "FAIL: an on-wire carrier port did not reach its routed crossing" >&2
  exit 1
}
off_face_route=$(
  grep -F 'name=off-face-route' "$WORK/r_route_noncell_port.tnlog"
) || {
  echo "FAIL: off-face route emitted no record" >&2
  exit 1
}
if printf '%s\n' "$off_face_route" | grep -Fq 'port-open-1'; then
  echo "FAIL: off-face route collected its carrier's east port" >&2
  exit 1
fi
address_route=$(
  grep -F 'name=address-route' "$WORK/r_route_address_all_faces.tnlog"
) || {
  echo "FAIL: address-bearing all-side route emitted no record" >&2
  exit 1
}
address_crossings='cross=over at crossing of address-route and port-open-1,'
address_crossings="${address_crossings}over at crossing of address-route and port-open-2"
printf '%s\n' "$address_route" |
  grep -Fq "$address_crossings" || {
  echo "FAIL: NE-to-SW all-side route lost its north-west face order" >&2
  exit 1
}
if printf '%s\n' "$address_route" | grep -Eq 'port-open-[34]'; then
  echo "FAIL: NE-to-SW all-side route collected an untraversed face" >&2
  exit 1
fi
wrap_route=$(
  grep -F 'name=wrap-route' "$WORK/r_route_address_all_faces.tnlog"
) || {
  echo "FAIL: wrapped address-bearing all-side route emitted no record" >&2
  exit 1
}
wrap_crossings='cross=under at crossing of wrap-route and port-open-1,'
wrap_crossings="${wrap_crossings}over at crossing of wrap-route and port-open-2"
printf '%s\n' "$wrap_route" |
  grep -Fq "$wrap_crossings" || {
  echo "FAIL: SE-to-NW all-side route lost its east-north face order" >&2
  exit 1
}
same_corner_route=$(
  grep -F 'name=same-corner-route' "$WORK/r_route_address_all_faces.tnlog"
) || {
  echo "FAIL: same-corner all-side route emitted no record" >&2
  exit 1
}
if printf '%s\n' "$same_corner_route" | grep -Fq 'port-open-'; then
  echo "FAIL: same-corner all-side route invented a hull-face crossing" >&2
  exit 1
fi
dependent_route=$(
  grep -F 'name=dependent-route' "$WORK/r_route_address_all_faces.tnlog"
) || {
  echo "FAIL: named-string-dependent all-side route emitted no record" >&2
  exit 1
}
for crossing in \
  'over at crossing of dependent-route and carrier' \
  'over at crossing of dependent-route and port-open-1' \
  'over at crossing of dependent-route and port-open-2'
do
  printf '%s\n' "$dependent_route" | grep -Fq "$crossing" || {
    echo "FAIL: named-string-dependent route lost $crossing" >&2
    exit 1
  }
done
grep -Fq 'name=clearance-route' \
    "$WORK/r_route_address_all_faces.tnlog" || {
  echo "FAIL: address in the hull clearance annulus was rejected" >&2
  exit 1
}
grep -Fq 'name=selected-port-route' \
    "$WORK/r_route_address_all_faces.tnlog" || {
  echo "FAIL: a selected authored port was rejected as an inside route end" >&2
  exit 1
}
exact_route=$(
  grep -F 'name=exact-route' "$WORK/r_route_dependent_turns.tnlog"
) || {
  echo "FAIL: exact all-side route emitted no record" >&2
  exit 1
}
for crossing in \
  'over at crossing of exact-route and port-open-1' \
  'over at crossing of exact-route and port-open-2'
do
  printf '%s\n' "$exact_route" | grep -Fq "$crossing" || {
    echo "FAIL: exact all-side route lost $crossing" >&2
    exit 1
  }
done
grep -Fq 'string|id=precision-route|kind=open|pts=5' \
    "$WORK/r_route_dependent_turns.tnlog" || {
  echo "FAIL: native coordinate precision collapsed a representable turn" >&2
  exit 1
}
deferred_route=$(
  grep -F 'name=h' "$WORK/r_route_dependent_turns.tnlog"
) || {
  echo "FAIL: leg-dependent all-side route emitted no record" >&2
  exit 1
}
if printf '%s\n' "$deferred_route" | grep -Fq 'leg-s-1-1'; then
  echo "FAIL: leg-dependent route used the pre-settlement default turn" >&2
  exit 1
fi
for crossing in \
  'stringcross|under=port-open-1|over=address-route|hits=1' \
  'stringcross|under=port-open-2|over=address-route|hits=1' \
  'stringcross|under=wrap-route|over=port-open-1|hits=1' \
  'stringcross|under=port-open-2|over=wrap-route|hits=1' \
  'stringcross|under=carrier|over=dependent-route|hits=1' \
  'stringcross|under=port-open-1|over=dependent-route|hits=1' \
  'stringcross|under=port-open-2|over=dependent-route|hits=1'
do
  grep -Fq "$crossing" "$WORK/r_route_address_all_faces.tnlog" || {
    echo "FAIL: address-bearing all-side route missed $crossing" >&2
    exit 1
  }
done
grep -Fq \
    'stringcross|under=probe|over=port-open-1|hits=1' \
    "$WORK/r_port_open_crossing.tnlog" || {
  echo "FAIL: explicit crossing did not lengthen the generated port leg" >&2
  exit 1
}
grep -Fq \
    'stringcross|under=near-probe|over=port-open-1|hits=1' \
    "$WORK/r_port_open_crossing.tnlog" || {
  echo "FAIL: generated port reach discarded one of several references" >&2
  exit 1
}
grep -Fq 'string|id=horizontal|kind=wind|class=1,0|pts=12' \
    "$WORK/k_torus.tnlog" || {
  echo "FAIL: the horizontal torus class did not reach the winding renderer" >&2
  exit 1
}
grep -Fq 'string|id=vertical|kind=wind|class=0,1|pts=12' \
    "$WORK/k_torus.tnlog" || {
  echo "FAIL: the vertical torus class did not reach the winding renderer" >&2
  exit 1
}
plane_frame=$(grep '^frame|' "$WORK/k_plane.tnlog") || {
  echo "FAIL: frame=plane emitted no frame record" >&2
  exit 1
}
plane_frame_canonical=$(
  printf '%s\n' "$plane_frame" |
    sed -E 's/^frame\|id=frame-[0-9]+\|/frame|/'
)
[ "$plane_frame_canonical" = \
  'frame|a=-0.45|b=1|c=-0.60|d=0|dx=-0.55|dy=0.60|map=plane|scope=picture|transverse-x=0|transverse-y=1' ] || {
  echo "FAIL: frame=plane did not record the fixed projected basis" >&2
  exit 1
}
plane_physical_open=$(grep -F '|from=addr-13|' "$WORK/k_plane.tnlog") || {
  echo "FAIL: the plane fixture lost its projected open physical port" >&2
  exit 1
}
for field in '|kind=index|' '|port-type=physical|' \
             '|to-open-type=physical|' '|to-open=n'
do
  printf '%s\n' "$plane_physical_open" | grep -Fq "$field" || {
    echo "FAIL: the plane fixture lost physical open field $field" >&2
    exit 1
  }
done
[ "$(grep -c '|origin=port-open|' \
      "$WORK/r_unmatched_port_legs.tnlog" || true)" -eq 10 ] || {
  echo "FAIL: unmatched typed ports did not materialize exactly ten open legs" >&2
  exit 1
}
[ "$(grep -c '|origin=port-open|' \
      "$WORK/r_many_unmatched_ports.tnlog" || true)" -eq 36 ] || {
  echo "FAIL: high-multiplicity typed ports did not materialize 36 open legs" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=phys:45, phys:n' \
    "$WORK/r_unmatched_port_legs.tnlog" || {
  echo "FAIL: flat unmatched ports lost their typed boundary bearings" >&2
  exit 1
}
grep -Fq 'kernel-boundary|signature=open:22.479434, phys:53.130102' \
    "$WORK/r_unmatched_port_legs.tnlog" || {
  echo "FAIL: plane unmatched ports lost their transported boundary bearings" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_unmatched_port_legs.tnlog" \
  "$KERNEL/regression/r_unmatched_port_legs.tex" >/dev/null || {
  echo "FAIL: unmatched typed ports leaked a private open-end sentinel" >&2
  exit 1
}
[ "$(grep -Ec 'check\|scope=[0-9]+\|relation=1\|result=equal' \
      "$WORK/r_physical_port_signature_equiv.tnlog" || true)" -eq 6 ] || {
  echo "FAIL: in-plane physical policy sugar diverged from explicit typed ports" >&2
  exit 1
}
[ "$(grep -c '^frame|.*|transverse-x=0|transverse-y=1$' \
      "$WORK/r_plane_transverse_physical.tnlog" || true)" -eq 3 ] || {
  echo "FAIL: plane frames did not expose their transverse physical axis" >&2
  exit 1
}
for signature in \
  'open:233.130102, open:53.130102, open:e, open:w, phys:n' \
  'open:233.130102, open:53.130102, open:e, open:w, phys:s' \
  'open:233.130102, open:53.130102, open:e, open:w, phys:n, phys:s'
do
  grep -Fq "kernel-boundary|signature=$signature" \
      "$WORK/r_plane_transverse_physical.tnlog" || {
    echo "FAIL: plane transverse policy lost boundary $signature" >&2
    exit 1
  }
done
[ "$(grep -c '|origin=port-open|' \
      "$WORK/r_plane_transverse_physical.tnlog" || true)" -eq 12 ] || {
  echo "FAIL: plane transverse policy consumed an in-plane virtual port" >&2
  exit 1
}
[ "$(grep -c 'kernel-boundary|signature=$' \
      "$WORK/r_unmatched_port_legs.tnlog" || true)" -eq 5 ] || {
  echo "FAIL: explicitly wired ports retained an implicit open leg" >&2
  exit 1
}
basis_atom_count=$(grep -c '^atom|' "$WORK/r_basis_plane.tnlog" || true)
[ "$basis_atom_count" -eq 3 ] || {
  echo "FAIL: the declared basis did not populate three member atoms" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+,atom-[0-9]+,atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_plane.tnlog" || {
  echo "FAIL: selecting one basis cell did not select all three members" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_plane.tnlog" || {
  echo "FAIL: a three-coordinate address did not select one basis member" >&2
  exit 1
}
basis_override_atoms=$(grep -c '^atom|' "$WORK/r_basis_override.tnlog" || true)
[ "$basis_override_atoms" -eq 2 ] || {
  echo "FAIL: an authored basis member did not override population" >&2
  exit 1
}
override_selection_atoms=$(
  grep -c '^atom|' "$WORK/r_basis_override_selection.tnlog" || true
)
[ "$override_selection_atoms" -eq 64 ] || {
  echo "FAIL: whole-cell overrides did not suppress their basis members" >&2
  exit 1
}
grep -Eq '^atom.*[|]name=X([|]|$)' \
    "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: the whole-cell override record disappeared" >&2
  exit 1
}
if grep -E '^atom.*[|]name=X([|]|$)' \
    "$WORK/r_basis_override_selection.tnlog" | grep -Fq '|member='; then
  echo "FAIL: a whole-cell override became a basis-member record" >&2
  exit 1
fi
override_spacing_count=$(
  grep -Fc '|code=basis-spacing|' \
    "$WORK/r_basis_override_selection.tnlog" || true
)
[ "$override_spacing_count" -eq 6 ] || {
  echo "FAIL: realized and suppressed basis collisions were not distinguished" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k2|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: a realized collision after a partial override was not diagnosed" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k4|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: an authored member replacement left the spacing population" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k6|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=1|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: a spanning member lost its canonical-anchor collision" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k9|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=1|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: an outside canonical anchor left the spacing population" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k10|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: the dense basis fast path changed its deterministic witness" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k11|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: one override restored the live-record cross product" >&2
  exit 1
}
if grep -Eq '^warning[|]picture=k(1|3|5|7|8|12)[|]code=basis-spacing[|]' \
    "$WORK/r_basis_override_selection.tnlog"; then
  echo "FAIL: suppressed, aliased, or stale basis state emitted a warning" >&2
  exit 1
fi
override_spacing_messages=$(
  grep -Fc '[TKZ-FRAME-BASIS-SPACING]' \
    "$WORK/r_basis_override_selection.tex.transcript" || true
)
[ "$override_spacing_messages" -eq 6 ] || {
  echo "FAIL: override spacing events and human diagnostics diverged" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_override_selection.tnlog" || {
  echo "FAIL: a whole-cell override was selected more than once" >&2
  exit 1
}
if ! grep -F '|addr=(1,1,1)|' "$WORK/r_basis_override.tnlog" |
     grep -F '|member=1|' | grep -Eq '[|]name=X([|]|$)'; then
  echo "FAIL: an authored member lost its normalized basis address" >&2
  exit 1
fi
outside_translation_atoms=$(
  grep -c '^atom|' "$WORK/r_basis_outside_translation.tnlog" || true
)
[ "$outside_translation_atoms" -eq 8 ] || {
  echo "FAIL: the outside-anchor translation fixture lost a basis record" >&2
  exit 1
}
outside_translation_count=$(
  grep -Fc '|code=basis-spacing|' \
    "$WORK/r_basis_outside_translation.tnlog" || true
)
[ "$outside_translation_count" -eq 1 ] || {
  echo "FAIL: the complete canonical-anchor translation was not unique" >&2
  exit 1
}
grep -Fxq \
  'warning|picture=k1|code=basis-spacing|member-a=1|member-b=2|dr=2|dc=2|dist=0|floor=0.327573|margin=-0.327573094' \
  "$WORK/r_basis_outside_translation.tnlog" || {
  echo "FAIL: the row/column-zero anchor collision was not diagnosed" >&2
  exit 1
}
outside_translation_messages=$(
  grep -Fc '[TKZ-FRAME-BASIS-SPACING]' \
    "$WORK/r_basis_outside_translation.tex.transcript" || true
)
[ "$outside_translation_messages" -eq 1 ] || {
  echo "FAIL: outside-anchor event and human diagnostic diverged" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_basis_outside_translation.tnlog" \
  "$KERNEL/regression/r_basis_outside_translation.tex" >/dev/null || {
  echo "FAIL: the outside-anchor stream did not pass the one-pass audit" >&2
  exit 1
}
grep -Fq '|name=bond-1-1-1-2|origin=grid|' \
    "$WORK/r_basis_override.tnlog" || {
  echo "FAIL: an explicit origin singleton lost ordinary grid bonds" >&2
  exit 1
}
replacement_atoms=$(grep -c '^atom|' "$WORK/r_basis_frame_replace.tnlog" || true)
[ "$replacement_atoms" -eq 1 ] || {
  echo "FAIL: a replaced frame retained its earlier basis population" >&2
  exit 1
}
if grep -Eq '^atom.*[|]member=' "$WORK/r_basis_frame_replace.tnlog"; then
  echo "FAIL: a replaced frame retained basis member metadata" >&2
  exit 1
fi
equation_basis_atoms=$(grep -c '^atom|' "$WORK/r_basis_equation.tnlog" || true)
[ "$equation_basis_atoms" -eq 4 ] || {
  echo "FAIL: an inherited equation basis was not populated in both panels" >&2
  exit 1
}
[ "$(grep -Ec '^atom.*[|]member=[12]([|]|$)' \
      "$WORK/r_basis_equation.tnlog" || true)" -eq 4 ] || {
  echo "FAIL: an inherited equation basis lost its member indices" >&2
  exit 1
}
if grep -Eq '^atom.*[|]member=' "$WORK/r_basis_equation_replace.tnlog"; then
  echo "FAIL: an outer bare frame retained a panel basis" >&2
  exit 1
fi
grep -Eq '^mark.*[|]members=atom-[0-9]+([|]|$)' \
    "$WORK/r_default_basis_member.tnlog" || {
  echo "FAIL: default basis member one did not resolve to the ordinary cell" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+,atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_range_empty.tnlog" || {
  echo "FAIL: a range over an empty row did not retain both populated rows" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_range_explicit_empty.tnlog" || {
  echo "FAIL: an explicit-basis range did not skip an empty cell" >&2
  exit 1
}
grep -Eq '^mark.*[|]members=atom-[0-9]+([|]|$)' \
    "$WORK/r_basis_padded_address.tnlog" || {
  echo "FAIL: a padded member address did not resolve canonically" >&2
  exit 1
}
[ "$(grep -c '^atom|' "$WORK/r_basis_member_wide.tnlog" || true)" -eq 1 ] || {
  echo "FAIL: a displaced member span did not suppress slot population" >&2
  exit 1
}
basis_spacing_count=$(
  grep -Fc '|code=basis-spacing|' "$WORK/r_basis_spacing.tnlog" || true
)
[ "$basis_spacing_count" -eq 9 ] || {
  echo "FAIL: affine basis spacing did not emit exactly nine warnings" >&2
  exit 1
}
for expected in \
  'warning|picture=k1|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0.25|floor=0.327573|margin=-0.077573094' \
  'warning|picture=k2|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0.1875|floor=0.321248|margin=-0.133748076' \
  'warning|picture=k3|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=-1|dist=0|floor=0.348706|margin=-0.348705634' \
  'warning|picture=k4|code=basis-spacing|member-a=1|member-b=2|dr=1|dc=0|dist=0|floor=0.327573|margin=-0.327573094' \
  'warning|picture=k5|code=basis-spacing|member-a=1|member-b=3|dr=0|dc=0|dist=0.25|floor=0.327573|margin=-0.077573094' \
  'warning|picture=k8|code=basis-spacing|member-a=2|member-b=3|dr=0|dc=0|dist=0.25|floor=0.343027|margin=-0.093026792' \
  'warning|picture=k9|code=basis-spacing|member-a=2|member-b=3|dr=0|dc=0|dist=0.25|floor=0.343027|margin=-0.093026792' \
  'warning|picture=k10|code=basis-spacing|member-a=2|member-b=3|dr=0|dc=0|dist=0.25|floor=0.33424|margin=-0.084240243' \
  'warning|picture=k12|code=basis-spacing|member-a=1|member-b=2|dr=0|dc=0|dist=0.25|floor=0.25|margin=-0.0000004'
do
  grep -Fxq "$expected" "$WORK/r_basis_spacing.tnlog" || {
    echo "FAIL: affine basis spacing lost witness: $expected" >&2
    exit 1
  }
done
if grep -Eq '^warning[|]picture=k(6|7|11)[|]code=basis-spacing[|]' \
    "$WORK/r_basis_spacing.tnlog"; then
  echo "FAIL: a safe or exact-boundary basis emitted a spacing warning" >&2
  exit 1
fi
basis_spacing_message_count=$(
  grep -Fc '[TKZ-FRAME-BASIS-SPACING]' \
    "$WORK/r_basis_spacing.tex.transcript" || true
)
[ "$basis_spacing_message_count" -eq 9 ] || {
  echo "FAIL: basis-spacing events and human diagnostics diverged" >&2
  exit 1
}
if grep -Fq '|code=basis-spacing|' \
    "$WORK/k_czx.tnlog" "$WORK/s9_sugar.tnlog"; then
  echo "FAIL: a contracted CZX or planes basis emitted a spacing warning" >&2
  exit 1
fi
sheet_coincide_count=$(
  grep -Fc '|code=sheet-coincide|' \
    "$WORK/r_sheet_coincide_removed.tnlog" || true
)
[ "$sheet_coincide_count" -eq 4 ] || {
  echo "FAIL: removed sites did not filter realized sheet-spacing pairs" >&2
  exit 1
}
for expected in \
  'warning|picture=2|code=sheet-coincide|dist=0.299995|floor=0.327573|dr=0|dc=0' \
  'warning|picture=3|code=sheet-coincide|dist=0.299995|floor=0.327573|dr=0|dc=0' \
  'warning|picture=5|code=sheet-coincide|dist=0|floor=0.327573|dr=-1|dc=0' \
  'warning|picture=6|code=sheet-coincide|dist=0.327573|floor=0.327573|dr=0|dc=0'
do
  grep -Fxq "$expected" "$WORK/r_sheet_coincide_removed.tnlog" || {
    echo "FAIL: surviving adjacent sheets lost witness: $expected" >&2
    exit 1
  }
done
if grep -Eq '^warning[|]picture=(1|4)[|]code=sheet-coincide[|]' \
    "$WORK/r_sheet_coincide_removed.tnlog"; then
  echo "FAIL: a removed adjacent-sheet endpoint retained a warning" >&2
  exit 1
fi
sheet_coincide_messages=$(
  grep -Fc 'Package tenkz Warning: sheet vector:' \
    "$WORK/r_sheet_coincide_removed.tex.transcript" || true
)
[ "$sheet_coincide_messages" -eq 4 ] || {
  echo "FAIL: sheet-coincide events and human diagnostics diverged" >&2
  exit 1
}
awk '
  /^picture[|]id=/ {
    id = $0
    sub(/^picture[|]id=/, "", id)
    sub(/[|].*$/, "", id)
    picture[id] = NR
  }
  /^warning[|]picture=.*[|]code=basis-spacing[|]/ {
    id = $0
    sub(/^warning[|]picture=/, "", id)
    sub(/[|].*$/, "", id)
    if (!(id in picture) || picture[id] >= NR)
      exit 1
    warnings++
  }
  END { if (warnings != 9) exit 1 }
' "$WORK/r_basis_spacing.tnlog" || {
  echo "FAIL: a basis-spacing warning preceded its picture header" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_basis_spacing.tnlog" "$KERNEL/regression/r_basis_spacing.tex" \
  >/dev/null || {
  echo "FAIL: the basis-spacing stream did not pass the one-pass audit" >&2
  exit 1
}
awk '
  /^picture[|]id=k1[|]/ { picture = NR }
  /^warning[|]picture=k1[|]code=plane-tall-window[|]/ { warning = NR }
  END { exit !(picture && warning && picture < warning) }
' "$WORK/r_plane_warning.tnlog" || {
  echo "FAIL: the plane guard warning did not follow its picture header" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_plane_warning.tnlog" "$KERNEL/regression/r_plane_warning.tex" \
  >/dev/null || {
  echo "FAIL: the plane warning stream did not pass the one-pass audit" >&2
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
for carrier in A B K; do
  if ! grep -F "|name=$carrier|" "$WORK/r_physical_policy.tnlog" |
       grep -Fq '|physical=up'; then
    echo "FAIL: physical policy missed address-bearing atom $carrier" >&2
    exit 1
  fi
done
for overlay in R M O X; do
  overlay_record=$(grep -F "|name=$overlay|" "$WORK/r_physical_policy.tnlog") || {
    echo "FAIL: geometric overlay $overlay disappeared from the model" >&2
    exit 1
  }
  if printf '%s\n' "$overlay_record" | grep -Fq '|physical='; then
    echo "FAIL: physical policy leaked onto geometric overlay $overlay" >&2
    exit 1
  fi
done
if ! grep -F '|origin=port-open|' "$WORK/r_physical_policy.tnlog" |
     grep -Fq '|port-label=$m$|port-slot=1|port-type=physical'; then
  echo "FAIL: an overlay's explicit physical port depended on picture policy" >&2
  exit 1
fi
grep -Fq 'kernel-boundary|signature=phys:n, phys:n, phys:n' \
    "$WORK/r_physical_policy.tnlog" || {
  echo "FAIL: overlay explicit-port boundary diverged from two policy ports" >&2
  exit 1
}

affine_log="$WORK/r_affine_geometric_addresses.tnlog"
affine_topology_atoms=$(
  awk '
    /^picture\|id=k1\|/ { inside=1; next }
    /^picture\|/ { inside=0 }
    inside && /^atom\|/ { count++ }
    END { print count + 0 }
  ' "$affine_log"
)
[ "$affine_topology_atoms" -eq 11 ] || {
  echo "FAIL: affine route topology did not contain nine cells and two beads" >&2
  exit 1
}
affine_policy_atoms=$(
  awk '
    /^picture\|id=k2\|/ { inside=1; next }
    /^picture\|/ { inside=0 }
    inside && /^atom\|/ { count++ }
    END { print count + 0 }
  ' "$affine_log"
)
[ "$affine_policy_atoms" -eq 11 ] || {
  echo "FAIL: affine ownership picture did not contain eleven atoms" >&2
  exit 1
}
affine_policy_fields=$(
  awk '
    /^picture\|id=k2\|/ { inside=1; next }
    /^picture\|/ { inside=0 }
    inside && /^atom\|/ && /\|physical=up/ { count++ }
    END { print count + 0 }
  ' "$affine_log"
)
[ "$affine_policy_fields" -eq 9 ] || {
  echo "FAIL: affine physical policy was not owned by exactly nine cells" >&2
  exit 1
}
for overlay in policy-bead-one policy-bead-two; do
  overlay_record=$(grep -F "|name=$overlay|" "$affine_log") || {
    echo "FAIL: affine ownership overlay $overlay disappeared" >&2
    exit 1
  }
  if printf '%s\n' "$overlay_record" | grep -Fq '|physical='; then
    echo "FAIL: affine physical policy leaked onto $overlay" >&2
    exit 1
  fi
done
affine_grid_bonds=$(grep -c '|origin=grid|' "$affine_log" || true)
[ "$affine_grid_bonds" -eq 12 ] || {
  echo "FAIL: affine three-by-three topology did not retain twelve grid bonds" >&2
  exit 1
}
grep -Fq \
  'stringcross|under=bond-2-2-3-2|over=anyon|hits=1' "$affine_log" || {
  echo "FAIL: affine route missed its vertical grid crossing" >&2
  exit 1
}
grep -Fq \
  'stringcross|under=bond-2-2-2-3|over=anyon|hits=1' "$affine_log" || {
  echo "FAIL: affine route missed its horizontal grid crossing" >&2
  exit 1
}
if ! grep -F '|name=anyon|' "$affine_log" |
     grep -Fq '|route=orth|'; then
  echo "FAIL: affine route lost its source-shaped polyline" >&2
  exit 1
fi
if ! grep -F '|name=anyon|' "$affine_log" |
     grep -Fq 'midway istar and c22, midway c32 and c23, midway c22 and i'; then
  echo "FAIL: affine route lost its three logical waypoints" >&2
  exit 1
fi
if ! grep -F '|origin=port-open|' "$affine_log" |
     grep -Fq '|port-label=$m$|port-slot=1|port-type=physical'; then
  echo "FAIL: affine overlay explicit port depended on inherited policy" >&2
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
[ "$skin_pairing_count" -eq 26 ] || {
  echo "FAIL: declared skin pairings were not materialized as WIRE records" >&2
  exit 1
}
grep -Eq \
  '^wire.*\|host=atom-1\|kind=pairing\|name=skin-atom-1-3\|origin=skin\|route=arc\|species=cool' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: a slotted skin WIRE lost its host, route, name, or species" >&2
  exit 1
}
grep -Fq 'stringbead|id=skin-atom-1-1|t=0.5|' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: an on-wire address did not follow the saved pairing route" >&2
  exit 1
}
grep -Fq 'stringcross|under=skin-atom-1-1|over=probe-a|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: a declared string/skin-pairing crossing missed the shared ledger" >&2
  exit 1
}
grep -Fq 'stringcross|under=skin-atom-1-1|over=probe-b|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: a second indexed crossing was split from its pairing" >&2
  exit 1
}
grep -Eq 'stringcross\|under=skin-atom-1-1\|over=wire-[0-9]+\|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: an unnamed string-owned crossing missed its turned pairing host" >&2
  exit 1
}
grep -Fq 'stringcross|under=skin-atom-1-1|over=index-probe|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: an index/pairing crossing missed the shared path ledger" >&2
  exit 1
}
grep -Fq 'stringcross|under=leg-n-1-1|over=skin-atom-2-1|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: a coordinate-bearing pairing crossing was split at its comma" >&2
  exit 1
}
grep -Fq 'stringcross|under=skin-atom-1-1|over=skin-atom-1-3|hits=1' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: ordered same-skin pairings missed their generated crossing order" >&2
  exit 1
}
grep -Fq '|skin=slotted-dot|wide=2' \
  "$WORK/k_skin_pairings.tnlog" || {
  echo "FAIL: the span-aware paired-dot fixture disappeared" >&2
  exit 1
}
mpo_atoms=$(grep -Ec '^atom.*[|]skin=mpo([|]|$)' \
  "$WORK/r_mpo_skin_prelude.tnlog" || true)
[ "$mpo_atoms" -eq 3 ] || {
  echo "FAIL: the stock MPO name did not remain in all three atom records" >&2
  exit 1
}
mpo_hulls=$(grep -c '^glyph-geometry|' \
  "$WORK/r_mpo_skin_prelude.tnlog" || true)
[ "$mpo_hulls" -eq 3 ] || {
  echo "FAIL: the stock MPO declaration did not resolve to three box hulls" >&2
  exit 1
}
sed 's/skin=mpo/skin=box/g' "$WORK/r_mpo_skin_prelude.tnlog" \
  >"$WORK/r_mpo_skin_prelude.normalized.tnlog"
cmp -s "$WORK/r_mpo_skin_box.tnlog" \
  "$WORK/r_mpo_skin_prelude.normalized.tnlog" || {
  echo "FAIL: the stock MPO declaration changed box geometry or events" >&2
  diff -u "$WORK/r_mpo_skin_box.tnlog" \
    "$WORK/r_mpo_skin_prelude.normalized.tnlog" >&2 || true
  exit 1
}
pill_atoms=$(grep -Ec '^atom.*[|]skin=pill([|]|$)' \
  "$WORK/r_pill_skin_prelude.tnlog" || true)
[ "$pill_atoms" -eq 3 ] || {
  echo "FAIL: the stock pill name did not remain in all three atom records" >&2
  exit 1
}
pill_glyphs=$(grep -Ec '^ink-use\|.*\|class=glyph\|.*\|shape=roundrect' \
  "$WORK/r_pill_skin_prelude.tnlog" || true)
[ "$pill_glyphs" -eq 3 ] || {
  echo "FAIL: the stock pill did not ink three rounded silhouettes" >&2
  exit 1
}
pill_hulls=$(grep -Ec \
  '^glyph-geometry\|.*\|shape=roundrect\|.*\|radius=[1-9][0-9]*\|' \
  "$WORK/r_pill_skin_prelude.tnlog" || true)
[ "$pill_hulls" -eq 3 ] || {
  echo "FAIL: a pill hull lost the roundrect family or its cap radius" >&2
  exit 1
}
sed 's/skin=pill/skin=roundrect/g' "$WORK/r_pill_skin_prelude.tnlog" \
  >"$WORK/r_pill_skin_prelude.normalized.tnlog"
cmp -s "$WORK/r_pill_skin_roundrect.tnlog" \
  "$WORK/r_pill_skin_prelude.normalized.tnlog" || {
  echo "FAIL: the stock pill declaration changed roundrect geometry or events" >&2
  diff -u "$WORK/r_pill_skin_roundrect.tnlog" \
    "$WORK/r_pill_skin_prelude.normalized.tnlog" >&2 || true
  exit 1
}
cap_port_glyphs=$(grep -Ec \
  '^glyph-geometry\|.*\|shape=roundrect\|.*\|radius=[1-9][0-9]*\|' \
  "$WORK/r_pill_skin_cap_ports.tnlog" || true)
[ "$cap_port_glyphs" -eq 2 ] || {
  echo "FAIL: a near-cap ported pill fell back to a sharp hull family" >&2
  exit 1
}
grep -Fq '|origin=port-open|port-face=168|port-slot=1|port-type=virtual' \
  "$WORK/r_pill_skin_cap_ports.tnlog" || {
  echo "FAIL: an unconsumed pill port did not materialize its open leg" >&2
  exit 1
}
grep -Fq '|origin=port-open|port-face=230|port-slot=1|port-type=physical' \
  "$WORK/r_pill_skin_cap_ports.tnlog" || {
  echo "FAIL: a physical pill port lost its type on materialization" >&2
  exit 1
}
mirror_atoms=$(grep -Ec '^atom.*[|]skin=triwest([|]|$)' \
  "$WORK/r_tri_apex_mirror.tnlog" || true)
[ "$mirror_atoms" -eq 2 ] || {
  echo "FAIL: the mirrored triangle name did not remain in its atom records" >&2
  exit 1
}
mirror_glyphs=$(grep -Ec '^ink-use\|.*\|class=glyph\|.*\|shape=triangle' \
  "$WORK/r_tri_apex_mirror.tnlog" || true)
[ "$mirror_glyphs" -eq 3 ] || {
  echo "FAIL: an apex-mirror silhouette left the triangle family" >&2
  exit 1
}
# The apex is the vertex the audit records first.  On the east-apex skin it
# must stand at the silhouette's own east extreme and on the mirrored skin at
# its west extreme, each a half stroke inside the stroked envelope.  A skin
# that fell back to the fixed apex would put all three apexes on one side.
python3 - "$WORK/r_tri_apex_mirror.tnlog" <<'MIRROR' || exit 1
import sys

expected = ["east", "west", "west"]
records = []
for line in open(sys.argv[1], encoding="utf-8"):
    if not line.startswith("glyph-geometry|"):
        continue
    attrs = dict(part.split("=", 1) for part in line.strip().split("|")[1:])
    if attrs["shape"] != "triangle":
        continue
    records.append({key: int(attrs[key]) for key in
                    ("xmin", "xmax", "stroke", "x1", "x2", "x3")})
if len(records) != len(expected):
    print("FAIL: the apex-mirror fixture lost a measured triangle",
          file=sys.stderr)
    raise SystemExit(1)
for side, record in zip(expected, records):
    corners = (record["x2"], record["x3"])
    if side == "east":
        held = (record["x1"] > max(corners)
                and record["x1"] + record["stroke"] == record["xmax"])
    else:
        held = (record["x1"] < min(corners)
                and record["x1"] - record["stroke"] == record["xmin"])
    if not held:
        print(f"FAIL: a canonical isometry did not point its apex {side}",
              file=sys.stderr)
        raise SystemExit(1)
MIRROR
grep -Fq '|origin=port-open|port-face=12|port-slot=1|port-type=virtual' \
  "$WORK/r_tri_apex_mirror.tnlog" || {
  echo "FAIL: an east-apex grazing port did not materialize its open leg" >&2
  exit 1
}
grep -Fq '|origin=port-open|port-face=168|port-slot=1|port-type=virtual' \
  "$WORK/r_tri_apex_mirror.tnlog" || {
  echo "FAIL: a west-apex grazing port did not materialize its open leg" >&2
  exit 1
}
grep -Fq '|origin=port-open|port-face=270|port-slot=1|port-type=physical' \
  "$WORK/r_tri_apex_mirror.tnlog" || {
  echo "FAIL: a mirrored triangle physical port lost its type" >&2
  exit 1
}
command -v pdftoppm >/dev/null 2>&1 || {
  echo "FAIL: kernel pixel gate requires pdftoppm" >&2
  exit 1
}
for pixel_fixture in \
    k_plane k_skin_pairings r_dir_open_bearings r_hull_live r_ink_semantics \
    r_label_turn r_mpo_skin_box r_mpo_skin_prelude r_parallel_lanes \
    r_physical_dir r_pill_skin_prelude r_pill_skin_roundrect r_ring_closure \
    r_wire_stroke; do
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
cmp -s "$WORK/r_mpo_skin_box.png" "$WORK/r_mpo_skin_prelude.png" || {
  echo "FAIL: the stock MPO declaration changed box pixels" >&2
  exit 1
}
cmp -s "$WORK/r_pill_skin_roundrect.png" "$WORK/r_pill_skin_prelude.png" || {
  echo "FAIL: the stock pill declaration changed roundrect pixels" >&2
  exit 1
}
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
  "$WORK/k_plane.png" "$WORK/r_dir_open_bearings.png" \
  "$WORK/r_ink_semantics.png" "$WORK/r_label_turn.png" \
  "$WORK/r_parallel_lanes.png" "$WORK/r_physical_dir.png" \
  "$WORK/r_ring_closure.png" "$WORK/r_wire_stroke.png" >"$PIXEL_CURRENT"

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

frame_negative="$KERNEL/negative/n_frame_word.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$frame_negative" >"$WORK/n_frame_word.transcript" 2>&1 ); then
  echo "FAIL: a word outside the frame alphabet was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-FRAME-WORD]' "$WORK/n_frame_word.transcript" || {
  echo "FAIL: unknown frame word lacked TKZ-FRAME-WORD" >&2
  exit 1
}

skin_negative="$KERNEL/negative/n_unknown_skin.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_negative" >"$WORK/n_unknown_skin.transcript" 2>&1 ); then
  echo "FAIL: a skin word outside the primitive and declared sets was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-KERNEL-SKIN]' "$WORK/n_unknown_skin.transcript" || {
  echo "FAIL: unknown skin lacked TKZ-KERNEL-SKIN" >&2
  exit 1
}

for circle_open_case in ne:from se:to sw:from nw:to; do
  direction=${circle_open_case%%:*}
  endpoint=${circle_open_case#*:}
  circle_open_negative="$KERNEL/negative/n_circle_open_$direction.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$circle_open_negative" \
         >"$WORK/n_circle_open_$direction.transcript" 2>&1 ); then
    echo "FAIL: circle frame accepted diagonal open $direction" >&2
    exit 1
  fi
  grep -Fq '[TKZ-CIRCLE-OPEN-DIRECTION]' \
    "$WORK/n_circle_open_$direction.transcript" || {
    echo "FAIL: diagonal circle open $direction lacked its coded diagnostic" >&2
    exit 1
  }
  grep -Fq "direction '$direction'" \
    "$WORK/n_circle_open_$direction.transcript" || {
    echo "FAIL: diagonal circle diagnostic lost bearing $direction" >&2
    exit 1
  }
  grep -Fq "at the $endpoint end" \
    "$WORK/n_circle_open_$direction.transcript" || {
    echo "FAIL: diagonal circle diagnostic lost endpoint $endpoint" >&2
    exit 1
  }
done

transverse_negative="$KERNEL/negative/n_flat_open_transverse.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$transverse_negative" \
       >"$WORK/n_flat_open_transverse.transcript" 2>&1 ); then
  echo "FAIL: a flat frame accepted a transverse open end" >&2
  exit 1
fi
grep -Fq '[TKZ-OPEN-TRANSVERSE-FRAME]' \
  "$WORK/n_flat_open_transverse.transcript" || {
  echo "FAIL: the flat transverse rejection lacked its coded diagnostic" >&2
  exit 1
}

for basis_case in \
  n_frame_basis_parse n_frame_basis_semicolon n_frame_basis_kind \
  n_frame_basis_member \
  n_frame_basis_member_zero \
  n_frame_basis_cell_member n_frame_basis_member_cell \
  n_frame_basis_displaced_policy n_frame_basis_invalid_word \
  n_frame_basis_grid n_frame_basis_group n_frame_basis_circle \
  n_frame_basis_policy
do
  basis_negative="$KERNEL/negative/$basis_case.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$basis_negative" >"$WORK/$basis_case.transcript" 2>&1 ); then
    echo "FAIL: malformed basis case $basis_case was accepted" >&2
    exit 1
  fi
done

for leg_plan_case in vector basis corridor face reach; do
  leg_plan_negative="$KERNEL/negative/n_leg_plan_$leg_plan_case.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$leg_plan_negative" \
         >"$WORK/n_leg_plan_$leg_plan_case.transcript" 2>&1 ); then
    echo "FAIL: malformed physical-leg plan $leg_plan_case was accepted" >&2
    exit 1
  fi
  leg_plan_code=$(printf '%s' "$leg_plan_case" | tr '[:lower:]' '[:upper:]')
  grep -Fq "[TKZ-LEG-PLAN-$leg_plan_code]" \
    "$WORK/n_leg_plan_$leg_plan_case.transcript" || {
    echo "FAIL: physical-leg plan $leg_plan_case lacked its coded diagnostic" >&2
    exit 1
  }
done
grep -Fq '[TKZ-FRAME-BASIS-PARSE]' \
  "$WORK/n_frame_basis_parse.transcript" || {
  echo "FAIL: malformed basis member lacked TKZ-FRAME-BASIS-PARSE" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-PARSE]' \
  "$WORK/n_frame_basis_semicolon.transcript" || {
  echo "FAIL: semicolon basis coordinate lacked TKZ-FRAME-BASIS-PARSE" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-KIND]' \
  "$WORK/n_frame_basis_kind.transcript" || {
  echo "FAIL: unknown basis kind lacked TKZ-FRAME-BASIS-KIND" >&2
  exit 1
}
[ "$(grep -Fc '[TKZ-FRAME-BASIS-PARSE]' \
    "$WORK/n_frame_basis_parse.transcript" || true)" -eq 1 ] || {
  echo "FAIL: malformed basis emitted duplicate parse diagnostics" >&2
  exit 1
}
[ "$(grep -Fc '[TKZ-FRAME-BASIS-KIND]' \
    "$WORK/n_frame_basis_kind.transcript" || true)" -eq 1 ] || {
  echo "FAIL: unknown basis kind emitted duplicate diagnostics" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-MEMBER-RANGE]' \
  "$WORK/n_frame_basis_member.transcript" || {
  echo "FAIL: missing basis member lacked TKZ-FRAME-MEMBER-RANGE" >&2
  exit 1
}
for overlap_case in n_frame_basis_cell_member n_frame_basis_member_cell; do
  grep -Eq '\[TKZ-(LANG-OCCUPANCY|CELL-OCCUPIED|FRAME-MEMBER-OCCUPIED)\]' \
    "$WORK/$overlap_case.transcript" || {
    echo "FAIL: $overlap_case lacked an occupancy diagnostic" >&2
    exit 1
  }
done
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode \
       "$KERNEL/negative/n_frame_basis_cell_member.tex" \
       >"$WORK/n_frame_basis_cell_member.recovery.transcript" 2>&1 ); then
  :
fi
if grep -Eq '^atom.*[|]member=' \
    "$WORK/n_frame_basis_cell_member.tnlog"; then
  echo "FAIL: a rejected aligned member acquired valid member fields" >&2
  exit 1
fi
grep -Fq '[TKZ-FRAME-BASIS-POLICY]' \
  "$WORK/n_frame_basis_displaced_policy.transcript" || {
  echo "FAIL: displaced singleton policy lacked TKZ-FRAME-BASIS-POLICY" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-WORD]' \
  "$WORK/n_frame_basis_invalid_word.transcript" || {
  echo "FAIL: invalid basis frame lacked TKZ-FRAME-WORD" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-MEMBER-RANGE]' \
  "$WORK/n_frame_basis_member_zero.transcript" || {
  echo "FAIL: zero basis member lacked TKZ-FRAME-MEMBER-RANGE" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-GRID]' \
  "$WORK/n_frame_basis_grid.transcript" || {
  echo "FAIL: implicit multi-member topology lacked TKZ-FRAME-BASIS-GRID" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-SCOPE]' \
  "$WORK/n_frame_basis_group.transcript" || {
  echo "FAIL: group basis lacked TKZ-FRAME-BASIS-SCOPE" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-CIRCLE]' \
  "$WORK/n_frame_basis_circle.transcript" || {
  echo "FAIL: circle basis lacked TKZ-FRAME-BASIS-CIRCLE" >&2
  exit 1
}
grep -Fq '[TKZ-FRAME-BASIS-POLICY]' \
  "$WORK/n_frame_basis_policy.transcript" || {
  echo "FAIL: cell-level basis policy lacked TKZ-FRAME-BASIS-POLICY" >&2
  exit 1
}
( cd "$WORK" &&
  TEXINPUTS="$REPO/tex/tenkz//:" \
    timeout 120 xelatex -interaction=nonstopmode \
    "$KERNEL/negative/n_frame_basis_grid.tex" \
    >"$WORK/n_frame_basis_grid.recovery.transcript" 2>&1 ) || true
if grep -Fq '|origin=grid|' "$WORK/n_frame_basis_grid.tnlog"; then
  echo "FAIL: rejected multi-member grid topology polluted recovery output" >&2
  exit 1
fi
( cd "$WORK" &&
  TEXINPUTS="$REPO/tex/tenkz//:" \
    timeout 120 xelatex -interaction=nonstopmode \
    "$KERNEL/negative/n_frame_basis_group.tex" \
    >"$WORK/n_frame_basis_group.recovery.transcript" 2>&1 ) || true
group_recovery_atoms=$(
  grep -c '^atom|' "$WORK/n_frame_basis_group.tnlog" || true
)
[ "$group_recovery_atoms" -eq 2 ] || {
  echo "FAIL: a rejected group basis changed outer picture population" >&2
  exit 1
}

for wind_case in n_wind_zero n_wind_via n_wind_shape; do
  wind_negative="$KERNEL/negative/$wind_case.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$wind_negative" >"$WORK/$wind_case.transcript" 2>&1 ); then
    echo "FAIL: $wind_case was accepted" >&2
    exit 1
  fi
done
grep -Fq '[TKZ-WIND-ZERO]' "$WORK/n_wind_zero.transcript" || {
  echo "FAIL: the zero winding rejection lacked TKZ-WIND-ZERO" >&2
  tail -20 "$WORK/n_wind_zero.transcript" >&2
  exit 1
}
grep -Fq '[TKZ-WIND-VIA]' "$WORK/n_wind_via.transcript" || {
  echo "FAIL: the winding-waypoint rejection lacked TKZ-WIND-VIA" >&2
  tail -20 "$WORK/n_wind_via.transcript" >&2
  exit 1
}
grep -Fq '[TKZ-WIND-SHAPE]' "$WORK/n_wind_shape.transcript" || {
  echo "FAIL: the malformed winding rejection lacked TKZ-WIND-SHAPE" >&2
  tail -20 "$WORK/n_wind_shape.transcript" >&2
  exit 1
}
for wind_case in n_wind_via n_wind_shape; do
  rm -f "$WORK/$wind_case".{aux,log,pdf,tnlog}
  ( cd "$WORK" &&
    TEXINPUTS="$REPO/tex/tenkz//:" \
      timeout 120 xelatex -interaction=nonstopmode \
      "$KERNEL/negative/$wind_case.tex" \
      >"$WORK/$wind_case.recovery.transcript" 2>&1 ) || true
  if [ -f "$WORK/$wind_case.tnlog" ] &&
     grep -Eq '^string\|' "$WORK/$wind_case.tnlog"; then
    echo "FAIL: $wind_case drew a string after its rejection" >&2
    exit 1
  fi
done

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

plane_transverse_signature="$KERNEL/negative/n_plane_transverse_signature.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$plane_transverse_signature" \
       >"$WORK/n_plane_transverse_signature.transcript" 2>&1 ); then
  echo "FAIL: a plane transverse leg was identified with an in-plane port" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-SIGNATURE]' \
    "$WORK/n_plane_transverse_signature.transcript" || {
  echo "FAIL: plane transverse mismatch lacked TKZ-EQ-SIGNATURE" >&2
  exit 1
}
grep -Fq 'signature=phys:n' \
    "$WORK/n_plane_transverse_signature.tnlog" || {
  echo "FAIL: plane policy did not expose its transverse north bearing" >&2
  exit 1
}
grep -Fq 'signature=phys:53.130102' \
    "$WORK/n_plane_transverse_signature.tnlog" || {
  echo "FAIL: authored plane port lost its projected in-plane bearing" >&2
  exit 1
}
grep -Fq 'result=mismatch' \
    "$WORK/n_plane_transverse_signature.tnlog" || {
  echo "FAIL: plane transverse mismatch was not recorded" >&2
  exit 1
}

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

cluster_ports_negative="$KERNEL/negative/n_cluster_ports.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$cluster_ports_negative" >"$WORK/n_cluster_ports.transcript" 2>&1 ); then
  echo "FAIL: a glyphless cluster carrier accepted ports" >&2
  exit 1
fi
grep -Fq '[TKZ-PORT-CLUSTER]' "$WORK/n_cluster_ports.transcript" || {
  echo "FAIL: cluster-port rejection lacked TKZ-PORT-CLUSTER" >&2
  exit 1
}

cluster_endpoint_negative="$KERNEL/negative/n_cluster_port_endpoint.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$cluster_endpoint_negative" \
       >"$WORK/n_cluster_port_endpoint.transcript" 2>&1 ); then
  echo "FAIL: an implicit endpoint invented a cluster-carrier port" >&2
  exit 1
fi
grep -Fq '[TKZ-PORT-CLUSTER]' \
  "$WORK/n_cluster_port_endpoint.transcript" || {
  echo "FAIL: cluster endpoint rejection lacked TKZ-PORT-CLUSTER" >&2
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

singular_basis_negative="$KERNEL/negative/n_geom_singular_basis.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$singular_basis_negative" \
       >"$WORK/n_geom_singular_basis.transcript" 2>&1 ); then
  echo "FAIL: a singular carrier basis was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-GEOM-SINGULAR-BASIS]' \
    "$WORK/n_geom_singular_basis.transcript" || {
  echo "FAIL: singular basis rejection lacked TKZ-GEOM-SINGULAR-BASIS" >&2
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
  n_duplicate_port \
  n_port_open_cross_undeclared \
  n_port_type \
  n_closure_port_type \
  n_closure_implicit_port_type \
  n_cup_implicit_port_type \
  n_cell_trace_port_type \
  n_authored_port_type_implicit \
  n_authored_port_type_implicit_from \
  n_port_cell_type \
  n_cell_port_type \
  n_physical_dir_mismatch \
  n_route_end_inside_hull \
  n_physical_open_port_type \
  n_interface_open_port_type \
  n_physical_trace_required_type \
  n_grid_port_type_implicit \
  n_grid_port_type_explicit \
  n_port_type_multiple_consumers \
  n_port_policy_type \
  n_atom_up_key \
  n_sealed_duplicate_port \
  n_sealed_malformed_port \
  n_port_slot \
  n_noncell_port_slot \
  n_port_open_name \
  n_padded_duplicate_port \
  n_rounding_duplicate_port \
  n_atom_down_key \
  n_malformed_via \
  n_malformed_cross \
  n_malformed_mark_target \
  n_noncell_leg \
  n_signature_carrier_port
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
  [ "$contract_negative" = n_duplicate_port ] &&
    expected='[TKZ-PORT-DUPLICATE]'
  [ "$contract_negative" = n_port_open_cross_undeclared ] &&
    expected='[TKZ-CROSS-UNDECLARED]'
  [ "$contract_negative" = n_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_closure_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_closure_implicit_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_cup_implicit_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_cell_trace_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_authored_port_type_implicit ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_authored_port_type_implicit_from ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_port_cell_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_cell_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_physical_dir_mismatch ] &&
    expected='[TKZ-EQ-SIGNATURE]'
  [ "$contract_negative" = n_route_end_inside_hull ] &&
    expected='[TKZ-ROUTE-END-INSIDE]'
  [ "$contract_negative" = n_physical_open_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_interface_open_port_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_physical_trace_required_type ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_grid_port_type_implicit ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_grid_port_type_explicit ] &&
    expected='[TKZ-PORT-TYPE]'
  [ "$contract_negative" = n_port_type_multiple_consumers ] &&
    expected='[TKZ-PORT-CONSUMED]'
  [ "$contract_negative" = n_port_policy_type ] &&
    expected='[TKZ-PORT-POLICY-TYPE]'
  [ "$contract_negative" = n_atom_up_key ] &&
    expected='[TKZ-LANG-UNKNOWN-KEY]'
  [ "$contract_negative" = n_sealed_duplicate_port ] &&
    expected='[TKZ-PORT-DUPLICATE]'
  [ "$contract_negative" = n_sealed_malformed_port ] &&
    expected='[TKZ-PORT-PARSE]'
  [ "$contract_negative" = n_port_slot ] &&
    expected='[TKZ-PORT-SLOT]'
  [ "$contract_negative" = n_noncell_port_slot ] &&
    expected='[TKZ-PORT-SLOT]'
  [ "$contract_negative" = n_port_open_name ] &&
    expected='[TKZ-LANG-NAME-COLLISION]'
  [ "$contract_negative" = n_padded_duplicate_port ] &&
    expected='[TKZ-PORT-DUPLICATE]'
  [ "$contract_negative" = n_rounding_duplicate_port ] &&
    expected='[TKZ-PORT-DUPLICATE]'
  [ "$contract_negative" = n_atom_down_key ] &&
    expected='[TKZ-LANG-UNKNOWN-KEY]'
  [ "$contract_negative" = n_signature_carrier_port ] &&
    expected='[TKZ-EQ-SIGNATURE]'
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

for cell_port_alias_case in \
  n_skin_pairing_port_alias \
  n_cell_port_alias_skin_wire \
  n_cell_port_alias_skin_declared \
  n_cell_port_alias_skin_physical; do
  cell_port_alias_negative="$KERNEL/negative/$cell_port_alias_case.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$cell_port_alias_negative" \
         >"$WORK/$cell_port_alias_case.transcript" 2>&1 ); then
    echo "FAIL: $cell_port_alias_case aliased one paired cell lane" >&2
    exit 1
  fi
  grep -Fq '[TKZ-CELL-PORT-BEARING-ALIAS]' \
    "$WORK/$cell_port_alias_case.transcript" || {
    echo "FAIL: $cell_port_alias_case lacked its cell-port diagnostic" >&2
    exit 1
  }
  grep -Fq 'atom-1.n@1 receives pairing bearing 80 and bearing' \
    "$WORK/$cell_port_alias_case.transcript" || {
    echo "FAIL: $cell_port_alias_case lost its lane or bearing context" >&2
    exit 1
  }
done
for alias_context in \
  'n_skin_pairing_port_alias|100 from skin aliased-face' \
  'n_cell_port_alias_skin_wire|100 from wire wire-2/to' \
  'n_cell_port_alias_skin_declared|100 from ports=' \
  'n_cell_port_alias_skin_physical|bearing 90' \
  'n_cell_port_alias_skin_physical|from physical policy'; do
  alias_case=${alias_context%%|*}
  alias_detail=${alias_context#*|}
  grep -Fq "$alias_detail" "$WORK/$alias_case.transcript" || {
    echo "FAIL: $alias_case lost diagnostic context '$alias_detail'" >&2
    exit 1
  }
done

skin_cluster_negative="$KERNEL/negative/n_skin_pairing_cluster.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_cluster_negative" \
       >"$WORK/n_skin_pairing_cluster.transcript" 2>&1 ); then
  echo "FAIL: a cluster carrier accepted a paired skin" >&2
  exit 1
fi
grep -Fq '[TKZ-SKIN-PAIRING-CLUSTER]' \
  "$WORK/n_skin_pairing_cluster.transcript" || {
  echo "FAIL: paired cluster lacked TKZ-SKIN-PAIRING-CLUSTER" >&2
  exit 1
}

for pairing_negative in \
  n_skin_pairings_parse \
  n_skin_pairing_item_parse \
  n_skin_pairing_cross_parse \
  n_skin_pairing_cross_index; do
  source="$KERNEL/negative/$pairing_negative.tex"
  if ( cd "$WORK" &&
       TEXINPUTS="$REPO/tex/tenkz//:" \
         timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
         "$source" >"$WORK/$pairing_negative.transcript" 2>&1 ); then
    echo "FAIL: malformed pairing contract in $pairing_negative was accepted" >&2
    exit 1
  fi
done
grep -Fq '[TKZ-SKIN-PAIRING-PARSE]' \
  "$WORK/n_skin_pairings_parse.transcript" || {
  echo "FAIL: malformed pairings= lacked TKZ-SKIN-PAIRING-PARSE" >&2
  exit 1
}
grep -Fq '[TKZ-SKIN-PAIRING-PARSE]' \
  "$WORK/n_skin_pairing_item_parse.transcript" || {
  echo "FAIL: a malformed pairing item lacked TKZ-SKIN-PAIRING-PARSE" >&2
  exit 1
}
grep -Fq "'malformed-item' must be one braced port-pair-list" \
  "$WORK/n_skin_pairing_item_parse.transcript" || {
  echo "FAIL: a malformed pairing item reported its host instead of its skin" >&2
  exit 1
}
grep -Fq '[TKZ-SKIN-PAIRING-CROSS-PARSE]' \
  "$WORK/n_skin_pairing_cross_parse.transcript" || {
  echo "FAIL: malformed pairing cross lacked its parse diagnostic" >&2
  exit 1
}
grep -Fq '[TKZ-SKIN-PAIRING-CROSS-INDEX]' \
  "$WORK/n_skin_pairing_cross_index.transcript" || {
  echo "FAIL: out-of-range pairing cross lacked its index diagnostic" >&2
  exit 1
}

skin_name_negative="$KERNEL/negative/n_skin_pairing_name.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_name_negative" >"$WORK/n_skin_pairing_name.transcript" 2>&1 ); then
  echo "FAIL: a generated skin pairing replaced an author name" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-NAME-COLLISION]' \
  "$WORK/n_skin_pairing_name.transcript" || {
  echo "FAIL: a generated pairing name collision lacked its diagnostic" >&2
  exit 1
}

reserved_self_negative="$KERNEL/negative/n_reserved_self.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$reserved_self_negative" >"$WORK/n_reserved_self.transcript" 2>&1 ); then
  echo "FAIL: the crossing keyword self was accepted as an author name" >&2
  exit 1
fi
grep -Fq '[TKZ-LANG-NAME-RESERVED]' \
  "$WORK/n_reserved_self.transcript" || {
  echo "FAIL: reserved name=self lacked its grammar diagnostic" >&2
  exit 1
}

skin_cross_negative="$KERNEL/negative/n_skin_pairing_cross.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_cross_negative" >"$WORK/n_skin_pairing_cross.transcript" 2>&1 ); then
  echo "FAIL: an undeclared string/skin-pairing crossing was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-CROSS-UNDECLARED]' \
  "$WORK/n_skin_pairing_cross.transcript" || {
  echo "FAIL: string/skin-pairing crossing lacked TKZ-CROSS-UNDECLARED" >&2
  exit 1
}

skin_index_cross_negative="$KERNEL/negative/n_skin_pairing_index_cross.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$skin_index_cross_negative" \
       >"$WORK/n_skin_pairing_index_cross.transcript" 2>&1 ); then
  echo "FAIL: an undeclared index/skin-pairing crossing was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-CROSS-UNDECLARED]' \
  "$WORK/n_skin_pairing_index_cross.transcript" || {
  echo "FAIL: an index/pairing crossing lacked TKZ-CROSS-UNDECLARED" >&2
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
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_bundle_modulo.tnlog" "$KERNEL/regression/r_bundle_modulo.tex" \
  >"$WORK/r_bundle_modulo.audit" || {
  echo "FAIL: bundle modulo regression failed the event audit" >&2
  cat "$WORK/r_bundle_modulo.audit" >&2
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

nested_equation="$KERNEL/negative/n_nested_equation.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode -halt-on-error \
       "$nested_equation" \
       >"$WORK/n_nested_equation.transcript" 2>&1 ); then
  echo "FAIL: a nested equation audit scope was accepted" >&2
  exit 1
fi
grep -Fq '[TKZ-EQ-NESTED]' "$WORK/n_nested_equation.transcript" || {
  echo "FAIL: nested equation lacked TKZ-EQ-NESTED" >&2
  exit 1
}
grep -Eq '(^|[|])scope=1([|]|$)' "$WORK/n_nested_equation.tnlog" || {
  echo "FAIL: nested equation did not preserve its outer audit scope" >&2
  exit 1
}
if grep -Eq '(^|[|])scope=2([|]|$)' "$WORK/n_nested_equation.tnlog"; then
  echo "FAIL: a rejected nested equation mutated scope ownership" >&2
  exit 1
fi

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
grep -Fq 'check|scope=1|relation=1|result=off|reason=first' \
  "$WORK/r_multiple_off.tnlog" || {
  echo "FAIL: the first equation opt-out was not preserved" >&2
  exit 1
}
grep -Fq 'check|scope=1|relation=3|result=off|reason=third' \
  "$WORK/r_multiple_off.tnlog" || {
  echo "FAIL: the later equation opt-out was silently dropped" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_multiple_off.tnlog" "$KERNEL/regression/r_multiple_off.tex" \
  >"$WORK/r_multiple_off.audit" || {
  echo "FAIL: multiple equation opt-outs failed the event audit" >&2
  cat "$WORK/r_multiple_off.audit" >&2
  exit 1
}

grep -Fq 'check|scope=1|relation=1|result=equal' \
  "$WORK/r_check_scope_nested.tnlog" || {
  echo "FAIL: brace-nested relation lost its equation scope" >&2
  exit 1
}
grep -Fq 'check|scope=2|relation=1|result=off|reason=documented' \
  "$WORK/r_check_scope_nested.tnlog" || {
  echo "FAIL: later equation opt-out lost its own scope" >&2
  exit 1
}
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_check_scope_nested.tnlog" \
  "$KERNEL/regression/r_check_scope_nested.tex" \
  >"$WORK/r_check_scope_nested.audit" || {
  echo "FAIL: scoped brace-nested relations failed the event audit" >&2
  cat "$WORK/r_check_scope_nested.audit" >&2
  exit 1
}
grep -Fv 'check|scope=1|relation=1|' \
  "$WORK/r_check_scope_nested.tnlog" \
  >"$WORK/r_check_scope_nested_truncated.tnlog"
python3 "$REPO/scripts/tenkz_audit.py" \
  "$WORK/r_check_scope_nested_truncated.tnlog" \
  "$KERNEL/regression/r_check_scope_nested.tex" \
  >"$WORK/r_check_scope_nested_truncated.audit" || {
  echo "FAIL: a missing record stole the later equation scope" >&2
  cat "$WORK/r_check_scope_nested_truncated.audit" >&2
  exit 1
}

scope_malformed="$KERNEL/negative/n_check_scope_malformed_then_valid.tex"
if ( cd "$WORK" &&
     TEXINPUTS="$REPO/tex/tenkz//:" \
       timeout 120 xelatex -interaction=nonstopmode \
       "$scope_malformed" \
       >"$WORK/n_check_scope_malformed_then_valid.transcript" 2>&1 ); then
  echo "FAIL: malformed scoped equation was accepted" >&2
  exit 1
fi
grep -Fq \
  'check|scope=1|result=malformed|reason=relation-count|panels=2|relations=2' \
  "$WORK/n_check_scope_malformed_then_valid.tnlog" || {
  echo "FAIL: malformed relation count lost its equation scope" >&2
  exit 1
}
grep -Fq 'check|scope=1|relation=1|result=equal' \
  "$WORK/n_check_scope_malformed_then_valid.tnlog" || {
  echo "FAIL: malformed equation lost its per-relation scope" >&2
  exit 1
}
grep -Fq 'check|scope=2|relation=1|result=equal' \
  "$WORK/n_check_scope_malformed_then_valid.tnlog" || {
  echo "FAIL: later valid equation inherited the malformed scope" >&2
  exit 1
}
regression_count=$(find "$WORK" -maxdepth 1 -name 'r_*.tex' | wc -l | tr -d ' ')
echo "PASS: $regression_count review regressions hold"

fail=0
for pair in s1 s2 s3 s4 s5 s6 s7 s8 s9 s10; do
  if ! cmp -s "$WORK/${pair}_sugar.tnlog" "$WORK/${pair}_kernel.tnlog"; then
    echo "FAIL: sugar pair $pair diverges from its kernel expansion" >&2
    diff "$WORK/${pair}_sugar.tnlog" "$WORK/${pair}_kernel.tnlog" >&2 || true
    fail=1
  fi
done
[ "$fail" -eq 0 ] && echo "PASS: 10 sugar spellings byte-identical to their expansions"

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

# Registry sweep, 2026-08-22 (#6198)

Every key row of `tex/tenkz/tenkz-language-registry.tex` settled against the
implementation by compiling: what the key accepts, what it changes on the
page, the stated default, and the cited consumers.  Eight compile agents
swept sixty-seven rows; fifty stood accurate, and the seventeen below took
a correction in this change or a filed follow-up.  The registry rows and
the small validation fixes land together; the two rows found inert keep
truth-stating descriptions until their retirement issues execute.

| Row | Verdict | Finding | Resolution |
|---|---|---|---|
| `kernel-atom:name` | reword | name=anchor compiles and is functionally addressable: `at=1 e of anchor` resolves correctly (tnlog shows atom\|...\|name=anchor). ports/at etc. all read the {name} field (tenkz-kernel.code.tex:1415-1424, 2031, commit reg... | row default corrected to none |
| `kernel-declare:hue` | reword | Compiled p_hue_plain (hue=red), p_hue_source (hue=source:red), p_hue_none (species declared with no hue at all, gets house-cycle hue), and p_hue_bad (hue=notacolorxyz). ACCEPTS: legal color names accepted; illegal name r... | row states what source: does today |
| `kernel-mark:label pos` | reword | Registry: angle, default auto. lp_default/lp_n/lp_s/lp_45 probes (form=label mark) on a 2-atom row: omitting the key gives raster hash c1d880… identical to explicit 'label pos=n' (same hash), while 'label pos=s' (0c1813…... | row states compass word or degree value |
| `kernel-mark:name` | defect | Registry: identifier, default generated, description 'Addressable name.' ACCEPTS/DEFAULT check out: name=R parses fine and .tnlog shows the omitted-key case gets an auto id (id=mark-3); name=self is refused with a dedica... | row states no address grammar resolves a mark yet |
| `kernel-mark:slot` | defect | Registry: semantic-slot, default 'selected'. ACCEPTS: all 5 words (selected, secondary, complement, collar, neutral) compile and each gives a distinct raster hash on an enclosure mark (s_slot_selected/secondary/complemen... | row default corrected to passive; species= precedence stated |
| `kernel-mark:tint` | reword | Registry: flag, default false, description 'Interior tint under the contour.' Compiled on form=enclosure: tn_encl_notint (no key) and tn_encl_tintfalse (tint=false) give the identical raster hash b0b2bb5…, confirming def... | row scoped to enclosures |
| `kernel-picture:align` | defect | align only shows a page effect when the tenkz picture sits inline against surrounding text/glyphs, since it sets the tikzpicture's `baseline=` option (tenkz-kernel.code.tex:20034), not the picture's own ink layout. Probe... | fixed: a dedicated validator refuses anything but midline or a row number |
| `kernel-picture:cols` | defect | cols omitted vs cols=3 explicit (with rows={ket}, 3 populated cells): identical raster (d66b63e...), confirming default=3. cols=2 vs cols=3: distinct raster (fewer populated cells), confirming real page effect. BUT regis... | fixed: the key now rides the positive-integer validator |
| `kernel-picture:planes` | defect | Sugar expansion itself is faithful: on a lattice=1x1 two-member-basis picture, planes and frame={plane, basis={ket at (0,0), bra at (2,2)}} (direct) render byte-identical PNGs (sha256 1f8ec40a...). Same type-mismatch def... | fixed: same flag semantics as sandwich |
| `kernel-picture:sandwich` | defect | sandwich sugar expansion itself is faithful: \begin{tenkz}[sandwich,...] and \begin{tenkz}[rows={ket,op,bra},...] with identical bodies produce byte-identical PNGs (sha256 8e37fb7b...). BUT the row's stated type is 'flag... | fixed: flag-shaped sugar validates true|false; false expands nothing |
| `kernel-picture:surface` | reword | Sugar expansion is faithful and functional: surface=torus on a lattice=2x2 grid and the direct west=trace,east=trace,north=trace,south=trace spelling render byte-identical PNGs (sha256 984ea5e2...). BUT the stated type i... | row retyped enum(torus) |
| `kernel-setup:pitch` | defect | Compiled p_pitch_default(no pitch set), p_pitch_20mm (\tnset{pitch=20mm}), p_pitch_1em (\tnset{pitch=1em}), p_pitch_bad (\tnset{pitch=notalength}). ACCEPTS: mm and em lengths compile fine (exit 0); an illegal length valu... | row default corrected to 11mm |
| `kernel-setup:sizes` | defect | Compiled p_sizes_a (\tnset{sizes={review-table}}), p_sizes_b (\tnset{sizes={anything-goes-here}}), and the shared no-op probe with no sizes= at all -- all three rasters are byte-identical (5b9e866...), and the .tnlog str... | row states the truth pending retirement (issue filed) |
| `kernel-setup:theme` | defect | Compiled p_theme_house (\tnset{theme=house}), p_theme_other (\tnset{theme=zorkmid}, a nonsense identifier -- accepted with no error), and p_theme_absent (no theme= at all): all three rasters are byte-identical (5b9e866..... | row states the truth pending retirement (issue filed) |
| `kernel-wire:crossing` | defect | ACCEPTS: all 5 enum members parse (over, under, alternate accepted bare; alternate=over/alternate=under require outer braces `crossing={alternate=over}` since a bare `=` inside a keyval list is a LaTeX3 keyval syntax req... | row narrowed to the hull-route habit; the key IS read (route_habit seeds the derived crossing set) -- the sweep's no-effect scenarios never used a hull route |
| `kernel-wire:kind` | defect | Registry (line 198): {enum(index\|string\|pairing)}{index}{kernel}{Bond, travelling string, or generated skin pairing.} ACCEPTS: kind=index and kind=string both compile; but kind=pairing -- explicitly listed in the row's... | row corrected to enum(index|string); a pairing is generated, never authored |
| `kernel-wire:via` | reword | Registry (line 200): {address-list}{empty}{kernel}{Waypoints.} ACCEPTS: via={(1,3)} and via={(1,2)} parse and compile for both kind=index and kind=string wires. PAGE: for kind=index (bond, the DEFAULT kind), via has ZERO... | row states the index-bond limitation |

The fifty accurate rows are recorded in the sweep transcript (session
artifacts, 2026-08-22); each carries its compile evidence -- probe names,
raster hashes, and refusal messages.  Two verdicts were corrected on
re-review: `kernel-wire:crossing` is read by the hull-route habit pass
(`route_habit`), which the sweep's scenarios never exercised, and the
`kernel-picture:align` baseline effect is real; both rows keep their keys.

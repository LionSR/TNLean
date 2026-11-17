# One failure union for retained properties and literal histories

The existing joint interval theorem concerns the retained-space property only.
This contribution adds the stronger deterministic inclusion needed to retain
literal local sampling histories on the same event. It uses the existing
balanced interval spaces and their actual root merge list. There is no second
tree, public predicate family, or union over all overlapping intervals.

## The deterministic statement

Let P(a,b,S) be an interval property, true on every valid full short leaf.
Let H_J be prescribed events in an arbitrary choice space. The only local
implication is, at EACH ROOT-LISTED J and every choice omega,

    P(actual left child) and P(actual right child) and omega in H_J
      imply P(actual retained parent).

Write E_J for the event that both actual children satisfy P but H_J fails.
The theorem proves that failure of

    P(root) and, for every listed J, P(J) and omega in H_J

is contained in the single union of E_J over that same merge list.
It neither assumes H_J nor requires a property at unlisted long intervals.
Short roots, empty roots, and endpoint intervals are included.

For a fixed omega, the proof uses only the local conjunction
Q(a,b,S) = P(a,b,S) and (width < b-a implies omega in H_(a,b)).
This is internal to the proof, not a new declaration or alternative model.
Apply the existing `joint_failure_subset_iUnion_guardedIntervalFailure` to Q.
A guarded Q-failure has two P-good children. Outside the E union their history
holds; the supplied local implication gives parent P, contradicting the Q
failure. Every listed interval is long by the existing geometry theorem,
so Q gives both its retained property and literal history.

## The probability companion

The companion permits an arbitrary finite independent coordinate index, with
one explicitly prescribed coordinate for each listed interval. Its only
probabilistic inputs are measurability of E_J and the TRUE section bound

    mu_coordinate(J) {u : update(omega, coordinate(J), u) belongs to E_J} <= beta

for every baseline omega. No conditional law or comparison event is substituted.
The existing finite-list product-section theorem bounds the same E union by
list.length*beta; the existing actual merge count gives

    outerMeasure(strong joint failure) <= (r-p-1)_+ * beta.

There is no second history union and hence no second factor in the node count.
The coordinate can contain an entire finite sample sequence. The conclusion
uses outer measure, and does not require a separate measurability hypothesis
on the strong joint failure event itself. A physical application may also
prove that event measurable, but it is not needed for this upper bound.

## Source and remaining physical obligations

This is a conditional auxiliary to ALVV, arXiv:1602.08828v2, repeated sampling
in lines 749–755 and the `t:alg1` merge analysis in lines 1777–1817. It is not
a complete physical probability or energy theorem.

The intended actual H_J is QICLean's literal `canonicalHalfSamplingRawGood`
for the same parent's actual candidate and finite sequence. That event retains
the original-target stopped history. Final retained-space viability alone
does NOT supply the same terminal untrimmed image's improving-target bound
Delta/(91/100)^2. A later physical application must instantiate the actual
histories, prove their measurable guarded sections and probability bounds,
and derive the local history-to-parent implication from the SAME family.
Those analytic inputs are deliberately explicit here; none is counted as proved
by this generic deterministic/measure-theoretic contribution.

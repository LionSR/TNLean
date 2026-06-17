# Report on Chapter 12: Symmetries, String Order, and SPT Classification

## Executive conclusion

Chapter 12 is useful, but its final interpretation should be tightened.

The chapter correctly develops the MPS algebraic ingredients behind 1D SPT order:

1. a physical on-site symmetry gives a virtual gauge;
2. the virtual gauges form a projective representation;
3. the projective representation determines a cocycle;
4. changing virtual phases changes the cocycle by a coboundary;
5. a twisted transfer channel has non-decaying boundary-refined string order exactly when the physical unitary is implemented virtually.

However, Chapter 12 does **not** prove the physical 1D SPT classification theorem.

The issue is not with the virtual-cocycle extraction itself. That part is essentially right. The issue is that the chapter identifies, or at least suggests, too strongly that existence of string order is an SPT invariant. With the chapter's broad definition of string order this statement is formally defensible, but it is not a meaningful SPT invariant: it holds for all injective symmetric tensors, including tensors in different SPT phases.

The actual SPT invariant is the projective cocycle class of the virtual symmetry representation, not the mere existence of string order.

---

## 1. What Chapter 12 proves correctly

The chapter has the right backbone.

Given an injective MPS tensor and an on-site physical symmetry, the fundamental theorem implies that the physical action can be pushed through the tensor as a virtual gauge transformation.

Schematically, if the physical symmetry is represented by a matrix \(U(g)\), then one obtains virtual matrices \(\rho(g)\) satisfying a covariance relation of the form

$$
\sum_j U(g)_{ij} A^j
=
\rho(g)^{-1} A^i \rho(g)
$$

up to convention and possible scalar phases.

Since the virtual matrices are only determined up to scalar phase, the multiplication law is generally projective:

$$
\rho(g)\rho(h)
=
\omega(g,h)\rho(gh).
$$

Associativity forces the cocycle condition:

$$
\omega(g,h)\omega(gh,k)
=
\omega(h,k)\omega(g,hk).
$$

Changing phases of the virtual representatives changes omega by a coboundary. Therefore the invariant extracted from the tensor is the cohomology class

$$
[\omega].
$$

This part is the correct MPS route to the usual 1D bosonic SPT label.

---

## 2. What the string-order section proves

The source paper for the string-order section is:

**D. Pérez-García, M. M. Wolf, M. Sanz, F. Verstraete, J. I. Cirac, "String order and symmetries in quantum spin lattices," Phys. Rev. Lett. 100, 167202 (2008), arXiv:0802.0447.**

That paper proves, in the finitely correlated state / MPS setting, that non-decaying string order is equivalent to the presence of a local symmetry.

In modern MPS language, the key object is the twisted transfer map

$$
\mathcal E_u(X)
=
\sum_{i,j}
\langle j|u|i\rangle
A^i X A^{j\dagger}.
$$

The string correlator can be written as

$$
\mathrm{tr}
\left[
\Lambda\,\mathcal E_x\,\mathcal E_u^N\,\mathcal E_y(\mathbf 1)
\right].
$$

Its large-N behavior is controlled by the peripheral spectrum of the twisted transfer map.

For injective MPS, the twisted transfer map has a peripheral eigenvalue precisely when the physical unitary can be implemented by a virtual unitary. In other words,

$$
\text{non-decaying twisted transfer}
$$

is equivalent to

$$
\text{virtual implementability of the physical unitary}.
$$

This is the right content of the string-order theorem.

---

## 3. Important distinction: ordinary string order versus boundary-refined string order

The source paper begins with physical endpoint operators. The string order parameter has the form

$$
\langle x\,u^{\otimes N}\,y\rangle,
$$

where \(x\) and \(y\) are local endpoint observables.

Chapter 12 appears to formalize a broader algebraic version using virtual boundary witnesses. That is, string order is witnessed by expressions of the form

$$
\mathrm{tr}
\left[
\Lambda\,X\,\mathcal E_u^N(Y)
\right].
$$

With this broader definition, if the twisted transfer map has a peripheral eigenoperator, one can choose suitable boundary matrices \(X\) and \(Y\) to obtain a non-decaying sequence.

This distinction matters.

Under the broad boundary-refined definition, Theorem 12.61 is basically true: every injective symmetric MPS has boundary-refined string order for every symmetry element.

Under the more physical fixed-endpoint definition, the statement would be too strong: a particular chosen pair of endpoint operators may have zero overlap with the relevant virtual eigenoperator.

So the chapter should explicitly say:

> The string order used here is an existence statement over suitable boundary witnesses, not a fixed physical endpoint string order parameter.

Without this clarification, the reader may incorrectly identify the result with ordinary string order in the Haldane-chain sense.

---

## 4. The issue with Theorem 12.61

Theorem 12.61 says that string order holds for every group element of an injective symmetric MPS.

Given the chapter's broad boundary-witness definition, this is acceptable.

But conceptually it should be read as:

> For every physical symmetry element, the corresponding twisted transfer map has a peripheral eigenoperator. Hence suitable boundary witnesses can produce non-decaying string order.

It should not be read as:

> Every symmetric injective MPS has a physically robust, fixed-endpoint string order parameter that distinguishes an SPT phase.

The theorem detects symmetry / virtual implementability. It does not detect nontrivial SPT order.

---

## 5. The issue with Theorem 12.62

Theorem 12.62 says that string order is an SPT invariant.

As written, this is misleading.

The proof only uses Theorem 12.61, which says that string order exists universally for all injective symmetric tensors satisfying the canonical assumptions. Therefore Theorem 12.62 does not actually use the SPT cocycle class.

This means the theorem proves only the following weak statement:

> If two tensors are injective and symmetric under the same on-site representation, then both have boundary-refined string order for every group element.

That statement is true, but it is not an SPT invariant in any meaningful sense. It holds even for tensors in different SPT phases.

So Theorem 12.62 should not be presented as a substantive SPT statement.

A better title would be:

> Boundary-refined string order is universal for injective symmetric tensors.

or:

> Symmetry implies boundary-refined string order.

---

## 6. Why string order is not equivalent to SPT phase

A single string order parameter, or even the mere existence of string order for each group element, is not equivalent to being in a particular SPT phase.

The SPT phase is determined by how all virtual symmetry operators multiply:

$$
\rho(g)\rho(h)
=
\omega(g,h)\rho(gh).
$$

The invariant is the cohomology class of omega.

String order for a single unitary \(u\) only tells us that a virtual operator associated with \(u\) exists. It does not determine how virtual operators for different group elements multiply.

A trivial symmetric product state can have non-decaying string expectation for a symmetry. It is nevertheless in the trivial SPT phase.

Thus:

$$
\text{existence of string order}
$$

does not imply

$$
\text{nontrivial SPT order}.
$$

The correct relationship is:

1. string order detects virtual implementability of individual symmetry elements;
2. SPT classification uses the projective multiplication law of all virtual symmetry implementers;
3. refined string-order selection rules can diagnose the projective class, but ordinary existence of string order is not the classifying invariant.

---

## 7. What Chen--Gu--Wen prove

The relevant paper is:

**X. Chen, Z.-C. Gu, X.-G. Wen, "Classification of Gapped Symmetric Phases in 1D Spin Systems," Phys. Rev. B 83, 035107 (2011), arXiv:1008.3745.**

Chen--Gu--Wen classify 1D short-range-correlated MPS phases under symmetric local unitary equivalence. Their result is that, without symmetry, all 1D short-range-entangled bosonic phases are trivial, while with on-site symmetry different SPT phases are labelled by projective representations of the symmetry group.

In MPS language, this means that phases are labelled by

$$
H^2(G,U(1)).
$$

This paper proves the classification in the symmetric-local-unitary / fixed-point MPS language.

This is stronger than what Chapter 12 proves. Chapter 12 extracts a cocycle from a symmetric tensor, but it does not prove that this cocycle class is equivalent to a symmetric phase-equivalence class.

---

## 8. What Schuch--Pérez-García--Cirac prove

The relevant paper is:

**N. Schuch, D. Pérez-García, I. Cirac, "Classifying quantum phases using Matrix Product States and PEPS," Phys. Rev. B 84, 165139 (2011), arXiv:1010.3732.**

This is closer to the MPS / parent-Hamiltonian formulation.

For 1D MPS, it shows that:

1. without symmetries, all injective MPS lie in the same phase;
2. with on-site symmetry and no symmetry breaking, phases are classified by the projective representation class of the virtual symmetry action;
3. with symmetry breaking, one must also track block structure and how the symmetry permutes the blocks.

This is the paper that most directly supplies the missing step in Chapter 12: the relation between virtual cocycle classes and actual phase equivalence of MPS parent Hamiltonians.

---

## 9. What Chapter 12 is missing for a true SPT classification proof

To prove the physical classification theorem, Chapter 12 would need two additional pieces.

### 9.1 Invariance under symmetric gapped paths

One must prove:

$$
\text{symmetric gapped path}
\quad\Rightarrow\quad
[\omega_A]=[\omega_B].
$$

That is, the virtual cocycle class cannot change along a symmetric gapped path.

Chapter 12 does not prove this. It extracts the cocycle at a fixed tensor.

### 9.2 Completeness

One must also prove:

$$
[\omega_A]=[\omega_B]
\quad\Rightarrow\quad
\text{there exists a symmetric gapped path from A to B}.
$$

This is the constructive half. It usually proceeds by blocking, going to a fixed-point/isometric or canonical form, aligning the virtual projective representations, and constructing a symmetric path of tensors or parent Hamiltonians.

Chapter 12 does not provide this construction.

Thus Chapter 12 proves the map

$$
\text{symmetric injective MPS}
\longrightarrow
H^2(G,U(1)),
$$

but it does not prove that this map classifies symmetric gapped phases.

---

## 10. How to revise Chapter 12

### Recommended renaming

Rename Section 12.6 from:

> SPT Phase Classification

to something less strong, such as:

> Cocycle Labels and SPT Terminology

or:

> Virtual Cocycle Labels for Symmetric Injective MPS

or:

> Ingredients for 1D MPS SPT Classification

### Revised statement replacing Theorem 12.62

Replace Theorem 12.62 by something like:

**Proposition.**  
Let \(A\) be an injective MPS tensor in canonical form and symmetric under an on-site unitary representation \(U\) of \(G\). Then for every group element \(g\), the twisted transfer channel associated with \(U(g)\) has spectral radius one. Equivalently, \(U(g)\) is implemented by a virtual unitary. Consequently, suitable boundary witnesses give non-decaying boundary-refined string order.

Then add:

**Remark.**  
This existence of boundary-refined string order is not an SPT invariant in the classifying sense. It is a symmetry diagnostic. The SPT invariant is the cohomology class of the projective virtual representation.

### Add an external classification theorem

After Definition 12.60, add a theorem labelled as external or quoted:

**Theorem (CGW / Schuch--Pérez-García--Cirac).**  
For 1D bosonic injective MPS with a fixed on-site unitary symmetry and no symmetry breaking, symmetric phases are classified by the cohomology class of the virtual projective representation.

Then state explicitly:

> Chapter 12 proves the cocycle extraction part of this theorem, but the phase-classification part requires an argument using symmetric local unitaries or symmetric gapped paths of parent Hamiltonians.

---

## 11. Recommended report sentence

A concise version of the diagnosis is:

> Chapter 12 correctly formalizes how physical symmetries of injective MPS produce virtual projective representations and cocycle labels. It also correctly formalizes the Pérez-García--Wolf--Sanz--Verstraete--Cirac relation between string order and local symmetry, provided "string order" is understood as an existence statement over suitable boundary witnesses. However, the chapter does not prove the SPT classification theorem. Definition 12.60 defines phase equivalence by cohomologous cocycles, rather than deriving it from symmetric gapped paths or symmetric local unitaries. Theorem 12.62 should not be interpreted as saying that string order classifies or characterizes SPT phases; the mere existence of boundary-refined string order is universal for injective symmetric tensors. The actual SPT invariant is the cohomology class of the virtual projective representation, while refined string-order selection rules can diagnose this class.

---

## 12. References

1. D. Pérez-García, M. M. Wolf, M. Sanz, F. Verstraete, J. I. Cirac, "String order and symmetries in quantum spin lattices," Phys. Rev. Lett. 100, 167202 (2008), arXiv:0802.0447.

2. X. Chen, Z.-C. Gu, X.-G. Wen, "Classification of Gapped Symmetric Phases in 1D Spin Systems," Phys. Rev. B 83, 035107 (2011), arXiv:1008.3745.

3. X. Chen, Z.-C. Gu, X.-G. Wen, "Complete classification of 1D gapped quantum phases in interacting spin systems," Phys. Rev. B 84, 235128 (2011), arXiv:1103.3323.

4. N. Schuch, D. Pérez-García, I. Cirac, "Classifying quantum phases using Matrix Product States and PEPS," Phys. Rev. B 84, 165139 (2011), arXiv:1010.3732.

5. F. Pollmann, A. M. Turner, "Detection of Symmetry Protected Topological Phases in 1D," Phys. Rev. B 86, 125441 (2012), arXiv:1204.0704.

# Internal intervals of the actual balanced recursion

The midpoint recursion with positive leaf width gives an ordered list of its internal intervals: first the two child lists, then their parent. The empty or short root contributes no merge. The list length is at most max(r-p-1,0), so a chain root has at most max(L-1,0) merges.

The proof uses strong induction on interval length. At every long parent both child lengths are positive, strictly smaller, and sum to the parent length. This counts descendants of one specified root; it does not count all overlapping intervals in the chain.

This elementary auxiliary supports the failure-probability sum in Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Figure fig:algo1 and lines 1777–1817. It constructs no sampled spaces and asserts no adaptive probability or running time.

The temporary inspection source is deleted. Combined ordinary-build and
compiled blueprint checks remain pending.

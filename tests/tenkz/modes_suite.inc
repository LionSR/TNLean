% The shared source suite of modes_test: input twice, once per glyph policy.
% B1 periodic word with leg labels, B3 sandwich transfer map, B4 blocking
% with brace below, B7 zipper with fuse, S1 ket/op/bra window.
B1 periodic word with leg labels:
\begin{tenkz}[periodic, physical=up, bond label={$D$ at 1-2}]
  \tn[up=$i_1$]{A} & \tn[up=$i_2$]{A} & \tn[up=$i_3$]{A}
\end{tenkz}

\medskip
B3 sandwich transfer map:
% E_A = sum_i A^i (x) conj(A^i): a map on the doubled virtual space --
% four open virtual legs; west pair = input (X plugs in there), east pair
% = output.  The contracted physical leg IS the sum over i (contrast B8,
% where the sum is explicit and the leg stays open).
\[
  \mathcal{E}_A \;=\;
  \begin{tenkz}[sandwich]
    \tn{A} \\
    \tn*{A}
  \end{tenkz}
\]

B4 blocking with brace below:
% TI blocking: A^{(L)}_{(i_1...i_L)} = A^{i_1} ... A^{i_L} as D x D
% matrices -- the virtual boundary indices stay open on BOTH sides; the
% physical counts differ only by grouping (L legs vs one combined index).
\[
  \begin{tenkz}[physical=up]
    \tn[up=$i_1$]{A}\tnspan[brace below]{4}{L\text{ copies}} &
    \tn[up=$i_2$]{A} & \tndots & \tn[up=$i_L$]{A}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tn[pill, wide=2, up={$i_1\cdots i_L$}]{A^{(L)}}
  \end{tenkz}
\]

B7 zipper with fuse:
% Zipper (pulling through, arXiv:2203.12563): V (O-window (x) A-window)
%   = (B-window) V, with V : C^{D_O} x C^{D_A} -> C^{D_B} fusing the two
% bond spaces and B^i = sum_j V (O^{i j} (x) A^j) the fused site.  LHS:
% V's single combined leg is the open west index; the east O/A pair stays
% open.  RHS: the fused-bond B word; the bond-SPLITTING glyph (V at the
% east end of a one-row word) is a tracked Phase-1 primitive, so V closes
% the equation as a symbol here.
\[
  \begin{tenkz}[rows={op, ket}]
    \tnfuse[span=2]{V} & \tn[mpo]{O}\tnspan[brace above]{3}{n} & \tndots & \tn[mpo]{O} \\
                       & \tn{A}                                & \tndots & \tn{A}
  \end{tenkz}
  \;=\;
  \begin{tenkz}[physical=up]
    \tn[box, up=$i_1$]{B}\tnspan[brace above]{3}{n} & \tndots & \tn[box, up=$i_n$]{B}
  \end{tenkz}
  \,V
\]

S1 ket/op/bra window:
% Local window of <psi|O|psi>: physical indices contract vertically
% (ket-op, op-bra); all six virtual indices stay open -- this is a window
% of a larger contraction, not a scalar.
\[
  \begin{tenkz}[rows={ket, op, bra}]
    \tn{A} & \tn{A} & \tn{A} \\
    \tn[mpo]{O} & \tn[mpo]{O} & \tn[mpo]{O} \\
    \tn*{A} & \tn*{A} & \tn*{A}
  \end{tenkz}
\]

% mixed / scripted labels on one wire and across rows: box heights must be
% uniform under the glyph strut
\[
  \begin{tenkz}[rows={op:operator, op:operator}]
    \tn[mpo]{T_g} & \tn[mpo]{T_g} & \tndots & \tn[mpo]{T_g} \\
    \tn[mpo]{T_h} & \tn[mpo]{T_h} & \tndots & \tn[mpo]{T_h}
  \end{tenkz}
  \qquad
  \begin{tenkz}[physical=up]
    \tn{A} & \tnX{X} & \tn{T_g} & \tn{A^{(2)}}\tncut{S} & \tn{B}
  \end{tenkz}
\]

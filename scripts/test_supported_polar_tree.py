#!/usr/bin/env python3
"""Typed diagram boundaries and finite-dimensional supported polar-merge regressions."""
from pathlib import Path
import re
import unittest

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src/chapter/ch32_log_depth_unequal_mera.tex"


def polar_factors(matrix):
    left, values, right = np.linalg.svd(matrix, full_matrices=False)
    active = values > 1e-12
    return (left[:, active] @ right[active, :],
            right.conj().T @ np.diag(values) @ right)


def blocked_diagonal_tensor(columns, length):
    d, bond = columns.shape
    products = [np.array([1.0 + 0j])] * bond
    for _ in range(length):
        products = [np.kron(products[j], columns[:, j]) for j in range(bond)]
    result = np.zeros((d ** length, bond ** 2), dtype=complex)
    for j in range(bond):
        result[:, j * bond + j] = products[j]
    return result


class SupportedPolarTreeTests(unittest.TestCase):
    def test_typed_diagram_boundary(self):
        source = SOURCE.read_text()
        diagram = source.split(r"\begin{tenkzequation}", 1)[1].split(
            r"\end{tenkzequation}", 1)[0]
        self.assertEqual(diagram.count(r"\begin{tenkz}"), 2)
        self.assertEqual(diagram.count(r"$\C^\chi$"), 2)
        self.assertEqual(diagram.count(r"$\mathcal H_l$"), 2)
        self.assertEqual(diagram.count(r"$\mathcal H_r$"), 2)
        self.assertEqual(re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", diagram),
                         [("w.135", "vl.270"), ("w.45", "vr.270")])
        self.assertNotIn("D^2", diagram)
        self.assertNotIn(r"\begin{tenkzeq}", source)
        self.assertIn("entire subtrees, not free gates", source)

    def test_nonsquare_support_and_overlapping_sectors(self):
        # Three inequivalent one-dimensional normal sectors with overlapping
        # physical ranges; chi = 3 is deliberately not a square.
        columns = np.array([[1, .6, .2], [0, .8, .3j], [0, 0, np.sqrt(.87)]],
                           dtype=complex)
        np.testing.assert_allclose(np.sum(abs(columns) ** 2, axis=0), 1)
        bond = columns.shape[1]
        support = np.arange(bond) * (bond + 1)
        pair_support = np.array([a * bond ** 2 + b for a in support for b in support])
        for left_length, right_length in [(1, 1), (1, 2), (2, 3)]:
            left, positive_left = polar_factors(blocked_diagonal_tensor(columns, left_length))
            right, positive_right = polar_factors(blocked_diagonal_tensor(columns, right_length))
            parent, _ = polar_factors(blocked_diagonal_tensor(columns, left_length + right_length))
            pair_tensor = np.array([
                (positive_left[a].reshape(bond, bond) @
                 positive_right[b].reshape(bond, bond)).reshape(-1)
                for a in range(bond ** 2) for b in range(bond ** 2)])
            merge, _ = polar_factors(pair_tensor)
            supported_merge = merge[np.ix_(pair_support, support)]
            joined = np.kron(left[:, support], right[:, support])
            np.testing.assert_allclose(joined @ supported_merge, parent[:, support], atol=1e-12)
            np.testing.assert_allclose(supported_merge.conj().T @ supported_merge,
                                       np.eye(bond), atol=1e-12)
            # A coherent complex sector vector, including a vanishing amplitude.
            amplitude = np.array([1 + 2j, 0, -.7j])
            np.testing.assert_allclose(joined @ supported_merge @ amplitude,
                                       parent[:, support] @ amplitude, atol=1e-12)
            # The full-input polar map is not an isometry on the cross-sector pairs.
            self.assertGreater(np.linalg.norm(parent.conj().T @ parent - np.eye(bond ** 2)), 1)


if __name__ == "__main__":
    unittest.main()

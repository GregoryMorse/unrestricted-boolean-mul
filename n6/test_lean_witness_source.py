"""Check the transcribed Lean positive data against the original JSON.

These are source/provenance regressions, not substitutes for kernel checking.
"""
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


def lean_data():
    source = (ROOT / "UnrestrictedBooleanMul/N6/Upper.lean").read_text(encoding="utf-8")
    masks = re.search(r"def sixMask[^=]*:=\s*!\[([^]]+)\]", source).group(1)
    masks = [int(x) for x in masks.split(",")]
    rows = source.split("def sixOutputSupport", 1)[1].split("def bitCoefficient", 1)[0]
    outputs = [[int(x) for x in row.split(",")] for row in re.findall(r"\{([\d, ]+)\}", rows)]
    return masks, outputs


def coefficient_check(a, b, masks_left, masks_right, outputs):
    for s, row in enumerate(outputs):
        for i in range(a):
            for j in range(b):
                value = sum(((masks_left[k] >> i) & 1) * ((masks_right[k] >> j) & 1)
                            for k in row) % 2
                if value != int(i + j == s):
                    return False
    return True


class LeanWitnessSourceTests(unittest.TestCase):
    def test_exact_original_data(self):
        masks, outputs = lean_data()
        original = json.loads((ROOT / "n6/artifact/n6_bilinear_rank17_solution.json").read_text())
        self.assertEqual([[m, m] for m in masks], original["gates"])
        self.assertEqual(outputs, original["outputs"])

    def test_square_coefficients(self):
        masks, outputs = lean_data()
        self.assertTrue(coefficient_check(6, 6, masks, masks, outputs))

    def test_rectangular_coefficients(self):
        masks, outputs = lean_data()
        rows = [[k - 1 for k in row if k != 0] for row in outputs[1:]]
        self.assertTrue(coefficient_check(5, 6, [m >> 1 for m in masks[1:]], masks[1:], rows))

    def test_wrong_output_rejected(self):
        masks, outputs = lean_data()
        outputs[0] = []
        self.assertFalse(coefficient_check(6, 6, masks, masks, outputs))

    def test_wrong_shift_rejected(self):
        masks, outputs = lean_data()
        rows = [[k - 1 for k in row if k != 0] for row in outputs[1:]]
        self.assertFalse(coefficient_check(5, 6, masks[1:], masks[1:], rows))


if __name__ == "__main__":
    unittest.main()

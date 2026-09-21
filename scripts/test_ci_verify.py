import tempfile
from pathlib import Path
import unittest

import ci_verify as ci


class ScopedCITests(unittest.TestCase):
    def test_profiles_have_distinct_audits(self):
        self.assertEqual(len({x[0] for x in ci.PROFILES.values()}), 4)
        for audit, roots in ci.PROFILES.values():
            self.assertTrue(audit.endswith('.lean'))
            self.assertTrue(roots)

    def test_n4_is_research_free(self):
        modules = ci.inspect("n4")["modules"]
        self.assertIn("UnrestrictedBooleanMul.N4.Main", modules)
        self.assertFalse(any(".N5" in x or ".N6" in x or x.endswith(".Research") for x in modules))
        self.assertEqual(len(ci.inspect("n4")["expected_axioms"]), 6)

    def test_nested_comments_are_not_code(self):
        self.assertEqual(ci.code_only('/- sorry /- axiom -/ native_decide -/\ntheorem x := 0').strip(), 'theorem x := 0')
        self.assertIn("sorry", ci.code_only('/- not code -/ theorem x := by sorry'))

    def test_axiom_failure_controls(self):
        good = "'x' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(set(ci.validate_axioms(good, ["x"])["x"]), ci.ALLOWED)
        for text, expected in ((good.replace("Quot.sound", "Lean.ofReduceBool"), ["x"]),
                               (good, ["x", "missing"]), (good + "\n" + good, ["x"]),
                               ("", ["x"])):
            with self.assertRaises(ValueError):
                ci.validate_axioms(text, expected)

    def test_zero_axioms(self):
        self.assertEqual(ci.validate_axioms("'x' does not depend on any axioms", ["x"]), {"x": []})


if __name__ == "__main__":
    unittest.main()

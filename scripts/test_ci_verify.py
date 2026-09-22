import tempfile
import json
from pathlib import Path
import unittest

import ci_verify as ci


class ScopedCITests(unittest.TestCase):
    def test_n4_msc_matches_published_arxiv_classification(self):
        metadata = (ci.ROOT / 'formalization.yaml').read_text(encoding='utf-8')
        rows = [line.strip() for line in metadata.splitlines()
                if line.strip().startswith('msc2020:')]
        self.assertEqual(rows, ['msc2020: [68Q06, 68Q17, 68W30, 15A75, 94D10]'])
        self.assertIn('68Q06 is primary; the remaining codes are secondary', metadata)

    def test_small_runners_are_rejected(self):
        for physical in (0, 7 * 1024**3, 14 * 1024**3 - 1):
            with self.assertRaises(RuntimeError):
                ci.validate_runner_memory(physical)
        ci.validate_runner_memory(14 * 1024**3)

    def test_palomar_preflight_declares_confirmed_authority(self):
        workflow = (ci.ROOT / '.github/workflows/palomar.yml').read_text(encoding='utf-8')
        request_id = next(line.split('request_id:', 1)[1].strip()
                          for line in workflow.splitlines() if line.strip().startswith('request_id:'))
        self.assertRegex(request_id, r'^[a-z0-9]{12}$')
        options = next(line.split('options:', 1)[1].strip().strip("'")
                       for line in workflow.splitlines() if line.strip().startswith('options:'))
        self.assertEqual(json.loads(options), {
            'comparator_config_path': 'comparator.json',
            'formalization_metadata_path': 'formalization.yaml',
            'authorization_relationship': 'I am a responsible author or maintainer',
        })

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

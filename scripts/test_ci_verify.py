import tempfile
import json
from pathlib import Path
import unittest

import ci_verify as ci
from check_lean_sources import check_source


class ScopedCITests(unittest.TestCase):
    def test_comparator_checks_models_and_all_six_statements(self):
        source = (ci.ROOT / 'scripts/ci_verify.py').read_text(encoding='utf-8')
        self.assertIn('["lake", "comparator", "--config", "scripts/comparator-model.json"]', source)
        self.assertIn('["lake", "comparator", "--config", "comparator.json"]', source)
        self.assertNotIn('inadvisably', source)
        probe = json.loads((ci.ROOT / 'scripts/comparator-model.json').read_text())
        self.assertEqual(probe['challenge_module'], 'Challenge.ModelProbe')
        self.assertEqual(probe['solution_module'], 'Solution.ModelProbe')
        self.assertEqual(probe['theorem_names'], ['UnrestrictedBooleanMul.comparator_model_probe'])
        self.assertEqual(set(probe['permitted_axioms']), ci.ALLOWED)
        for path in ('Challenge.lean', 'UnrestrictedBooleanMul/Mul.lean'):
            text = (ci.ROOT / path).read_text(encoding='utf-8')
            for name, argument, coordinate, bound in (
                ('aVar', 'i', 'i.val', 'Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n n)'),
                ('bVar', 'j', 'n + j.val', 'Nat.add_lt_add_left j.isLt n')
            ):
                expected = (f'def {name} (n : Nat) ({argument} : Fin n) : ANF (2 * n) :=\n'
                            f'  X ⟨{coordinate}, Eq.mpr (congrArg (fun k : Nat => {coordinate} < k) '
                            f'(Nat.two_mul n))\n    ({bound})⟩')
                self.assertIn(expected, text)

    def test_ci_installer_preserves_the_exact_official_compiler(self):
        installer = (ci.ROOT / 'scripts/install_ci_lean.sh').read_text(encoding='utf-8')
        self.assertIn('leanprover/lean4:v' + ci.COMPILER_VERSION, installer)
        self.assertIn('https://github.com/leanprover/lean4/releases/download/v' + ci.COMPILER_VERSION, installer)
        self.assertIn('1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997', installer)
        self.assertIn('sha256sum --check --strict', installer)
        self.assertNotIn('--insecure', installer)

    def test_repository_wide_source_policy_controls(self):
        for source in ('module\n', '-- copyright\n/- nested /- c -/ -/\nmodule\n',
                       'module\n/-! docs -/\npublic import Mathlib\n'):
            check_source('unused/N5.lean', source)
        for source in ('', 'import Mathlib\n', 'moduleFake\n',
                       '/-! docs -/\nmodule\n', '/-- docs -/\nmodule\n',
                       '/- unterminated', 'module\n' + '\n' * 10_000):
            with self.assertRaises(ValueError):
                check_source('unused/N5.lean', source)
        with self.assertRaises(ValueError):
            check_source('unused/N5.lean', 'module\n', '120000')
        check_source('lakefile.lean', 'import Lake\n')

    def test_requested_compiler_is_strictly_pinned(self):
        ci.validate_compiler_version('Lean (version 4.35.0-rc3, commit '+ci.COMPILER_COMMIT+', Release)')
        for version in ('Lean (version 4.33.1, commit 819816b2e0a3, Release)',
                        'Lean (version 4.35.0-rc2, commit '+ci.COMPILER_COMMIT+', Release)',
                        'Lean (version 4.35.0-rc3, commit 00000000, Release)'):
            with self.assertRaises(ValueError):
                ci.validate_compiler_version(version)
        self.assertEqual((ci.ROOT/'lean-toolchain').read_text().strip(),
                         'leanprover/lean4:v'+ci.COMPILER_VERSION)
        manifest=json.loads((ci.ROOT/'lake-manifest.json').read_text())
        mathlib=next(p for p in manifest['packages'] if p['name']=='mathlib')
        self.assertEqual(mathlib['inputRev'],'v4.35.0-rc3')
        self.assertEqual(mathlib['rev'],'c55e6e786f49471c72fbddbec5415808896aec1e')

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
        self.assertIn('uses: ./.github/workflows/palomar-source.yml', workflow)
        self.assertIn("if: vars.PALOMAR_NAMESPACE_ENABLED == 'true'", workflow)
        self.assertIn('needs: source', workflow)
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

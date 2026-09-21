"""Small positive/negative controls for the repository integration layer."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

from quick import check_hashes
from verify_upper import validate, verify, WITNESS


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads(WITNESS.read_text(encoding="utf-8"))

    def test_all_original_hashes(self):
        self.assertEqual(check_hashes(), 50)

    def test_wrong_manifest_fails(self):
        with patch.object(Path, "read_bytes", return_value=b"not a manifest"):
            with self.assertRaises(ValueError):
                check_hashes()

    def test_missing_endpoint_audit_fails(self):
        original = Path.read_bytes
        def read(path):
            if path.name == "rect56_zero_local_lowaudit.txt":
                raise FileNotFoundError(path)
            return original(path)
        with patch.object(Path, "read_bytes", read):
            with self.assertRaises(FileNotFoundError):
                check_hashes()

    def test_changed_file_fails(self):
        original = Path.read_bytes
        def read(path):
            result = original(path)
            return result + b"corruption" if path.name == WITNESS.name else result
        with patch.object(Path, "read_bytes", read):
            with self.assertRaises(ValueError):
                check_hashes()

    def test_complete_scalar_replays(self):
        self.assertEqual(verify(self.data), {"square_gates": 17, "square_inputs": 4096,
                                          "rectangular_gates": 16, "rectangular_inputs": 2048})

    def test_wrong_coefficient_fails(self):
        self.data["outputs"][0] = []
        with self.assertRaises(ValueError):
            verify(self.data)

    def test_malformed_witnesses_fail(self):
        variants = []
        for selector in (-1, 64, True, "1"):
            data = deepcopy(self.data)
            data["gates"][0][0] = selector
            variants.append(data)
        for indices in ([0, 0], [17], [-1], [False]):
            data = deepcopy(self.data)
            data["outputs"][0] = indices
            variants.append(data)
        data = deepcopy(self.data)
        data["gates"] *= 100
        variants.extend([data, {}, {"rank": True}, None])
        for data in variants:
            with self.subTest(data=data):
                with self.assertRaises(ValueError):
                    validate(data)

    def test_optimized_runner_fails_closed(self):
        result = subprocess.run([sys.executable, "-E", "-B", "-O", str(Path(__file__).with_name("quick.py"))],
                                capture_output=True, text=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("assertions must remain enabled", result.stderr)


if __name__ == "__main__":
    unittest.main()

"""Run with python3 -m unittest test_five_square_sweep_245212."""
import sqlite3
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import five_square_sweep_245212 as sweep
from five_square_boxes_245212 import count_support


class SweepTests(unittest.TestCase):
    def test_exact_reference_and_vertex_bound(self):
        self.assertEqual(count_support(11, 1009), (137, 30372, 0, 0))
        self.assertEqual(count_support(13, 191), (0, 0, 0, 0))
        with self.assertRaises(ValueError):
            count_support(11, 15)

    def test_failed_support_is_not_a_receipt(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "results.sqlite3"
            counts = (1,2,0,0)
            with patch.object(sweep, "count_support", side_effect=[counts,ArithmeticError("witness")]):
                db = sqlite3.connect(path)
                try:
                    with self.assertRaisesRegex(RuntimeError, "q=11, r=19: witness"):
                        sweep.sweep(db, (11,12), (17,20), 1)
                finally:
                    db.close()
            db = sqlite3.connect(path)
            try:
                with patch.object(sweep, "count_support", return_value=counts) as check:
                    result = sweep.sweep(db, (11,12), (17,20), 1)
                    check.assert_called_once_with(11,19)
                    self.assertEqual((result["reused"],result["checked"]), (1,1))
                with patch.object(sweep, "count_support", side_effect=AssertionError("unexpected replay")):
                    resumed = sweep.sweep(db, (11,12), (17,20), 2)
                    self.assertEqual(resumed["results_sha256"], result["results_sha256"])
                    self.assertEqual(resumed["workers"], 0)
                with patch.object(sweep, "proof_digest", return_value="changed"), \
                     patch.object(sweep, "count_support", return_value=counts):
                    changed = sweep.sweep(db, (11,12), (17,20), 1)
                    self.assertEqual((changed["reused"],changed["checked"]), (0,2))
            finally:
                db.close()

    def test_transitive_source_change_invalidates_receipts(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder) / "entry_245212.py"
            root.write_text("from inner_245212 import v\n")
            inner = root.with_name("inner_245212.py")
            inner.write_text("from arithmetic_245212 import v\n")
            arithmetic = root.with_name("arithmetic_245212.py")
            arithmetic.write_text("v=1\n")
            with patch.object(sweep, "__file__", str(root)):
                before = sweep.proof_digest()
                arithmetic.write_text("v=2\n")
                self.assertNotEqual(sweep.proof_digest(), before)

    def test_parallel_worker_error_names_the_support(self):
        with self.assertRaisesRegex(RuntimeError, "q=11, r=15"):
            list(sweep.checked_rows([(11,15),(11,1009)], 2, sweep.proof_digest()))


if __name__ == "__main__":
    unittest.main()

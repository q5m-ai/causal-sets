"""Adversarial tests for source accounting; these are not Lean proof tests."""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_written_coverage import (
    CoverageError, DEFAULT_MANIFEST, source_blobs, text_identity, validate,
)


class WrittenCoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "--quiet")
        self.git("config", "user.name", "Source roster test")
        self.git("config", "user.email", "test@example.invalid")
        (self.root / "notes").mkdir()
        (self.root / "notes/a.md").write_text(
            "# A\n\nUnnumbered claim needing review.\n\n"
            "```math\nx=1\\tag{A1}\n```\n"
        )
        (self.root / "notes/b.markdown").write_text("# B\n\nNo equation label.\n")
        (self.root / "ignored.txt").write_text("not a Markdown source\n")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "Fixture")
        commit = self.git("rev-parse", "HEAD").strip()
        self.data = {
            "schema_version": 1,
            "scope": "all-markdown-at-source-commit",
            "meaning": "source-accounting-only",
            "source_commit": commit,
            "sources": [
                {
                    "path": path,
                    "blob": blob,
                    **text_identity((self.root / path).read_bytes()),
                    "review_state": "pending",
                    "indexes": [],
                    "reason": "Numbered and unnumbered claims await review.",
                }
                for path, blob in sorted(source_blobs(self.root, commit).items())
            ],
        }

    def git(self, *args):
        return subprocess.check_output(
            ["git", "-C", str(self.root), "-c", "core.hooksPath=/dev/null",
             "-c", "commit.gpgsign=false", *args], stderr=subprocess.PIPE, text=True
        )

    def reject(self, message, mutate):
        data = deepcopy(self.data)
        mutate(data)
        with self.assertRaisesRegex(CoverageError, message):
            validate(self.root, data)

    def test_valid_roster_includes_unlabelled_source(self):
        result = validate(self.root, self.data)
        self.assertEqual(result["pending"], 2)
        self.assertEqual(self.data["sources"][1]["tex_tags"], [])

    def test_omission(self):
        self.reject("omitted pinned sources", lambda d: d["sources"].pop())

    def test_duplicate(self):
        self.reject("duplicate source", lambda d: d["sources"].append(d["sources"][0]))

    def test_foreign_file(self):
        self.reject("not a pinned Markdown source", lambda d: d["sources"][0].update(path="extra.md"))

    def test_moving_ref_rejected(self):
        self.reject("full, lowercase Git SHA", lambda d: d.update(source_commit="HEAD"))

    def test_tree_is_not_a_commit_pin(self):
        tree = self.git("rev-parse", "HEAD^{tree}").strip()
        self.reject("must name a commit", lambda d: d.update(source_commit=tree))

    def test_stale_blob(self):
        self.reject("stale Git blob", lambda d: d["sources"][0].update(blob="0" * 40))

    def test_stale_text_hash(self):
        self.reject("stale sha256", lambda d: d["sources"][0].update(sha256="0" * 64))

    def test_stale_label_list(self):
        self.reject("stale tex_tags", lambda d: d["sources"][0].update(tex_tags=[]))

    def test_labels_cannot_be_promoted_to_proof(self):
        self.reject("invalid review_state", lambda d: d["sources"][0].update(review_state="proved"))
        self.reject("must not claim proof verification", lambda d: d.update(meaning="all-proved"))

    def test_exclusion_requires_reason(self):
        self.reject("explicit review/exclusion reason", lambda d: d["sources"][0].update(
            review_state="excluded", reason=""))

    def test_partial_index_must_exist(self):
        self.reject("invalid or missing index", lambda d: d["sources"][0].update(
            review_state="partial", indexes=["missing.md"]))
        self.reject("reviewed source needs an index", lambda d: d["sources"][0].update(
            review_state="indexed"))

    def test_index_cannot_escape_checkout(self):
        self.reject("invalid or missing index", lambda d: d["sources"][0].update(
            review_state="partial", indexes=["../outside.md"]))
        self.reject("invalid or missing index", lambda d: d["sources"][0].update(
            review_state="partial", indexes=[str(self.root / "notes/a.md")]))

    def test_working_source_changes_do_not_move_frozen_pin(self):
        (self.root / "notes/a.md").write_text("different working content\n")
        self.assertEqual(validate(self.root, self.data)["pending"], 2)

    def test_actual_repository_roster(self):
        root = Path(__file__).resolve().parent
        data = json.loads((root / DEFAULT_MANIFEST).read_text())
        counts = validate(root, data)
        self.assertGreater(sum(counts.values()), 0)
        self.assertEqual(set(counts), {"pending", "partial", "indexed", "excluded"})


if __name__ == "__main__":
    unittest.main()

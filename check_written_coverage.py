#!/usr/bin/env python3
"""Validate the pinned written-source roster, not mathematical proof coverage.

Every Markdown blob at the declared Git commit must occur exactly once. TeX
labels are text locators only: definitions, examples and failed arguments may
have labels too, and unnumbered claims still require a human source review.
This check does not inspect Lean proof terms or certify a source-to-theorem
correspondence. That needs statement review and the separate full Lean audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

DEFAULT_MANIFEST = "formal/written-coverage-sources.json"
SHA = re.compile(r"[0-9a-f]{40}\Z")
TEX_TAG = re.compile(r"\\tag\s*\{([^{}\n]+)\}")
REVIEW_STATES = {"pending", "partial", "indexed", "excluded"}


class CoverageError(ValueError):
    """An incomplete or inconsistent source roster, not a failed proof."""


def git_bytes(root: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), *args], stderr=subprocess.PIPE
        )
    except subprocess.CalledProcessError as exc:
        raise CoverageError(
            "Cannot read pinned Git source; fetch the declared source commit first."
        ) from exc


def source_blobs(root: Path, commit: str) -> dict[str, str]:
    if not isinstance(commit, str) or not SHA.fullmatch(commit):
        raise CoverageError("source_commit must be a full, lowercase Git SHA")
    if git_bytes(root, "cat-file", "-t", commit).strip() != b"commit":
        raise CoverageError("source_commit must name a commit, not a tree or blob")
    files = {}
    for entry in git_bytes(root, "ls-tree", "-rz", "--full-tree", commit).split(b"\0"):
        if not entry:
            continue
        meta, path = entry.split(b"\t", 1)
        _, kind, blob = meta.split()
        name = path.decode("utf-8")
        if kind == b"blob" and name.lower().endswith((".md", ".markdown")):
            files[name] = blob.decode("ascii")
    if not files:
        raise CoverageError("pinned source contains no Markdown blobs")
    return files


def text_identity(raw: bytes) -> dict:
    text = raw.decode("utf-8")
    return {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "tex_tags": sorted(set(TEX_TAG.findall(text))),
    }


def local_document(root: Path, path: object) -> bool:
    if not isinstance(path, str) or not path:
        return False
    candidate = Path(path)
    if candidate.is_absolute() or ".." in candidate.parts:
        return False
    resolved = (root / candidate).resolve()
    return resolved.is_relative_to(root.resolve()) and resolved.is_file()


def validate(root: Path, data: dict) -> dict[str, int]:
    if data.get("schema_version") != 1:
        raise CoverageError("unsupported source-roster schema")
    if data.get("scope") != "all-markdown-at-source-commit":
        raise CoverageError("scope must retain all Markdown at the source commit")
    if data.get("meaning") != "source-accounting-only":
        raise CoverageError("the source roster must not claim proof verification")
    files = source_blobs(root, data.get("source_commit"))
    rows = data.get("sources")
    if not isinstance(rows, list):
        raise CoverageError("sources must be a list")
    seen = set()
    counts = dict.fromkeys(sorted(REVIEW_STATES), 0)
    for row in rows:
        if not isinstance(row, dict):
            raise CoverageError("each source must be an object")
        path = row.get("path")
        if not isinstance(path, str) or path not in files:
            raise CoverageError(f"not a pinned Markdown source: {path!r}")
        if path in seen:
            raise CoverageError(f"duplicate source: {path}")
        seen.add(path)
        if row.get("blob") != files[path]:
            raise CoverageError(f"stale Git blob: {path}")
        identity = text_identity(git_bytes(root, "cat-file", "blob", files[path]))
        for key, value in identity.items():
            if row.get(key) != value:
                raise CoverageError(f"stale {key}: {path}")
        state = row.get("review_state")
        if not isinstance(state, str) or state not in REVIEW_STATES:
            raise CoverageError(f"invalid review_state: {path}")
        counts[state] += 1
        indexes = row.get("indexes")
        if not isinstance(indexes, list) or not all(
            local_document(root, index) for index in indexes
        ):
            raise CoverageError(f"invalid or missing index document: {path}")
        if state in {"partial", "indexed"} and not indexes:
            raise CoverageError(f"reviewed source needs an index: {path}")
        reason = row.get("reason")
        if not isinstance(reason, str) or not reason.strip():
            raise CoverageError(f"source needs an explicit review/exclusion reason: {path}")
    missing = sorted(files.keys() - seen)
    if missing:
        raise CoverageError("omitted pinned sources: " + ", ".join(missing))
    return counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=Path(DEFAULT_MANIFEST))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    try:
        data = json.loads(args.manifest.read_text())
        if not isinstance(data, dict):
            raise CoverageError("manifest must be an object")
        counts = validate(root, data)
    except (CoverageError, OSError, UnicodeError, json.JSONDecodeError) as exc:
        print(f"Written-source roster: {exc}", file=sys.stderr)
        return 1
    print(f"Verified {sum(counts.values())} pinned Markdown sources: {counts}.")
    print("Source accounting only; not claim completeness or Lean proof verification.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

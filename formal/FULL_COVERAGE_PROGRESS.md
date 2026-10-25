# Full written-proof coverage: current scope and progress

**Work in progress; full Lean coverage is not complete.** This is the continuing
PR after [#190](https://github.com/q5m-ai/causal-sets/pull/190), not a declaration
that another small proof batch satisfies the full task. The acceptance criteria
remain [FULL_COVERAGE_PLAN.md](FULL_COVERAGE_PLAN.md).

## Explicit source-scope refresh

The current mathematical-source target is research integration
**I = `113f83d099449221fdacf20a404d57f5939e896d`**, fetched from
`issue-81-general-coverage`. It includes the earlier source
**S = `9e0068f91c219fe61984d20fdb3f6939eab907c4`**, the public review package
**R = `1ad9c9ae1d32b7405062371dbb018db7f30f7bc1`**, and the later integrated
research in #180, #184 and #187. R remains an older presentation pinned to S;
it is not silently repinned or upgraded to cover I.

The original [coverage map](PROOF_COVERAGE.md),
[mixed claim index](MIXED_NULL_CLAIMS.md), and
[supporting-spine index](WRITTEN_SUPPORTING_SPINES.md) retain their stated
historical pins. Their descriptions of an unmerged research PR are statements
about those snapshots, not the current GitHub state.

The implementation base is **`bdb92ec2657ce783abdc7c69a07caf13c10e49c2`**,
#190's merge into `lean-coverage-audit`. #189 is still the upstream PR into the
research integration. This follow-up does not silently merge #189, retarget
its work to old `main`, or copy later research into the implementation branch
and present it as new authorship. The newer mathematical sources are read from
immutable Git blobs at I, even where their files are absent from this branch.

## Source completeness before statement completeness

[`written-coverage-sources.json`](written-coverage-sources.json) accounts for
**every one of the 132 Markdown blobs at I**, including unlabelled documents,
older formal guides, summaries and historical research. Each entry retains its
Git blob, content fingerprint, syntactic TeX tags, review state and explicit
review or exclusion reason. Numbered displays are locators, not theorem counts.
Unnumbered hypotheses, estimates, conditional implications, negative claims,
normalizations and specializations still require source review.

The source-roster check verifies only that no pinned document was omitted,
duplicated or changed, and that referenced local index documents exist:

```sh
python3 check_written_coverage.py
python3 -m unittest -v test_check_written_coverage
```

It does **not** verify mathematical statements, declaration types, proof terms,
coverage percentages or the truth of a review classification. In particular,
`indexed` would mean an explicit claim index exists, not that its claims are
proved. Most sources remain `pending`. An exclusion needs a stated reason;
“there are no equation labels” is not an exclusion criterion. Existing code
and an earlier full audit cannot automatically mark a source as covered.

For each mathematical source, the next manual pass must split numbered and
unnumbered assertions into stable claim IDs, with:

- exact source location, hypotheses, quantifiers and conclusion;
- status: established written assertion, conditional implication, definition,
  imported conventional input, diagnostic/model certificate, superseded
  argument, or unresolved mathematics;
- exact Lean declaration and independently inspected statement, or the first
  missing producer and its dependencies;
- explicit stronger-to-weaker specializations and reasons for deduplication;
- separate statement-review and full proof-audit evidence.

A conditional claim must retain its premises in Lean. A desired geometric jet,
limit or target cannot become an admissibility field. A failed universal claim
is not repaired by choosing an easier subclass.

## Later research that the old snapshot did not cover

The later research handoffs provide navigation, not automatic acceptance of
all their assertions. The following additional families must be reconciled
source by source, including corrections to earlier attempts.

| Sources at I | Retained scope and remaining distinction |
| --- | --- |
| [Curved-3D phase freeze](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/curved-three-d-phase-freeze.md), with C3/F3/M3/CL3/UP3/CR3 predecessors | Scoped successes, actual-union reductions, ramp identities, critical estimates and negative controls are separate port obligations. PF3.3 is an exact reduction with a conditional consumer; PF3.2 remains unproved. The original arbitrary-smooth curved-3D theorem is not merely a missing Lean encoding. |
| [Null research handoff](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-research-handoff.md), and its linked proof spine/source audit | NF/TC/NX/NG/FL/DL, flat/conformal common-tip SE/CS, and their supporting estimates retain their actual metric, dimension, boundary and contact restrictions. A research-package merge does not certify a general null theorem. |
| [Intrinsic union continuation](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/intrinsic-union-continuation.md) and [null suspension matching](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-suspension-matching.md) | Spherical focal and flat all-null quotient obstructions are distinct. Complete growth, finite charges, physical-union matching and all complementary sectors require their own correspondences; a model sign is not a full-action proof. |
| [Geometric critical trace](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/geometric-critical-trace.md), [complementary trace](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-complementary-trace.md), and [independent null investigation](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/independent-null-investigation.md) | Clock/coarea, density-jet stability, conditional suspension pairing and critical Abel replacement are reusable but scoped reductions. They do not supply the missing general contact-extraction theorem. |
| [General theorem attempt](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-general-theorem-attempt.md) | Preserve the unfilled construction and failed approaches as unresolved research, not a universal theorem or a proof of impossibility. Separate any valid subsidiary identities from the failed conclusion. |

This table is a source-scope correction and reading queue, **not an exhaustive
claim index**. It supplements, rather than erases, the earlier CO/FLAT/SW/C2,
S1–S31, N/RC/F/SC/SA, higher-dimensional, quotient and mixed obligations.

## Current proof work

Two independent missing-producer batches are under implementation:

1. MA9's actual global coarea weight: definition, exact disintegration,
   endpoint, support, bounds and right limit. The previously proved spatial
   Gaussian limit did not establish these separate formulas.
2. MA13/MA14's explicit original-law moments and layer identities, including
   support/simplicity and the actual restricted interval rate. Existing generic
   probability foundations must be specialized with the original normalization.

These are dependency steps, not a replacement definition of full coverage.
Their results will be recorded only after targeted checking and integration;
a new full local all-source audit is required after the final Lean change.
The existing #190 receipt certifies its unchanged inputs only. No new proof
verification, issue closure, deployment or independent human acceptance is
claimed by this initial scope update.

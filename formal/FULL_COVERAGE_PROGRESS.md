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

GitHub's `math-authoring` job fetches the exact source commit (also on a shallow
PR checkout), then runs the roster check and its adversarial tests. It does
**not** verify mathematical statements, declaration types, proof terms,
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

The [later-integration family reconciliation](LATER_INTEGRATION_CLAIMS.md)
now individually accounts for all 26 added notes, their source-qualified display
ranges, valid scoped/conditional results, negative controls and unresolved
outputs. Its two planning reviews agreed on weighted MA/NM closure as the next
concrete analytic priority; neither claimed exhaustive statement coverage or
independent mathematical acceptance.

These tables are a source-scope correction and reading queue, **not an
exhaustive claim index**. They supplement, rather than erase, the earlier
CO/FLAT/SW/C2, S1–S31, N/RC/F/SC/SA, higher-dimensional, quotient and mixed
obligations.

## Current proof work

The following modules now pass targeted warnings-as-errors compilation and the
parent's integrated incremental checker against #190's merge base. All proof
workers have frozen their files. The final all-source gate is still pending;
the incremental run took **3:59.68** and is not that full audit.

| Written obligation | Actual new producer and precise boundary |
| --- | --- |
| MA9/MA10, NM4 | `MixedNullCoarea*`: the actual global weight, exact angular/radial disintegration, finite-density identity, literal rescaling, endpoint, support, bounds and right continuity. Signed measurable NM4 transport retains time dependence and all partners. `MixedNullErrorExtension` constructs a bounded auxiliary extension and proves it changes neither the actual coarea density nor either action term; only local closed-fibre bounds are needed. |
| MA13–MA15 | `MixedNullProbability*`: original-law support/simplicity, real first/second factorial moments, actual endpoint-excluded interval rate, expanded per-layer expectations and exact normalization. Original-coordinate null intervals/pairs are separately proved null; closed order remains in the discrete action. A separate normalized conditional-iid presentation is not identified here. |
| S13 scalar step | `ShortRemainderAdapter`: even/odd quantitative power/logarithmic bounds imply little-o at the **real** half-dimension and normalized signed cancellation, with nonzero dimension 2–6 controls. This does not produce S9–S12's geometric estimates. |
| MA/NM face support | `MixedNullFaces`: actual smooth lower-face differential, singular upper tip, future timelike/null normals, positive pairing/nonparallelism, nonzero joint-level differential, closed radial support and quantitative growth. A complete manifold-with-boundary atlas is separate. |
| NM5–NM7 | `MixedNullErrorGeometry`, `MixedNullErrorIntegrals`, `MixedNullWeightedError`, `MixedNullErrorRegularity`, `MixedNullWeightedGaussian` and `MixedNullErrorExtension`: the actual moving shell, logarithmic Jacobian and time errors, with literal constants and endpoints; the calculated error's monotonicity/right limit; Gaussian mass four and its actual normalized tail; local-bound weighted scalar errors and limits. No connected radial-slice premise or global bound on the original weight is introduced. |
| MA11/NM8 smooth scope | `MixedNullGenerator`, `MixedNullGeneratorTransport` and `MixedNullGeneratorLocal`: bounded-tip control, actual total generator derivative, independent endpoint integration by parts, generator-constant angular weights, affine/nonaffine C1 coordinate transport with all terms and artificial endpoints, and the original-action generator formula for **every C1 spacetime weight**, with compactness supplying local bounds. General absolutely-continuous traces remain separate debt. |
| NM9 | `MixedNullTip` and `MixedNullTipLocal`: density-uniform source-cylinder bound with local original-weight bounds, genuine ambient tip neighborhood, and nonzero fixed positive cylinder response, after complete signed partner cancellation. |
| NM10 | `MixedNullCollar`: actual sharp radial collar, fixed-width limit, quantitative response bound, subsequent shrinking-width limit, and the strictly positive complementary full-partner response. This formally refutes discarding that source complement, not the full-region convergence theorem. |
| NM11 | `MixedNullPartnerLedger`: integrability of bounded measurable pair cutoffs, exact short/complement restoration with the point term once, actual remainder identity and quantitative bound, and finite source partitions. No separate long-term vanishing is assumed or concluded. |
| NM sine example | `MixedNullSineGeometry`: nonzero second derivative at a genuine interior lower-face spatial point and two unequal joint radii. Global nonaffinity alone did not supply these witnesses. Spacetime remains flat. |

Parent statement review compared these declarations with the actual source
formulas and inspected their producer proofs. The MA, NM and general-metric
short-remainder source blobs are unchanged between the implementation branch
and I. Independently expanded regressions include sharp radial/angular weights,
actual unbounded coordinate time with a nonzero signed limit, endpoint cases,
negative exterior heights, slices with axis holes, supported null chains,
nonlinear reparameterizations, and the nonaffine sine floor.

Remaining mixed obligations include the **general absolutely-continuous-trace
FTC**, a complete smooth-face atlas, further partition/derivative identities,
and NM12's full finite-sigma primitive and remaining calibration/normalization
correspondences. A C1 theorem is not relabelled as the broader AC statement.
The full supporting-claim inventory still needs reconciliation beyond these
identified producers; source-roster and theorem counts are not coverage
percentages. The broader family queue and genuine research blockers above
remain unchanged.

These are dependency steps, not a replacement definition of full coverage.
A new full local all-source audit is required after the final Lean change.
The existing #190 receipt certifies its unchanged inputs only. No complete
coverage, issue closure, deployment or independent human acceptance is claimed.

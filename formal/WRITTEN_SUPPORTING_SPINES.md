# Additional written families and supporting proof obligations

This supplements [the family inventory](PROOF_COVERAGE.md) and
[complete-coverage acceptance contract](FULL_COVERAGE_PLAN.md). It is a bounded
source review, **not an exhaustive statement index or new proof**. Mathematical
sources are pinned to **S = `9e0068f91c219fe61984d20fdb3f6939eab907c4`**; the
review presentation is **R = `1ad9c9ae1d32b7405062371dbb018db7f30f7bc1`**.
The linked source notes are unchanged from S. The later
[current scope update](FULL_COVERAGE_PROGRESS.md) additionally includes the
research integrated after S; this bounded S-era review does not cover it.

A stronger port may discharge a narrower final result by an explicit proved
specialization. It does not silently discharge all intermediate estimates,
weighted statements, conditional criteria or negative results in that note.
Labels are source identifiers, not a count of theorems: some label definitions
or diagnostics. Unnumbered mathematical assertions also need accounting.

## Positive curved families requiring explicit rows

| Family and sources | Scope that must not disappear | Current Lean boundary |
| --- | --- | --- |
| [RC1–RC17](../notes/curved4-corrected-convergence.md) | Every fixed smooth positive time-and-circle-dependent conformal factor on the specified width-four sphere/circle slab; actual weighted lens, all complements, independent curvature target and separate expectation. RC12 is a conditional sufficient lens-scaling/power criterion, not a theorem about every caustic. | The measured-order expectation is not its focusing asymptotic theorem. SW may eventually specialize to RC's final limit, but RC12 and concrete examples need their own correspondence. |
| [N1–N29](../notes/nonpolynomial-short-limit.md) | The original smooth two-face subclass in the stated time slab with the fixed nonpolynomial conformal factor; actual nonpolynomial phase, full/face/corner estimates, weighted C5 endpoint-field assembly, and deterministic/expected unit-field limits. | This is distinct from the fixed polynomial-density curved pilot. `ConformalAction` gives finite-density equality, not the new phase, curvature or limit; flat `TwoFaceLimit` does not supply them. |
| [F1–F20](../notes/sphere-circle-focusing.md), [SC1–SC15](../notes/sphere-circle-complements.md), [SA1–SA13](../notes/sphere-circle-assembly.md) | Fixed unweighted sphere/circle focusing example: aggregate cut primitive, secondary transition, origin logarithms, complete short/off-cut remainder, final normalization and original-law expectation. | RC or SW may eventually imply the final unit-factor result. Their headline conclusions alone do not check every F/SC/SA producer. `SphereCircle` currently supplies measured geometry/order/expectation, not these asymptotics. |

## Supporting spines under the existing headlines

| Source | Required accounting | Why the nearest checked result is insufficient |
| --- | --- | --- |
| [General-metric short G1–G16](../notes/general-metric-short.md) | Whole-interval temporal locality, actual endpoint/volume corrections, dimension-dependent responses, finite-atlas full/face/corner restoration, intrinsic angle/area and fluxes, differing-cutoff overlap. | S1–S31 is a related later spine, not an exhaustive index of this source. Flat overlap/coarea theorems are not the global manifold/curvature producers. |
| [Physical long response CP3–CP10, including CP6a](../notes/curved4-physical-response.md) | Actual clock-fibre interval and clipped long primitive, uniform sublevel bound, signed dilation-increment identity/criterion, conditional logarithmic response. | Scalar cancellation does not construct a globally hyperbolic manifold clock inverse or physical pushforward. CP7–CP9 must retain their analytic hypotheses; CP11–CP12 are scalar diagnostics, not admitted spacetime counterexamples. |
| [Curved bulk C21–C23](../notes/curved-bulk-pilot.md), [remainder R10–R16](../notes/curved-remainders.md) | Negative statements about uniform frozen-phase/absolute-long bounds and integrable dominators before averaging, on the actual fixed admitted curved pilot. | The corrected averaged theorem in [A3–A15](../notes/curved-contact-long.md) does not erase these separate negative results. They do not assert divergence of the full long integral. |
| [Focal research CR1–CR19](../notes/curved4-focal-research.md), [globalization CG1–CG9](../notes/curved4-focal-globalization.md), then [CO1–CO16](../notes/curved4-complete-action-obstruction.md) | Physical null-index-form coefficients, endpoint weights, quartic contacts, all minimizing contacts and closing/source families, then complete model-to-action matching. | The model sign certificate and measured-order bridge do not identify the physical coefficient, complements or negative complete-action growth. Certificate CC1–CC13 in [the separate certificate note](../notes/curved4-focal-certificate.md) remains model arithmetic. |
| [Regulated wedge W1–W9](../notes/regulated-tangent-wedge.md) | Separate the checked scalar fixed-regulator statements from the written invariant-frame/induced-area assembly, compact-angle uniformity and cross-region subtraction extensions. | `weighted_wedgeRegulator_limit`, `wedgeProfileMean_error` and `weightedContinuumMean_complement` are real checked ingredients, not automatic coverage of every conventional extension in W9. Compare each claim with `TangentWedge`, `WeightedGraphAction` and `JointTransport`. |
| [Lens LA5–LA8](../notes/two-tip-lens-limit.md) | General quadrant pushforward/logarithmic-moment lemma with retained axis and outer terms, before TT-A/TT-B assembly. | Neither the null-plane cap nor the new one-tip Gaussian limit proves this lens lemma or the union's mixed-corner response. |
| [Finite-lift FL1–FL18](../notes/finite-lift-flat-reduction.md) | Actual physical-union overlap shells, the sum-volume primitive rather than a sum of kernels, and all stated flat G-SS quantifiers. | Restricted graph results and thin 4D quotient geometry do not prove arbitrary lifted unions counted once. This is a supporting spine of FLAT, not a new universal high-dimensional positive claim. |
| [Full-partner globalization G2–G9](../notes/full-partner-globalization.md) | Finite-density manifold/atlas foundations, cutoff compatibility, all-dimensional signed endpoint-weighted thin-torus long theorem, actual density and closing-fibre Jacobian. | `thinFlatTorusLimit4` is the unit-field thin slab in four dimensions, not every weighted or dimensional assertion here. The general universal long producer is not supplied. |

## Historical and unresolved material

- Preserve earlier failed proof routes and later corrections as history. Older
  “remaining short estimate” or “remaining global match” statements resolved
  later at S must not be reopened as current mathematical gaps merely because
  they remain in a historical note. The later written proofs still need Lean
  ports at their actual scopes.
- Keep current negative theorems, model-only sign certificates, scalar toy
  controls and conjectures separate. They are not interchangeable obstructions.
- R describes the curved-3D PR #180 work as unmerged; it is not part of S's fixed
  accepted mathematical input. The unresolved curved-3D classification is not
  silently promoted to a written theorem or a solved formalization task.
- No issue closure or independent human acceptance follows from this inventory.

For the completed mixed milestone, the more detailed
[MA/NM claim-level crosswalk](MIXED_NULL_CLAIMS.md) records numbered and associated
unnumbered statements individually. Comparable source-by-source indexes remain
part of the completion gate for the other families.

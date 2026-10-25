# Smooth flat one-tip mixed limit

**Scope:** the entire smooth globally strict-Euclidean-Lipschitz floor class of
[MA1–MA3](../notes/null-mixed-assembly.md), in flat 4D spacetime. The actual
continuum action and its separately defined original-law expectation converge
to the induced Lorentzian joint area. This completes the core unweighted limit,
**not** every supporting statement of MA1–MA15/NM1–NM12 or the full written
research programme. See [the complete-coverage queue](FULL_COVERAGE_PLAN.md).

**Validation:** the full local gate passed on frozen proof commit
`17618065b5286d07f7eb41a6eb586cd52d8e35a0`: **361 Lean sources, 3,607 public
library theorems and all public definitions**, in **45:48.72** with two workers.
All 365 formal inputs, nine dependency pins and the toolchain matched before
and after the run. See the [input-pinned receipt](receipts/mixed-null-limit-validation.json),
[full log](receipts/mixed-null-limit-full-audit.log.gz),
[input inventory](receipts/mixed-null-limit-inputs.json.gz), and
[resource measurement](receipts/mixed-null-limit-full-audit.time.txt).
The warm build excludes dependency setup; peak RSS is for one process, not the
concurrent total. The incremental gate passed in 1:37.80; 39 Markdown/checker
tests and 23 relevant mixed/Poisson diagnostics also passed.

## Exact contracts

`MixedNullContract.lean` defines `AdmissibleMixedNull H` by extending
`MixedNullData H` with smoothness of the floor in Euclidean coordinates.
The inputs are positive height at zero, a global Lipschitz constant strictly
below one, and smoothness. Global positivity of the floor is **not** required.
There is no root, area formula, overlap jet, asymptotic coefficient, action
identity or desired limit among the fields.

The region is unchanged: strictly above the floor and strictly below the
future cone ending at zero. The original closed causal relation and all causal
partners are retained. `mixedNullJoint` is the actual intersection of the floor
and cone, independently of the action.

The final theorems in [MixedNullLimit.lean](BoundaryDraft/MixedNullLimit.lean) are:

```lean
AdmissibleMixedNull.continuumMean_limit
    {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) :
    Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      atTop (𝓝 ((mixedNullJointMeasure H).real Set.univ))

AdmissibleMixedNull.expectedBDGAction_limit
    {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) :
    Tendsto (fun ρ : ℝ => expectedBDGAction ρ (mixedNullRegion H))
      atTop (𝓝 ((mixedNullJointMeasure H).real Set.univ))
```

The second observable remains the integral of `discreteBDGAction` against
`FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))`.
It is not defined by the continuum expression. The finite-density expectation
identity supplies the transfer only after the deterministic limit is proved.
There is no sample-wise limit or interchange of expectation with such a limit.

## Actual geometry and independent area

| Producer | What is derived |
| --- | --- |
| [MixedNullElementary](BoundaryDraft/MixedNullElementary.lean) | Quantitative MA5 with the original Lipschitz constant; an explicit interior point; positive finite four-volume; integrability of the original discrete action |
| [MixedNullFrontier](BoundaryDraft/MixedNullFrontier.lean) | Exact spatial and spacetime closures; the entire frontier equals the two bounding graphs; their intersection is the actual joint; compact faces and zero four-volume by coordinate transport/Tonelli |
| [MixedNullRadial](BoundaryDraft/MixedNullRadial.lean) | Unique positive radial root of the actual floor equation; equality with the fixed supremum definition; exact radial support; positive uniform bounds and Lipschitz continuity; global joint homeomorphism with radial inverse; finite positive sphere-area integral |
| [MixedNullGeometrySmooth](BoundaryDraft/MixedNullGeometrySmooth.lean) | Positive actual radial derivative; a smooth local ambient root extension from the inverse function theorem; its derivative obtained from the actual implicit equation |
| [MixedNullSurface](BoundaryDraft/MixedNullSurface.lean) | Differential of the actual spacetime parameterization; existence of two-dimensional unit tangent frames; cancellation of radial derivative products in the negative Lorentz metric; positive Gram Jacobian equal to radius squared; finite positive joint measure supported on the actual joint |
| [MixedNullGeometryPolar](BoundaryDraft/MixedNullGeometryPolar.lean) | Haar-to-sphere disintegration and evaluation of the actual spatial limiting integral as the sphere-area integral |

The measure is the full sphere's polar area with the **proved Lorentzian**
Jacobian, pushed forward by a global one-to-one parameterization. This is
parametric induced area, with the same standard of metric justification used
in `EllipsoidSurface.lean`. The measure was not defined from the action.
Ambient Euclidean spacetime area would have a different Jacobian and is not
substituted here. A canonical Hausdorff-measure identification is neither
needed for this stated parametric target nor proved by this batch.

The weaker `MixedNullData` suffices for roots, topology, measure identities and
the analytic limit to the sphere integral. Smoothness is explicitly restored
for the interpretation by a smooth positive induced joint metric. A nonplanar
sine floor is still a region in **flat spacetime**, not a curved-metric theorem.

## Actual analytic producer

The existing `MixedNullReduction` first performs the exact **signed**
all-partner cancellation. Only the resulting positive spacetime Gaussian is
used for domination; there is no domination claim about the density-normalized
absolute bilocal BDG kernel.

1. [MixedNullIntegration](BoundaryDraft/MixedNullIntegration.lean) proves
   vertical Fubini in the original spacetime measure, transports spatial
   coordinates to genuine Euclidean three-space, and obtains the actual
   finite-density time-fibre integral.
2. [MixedNullGaussian](BoundaryDraft/MixedNullGaussian.lean) substitutes
   proper-time square in each nonzero-radius fibre. The measurable cutoff
   weight, its right behavior at zero, exact normalization and fibre bound
   are proved. [NullGaussianRight](BoundaryDraft/NullGaussianRight.lean)
   supplies concentration with cutoff jumps away from zero allowed.
3. [MixedNullConcentration](BoundaryDraft/MixedNullConcentration.lean) derives
   a bounded spatial support from the original Lipschitz data. The reciprocal-
   radius dominator is proved integrable in three dimensions using the polar
   product measure. The origin is removed only as a null point **after** that
   integrability proof. Spatial dominated convergence yields
   `MixedNullData.continuumMean_tendsto_spatialLimit`.
4. `MixedNullData.spatialLimit_eq_area` and
   `MixedNullData.jointMeasure_real_univ` identify that intermediate with the
   independently justified induced-area target. `MixedNullLimit` assembles
   the deterministic result and then the original-law expectation result.

This is an alternative complete route to the same unweighted limit. It does
not require monotonicity of the floor's proper-time-square profile, connected
positive-phase radial slices, or an assumed coarea weight.

## Weighted support and honest remaining debt

[MixedNullWeighted](BoundaryDraft/MixedNullWeighted.lean) also proves absolute
bilocal integrability, exact weighted signed cancellation and the finite
source-partition identity for **signed bounded measurable** weights. Partners
remain in the whole original region, including cross-chart pairs. No claim
that a source complement vanishes is introduced.

The [source-pinned MA/NM claim crosswalk](MIXED_NULL_CLAIMS.md) separates every
numbered display and its associated geometric, probability and calibration
claims. In particular, the following remain open in that accounting:

- MA9's particular global sphere/radius weight representation, endpoint value
  and uniform bounds as explicitly stated in the note. The fibre-based limit
  above does not silently mark every alternative intermediate formula checked.
- MA11/NM's generator-derivative weighted asymptotics and quantitative errors,
  MA12/NM's density-uniform shrinking-tip bound, and associated cutoff/collar
  response statements. Zero four-volume of the frontier is not that estimate.
- Remaining ancillary smooth-face/normal-transversality statements and complete
  explicit correspondence for MA13's moment bounds and MA14's per-layer formula.
  Original-law integrability and the exact action expectation itself are proved.
- ND, TT, CC, CT, the curved short spine, CO/FLAT/SW/C2 and the other established
  families listed in [PROOF_COVERAGE.md](PROOF_COVERAGE.md).

No density rate, variance, sample-wise convergence, general null/mixed
classification, curved metric result, or independent human review is claimed.
Historical notes and issue/PR acceptance records are not rewritten.

## Independent regressions and reproduction

[MixedNullSupportRegression.lean](MixedNullSupportRegression.lean) expands the
smooth-class hypotheses, strict region, weighted point/pair terms and actual
probability integral independently. It checks a genuinely nonaffine sine floor,
an affine floor that becomes negative outside the domain, and the constant
cone-cap calibration (four pi times height squared, not the diamond's target).
It also instantiates the Gaussian helper with a discontinuous cutoff.
`MixedNullGeometryExamples` separately checks radius and area calibrations.

Use the [pinned setup](README.md#reproduce). Development feedback:

```sh
cd formal
LEAN_NUM_THREADS=2 ./check.sh --incremental --base origin/lean-coverage-audit
```

The base must first be fetched and be an ancestor. This changed-source check
is not the release/handoff gate. After freezing all proof inputs:

```sh
cd formal
LEAN_NUM_THREADS=2 ./check.sh
```

Keep the full all-source scope, warnings-as-errors and unchanged transitive
axiom whitelist. The final receipt must pin the inputs to the completed run;
subsequent documentation-only changes do not require repeating the Lean gate.

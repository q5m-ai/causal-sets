# Source-pinned mixed-null claim index: MA1–MA15 and NM1–NM12

## Scope, pins, and verification meaning

This is a claim-level comparison, **not a declaration that either entire note
has complete Lean coverage**.

**Later producer delta:** [MIXED_NULL_SUPPORT_CLAIMS.md](MIXED_NULL_SUPPORT_CLAIMS.md)
records subsequent global-weight, weighted-error, generator, cutoff, face and
probability proofs at a separate Lean pin. The classifications below remain
historical statements about L; they are not the latest implementation status.

- **Written source pin `S`:** `9e0068f91c219fe61984d20fdb3f6939eab907c4`.
  The sources read in full are
  [the MA assembly note at S](https://github.com/q5m-ai/causal-sets/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/null-mixed-assembly.md)
  and
  [the NM estimates note at S](https://github.com/q5m-ai/causal-sets/blob/9e0068f91c219fe61984d20fdb3f6939eab907c4/notes/null-mixed-estimates.md).
- **Lean comparison pin `L`:** `17618065b5286d07f7eb41a6eb586cd52d8e35a0`.
  Declaration names and source paths below refer to this frozen commit, not
  to an inferred future implementation.
- **Validation boundary:** this documentation-only inspection ran no Lean
  build. The subsequent [full local audit receipt](receipts/mixed-null-limit-validation.json)
  certifies the same frozen L inputs: 361 Lean sources, 3,607 public library
  theorems and all public definitions passed in 45:48.72. The index supplies
  source correspondence, not a substitute audit or independent human review.

The index covers every numbered display MA1–MA15 and NM1–NM12, splitting
its definitions, identities, estimates, and limits. It also indexes the
associated mathematical geometry, probability, partition, normal-rescaling,
calibration, and evaluator claims identified below: MA §§1–6 and NM §§1–7.
It is not a sentence-by-sentence index of historical priority, issue-management,
verification-ledger, or command-running prose. It does not recursively index
`first-attempt.md`, `general-contract.md`, the two-tip note, linked issues,
Python test assertions, or other source notes. Claims about the diagnostic
programs are distinguished from quantified Lean theorems in §7 below.

The pinned notes' historical statements that their publication added no Lean
proofs, and their issue/review statuses, remain unchanged. This later crosswalk
must not be read as a retroactive edit of those statements.

### Classification

| Mark | Meaning |
| --- | --- |
| **D** | Definition or hypothesis. A definition alone supplies no geometric, analytic, or probabilistic conclusion. “Source only” means the displayed object has no corresponding definition in the inspected Lean producers. |
| **T** | An actual compiled theorem at L with the stated scope, or an explicitly identified universal baseline theorem already asserting the claim. Exact declaration and source are given. This is not a full-audit receipt. |
| **P** | A narrower partial result. The cited theorem is real, but its conclusion or hypotheses do not establish the whole source claim in that row. The missing part is stated. |
| **B** | An existing baseline theorem supplies the mathematical ingredient, but an explicit specialization, transport, or normalization to the displayed mixed-region statement is still needed. This is not marked as a completed mixed declaration. |
| **G** | A remaining formal proof gap for the specified source claim: no matching producer or ready exact specialization was identified. This does not mean the written claim is false, novel, or necessarily difficult. |

A **P**, **B**, or **G** row is not counted as full coverage. A gap in a chosen
written proof route does not invalidate an independently proved conclusion.
Conversely, an independently proved conclusion does not check every formula
or estimate in that route.

### Source-key convention

All project declaration names below are in namespace `BoundaryDraft`, unless
a regression namespace is explicitly written. Standard Lean/mathlib names
retain their usual namespaces. Thus, for example,
`MixedNullData.radius_spec` denotes
`BoundaryDraft.MixedNullData.radius_spec`. In a comma-separated method list,
unqualified follow-on names inherit the namespace of the qualified first
name; for example, `MixedNullData.radius_spec`, `radius_unique` denotes those
two methods of `MixedNullData`. The following keys identify exact source files
at L; relative links are convenient working-tree links.

| Key | Source |
| --- | --- |
| Contract | [`BoundaryDraft/MixedNullContract.lean`](BoundaryDraft/MixedNullContract.lean) |
| Reduction | [`BoundaryDraft/MixedNullReduction.lean`](BoundaryDraft/MixedNullReduction.lean) |
| Elementary | [`BoundaryDraft/MixedNullElementary.lean`](BoundaryDraft/MixedNullElementary.lean) |
| Frontier | [`BoundaryDraft/MixedNullFrontier.lean`](BoundaryDraft/MixedNullFrontier.lean) |
| Radial | [`BoundaryDraft/MixedNullRadial.lean`](BoundaryDraft/MixedNullRadial.lean) |
| Smooth | [`BoundaryDraft/MixedNullGeometrySmooth.lean`](BoundaryDraft/MixedNullGeometrySmooth.lean) |
| Polar | [`BoundaryDraft/MixedNullGeometryPolar.lean`](BoundaryDraft/MixedNullGeometryPolar.lean) |
| Surface | [`BoundaryDraft/MixedNullSurface.lean`](BoundaryDraft/MixedNullSurface.lean) |
| Integration | [`BoundaryDraft/MixedNullIntegration.lean`](BoundaryDraft/MixedNullIntegration.lean) |
| Gaussian | [`BoundaryDraft/MixedNullGaussian.lean`](BoundaryDraft/MixedNullGaussian.lean) |
| Concentration | [`BoundaryDraft/MixedNullConcentration.lean`](BoundaryDraft/MixedNullConcentration.lean) |
| Weighted | [`BoundaryDraft/MixedNullWeighted.lean`](BoundaryDraft/MixedNullWeighted.lean) |
| Limit | [`BoundaryDraft/MixedNullLimit.lean`](BoundaryDraft/MixedNullLimit.lean) |
| Examples | [`BoundaryDraft/MixedNullGeometryExamples.lean`](BoundaryDraft/MixedNullGeometryExamples.lean) |

## 1. What the completed global theorem actually says

`MixedNullData H` requires positive `H 0` and a global strict Euclidean
Lipschitz bound. `AdmissibleMixedNull H` adds global smoothness in genuine
Euclidean coordinates. Neither contract assumes a root, a differential
identity, a target equality, an overlap jet, an action identity, or a limit.

The central compiled signatures are:

```lean
-- BoundaryDraft.MixedNullLimit
MixedNullData.continuumMean_tendsto_area
    {H : Spatial → ℝ} (hH : MixedNullData H) :
    Filter.Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      Filter.atTop (nhds (mixedNullArea H))

AdmissibleMixedNull.continuumMean_limit
    {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) :
    Filter.Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      Filter.atTop (nhds ((mixedNullJointMeasure H).real Set.univ))

AdmissibleMixedNull.expectedBDGAction_limit
    {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) :
    Filter.Tendsto (fun ρ : ℝ => expectedBDGAction ρ (mixedNullRegion H))
      Filter.atTop (nhds ((mixedNullJointMeasure H).real Set.univ))
```

The actual proof route is:

1. Complete-future signed interval cancellation, then exact vertical Fubini.
2. An actual finite time-fibre substitution and Gaussian concentration at
   every nonzero interior spatial point.
3. A proved integrable spatial dominator, `2 / ‖x‖` on a fixed ball.
4. Spatial dominated convergence to `mixedNullSpatialLimit H`.
5. Polar identification with `mixedNullArea H`, followed by the independent
   smooth parametric induced-metric interpretation.
6. Only then, the separate positive-density Poisson expectation equality.

In particular, `mixedNullFibreWeight r L` is a **single spatial fibre's**
cutoff Jacobian. It is not the sphere-and-radius-integrated `W_H` or `W_phi`
of MA9/NM4. Neither of those displayed global weights is defined in the
current mixed modules.

## 2. MA1–MA8 and their geometric prose

### Definitions and main result

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA1: smooth strict-Lipschitz floor, positive height at the origin | D | `MixedNullData` (Reduction), `AdmissibleMixedNull` (Contract). No positivity of the floor outside the spatial domain is required. |
| MA1: open spacetime region in strict cone coordinates | D | `mixedNullRegion` (Reduction). The equivalence to the written time inequalities is the actual theorem `mem_mixedNullRegion_iff` (Frontier), also `mixedNull_cons_mem_iff` (Integration). |
| MA1: spatial domain and actual joint | D | `mixedNullSpatialDomain`, `mixedNullJoint` (Contract). `mixedNullSpatialDomain_eq_image` (Frontier) separately proves the spatial projection identity. |
| MA1: `m = T/(1+lambda)` and `B = T/(1-lambda)` | D | These are source abbreviations, not stored conclusion fields. Their use as root bounds is proved by `MixedNullData.radius_bounds` (Radial). |
| MA1: independent area target | D | `mixedNullArea`, `mixedNullJointMeasure` (Contract) are initially sphere-integral/transport definitions. Their induced-area justification is MA7 below, not a consequence of naming them “area.” |
| MA2: phase, signed polynomial/kernel and continuum action | D | `intervalSq`, `bdgKernel`, `continuumMean` in [`Specification.lean`](BoundaryDraft/Specification.lean), with `bdgPolynomial` in [`Algebra.lean`](BoundaryDraft/Algebra.lean). These original definitions are unchanged. |
| MA2: finite-order action, distinct ordered pairs, marked-endpoint exclusion and null relations | D | `discreteBDGAction`, `intervalLayer`, `causalLayerPairs` in [`DiscreteBDG.lean`](BoundaryDraft/DiscreteBDG.lean); `causalIntervalInterior`, `intervalCount`, `intervalPairSum` in [`SpacetimeSprinkling.lean`](BoundaryDraft/SpacetimeSprinkling.lean). The pair condition is closed causality plus unequal endpoints, not chronological causality. |
| MA2: identification with the genuine simple finite-order observable | T | `intervalLayer_eq_card`, `discreteBDGAction_eq_finite_order` (DiscreteBDG). The convention is not inferred merely from the kernel polynomial. |
| MA2: actual finite-Poisson expectation, not action-defined expectation | D | `expectedBDGAction` in [`ExpectationBridge.lean`](BoundaryDraft/ExpectationBridge.lean) integrates the discrete action against `FinitePoisson.law`. The law and its probability properties are separated in §5 below. |
| MA3: exact expectation equals original continuum action | T | `MixedNullData.expectedBDGAction_eq` (Reduction), for positive density. |
| MA3: continuum action equals the full-region spacetime Gaussian | T | `MixedNullData.continuumMean_eq_spacetimeGaussian` (Reduction). |
| MA3: expectation equals the same spacetime Gaussian | T | `MixedNullData.expectedBDGAction_eq_spacetimeGaussian` (Reduction). |
| MA3: deterministic induced-area limit for the smooth class | T | `AdmissibleMixedNull.continuumMean_limit` (Limit), with the actual parametric induced-area justification in Surface. The weaker `MixedNullData.continuumMean_tendsto_area` does not advertise a smooth surface for a nonsmooth floor. |
| MA3: expected-action induced-area limit | T | `AdmissibleMixedNull.expectedBDGAction_limit` (Limit). This uses the original law and a separate positive-density equality, not a sample-wise limit. |
| MA3 prose: unit coefficient for the unweighted one-cone joint, fixed geometry | T | The target of the preceding limit is exactly the total induced parametric measure, without an extra weight. This does not establish a localized weighted response or a null-face/angle transition. |

### Radial geometry, closure, and strata

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA §2: radial gap is strictly increasing | T | `MixedNullData.radial_gap_strictMono` (Radial), actually on the whole real line. |
| MA §2: existence and uniqueness of a positive radial root | T | `MixedNullData.exists_radial_root`, `radius_spec`, `radius_unique` (Radial). `mixedNullRadius` is the independently defined supremum, and its root property is proved. |
| MA §2: explicit positive lower/upper root bounds | T | `MixedNullData.radius_bounds`, `uniform_radius_bounds` (Radial). The former retains a specified Euclidean Lipschitz constant. |
| MA §2: exact open radial support, including the origin | T | `MixedNullData.radial_support`, `radialSet_eq`, `radial_domain` (Radial). The last has an explicit nonnegative-radius hypothesis. |
| MA §2: smooth regular radial root | T | `AdmissibleMixedNull.radial_gap_hasDerivAt`, `radial_derivative_pos`, `exists_smooth_radius_extension`, `exists_smooth_radius_differential` (Smooth). Smoothness is expressed by actual local ambient smooth extensions agreeing with the sphere function, not an assumed formal tangent. |
| MA §2 proof prose: derivative at least the specifically chosen `1-lambda`, and gap tends to positive infinity | P | Smooth proves the actual derivative and its strict positivity; Radial proves monotonicity and a finite-bracket root by IVT. There is no exported theorem for this exact quantitative derivative bound or the gap's `atTop` limit. They are not needed by the implemented finite-bracket argument. |
| MA §2: radius is continuous/Lipschitz | T | `MixedNullData.radius_lipschitz`, `continuous_radius` (Radial). |
| MA §2: region is open/Borel and bounded | T | `MixedNullData.isOpen_region`, `isBounded_region`, `boundedCausalRegion` (Reduction). The last explicitly packages measurable-set and closed-interval-containment inputs. |
| MA §2: interior point `(-T/2,0)`, nonemptiness, positive finite volume | T | `MixedNullData.timeAxis_in_region`, `region_nonempty`, `region_volume_pos`, `region_volume_lt_top`, `region_volumeReal_pos` (Elementary). |
| MA §2 prose: the explicit `r < B` and `-B < t < 0` bounds throughout the region | P | They are established as local facts in the proof of `MixedNullData.isBounded_region` (Reduction). Its public conclusion is boundedness, not a theorem returning all these bounds for a supplied `lambda`. `MixedNullData.spatialDomain_ball` (Concentration) also returns a positive bounding ball existentially. |
| MA4: full spacetime closure | T | `MixedNullData.closure_region` (Frontier) proves equality with `mixedNullClosedRegion`, whose two closed time inequalities already imply the required closed spatial inequality. |
| MA4: exact spatial closure | T | `MixedNullData.closure_spatialDomain` (Frontier) identifies it with the non-strict spatial inequality. |
| MA §2 prose: closed radial support is precisely `0 <= r <= R` | P | The exact spatial closure, open radial support and unique root are proved separately. There is no dedicated closed-radial-support equivalence in the current API; it needs their explicit combination. |
| MA4: definitions of the two bounding faces | D | `mixedNullLowerFace`, `mixedNullUpperFace` (Frontier), using the closed spatial inequality. Their correspondence with the source's closed-domain graph descriptions uses `closure_spatialDomain`. |
| MA4: complete frontier, no additional lateral frontier set | T | `MixedNullData.frontier_region` (Frontier) is an equality with the union of those two actual faces. |
| MA4: intersection of the two faces is exactly the actual joint | T | `mixedNull_faces_inter` (Frontier), with no admissibility premise. |
| MA §2: reverse closure approximation, including axis, tip and joint | T | The proof of `MixedNullData.closure_region` constructs actual inward perturbations. Its proof does not assume the conclusion or rely on a root field. The path construction differs from the note's particular radial-then-midpoint presentation. |
| MA §2: both faces compact | T | `MixedNullData.compact_faces` (Frontier). |
| MA §2: graph boundaries and frontier have zero four-volume | T | `volume_timeGraph_zero`, `MixedNullData.lowerFace_volume_zero`, `upperFace_volume_zero`, `frontier_volume_zero` (Frontier). This is original four-volume, not an induced area convention. |
| MA §2 prose: four named disjoint strata; one singular future tip; lower axis point is smooth; no same-side creases or additional corners | P | Exact closure/frontier/intersection are proved. Smoothness of the floor is an input, and the joint is separately smooth and spacelike. There is no packaged disjoint-stratification theorem or formal face-with-boundary/singular-tip classification establishing all this descriptive differential geometry. |
| MA §2 prose: lower face smooth with boundary, upper face smooth away from its tip | G | No actual mixed-face derivative/manifold-with-boundary producer is present. The proved smooth **joint** is not a proof of both whole-face claims. |

### Causality, normals, and area

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA5: first two quantitative causal floor-increment inequalities | T | `mixedNull_floor_increment` (Elementary) retains the supplied Lipschitz constant and proves both inequalities, including null displacements. |
| MA5: final product is nonnegative when `lambda < 1` | B | Elementary real arithmetic from the contract and the causal time inequality, via `mul_nonneg`; the exported increment theorem itself returns only the first two inequalities. `MixedNullData.floor_future` (Reduction) already supplies the strict-floor preservation needed downstream. |
| MA5 prose: every closed ambient interval between region endpoints stays in the region | T | `MixedNullData.causallyConvex` (Reduction). `CausallyConvex` in [`ExpectationGeometry.lean`](BoundaryDraft/ExpectationGeometry.lean) is exactly closed-interval containment, not an intrinsic-path substitute. |
| MA5 prose: intrinsic causal paths agree with ambient order via contained causal line segments | G | The mixed API proves interval containment but does not define/prove this intrinsic-path equivalence. It is unnecessary for the existing ambient Poisson bridge. |
| MA6 first line: complete future slice is the full future cone intersected with strict past of the tip | T | `MixedNullData.complete_future` (Reduction), for every source in the region. No partner is restricted by a source weight. |
| MA6: almost-everywhere equality with the closed source-to-tip interval and equality of integrals | T | `future_chronologicalPast_ae_causalInterval`, `integral_future_chronologicalPast_eq_causalInterval` in [`NullBoundary.lean`](BoundaryDraft/NullBoundary.lean), actually used after `complete_future` in `future_kernel_identity`. |
| MA6 second line as a literal symmetric-difference inclusion in the frontier of the past cone | P | NullBoundary proves the required a.e. equality; its proof bounds the discrepancy by the zero-phase cone and proves the other difference empty. It does not export the displayed symmetric-difference/frontier inclusion or identify that frontier as a set. |
| MA6 prose: the exceptional cone has zero four-volume | T | `volume_nullCone_zero` (NullBoundary), independent of any limit. |
| MA7: actual joint parametrization, inverse and embedding with no multiplicity | T | `MixedNullData.jointParam_mem`, `jointParam_surjective`, `jointParam_injective`, `range_jointParam`, `jointParam_radial_inverse`, `jointHomeomorph`, `jointHomeomorph_apply` (Radial). |
| MA7: joint compact and away from the spatial origin | T | `MixedNullData.isCompact_joint`, `joint_spatial_ne_zero` (Radial). |
| MA7: actual differential cancels both radial-derivative products | T | `hasFDerivAt_mixedNullParamExtension`, `mixedNullParamDifferential_metric`, and the unconditional geometric producer `AdmissibleMixedNull.jointParam_smooth_metric` (Surface). The last supplies a smooth local extension of the actual parameter map and computes its `fderiv`. |
| MA7: positive definite induced joint metric and radius-squared area Jacobian | T | `mixedNullDirection_tangent_frame`, `AdmissibleMixedNull.jointParam_induced_area` (Surface). Actual orthonormal tangent frames exist; the density is the positive square root of the actual negative-Lorentz Gram determinant. |
| MA7: area is the sphere integral, finite and strictly positive, with the displayed two bounds | T | `MixedNullData.integrable_radius_sq`, `area_bounds`, `area_pos` (Radial), using `radius_bounds` for the source's `m,B`; `jointMeasure_univ`, `finite_jointMeasure`, `jointMeasure_pos`, `jointMeasure_real_univ`, `jointMeasure_supported`, `integral_jointMeasure` (Surface). This is **parametric induced area**, not ambient Euclidean spacetime area. |
| MA7 prose: spatial level-set regularity expressed as nonzero full differential of `H(x)-norm(x)` | P | The actual radial derivative is nonzero and smooth radial parametrizations are proved (Smooth). No theorem explicitly states the full level-set differential or a regular-level manifold structure for that exact function. The parametric MA7 interpretation does not require such a separate statement. |
| MA7 prose: lower face's induced metric is positive; upper face is null; explicit timelike/null future normals have positive pairing and are transverse | G | These **face** metric/normal statements have no mixed producer at L. Joint positivity alone does not certify the displayed face normals or their normalization. See NM §4 below. |
| MA7 prose: rescaling the marked null normal leaves area and observable unchanged | P | Neither the shared measure nor the action definition depends on a chosen null normal, and the actual joint metric is proved independently. A marked-normal/reparameterization invariance theorem, with transported generator terms, is not supplied. |
| MA8: complete signed future kernel identity at every source | T | `MixedNullData.future_kernel_identity` (Reduction), using `causalInterval_kernel_identity` in [`TimelikeInterval.lean`](BoundaryDraft/TimelikeInterval.lean). Positivity of density and actual chronological source-to-tip separation are discharged. |
| MA §3: bilocal absolute integrability before cancellation, including bounded measurable signed source weights | T | `MixedNullData.integrable_weighted_bilocal`, `integrable_weighted_continuous` (Weighted); the unweighted baseline is `integrableOn_bilocal_bdg` (ExpectationBridge). No absolute-kernel asymptotic replacement follows. |
| MA §3 / NM §2 warning that replacing the signed kernel by its absolute value does not preserve the cancellation | P | The actual interval and mixed identities use `bdgKernel` with its signs, not its absolute value. These modules do not separately exhibit an absolute-kernel counterexample or a theorem contrasting the two normalized limits. |

The parametric area result is the intended MA7 target standard. A separate
canonical/Hausdorff identification is not proved here, and is not silently
included in the **T** designation. Likewise, the flat-coordinate model does
not add a curvature-tensor theorem or a theorem about a curved bulk term.

## 3. MA9–MA12: distinguish the global conclusion from the written route

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA9 first line: definition of the positive-sigma global weight `W_H` | D | **Source only.** No global `W_H` definition occurs in the mixed producers. `mixedNullFibreJacobian` and `mixedNullFibreWeight` (Gaussian) are different, spatial-pointwise objects. |
| MA9 second line: assigned endpoint value, one quarter of the sphere area | D | **Source-only `W_H(0)` assignment.** The sphere integral itself is `mixedNullArea` (Contract), with its geometric interpretation proved in Surface. No global weight endpoint is defined or evaluated by these declarations. |
| MA9 coordinate mechanism: actual vertical Fubini and positive-radius square-root Jacobian | T | `mixedNull_vertical_integral`, `mixedNull_vertical_euclidean`, `MixedNullData.continuumMean_eq_spatialGaussian` (Integration); `mixedNull_fibre_substitution`, `mixedNull_fibre_as_positive_gaussian` (Gaussian). The fibre substitution assumes positive radius and an actual upper endpoint larger than it. |
| MA9: entire angular/radial/proper-time-squared disintegration, in exactly the displayed `W_H` order | P | `lintegral_mixedNull_polar` (Polar) is a genuine general nonnegative polar theorem, and the vertical substitution is genuine. They have not been assembled with joint measurability, Tonelli and endpoint handling into the displayed global `W_H` identity. The alternative spatial proof does not establish that identity. |
| MA9 prose: global weight measurable, nonnegative, bounded by `pi*B^2`, zero for `s >= B^2` | G | No global weight producer proves these properties. `mixedNullFibreWeight_measurable` and `mixedNullFibreWeight_bound` (Gaussian) concern a fixed positive spatial radius and the bound `1/(2*r)`, not the asserted integrated weight or its global support. |
| MA9 prose: radial slices lie inside `(0,R)`; pointwise indicator persistence; moving-endpoint nullity | P | `MixedNullData.radial_domain` (Radial) gives the zero-sigma radial domain. The exact positive-sigma radial-slice and product-a.e. statements used in the note's proof are not exported. The implemented proof avoids having to prove connectedness or monotonicity of those slices. |
| MA9 prose: right limit of the displayed global weight by fixed-product dominated convergence | G | No `W_H` right-continuity theorem is present. The proved `MixedNullData.spatialGaussian_limit` (Concentration) is a density limit of spatial integrals, not this assertion. |
| MA10: abstract Gaussian change of density scale | B | `nullGaussian_density_rescaling` in [`NullGaussian.lean`](BoundaryDraft/NullGaussian.lean) supplies an exact universal rescaling. Its normalization uses `u = sqrt(rho)*s` with the fixed constant inside `nullGaussian`; the note's `sqrt(c*rho)` convention needs another constant rescaling. Applying it to `W_H` additionally requires the missing MA9 construction. |
| MA10: the particular `W_H`-integral representation, the `pi*B^2*exp(-u^2)` dominator, and its displayed passage to `4*W_H(0)` | G | This complete displayed proof route is not implemented. Generic Gaussian concentration does not supply the missing weight definition/properties. |
| MA10: final unweighted limit equals the independent induced area | T | `MixedNullData.continuumMean_tendsto_spatialLimit` (Concentration), `MixedNullData.spatialLimit_eq_area` (Polar), `MixedNullData.spatialLimit_eq_jointMeasure` (Surface), and `AdmissibleMixedNull.continuumMean_limit` (Limit) prove the conclusion by the alternative route in §1. |
| MA §4 before MA11: exact finite sum for bounded measurable signed/overlapping source partitions | T | `MixedNullData.weightedContinuumMean_partition` (Weighted), with explicit finite index set, measurability, bounds on the region, and sum equal to one there. It retains all original partners. |
| MA11: limit for each smooth source weight equals its joint trace minus its generator term | G | No weighted asymptotic producer exists at L. `weightedContinuumMean_eq_spacetimeGaussian` is only finite-density cancellation. Neither `integral_jointMeasure` nor the unweighted limit computes this source-weight limit. |
| MA11 prose: generator chain rule, integration by parts, endpoint at the tip, absolute integrability of both displayed terms | G | No mixed weighted-trace/derivative package establishes these assertions. Smoothness of the floor is not a hypothesis on the source weight, and the finite-density weighted API asks only measurability/boundedness. |
| MA11 prose: generator derivatives cancel for a smooth partition; artificial radial endpoints cancel; angular weights can be transported on entire generators | G | The exact finite-density source partition is proved, but the displayed differentiated/asymptotic partition ledger and angular-generator weighted response are not. A finite chart cover with subordinate weights is also not constructed for this mixed proof. |
| MA12: uniform-in-density normalized weighted tip-cylinder bound | G | No theorem states the `4*M*pi*delta^2` bound for the actual weighted action. `mixedNull_fibre_bound` (Gaussian) and `integrable_mixedNullRadialDominator` (Concentration) are useful ingredients, not this weighted spatial-cylinder specialization. |
| MA12 prose: every sufficiently small fixed unit cylinder has limit `4*pi*delta^2` | G | No such cutoff action limit is proved. A null singleton or null frontier cannot establish it. |
| MA12 prose: exact collar and complementary limits, followed by collar limit zero as width decreases | G | These spatially weighted asymptotics and their nonzero complementary response remain unproved; see NM10. |
| MA §4 partner-cutoff prose: exact sum of cutoff and complementary partner contributions, plus its asymptotic remainder | G | There is no mixed two-endpoint-cutoff ledger producer. `weightedContinuumMean_partition` partitions **sources**, not partners. See NM11 for the split between the elementary finite-density ledger and its additional asymptotic estimate. |

The proved density limit uses one fixed geometry and no shrinking cutoff. No
rate, uniform geometry family, angle/null-face interchange, weighted tip
estimate, or sample-wise convergence is a consequence of that proof. The
note's specified orders of auxiliary limits remain constraints on the missing
estimates, not additional checked theorems.

## 4. NM1–NM12: estimates and localized responses

### NM1–NM4

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| NM1: geometry, root equation and explicit root bounds | T | Same objects and actual proofs as MA1/MA §2: Contract, `MixedNullData.radius_spec`, `radius_unique`, `radius_bounds` (Radial). The root equation is not an admissibility field. |
| NM §1: frontier/causality/boundedness/null four-volume assertions | P | Exact set-theoretic frontier, closed-interval containment, compact faces and zero four-volume are proved (Reduction, Elementary, Frontier). The additional whole-face smooth/null/spacelike and singular-stratum descriptions have the limitations listed in §2 above. |
| NM2: signed first-endpoint-weighted observable, all partners retained | D | `weightedContinuumMean` in [`WeightedGraphAction.lean`](BoundaryDraft/WeightedGraphAction.lean). It has the displayed point and full-partner pair terms. |
| NM2: unit source weight recovers the unchanged original action | T | `weightedContinuumMean_one` (WeightedGraphAction), for every density and region. |
| NM2 prose: finite-density integrability for bounded measurable signed weights | T | `MixedNullData.integrable_weighted_continuous`, `integrable_weighted_bilocal` (Weighted). This extends beyond the older continuous-weight helper in WeightedGraphAction. |
| NM3 first line: source-to-tip signed interval identity | T | `causalInterval_kernel_identity` (TimelikeInterval), used in `MixedNullData.future_kernel_identity` (Reduction). |
| NM3 second line: weighted exact Gaussian reduction | T | `MixedNullData.weightedContinuumMean_eq_spacetimeGaussian` (Weighted), for positive density and measurable weights bounded on the region. |
| NM §2 normalization prose: coefficient-factor algebra and moment cancellation | T | `coefficient_factorization`, `interval_moment_cancellation` in [`Algebra.lean`](BoundaryDraft/Algebra.lean). These are algebraic assertions, not a power-series representation theorem. |
| NM §2 normalization prose: actual rest-frame interval moment for every natural index | T | `standard_causalInterval_moment` in [`IntervalMoments.lean`](BoundaryDraft/IntervalMoments.lean), on `causalInterval 0 (timeAxis T)` for positive `T`. |
| NM §2 normalization prose: arbitrary-endpoint moment expressed solely by proper duration | B | The rest-frame moment and Lorentz interval transport exist; an explicit transported moment statement is not supplied by `standard_causalInterval_moment`. The exact kernel identity itself is already transported and proved. |
| NM §2 normalization prose: full Taylor-coefficient formula for the signed kernel and uniform-absolute-convergence termwise integration on the interval | P | Algebra proves the coefficient factor and cancellation, and IntervalMoments proves the integral of each moment. No theorem in this chain identifies the entire kernel series and justifies this specific interchange. The baseline kernel proof uses finite primitives instead. |
| NM4: `D_sigma`, global `W_phi(sigma)`, and its assigned zero value | D | **Source only.** No mixed global weighted coarea-density definition is present. |
| NM4: weighted polar/time-squared change of variables with the displayed global weight | G | The actual weighted spacetime Gaussian identity is proved, but the weighted multi-coordinate transport and Fubini/Tonelli conclusion in this exact form are not. The unweighted phase-only `mixedNull_vertical_euclidean` cannot simply accept an arbitrary spacetime weight. |
| NM4 prose: `D_sigma` inclusion, absolute global bound `M*pi*B^2`, compact sigma support | G | These integrated weighted-density properties are not the fixed-radius fibre bounds in Gaussian. |
| NM4 prose: positive-sigma slices need not start at zero; annular slices are allowed | P | The implemented global limit makes no connected-slice or monotonicity assumption. It does not prove the claimed existence of annular slices for the sine example or a classification of such slices. |

### NM5–NM10

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| NM5: explicit weighted near-cone bound `E(sigma)` with its logarithmic, endpoint and time-Lipschitz terms | G | No producer states or proves this error estimate, even though the unweighted global limit is complete. |
| NM5 Step 1: small radii remain in the positive-sigma slice, including endpoint strictness | G | No theorem establishes this simultaneous radial/proper-time bound for the actual slices. |
| NM5 Step 2: removed radii lie in the specified endpoint shell and yield the stated integrated cost | G | Strict radial monotonicity/root bounds are available (Radial), but not this quantitative shell estimate or its weighted integration. |
| NM5 Step 3: Jacobian-difference minimum bound and logarithmic integral after splitting at `sqrt(sigma)` | G | `mixedNullFibreWeight_bound` gives a one-sided fibre majorant only; it is not the difference estimate or the evaluated logarithmic remainder. |
| NM5 Step 4: time variation of the source weight contributes at most the stated linear-in-sigma cost | G | No time-Lipschitz source-weight estimate is present. |
| NM6: physical half-Gaussian mass is four | B | Exact generic ingredients `nullGaussian_density_rescaling` and `integral_nullGaussian` (NullGaussian) prove this on specializing the weight to the constant one and simplifying. There is no separately named NM6 mixed theorem. The implemented fibre proof uses these exact normalizations. |
| NM7: monotonicity/zero limit of `E` and the explicit complementary-error-function tail inequality | G | No `E` or `erfc` remainder producer occurs in the mixed modules. |
| NM7: weighted scalar limit after the specified two successive limits | G | `nullGaussian_density_limit_right` in [`NullGaussianRight.lean`](BoundaryDraft/NullGaussianRight.lean) is a conditional analytic tool. The actual `W_phi` and its hypotheses have not been produced, so it is not a weighted mixed limit. |
| NM7 specialized conclusion for unit source weight | T | `MixedNullData.continuumMean_tendsto_area` (Limit) proves this scalar conclusion by a different argument. It proves neither NM5 nor the quantitative NM7 inequality. |
| NM8: generator integration-by-parts formula for absolutely continuous radial traces | G | No weighted radial trace, weighted endpoint integral, or generator integration-by-parts theorem is supplied. This source assertion is broader than smooth source weights. |
| NM8 prose: tip boundary term is zero; derivative is the total time-plus-spatial generator derivative | G | No actual mixed source-weight chain-rule/endpoint theorem is present. These are not consequences of null four-volume. |
| NM8 prose: generator-constant measurable angular weights have exactly the induced-area weighted response | P | `MixedNullData.integral_jointMeasure` (Surface) gives the geometric transport for a measurable joint observable. It does not identify that integral with the limiting weighted action of its generator extension. |
| NM8 prose: independent screen metric and positive unit joint coefficient | T | `AdmissibleMixedNull.jointParam_smooth_metric`, `jointParam_induced_area` (Surface) prove the metric and Jacobian. Limit proves the **unweighted** unit coefficient. This row does not claim the missing weighted limit. |
| NM9: uniform normalized weighted tip estimate for every density | G | Same missing theorem as MA12. Existing singular domination proves integrability for the global scalar limit, not the displayed weighted cutoff bound. |
| NM9 prose: no residual point mass in the reduced weighted response, genuine tip-neighborhood control, and fixed-cylinder exact limit | G | These require the missing uniform bound/weighted limit. `frontier_volume_zero` (Frontier) is insufficient. |
| NM10: fixed collar's exact density limit | G | No actual collar-weight action limit is present. |
| NM10: upper bound by `8*pi*B*h`, and its limit as `h` decreases to zero | G | The root bound is available, but the displayed collar response has not first been identified with the actual weighted action. No theorem exports the complete estimate. |
| NM10 prose: complement has the stated nonzero limit, hence discarding it is a false localization route | G | No theorem demonstrates this obstruction for the actual weighted action. The absence of a complement-discarding step in the implemented proof is not a proof of the obstruction. |
| NM10 prose: finite source partitions add at finite density | T | `MixedNullData.weightedContinuumMean_partition` (Weighted). This is not additivity of actions of chart subregions. |
| NM10 prose: differentiated smooth-partition and radial-endpoint terms cancel in the limit | G | Requires the missing NM8 weighted identity and its summability conditions; finite-density partition linearity alone does not supply it. |

### NM11–NM12 and normal reparameterization

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| NM11: definitions of partner-cutoff `S`, complementary `N`, and remainder | D | **Source only.** There are no mixed declarations for these two-endpoint-cutoff objects. `weightedContinuumMean` weights the source alone. |
| NM11: exact finite-density equality `S+N` to the full Gaussian response | G | No mixed partner-cutoff definition, integrability specialization, or addition theorem is supplied. The split is algebraic once those integral obligations are checked, but it is not the compiled source-partition theorem. |
| NM11: remainder bounded by NM7, with source-weight generator accounting | G | The missing quantitative weighted estimate is additionally needed. No separate vanishing of `N` is claimed by the source or proved by this index. |
| NM §4: explicit future unit timelike normal, null normal, their positive Lorentz pairing | G | No actual mixed-face normal producer. The same-expression joint differential cancellation does not establish these fields. |
| NM §4: affine rescaling and nonaffine increasing generator reparameterization, including transformed measures and derivative/endpoints | G | No parameter-change theorem for these weighted generator integrals is present. The action and parametric joint measure having no marked-normal input is strictly weaker. |
| NM §4: no logarithmic marking term is used by the unweighted theorem | T | The actual definitions and the proof chain in Limit/Surface contain no normal marking or logarithmic corner weight. This is a statement of the encoded theorem's inputs/target, not a general normal-gauge theorem. |
| NM §4 comparison: positive spacelike planar weight `1/s` | B | `jointRapidity_identities` in [`EllipsoidAngle.lean`](BoundaryDraft/EllipsoidAngle.lean) proves the positive-branch `jointCoth k = 1/k` relation. Applying the appropriate planar two-face geometry and identifying the source's parameter remains a separate comparison, not part of the mixed limit. |
| NM §4 comparison: the two opposite singular geometric endpoints and their normal interpretation | G | No mixed comparison theorem proves these limiting normal statements or any exchange with density. The source itself forbids inferring such an interchange. |
| NM12 first line: round cap's explicit logarithmic `W_T(sigma)` formula on its positive support | G | No `W_T` density definition or radial-primitive evaluation is provided by the mixed modules. The constant-radius/area theorem is not that calculation. |
| NM12 second line: actual zero-sigma coarea value `W_T(0) = pi*T^2` | P | `mixedNullArea_constant` (Examples) evaluates the independently proved area to four times this number. The actual round coarea density and its endpoint identity are not defined/proved by that area theorem. |
| NM12 following prose: weight vanishes beyond `T^2` | G | No actual global round-weight support theorem is present. The finite upper cutoff of an individual positive-radius fibre is a different statement. |
| NM §7: integral of that weight equals round volume `pi*T^4/3` | G | No exact mixed constant-floor volume theorem or global-weight-volume identity is present. Positive finite volume is proved, but not this value. |
| NM §7: explicit density for time weight `phi=t` | G | No such time-weighted density or its generator-term calibration is implemented. Finite-density weighted cancellation is not its evaluation. |

## 5. MA13–MA15 and the actual probability bridge

For the **B** rows below, the intended specialization is concrete, not a new
assumption on geometry:

```lean
-- Given hH : MixedNullData H and hρ : 0 < ρ:
hH.boundedCausalRegion.sprinkling ρ hρ
```

Its region and density are the original ones, and its probability is the law
used by `expectedBDGAction`. The existing expected-action bridge already uses
this specialization internally. The distinction below is between that completed
bridge and separately exported, fully expanded MA13/MA14 formulas.

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA §5: finite, nonzero Borel volume | T | `MixedNullData.region_volume_pos`, `region_volume_lt_top`, `region_volumeReal_pos` (Elementary), and `isOpen_region` (Reduction). |
| MA §5: actual probability law at positive density | T | `MixedNullData.boundedCausalRegion` (Reduction) constructs the input used by `BoundedCausalRegion.sprinkling` (ExpectationBridge). `FinitePoisson.isProbabilityMeasure_law` in [`FinitePoisson.lean`](BoundaryDraft/FinitePoisson.lean) and the probability instance in SpacetimeSprinkling apply. The constructed law, not an arbitrary probability field, is used in the mixed expectation theorem. |
| MA §5: literal two-stage “Poisson count, then normalized iid locations, then forget labels” presentation | P | `FinitePoisson.law` uses an unnormalized Janossy sum of pushed-forward product measures; `FinitePoisson.weight_mul_pow` checks the stratum masses. The equivalent normalized conditional-sampling presentation is not separately identified by a mixed theorem. The absence of that presentation does not undermine the actual constructed law. |
| MA §5: support and almost-sure simplicity | B | `FiniteSprinkling.ae_supported`, `ae_nodup` (SpacetimeSprinkling), and `FiniteSprinkling.ae_discreteBDGAction_eq_finite_order` (DiscreteBDG) need the above explicit mixed sprinkling instance for separately displayed mixed statements. |
| MA §5: measurable causal relation, endpoint-excluded counts and discrete observable | T | `measurableSet_causalRelation`, `jointMeasurable_intervalCount`, `measurable_intervalCount` (SpacetimeSprinkling), and `measurable_discreteBDGAction` (DiscreteBDG) are universal statements; they already concern the unchanged observable. |
| MA13 first line: coefficient-16 quadratic absolute bound | T | `abs_discreteBDGAction_le`, `abs_bdgLayerWeight_le` (DiscreteBDG). The former uses `abs(bdgNormalization rho)` and the natural-number falling factorial; positive-density simplification gives the displayed convention. It does not replace 16 by the sum of absolute layer coefficients. |
| MA13: first real factorial moment | B | `FiniteSprinkling.integral_card` (PoissonExpectation) gives the result on the indicated mixed sprinkling. There is no separately named mixed first-moment theorem. |
| MA13: second real factorial moment | B | `FinitePoisson.lintegral_pairCard`, `integrable_pairCard` in [`PoissonIntegration.lean`](BoundaryDraft/PoissonIntegration.lean), together with `FiniteSprinkling.intensity_toReal`, supply the finite-intensity identity. The displayed real mixed formula needs explicit instantiation and conversion from the nonnegative integral. |
| MA13 consequence: original discrete action absolutely integrable before expectation | T | `MixedNullData.integrable_discrete_action` (Elementary), with the full original law in its statement. No bounded sample-cardinality premise is used. |
| MA14: layer-by-layer Campbell–Mecke expectation with restricted interval rate | B | `integral_intervalLayer` in [`PoissonExpectation.lean`](BoundaryDraft/PoissonExpectation.lean) is the exact generic real expectation; `poissonLayerMean` contains the closed-causal/unequal-endpoint indicator and Poisson PMF. Expanding it on the mixed sprinkling, including both intensity factors and the displayed restricted rate, is not a separately exported mixed layer theorem. |
| MA14 prose: layer integrands between zero and one, and integrability on both sides | B | `poissonLayerMean_nonneg`, `poissonLayerMean_le_one`, `integrable_poissonLayerMean`, `integrable_poissonLayerMean_section` (PoissonExpectation), and `integrable_intervalLayer` (DiscreteBDG) apply to that mixed sprinkling. |
| MA14 prose: remove marked endpoints without changing interval volume | T | `volume_causalIntervalInterior` (ExpectationGeometry) is universal. Counts still exclude only those endpoints. |
| MA14 prose: restricted timelike rate is the ambient Minkowski rate | B | `FiniteSprinkling.interval_rate` (ExpectationGeometry), with the mixed `causallyConvex` proof and actual endpoint membership. This specialization is already used inside the final expectation bridge; no standalone mixed-rate declaration is added. |
| MA14 prose: null/diagonal endpoint relations may be ignored only a.e. in the integral | T | `volume_nullCone_at`, `ae_causalFuture_chronological` (ExpectationGeometry) are universal. `FiniteSprinkling.integral_poissonBDGMean` (ExpectationBridge) uses them to remove these exceptional endpoint relations in iterated integration. Null relations remain in the discrete definitions. |
| MA14 prose: literal product-measure-null set of all null-related pairs/diagonal | B | `volume_dimensionNullPairs`, `volume_dimensionDiagonal` in [`DimensionCausalInterval.lean`](BoundaryDraft/DimensionCausalInterval.lean) prove the product-set assertions in dimension-indexed coordinates. `dimensionSpacetimeCoordinates_measurePreserving` and `dimensionSpacetimeCoordinates_intervalSq` in [`DimensionIntervalCompatibility.lean`](BoundaryDraft/DimensionIntervalCompatibility.lean) provide the four-dimensional coordinate bridge. A displayed mixed/original-coordinate product-set specialization is still separate from the already-used sectionwise argument. |
| MA14 prose: every null causal interval itself has zero four-volume | B | `volume_dimensionCausalInterval_null` (DimensionCausalInterval) is a genuine baseline theorem, not an inference from null endpoint-pair exclusion. Specialize to spatial dimension three and transport with `dimensionSpacetimeCoordinates_intervalSq` and `volume_oldCausalInterval_eq_dimension` (DimensionIntervalCompatibility). No new mixed null-interval theorem is needed as an assumption. |
| MA15 first line: signed layer factorial polynomial recovers the kernel | T | `bdgLayerWeight_polynomial`, `bdgLayerWeight_kernel` (DiscreteBDG), and `poissonBDGMean_eq_sum` (PoissonExpectation). The factorials are retained. |
| MA15 second line: expectation is the correctly normalized point-minus-full-pair continuum action | T | `MixedNullData.expectedBDGAction_eq` (Reduction), through `FiniteSprinkling.integral_discreteBDGAction` (PoissonExpectation), `integral_poissonBDGMean`, `expectation_eq_continuumMean` (ExpectationBridge), and `bdgNormalization_mul_density` (DiscreteBDG). |
| MA15 consequence: transfer of the established deterministic limit | T | `AdmissibleMixedNull.expectedBDGAction_limit` (Limit). No expectation/almost-sure-limit interchange occurs. |

## 6. Unnumbered calibrations and geometric controls

| Source claim | Mark | Exact correspondence and boundary |
| --- | --- | --- |
| MA §6 / NM §7: positive constant floor belongs to the smooth mixed class | T | `mixedNull_constant_admissible` (Examples). |
| MA §6 / NM §7: constant radius and area `4*pi*T^2` | T | `mixedNullRadius_constant`, `mixedNullArea_constant` (Examples). `MixedNullSupportRegression.lean` also contains an independently expanded anonymous expected-limit example with that target. |
| MA §6 / NM §7: exact round volume, coarea primitive and time-weight formula | G | See NM12: neither the area normalization nor the constant-member limit evaluates these separate quantities. |
| MA §6: affine floor, possibly negative outside the domain, with explicit radius | P | `mixedNull_affine_admissible`, `mixedNullRadius_affine`, `mixedNull_affine_exterior_negative` (Examples) cover `T + a*x[0]`, with `abs(a) < 1`. They do not state the note's arbitrary vector-dot-product affine family or its rotational transport. |
| Non-round geometric control | T | `mixedNull_affine_radius_nonconstant` (Examples) gives actual radii `2` and `2/3` for the same admitted floor. This is an affine control, not evidence that the **sine** radius varies. |
| MA §6 / NM §7: the exact `1 + (1/5)*sin(x[0])` floor is smooth and strictly Lipschitz | T | `mixedNullSineFloor`, `mixedNull_sine_admissible` (Examples); the proof uses Lipschitz constant `1/5`. `MixedNullSupportRegression.sineFloor_data` independently constructs the same-profile admissibility contract. |
| MA §6 / NM §7: sine floor is globally nonaffine | T | `mixedNull_sine_nonplanar` (Examples) proves a failed affine midpoint identity. |
| NM §7: sine floor is globally strictly positive | B | The formula and the universal lower bound for sine yield this by elementary specialization; `mixedNull_sine_admissible` itself stores only positive height at the origin, not global positivity. There is no named global-positivity theorem for this floor. |
| MA §6 / NM §7: sine lower face has nonzero second derivative at an interior point; its joint radius varies | G | No such derivative/interior witness or sine-radius-variation theorem is present. The nonaffine midpoint witnesses do not assert interior membership, and the affine unequal-radius control proves a different example. |
| NM §7: numerical evaluator's condition implies the stated bound on `Q''`, strict concavity, a unique maximum and interval slices possibly with two positive endpoints | G | No Lean theorem encodes this evaluator-specific condition or these conclusions. It is not a hypothesis of the mixed limit. |
| NM §7: existing null-plane cap has its original deterministic limit `pi*a*(2*T-a)` | T | `nullCapLimitGoal` in [`NullCapLimit.lean`](BoundaryDraft/NullCapLimit.lean), with its original positive cut parameters; `NullCapLimitGoal` is defined in Specification. This is a separate baseline class, not a mixed-floor instance. |
| NM §7: the null-plane cap's angular-radius formula and its no-extra-seam screen-area interpretation | G | The baseline concrete action/weight/limit does not prove this separate angular geometric parametrization or seam-area statement. No mixed theorem extends to lower null faces. |
| NM §7: the uncut diamond's full response is `pi*T^2` | P | `uncut_joint_area` (Algebra) evaluates the algebraic candidate at `a=T`; the original `nullCapLimitGoal` requires `a<T`. That algebraic endpoint is not a full diamond-limit theorem, and the source-to-tip angular argument has not been instantiated for the diamond here. |
| NM §7: original null-cap weight/support/action formulas remain available | T | `nullCapWeight`, `nullCapWeightCore` in [`NullCoordinates.lean`](BoundaryDraft/NullCoordinates.lean); `integral_nullCap_eq_weightCore` in [`NullCapReduction.lean`](BoundaryDraft/NullCapReduction.lean); `nullCap_continuumMean_eq_weightExtension` and `nullCapLimitGoal` (NullCapLimit). These are not the round mixed `W_T` of NM12. |

## 7. Evidence, uncertainties, and remaining obligations

### Regression evidence is not a substitute for a missing claim

[`MixedNullRegression.lean`](MixedNullRegression.lean) checks expanded
finite-density region/law/action contracts and a nonaffine floor.
[`MixedNullSupportRegression.lean`](MixedNullSupportRegression.lean) checks
expanded closure/frontier, discrete integrability, signed weighted cancellation,
a discontinuous **abstract Gaussian** cutoff, and deterministic/expected
limits with independent smooth-floor hypotheses and nonvacuity controls.
The abstract Gaussian cutoff example is not a proof of a geometric tip or
collar action limit. Anonymous `example` declarations in these files are
compile-time checks, not separately named producers.

The pinned notes additionally describe `mixed_poisson.py`,
`test_mixed_poisson.py`, `test_null_mixed.py`, `reproduce_null_mixed.py`,
`SineMixedCap`, and their generated tables. This index does not rerun or
certify those diagnostics, enumerate their assertions, or convert numerical
quadrature/refinement, sampled causal geometry, and symbolic calculations
into quantified Lean results. In particular, independent positive-layer
quadrature, annular-slice observations, time-weight tests, and cutoff
bookkeeping tests do not close the **G** rows above.

### Correspondence limitations requiring care

- **Same conclusion, different route:** the complete unweighted MA3 limit is
  established without the displayed global weights of MA9/NM4. A future
  source-claim-complete port must still construct and identify those weights
  if it claims coverage of their displayed formulas and estimates.
- **Same words, different object:** `mixedNullFibreWeight` is not `W_H`;
  `integral_jointMeasure` is not a weighted action limit; a source partition
  is not a partner cutoff; null four-volume is not normalized tip control.
- **Same geometry, different strength:** the actual joint is a smooth
  parametric spacelike surface with proved induced Gram density. This does
  not supply whole-face normal formulas, a formal manifold-with-boundary
  stratification, arbitrary normal reparameterization, or canonical
  Hausdorff identification.
- **Probability proof versus separately displayed corollaries:** the actual
  mixed expectation bridge is complete. Generic factorial moments, layer
  expectations, and rate identities are available, but the dedicated
  expanded MA13/MA14 statements identified as **B** are not asserted to have
  been separately compiled as mixed declarations.
- **Absence claims are scoped:** the **G** designations result from inspection
  of all `MixedNull*` producers at L and the baseline sources cited above.
  They are not a proof that no distant generic mathlib theorem could help.
  Explicitly incomplete correspondences include arbitrary-vector affine
  calibration and the complete uncut-diamond response; nearby theorems are
  not silently promoted to exact matches. Null-interval and product-nullity
  facts were located in the dimension-indexed baseline and are therefore
  classified as **B**, with the required coordinate transport identified,
  rather than as missing mathematics.

### What still prevents whole-note closure

1. The exact global `W_H`/`W_phi` coordinate representations, support,
   measurability and endpoint/right-continuity statements.
2. NM5's quantitative weighted remainder, NM7's error-function bound and
   weighted limit, and NM8/MA11's generator formula with its exact regularity,
   endpoint, integrability and partition hypotheses.
3. NM9/MA12's uniform normalized tip control and fixed-cutoff limit;
   NM10's actual collar/complement asymptotics and localization obstruction.
4. NM11's actual partner-cutoff ledger and its weighted remainder bound.
5. The additional face/normal/reparameterization assertions and the
   unproved concrete calibration formulas identified above.
6. Explicit specializations of the **B** probability/calibration statements
   if each displayed source claim is to have its own checked correspondence.

Arbitrary null/null joints, multiple tips or extra strata, curved mixed
geometry, dimension changes, degenerating geometry, rates outside the stated
missing estimates, variance, and individual-sprinkling convergence are not
proved by this package. The source notes themselves exclude these extensions;
this index neither adds them as solved obligations nor rewrites their issue
or independent-review history.

# Mixed supporting claims: checked-producer delta after the core limit

This is a **delta to the frozen [MA/NM index](MIXED_NULL_CLAIMS.md)**, not a
claim of complete note or research coverage. The older index retains its
comparison against `17618065b5286d07f7eb41a6eb586cd52d8e35a0`; its absence
statements are about that commit, not the following later producers.

- Written source: **I = `113f83d099449221fdacf20a404d57f5939e896d`**.
  [MA](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-mixed-assembly.md)
  and [NM](https://github.com/q5m-ai/causal-sets/blob/113f83d099449221fdacf20a404d57f5939e896d/notes/null-mixed-estimates.md)
  have the same Git blobs here as in the implementation branch and earlier S.
- New Lean input pin: **P = `d65b537235ce1e38ec27b74a88441905d1f4f354`**.
  Its last Lean-source commit is `3fb9fdf7d0ea02c9d051788290426363685460d9`;
  P adds source-accounting/CI documentation and tooling, not different proofs.
- Validation: targeted/incremental checks and the full all-source audit passed.
  The [input-pinned receipt](receipts/written-support-validation.json) records
  394 Lean sources, 3,872 public library theorems and all public definitions,
  unchanged inputs/dependencies, and the unchanged transitive-axiom rule.
  This verifies proof terms, not exhaustive correspondence or human acceptance.

All project names below have the prefix `BoundaryDraft`. Unqualified method
names following `MixedNullData` or `AdmissibleMixedNull` keep that namespace.
Files are under `formal/BoundaryDraft/`. Exact statements and independently
expanded regression contracts, not just names, were inspected.

## Unchanged contracts and objects

`MixedNullData H` still means positive `H 0` and a global Euclidean Lipschitz
constant strictly below one. `AdmissibleMixedNull H` separately adds smoothness.
There are no root, jet, area, response or limit fields. The original signed
kernel, closed causal order, spacetime measure, full partner region and finite
Poisson law are unchanged. Negative floor values outside the spatial domain
remain allowed. Smoothness of a floor does not assert curvature of spacetime.

`mixedNullGlobalWeight` and `mixedNullWeightedGlobalWeight` are **actual spatial
integrals**, not values assigned by a density limit. Their strict square-root
cutoff retains the sign of the floor. The constant extension to negative sigma
is auxiliary; the physical identities are on the positive ray, with the actual
zero endpoint evaluated separately.

## Geometry and exact global transport

| Written claim | New producers at P | Scope and remaining distinction |
| --- | --- | --- |
| MA/NM radial derivative bound, growth and closed support | `mixedNull_radial_derivative_lower_bound`, `MixedNullData.radial_gap_tendsto_atTop`, `closed_radial_domain` in `MixedNullFaces` | The derivative retains the specified Lipschitz constant. Growth/support use actual geometry, not root hypotheses. |
| Actual face smoothness, singular tip, causal type and normals | `mixedNullUpperParam_smooth`, `mixedNullUpperParam_not_differentiableAt_zero`, `mixedNullUpperParam_fderiv`, `mixedNullUpperParam_radial_null`; `AdmissibleMixedNull.lowerParam_smooth`, `lowerParam_fderiv`, `lowerParam_spacelike`, `floorNormal_future_unit`, `floorNormal_orthogonal`, `normals_inner`, `normals_inner_pos`, `normals_not_parallel` in `MixedNullFaces` | Genuine differentials and Lorentzian normal pairing. A complete manifold-with-boundary/disjoint-stratification package is not claimed. |
| MA7 full level differential nonzero | `AdmissibleMixedNull.joint_level_fderiv_ne_zero` in `MixedNullFaces` | The exact level function, not merely a positive radial derivative. |
| MA9 global weight and endpoint | `mixedNullCoareaKernel`, `mixedNullGlobalWeight`; `MixedNullData.measurable_coareaKernel`, `integrable_coareaKernel_zero`, `integrable_coareaKernel`, `measurable_globalWeight`, `globalWeight_zero` in `MixedNullCoarea` | The reciprocal-radius majorant is integrable before the origin is removed as null. The endpoint uses the independently proved area identity. |
| MA9 nonnegativity, bound, support and right limit | `MixedNullData.globalWeight_nonneg`, `globalWeight_bound`, `globalWeight_eq_zero`, `globalWeight_right_continuous`, `globalWeight_tendsto_area_quarter` | Exact bound and inclusive upper support endpoint, for the supplied Lipschitz constant. No positivity outside the domain or connected radial slices. |
| MA9/NM4 radial slices and angular/radial representation | `integral_mixedNull_polar`; `MixedNullData.coarea_radial_slice_subset`, `globalWeight_eq_polar`, `globalWeight_eq_angular_radial` in `MixedNullCoareaPolar` | Actual signed polar disintegration and fixed radial upper bound. An admitted affine slice with an axis hole is a regression, not a proof of every sine-evaluator slice claim. |
| MA9 finite-density action identity | `MixedNullData.integrable_coareaGaussian`, `integrable_globalWeight_gaussian`, `spatialGaussian_eq_globalWeight`, `continuumMean_eq_globalWeight` in `MixedNullCoareaAction` | Absolute product integrability before Fubini; the original action appears in the conclusion. |
| MA10 literal rescaling, majorant and passage to the target | `MixedNullData.continuumMean_eq_globalWeight_rescaled`, `globalWeight_rescaled_bound`, `coareaGaussian_majorant_integrable`, `continuumMean_tendsto_via_globalWeight` | This now proves the global-weight route itself, not a wrapper around the old spatial-fibre limit. |
| NM4 signed, spacetime-dependent weight | `MixedNullData.weightedGlobalWeight_eq_angular_radial`, `weightedGlobalWeight_zero`, `weightedGlobalWeight_bound`, `weightedGlobalWeight_eq_zero` in `MixedNullCoareaWeighted`; `mixedNull_fibre_integral_coarea`, `MixedNullData.coarea_vertical_integral`, `weighted_spacetimeGaussian_eq_globalWeight`, `weightedContinuumMean_eq_globalWeight` in `MixedNullCoareaTransport` | Merely measurable signed weights are allowed. These initial APIs have explicit global bounds; local equivalence below removes that restriction where asserted. |

## Quantitative weighted estimates, generator and cutoff responses

| Written claim | New producers at P | Scope and remaining distinction |
| --- | --- | --- |
| NM5 Step 1, including simultaneous endpoints | `MixedNullData.coarea_small_radius_mem`, `coarea_removed_radius_lower` in `MixedNullErrorGeometry` | Strict inclusion survives the stated small-radius/sigma endpoint case; the origin is handled explicitly. |
| NM5 Step 2, actual removed shell | `MixedNullData.radial_gap_lower`, `coarea_removed_shell`; `mixedNull_shell_integrable`, `mixedNull_shell_integral` in `MixedNullErrorIntegrals` | No monotone-slice or single-moving-root premise. |
| NM5 Step 3, Jacobian difference and logarithmic cost | `mixedNull_sqrt_gap`, `mixedNull_sqrt_gap_eq`, `mixedNull_radial_jacobian_difference`, `mixedNullJacobianErrorBound_bounds` | The split is evaluated at the actual square root of sigma. |
| NM5 Step 4 and full estimate | `MixedNullData.errorRadialIntegrand_difference_bound`, `errorRadialIntegral_difference_bound`, `weightedGlobalWeight_error` in `MixedNullWeightedError` | Actual time variation, shell and Jacobian terms with the literal constants and sigma range. No desired error estimate is an input. |
| NM7 properties of the calculated error | `mixedNullWeightedError_zero`, `mixedNullWeightedError_right_continuous`, `mixedNullWeightedError_monotoneOn` in `MixedNullErrorRegularity` | The explicit formula supplies its own zero limit and monotonicity. |
| NM6/NM7 mass and tail | `mixedNull_gaussian_mass`, `mixedNull_gaussian_tail`, `mixedNullErfc_zero`, `mixedNullErfc_tendsto_zero`, `mixedNullErfc_density_tendsto_zero` in `MixedNullWeightedGaussian` | Mass four and an actual normalized Gaussian tail integral, not an axiom for an error-function symbol. Density varies with the split fixed. |
| NM7 actual action error and scalar limit | `MixedNullData.weightedContinuumMean_error`, `weightedGlobalWeight_right_continuous_of_timeLipschitz`, `weightedContinuumMean_limit_of_timeLipschitz` | The geometric NM5 producer supplies the analytic consumer. Discontinuous spatial weights are admitted. |
| Original closed-box/local weight hypotheses | `MixedNullWeightBound`, `MixedNullTimeLipschitz`; `MixedNullData.weightBound_of_box`, `timeLipschitz_of_box`, `weightedContinuumMean_clip_eq`, `weightedGlobalWeight_clip_eq`, `weightedGlobalWeight_error_local`, `weightedContinuumMean_error_local`, `weightedContinuumMean_limit_local` in `MixedNullErrorExtension` | Auxiliary value clipping changes neither original action term nor any active coarea contribution. Coordinate time need not be globally bounded. |
| Time-only continuity and continuous-weight limits | `MixedNullData.weightedGlobalWeight_right_continuous`, `weightedContinuumMean_tendsto_globalWeight` in `MixedNullWeightedContinuity`; `weightedContinuumMean_tendsto_globalWeight_continuous` in `MixedNullGeneratorLocal` | The first permits radial/angular discontinuities; the last handles every continuous spacetime weight using compact closure bounds. |
| NM8 tip and total derivative | `mixedNull_generator_tip_zero`, `hasDerivAt_mixedNullGeneratorTrace`, `MixedNullData.generator_tip_zero_local` | The tip term vanishes by a bound. The derivative includes time and spatial contributions. |
| NM8/MA11 C1 endpoint and actual action formula | `MixedNullData.weightedGlobalWeight_generator_C1_unbounded`, `weightedContinuumMean_generator_limit_C1` in `MixedNullGeneratorLocal` | Every C1 spacetime weight; no global bound, action limit or desired endpoint identity is assumed. Compactness and actual trace integration supply the hypotheses. **General AC traces remain open.** |
| NM8 supplied generator-constant angular extension | `MixedNullData.weightedGlobalWeight_generator_constant`, `weightedGlobalWeight_generator_constant_joint` in `MixedNullGenerator` | Endpoint identity for a supplied measurable bounded extension with constant ray trace; no angular differentiability. A universal extension-constructor correspondence is separate. |
| NM8 affine/nonaffine radial transport | `mixedNull_generator_response_transport`, `mixedNull_generator_correction_transport`, `mixedNull_generator_reparameterized_ledger`, `mixedNull_generator_affine_marking`; `MixedNullData.weightedGlobalWeight_generator_reparameterized`, `weightedGlobalWeight_generator_affine` in `MixedNullGeneratorTransport` | C1 coordinate changes, both Jacobians and endpoints retained. The mixed endpoint versions retain their explicit global C1 weight bound; unbounded-weight transport wrappers are separate from the completed unbounded C1 action formula. No jointly measurable product coordinate map is asserted for arbitrary angular dependence. |
| Artificial radial boundary cancellation | `mixedNull_generator_cut_ledger` | Both neighboring corrections are kept. Pointwise derivative cancellation for every smooth source partition still needs its explicit correspondence. |
| NM9/MA12 uniform tip bound and neighborhood | `mixedNull_tip_weight_bound`, `mixedNull_tipCylinder_mem_nhds`, `MixedNullData.weightedContinuumMean_tip_bound`, `weightedContinuumMean_tip_bound_local` in `MixedNullTip` and `MixedNullTipLocal` | Actual full-partner action, all positive densities, local original-weight bounds. Nullity of the tip alone is not used as normalized control. |
| NM9 fixed unit-cylinder response | `MixedNullData.tipWeight_zero`, `weightedContinuumMean_tip_limit` | Exact nonzero response below the proved lower exit radius. |
| NM10 actual collar and complement | `mixedNullExitRadius`, `mixedNullCollarWeight`, `mixedNullCollarComplement`; `MixedNullData.collar_response_from_lipschitz`, `collarResponse_tendsto_zero`, `collarComplement_response_pos` in `MixedNullCollar` | Exact fixed-width action limits, literal upper bound, subsequent shrinking-width limit, strictly positive complementary response. This disproves discarding the source complement, not full-region convergence. |
| NM11 full partner-cutoff ledger and error | `mixedNullCutoffShort`, `mixedNullCutoffLong`, `mixedNullCutoffRemainder`; `MixedNullData.integrable_cutoff_bilocal`, `integrable_cutoff_outer`, `cutoff_ledger_eq_gaussian`, `cutoff_remainder_bound`, `cutoff_ledger_partition` in `MixedNullPartnerLedger` | Measurable pair cutoffs on the actual full causal domain; point term once. No separate vanishing of the long entry. |

## Original-law probability and concrete controls

| Written claim | New producers at P | Scope and remaining distinction |
| --- | --- | --- |
| MA13 support, simplicity and finite-order interpretation | `MixedNullData.poisson_isProbabilityMeasure`, `poisson_ae_supported`, `poisson_ae_nodup`, `poisson_ae_finite_order` in `MixedNullProbability` | Literal original finite-Poisson law, closed causality and marked-endpoint exclusions. |
| MA13 moments and integrable bound | `mixedNull_abs_discreteBDGAction_le`; `MixedNullData.poisson_card_probability`, `poisson_integral_card`, `poisson_integral_pairCard`, `poisson_integrable_action_bound` | Real falling factorial and coefficient 16, with separate integrability. The normalized conditional-iid presentation remains a correspondence gap. |
| MA14 actual restricted rate | `MixedNullData.poisson_restricted_interval_volume`, `poisson_restricted_interval_rate`, `poisson_intensity_interval_rate` in `MixedNullProbabilityGeometry` | Actual region and endpoint-excluded intervals, not a supplied rate field. |
| MA14 null intervals/pairs and diagonal | `mixedNull_volume_nullInterval`, `mixedNull_volume_nullPairs`, `mixedNull_volume_diagonal`, `mixedNull_restricted_nullPairs`, `mixedNull_restricted_diagonal` | Original-coordinate transport, including product-volume statements. Null relations are not removed from the discrete observable. |
| MA14 expanded layer expectations | `MixedNullData.poisson_integral_layer_restricted`, `poisson_integral_layer_minkowski`, `poisson_integral_layer_future` in `MixedNullProbabilityLayers` | Both intensity factors, factorial denominators, original law and full partners are visible. Measurability, bounds and integrability are separately proved. |
| MA15 expanded signed action | `MixedNullData.poisson_integral_action` | Exact finite-density normalization; not an expectation/sample-wise-limit interchange. |
| NM sine lower-face interior curvature and varying joint radius | `mixedNull_sine_interior_second_deriv`, `mixedNull_sine_radius_nonconstant` in `MixedNullSineGeometry` | Actual interior second directional derivative and unequal radii, not just global nonaffinity or an affine control. |
| NM12 round zero endpoint/support | `MixedNullData.globalWeight_zero`, `globalWeight_eq_zero`, with constant-floor specialization in `MixedNullCoareaRegression` | Exact actual endpoint and upper support. These do not evaluate the full finite-sigma logarithmic primitive or volume. |
| Actual coordinate-time weighted response | `MixedNullData.weightedGlobalWeight_coordinateTime`, `weightedContinuumMean_coordinateTime_limit`, `mixedNull_coordinateTime_constant_limit` in `MixedNullGeneratorLocal` | Genuine unbounded-in-ambient-space weight, total generator derivative and nonzero signed response. The full finite-sigma density formula remains separate. |

## Remaining debt and verification boundary

The following are not silently promoted by the new producers:

- general absolutely-continuous radial traces, rather than an everywhere
  interior derivative or C1 trace;
- the full face-with-boundary/stratification package, intrinsic causal-path
  equivalence and literal symmetric-difference/frontier correspondence;
- every smooth-partition derivative identity, universal angular-extension
  constructor and unbounded-weight reparameterization specialization;
- absolute-kernel contrast and the separate Taylor-series interchange route;
- the complete NM12 logarithmic primitive, weight-volume identity, time-weight
  finite-sigma formula, arbitrary-vector affine family, and remaining diamond
  and null-plane angular/geometric calibrations;
- sine-specific annular-slice/evaluator concavity claims, which are not the
  affine axis-hole regression;
- the normalized conditional-iid probability presentation.

This is not an exhaustive new inventory of all unnumbered claims. Unmentioned
rows of the earlier frozen index remain obligations unless an exact new
correspondence is reviewed. Neither a source-roster count nor a larger theorem
count is a coverage percentage. The broader research queue, unresolved PF3-L
and general contact/correction questions, and independent human acceptance
remain separate.

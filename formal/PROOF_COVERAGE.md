# Written mathematics versus Lean coverage

## Scope and source identities

**This is a stocktake and a first port, not a claim that the whole research
programme is now Lean verified.** A successful checker run certifies encoded
statements only. Written proofs, numerical tests, model certificates, and
independent human acceptance are different kinds of evidence.

The inventory uses these immutable sources:

- Mathematical integration **S = `9e0068f91c219fe61984d20fdb3f6939eab907c4`**,
  on `issue-81-general-coverage`. All pre-existing files below are read at S.
- Main **M = `6a72d1aa0293ca4660550ee8af2431e3b7424f3e`**. Main lacks the
  later smooth flat 2D and thin-torus ports and much of the written research.
  Auditing only main would give an incomplete inventory.
- Review package **R = `1ad9c9ae1d32b7405062371dbb018db7f30f7bc1`**:
  [`research/manuscript.md`](https://github.com/q5m-ai/causal-sets/blob/1ad9c9ae1d32b7405062371dbb018db7f30f7bc1/research/manuscript.md),
  [`coverage.md`](https://github.com/q5m-ai/causal-sets/blob/1ad9c9ae1d32b7405062371dbb018db7f30f7bc1/research/coverage.md), and
  [`artifact.md`](https://github.com/q5m-ai/causal-sets/blob/1ad9c9ae1d32b7405062371dbb018db7f30f7bc1/research/artifact.md).
  R itself pins its mathematical claims to S; it is not a new proof.

S contains **344 local Lean sources including the aggregate audit**. Its
thin-torus receipt records 3,485 public theorems, plus all public definitions.
Neither number is a percentage of research coverage: a thousand supporting
lemmas do not imply that one unencoded geometric theorem is checked.
The current addition is identified separately below. Historical issue/PR
receipts and the public review snapshot are not rewritten.

## Classification

- **Checked:** an actual proof term, with its original hypotheses and target.
- **Conditional checked:** a proved implication whose geometric inputs have
  not been supplied at the proposed broader scope.
- **Written:** a conventional argument in the cited note, not a compiled term
  or a claim of independent human acceptance.
- **External input:** conventional differential geometry/analysis still needs
  an encoded statement and proved/imported theorem at the required scope.
- **Model certificate / diagnostic:** arithmetic or finite tests, not a proof
  of the model-to-physical-action correspondence.
- **Unresolved:** mathematics not yet proved or refuted, not merely a port gap.

All Lean names in the next table are in namespace `BoundaryDraft` unless a
longer namespace is shown. The linked files contain proof bodies, not just
`Goal : Prop` declarations. Their assembly proofs use actual producers before
transferring the expectation; they do not assume the desired limit.

## Existing checked end-to-end results

| Claim and exact scope | Actual Lean proof and dependency spine | Boundary |
| --- | --- | --- |
| 4D admissible graph caps, including retained positive-height critical points | [GraphLimit](BoundaryDraft/GraphLimit.lean): `AdmissibleGraphCap.graphCapLimit`; constructed collar/coarea, right-continuous canonical density, signed kernel mass and tail; [ExpectedLimits](BoundaryDraft/ExpectedLimits.lean): `AdmissibleGraphCap.expectedBDGAction_limit` | Not arbitrary future faces or manifold charts |
| Unequal-axis ellipsoid with original positive-axis/strict-slope hypotheses | [EllipsoidLimit](BoundaryDraft/EllipsoidLimit.lean): `ellipsoidLimitGoal`; [EllipsoidHausdorff](BoundaryDraft/EllipsoidHausdorff.lean) identifies the canonical measure with the parametric target; [ExpectedLimits](BoundaryDraft/ExpectedLimits.lean): `ellipsoid_expectedBDGAction_limit` | Concrete variable-angle example, not a general curved metric |
| Original flat 4D plane-cut null diamond, exactly `0 < a < T` | [NullCapLimit](BoundaryDraft/NullCapLimit.lean): `nullCapLimitGoal`; exact interval cancellation and Gaussian concentration; [ExpectedLimits](BoundaryDraft/ExpectedLimits.lean): `nullCap_expectedBDGAction_limit` | Algebraic `nullJointArea` target; general induced null-joint interpretation is not supplied |
| Original 4D C³ combined-budget two-face class | [TwoFaceLimit](BoundaryDraft/TwoFaceLimit.lean): `twoFaceLimitGoal`, `twoFaceExpectedLimitGoal`; actual short overlap, derivative-controlled remainder, long jet, intrinsic coefficient | No weakening of `AdmissibleTwoFace`; not all G-SS |
| 4D independent-envelope class E | [IndependentFaceLimit](BoundaryDraft/IndependentFaceLimit.lean): `AdmissibleIndependentTwoFace.twoFaceLimit`, `expectedBDGAction_limit`; independent short and long producers at one fixed cutoff | The exact class E, not arbitrary topology or metrics |
| Smooth flat 3D combined-budget pilot | [Pilot3Limit](BoundaryDraft/Pilot3Limit.lean): `SmoothPilot3.action_limit`, `expectedAction_limit`; intrinsic curve area, actual short/long producers and exact action split | Flat `SmoothPilot3`, not the curved 3D problem |
| Smooth flat 2D combined-budget class | [TwoDLimit](BoundaryDraft/TwoDLimit.lean): `SmoothTwoD.tendsto_action`, `tendsto_expectedAction`; counted endpoints, actual short/long producers, original dimension-indexed action | Not the whole curved 2D G-SS theorem |
| Fixed thin cubic quotient-torus slab in 4D, positive period and `0 < T < L / 2` | [ThinTorusLimit](BoundaryDraft/ThinTorusLimit.lean): `thinFlatTorusLimit4`; physical interval lifts/volume, exact plane-kernel reduction, separate original-law expectation | Not first-cut/thick slabs, arbitrary flat quotients, or all dimensions |

### Reusable checked foundations, not broader limit proofs

| Component | Actual declarations/files | Missing instantiation or conclusion |
| --- | --- | --- |
| Finite Poisson law and original discrete action | [FinitePoisson](BoundaryDraft/FinitePoisson.lean), [DiscreteBDG](BoundaryDraft/DiscreteBDG.lean), [ExpectationBridge](BoundaryDraft/ExpectationBridge.lean): `FiniteSprinkling.expectation_eq_continuumMean` | New geometry must discharge measurability, finite volume and interval containment |
| General measured-order 4D expectation | [MeasuredOrderBDG4](BoundaryDraft/MeasuredOrderBDG4.lean): `MeasuredOrderBDG4.expectation_eq` | A measurable order and finite atomless physical measure, not a metric asymptotic theorem |
| Dimension-indexed kernels, interval geometry and expectation | [DimensionMellin](BoundaryDraft/DimensionMellin.lean): `integral_dimensionKernel_mellin`, `integral_dimensionKernel_transverse_zero`; [DimensionCancellation](BoundaryDraft/DimensionCancellation.lean): `dimensionKernel_transverse_cancellation`; [DimensionMeasureExpectation](BoundaryDraft/DimensionMeasureExpectation.lean): `dimensionFiniteMeasureAction_expectation`; [DimensionWedge](BoundaryDraft/DimensionWedge.lean): `dimensionWeighted_wedge_limit` | Signed cancellation requires its actual jet and real-half-dimension little-o remainder. The wedge has a fixed regulator. Neither proves all-dimensional global geometry |
| Positive controlled conformal metric on original two-face coordinate regions | [ConformalAction](BoundaryDraft/ConformalAction.lean): `ControlledConformalFactor.expectedAction_eq`, `AdmissibleTwoFace.conformal_expectedAction_eq` | Exact finite-density equality only; no Lean curvature calculation or curved continuum limit |
| Compact quotient and sphere/circle geometry | [CompactTorus](BoundaryDraft/CompactTorus.lean), [SphereCircle](BoundaryDraft/SphereCircle.lean): `SphereCircle.expectation_eq`; [UltrastaticMeasuredOrder](BoundaryDraft/UltrastaticMeasuredOrder.lean) | Sphere/circle focusing asymptotics and arbitrary conformal weights are not proved by the measured-order instance |

## Principal written claims and the missing Lean terms

The four principal statements of the pinned manuscript, **CO, FLAT, SW and
C2, are all written-only at their full quantified scope**. The narrower
checked results above must not be relabeled as their proofs.

| Written claim, labels and hypotheses | Existing checked foothold | What a genuine completed port must add |
| --- | --- | --- |
| **CO**, [CO1–CO16](../notes/curved4-complete-action-obstruction.md): the specified analytic 4D compact-torus metric/slab, zero independent target, negative complete-action growth | Scalar signed kernel and measured-order probability foundations | Actual metric/order/volume and G-SS instance; all minimizing paths; quartic physical interval matching and opening/closing fibres; CO13 model-to-action transfer; all complements and leading sign; separate actual-law expectation |
| **FLAT**, [CFT1–CFT4](../notes/corrected-flat-theorem.md), [K1–K10](../notes/flat-klein-bottle-obstruction.md): every flat G-SS member in dimensions 2–4; specified Klein-bottle failures in every higher dimension | Restricted 2D/3D/4D graph theorems and thin 4D torus | Faithful development of arbitrary relevant lifted diamonds, physical unions counted once, dependent/infinite-order masks, whole target transport; actual Klein geometry and complete surviving response. Restricted coordinate theorems do not discharge these quantifiers |
| **SW**, [SW1–SW14](../notes/sphere-dependent-conformal-limit.md): width-four sphere/period-20-circle slab, every fixed smooth positive spacetime-dependent conformal factor | `SphereCircle` measured order; finite-measure expectation | Physical weighted sphere lenses, both orientations and endpoints, antipodal abundance, integrable closing-fibre remainder, independent curvature target and full assembly |
| **C2**, [C2.1–C2.18](../notes/curved-two-d-limit.md): every smooth curved 2D G-SS member, all admitted topology and counted endpoints | Flat `SmoothTwoD`, dimension-two kernel and generic expectation | Global null-coordinate/cover construction, actual weighted rectangle unions, both overlap corners, physical long primitive/remainder, S30 and full target restoration |
| Shared curved short theorem **S30**, [S1–S30](../notes/general-metric-short-remainders.md), under the smooth G-SS contract | Flat moment/cancellation, coarea and overlap techniques; controlled conformal finite-density API | Intrinsic metric/curvature/normal target; actual thin interval and endpoint measures S1–S8; derivative/contact estimates S9–S18; full-cone S19, face S20–S25, joint S26–S29; all ordered chart pairs and compensation in S30 |
| Minkowski all-dimensional limit [A1–A3](../notes/all-dimensional-flat-limit.md), smooth or its stated sufficient finite regularity; bounded 5D/6D short/long transfer | Dimension kernels, fixed-regulator wedge theorem and dimension-indexed Poisson bridge | Dimension-dependent actual overlap jets, critical remainders, intrinsic target and assembled action. Not an all-C³ theorem |
| Controlled curved 4D two-face pilot [curved assembly](../notes/curved-assembly.md), fixed metric density `q(t)=1+t²` and its original geometric assumptions | Exact `conformal_expectedAction_eq` | Actual curved interval formula, averaged long contacts, interior/face/joint producers, cutoff/partition cancellation, independently computed curvature and joint area |
| Thin/first-cut torus families in every dimension; reflection-holonomy and 7D sphere-focusing obstructions | Thin **4D** port and generic measured-order bridge | Physical first-cut/route unions and dimension-dependent surviving responses; [holonomy](../notes/flat-holonomy-obstruction.md) H1–H15 and [focusing](../notes/seven-dimensional-focusing-obstruction.md) O1–O17 require their complete matching, not merely a selected sector |
| Positive curved RPL/FCDC, Rosen plane-wave and Hadamard-optical classes | Conditional scalar cancellation and probability foundations | [RPL/FCDC](../notes/geometric-long-cancellation.md) actual geometric hypotheses; [PW-4](../notes/nonconformal-plane-wave-limit.md) actual interval and target; [HO-4](../notes/hadamard-optical-limit.md) whole-domain containment/index comparison and contact remainder. External manifold/index-form results need precise formal counterparts |
| Flat one-tip mixed class [MA1–MA10](../notes/null-mixed-assembly.md); all-dimensional cone-ending class [ND1–ND9](../notes/null-cone-dimensions.md) | Concrete old null cap; **new finite-density MA port below** | Radial-root regularity and independent screen area, exact proper-time-square transport and dominated concentration for MA; separate beta-mixture/2D counting proofs for ND |
| Selected flat two-tip lens/union [TT-A/TT-B](../notes/two-tip-null-limit.md), conformal one-cone [CC1–CC14](../notes/conformal-cone-limit.md), regular conformal two-tip [CT](../notes/conformal-two-tip-limit.md) | Generic finite-law bridge only, not these null geometry instances | Actual whole physical union and masks, floor/generator/tip/crease terms, curved phase/remainder where applicable, independent induced screen target, full action and separate expectation |

The CO model sign enclosure in
[`certificates/curved4-focal-model.json`](../certificates/curved4-focal-model.json)
is an **arithmetic certificate for a model**. Its checker and numerical
regressions do not encode CO13, the physical coefficient, or the complete
counterexample in Lean. Other finite quadrature/symbolic tests likewise remain
diagnostics unless a precise certified assertion is separately identified.

### Unresolved mathematics is not formalization debt

The universal curved 3D G-SS response, broader null/mixed regimes outside the
selected classes, and general corrected geometric classifications remain
separate unresolved questions. Universal original-target convergence is
reported **false** in the written counterexample scopes above; a full port
must prove those negative statements, not try to prove the false universal
conjecture. Rates, variance, sample-wise convergence and timelike Conjecture 2
are not supplied by any expectation transfer. See the source-pinned
[intrinsic coverage ledger](../notes/intrinsic-coverage-ledger.md) and
[null/mixed coverage](../notes/null-mixed-required-coverage.md) for exact
remaining contracts. The historical intrinsic ledger predates the integrated
CT extension: its older TT-only multiple-tip row must be read alongside
CT1–CT12 and the pinned review-package coverage table, not used to erase that
additional written result. No issue closure or independent human approval
follows from this stocktake.

## First actual gap closure: mixed finite-density reduction

New [MixedNullReduction.lean](BoundaryDraft/MixedNullReduction.lean) introduces
`MixedNullData H`: positive height at the origin and a global Euclidean
Lipschitz constant strictly below one. These are weaker than MA's smooth
geometric assumptions because finite-density reduction does not need
smoothness. No interval identity, asymptotic jet, limit, or target is an input.

It proves, for the actual strict cone-ending region:

- `MixedNullData.isOpen_region`, `isBounded_region`, `causallyConvex`:
  measurability/boundedness and containment of the **closed ambient interval**;
- `floor_future`, `complete_future`: MA5–MA6, retaining all causal partners;
- `future_kernel_identity`, `continuumMean_eq_spacetimeGaussian`: MA8 and
  exact cancellation of the original signed bilocal action;
- `expectedBDGAction_eq`, `expectedBDGAction_eq_spacetimeGaussian`: the separate
  original-law finite-density transfer, with geometric premises discharged.

[MixedNullRegression.lean](MixedNullRegression.lean) independently expands the
strict region and actual probability integral, checks constant floors, and
instantiates a nonempty genuinely nonaffine sine floor. **This closes only the
finite-density part of MA3**, not MA7's induced area or MA9–MA10's limit.
It neither expands the old null-cap theorem nor supplies the curved CC theorem.

## Minimal dependency DAG and finite port plan

```text
geometric contract + independent target + physical order/measure
           |                              |
actual interval and endpoint transport    |-- finite-law expectation identity
           |
actual short producers ----- actual long/contact producers
           |                              |
           +---- complete action restoration at ONE fixed cutoff
                                          |
                              deterministic limit / obstruction
                                          |
                              separate original-law expectation
```

The following are bounded proposals, not automatically created issues or
promises that unknown mathematics has been solved:

1. **Finish MA (lowest-risk next complete port).** Build on the new exact
   reduction: radial root and induced screen-area theorem, exact scalar
   transport, right-hand density limit and Gaussian concentration. Completion
   means deterministic **and** expected limits with the independently defined
   geometric target for every original MA floor, including the sine example.
2. **Shared curved short spine (highest reuse, high specification risk).**
   Freeze intrinsic curvature/measure/normal conventions first. Port S1–S8,
   then derivative-controlled S9–S18, then S19/S25/S29 and S30. Each stage
   needs actual geometric producers, not a structure containing a desired
   phase jet. Start with the already specified controlled curved pilot as a
   concrete consumer; general manifold S30 remains a larger port. A small
   analytic sub-batch can first adapt S13's even/odd quantitative estimates to
   `dimensionKernel_transverse_cancellation`, with dimensions 2–6 regressions.
   That adapter would not derive the geometric estimates or S14's physical
   coefficient.
3. **Manuscript positive theorems.** Separate C2, FLAT and SW consumers after
   their shared inputs. C2 needs physical rectangle unions; FLAT needs the
   arbitrary flat-cover/union theorem and K's negative clause; SW needs
   weighted sphere/contact estimates. Passing one selected example is not
   completion of any quantified manuscript theorem.
4. **Complete obstructions (highest consequence and analytic risk).** CO's
   minimizing-path classification and CO13 transfer are priority review/port
   targets; model-sign arithmetic is a separate dependency. Require all
   complementary sectors and the independent target before an expected
   counterexample theorem. Apply the same discipline to K/H/O.
5. **Remaining established families.** Reuse only proved compatible inputs
   for ND/TT/CC/CT, higher-dimensional Minkowski and PW/HO. A bounded CT11
   sub-batch could prove exact two-past-set action valuation after deriving
   containment and actual restricted-volume compatibility; arbitrary bilocal
   additivity is false. Stop at each stated scope. Do not turn this into an
   ever-expanding classification task.

For every batch: inspect the theorem statement as well as its proof, preserve
the actual action/order/target/law, add independently expanded regressions,
use incremental checks during editing, and require the full local audit
before handoff. Human intended-statement, physical-scope and literature review
under #94/#86 remains separate even after all terms compile.

## Efficient verification without weakening the gate

`check.sh` still builds, rechecks **every local source** with warnings as errors
(including unimported modules and other namespaces), audits every public
root's transitive dependencies, and runs the aggregate audit last. The only
axioms allowed remain `propext`, `Classical.choice`, and `Quot.sound`.

Both audit entry points now reuse the **pinned Lean collector's visited set**
across roots in one fixed environment. The old implementation restarted the
same traversal for every declaration, repeatedly walking shared mathlib and
local dependencies. The new state contains the union of all axioms reachable
from roots processed so far; that union is checked after each root. No state
is reused across processes, sources, edits or runs. This changes work, not the
set of audited dependencies. The aggregate log lists audited theorem names
and the final axiom union, not misleading per-theorem cumulative axiom sets.

`test_formal_axioms.py` executes both real audit bodies with pinned Lean, tests
hidden private/opaque/definition/constructor dependencies, unused private
axioms, other namespaces and `sorry`, and compares the accumulated union with
stock `Lean.collectAxioms` after every prefix of a fixture's roots.
`test_formal_check.py` separately tests discovery, failures and orchestration.
No full legacy audit is rerun merely to benchmark it; the historical 2:42:37
receipt is evidence about that earlier run, not a controlled same-host speedup
measurement. Final timings and input identity are recorded in the validation
receipt accompanying this change.

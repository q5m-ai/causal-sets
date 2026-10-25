# Complete Lean coverage: acceptance contract and work queue

**Target: all currently asserted written results, not just another end-to-end
example. Status: incomplete.** The mixed one-tip limit is the first dependency
batch, not the definition of completion. A passing full Lean audit certifies
encoded statements; it does not certify coverage of the written mathematics.

## Fixed scope

Use mathematical source **S = `9e0068f91c219fe61984d20fdb3f6939eab907c4`**
and its review presentation **R = `1ad9c9ae1d32b7405062371dbb018db7f30f7bc1`**,
as explained in [the coverage inventory](PROOF_COVERAGE.md). Retain the checked
results already integrated at S and the subsequent mixed finite-density port.
Do not restart from the older `main` snapshot. Later mathematical changes need
an explicit scope update rather than silently changing the acceptance target.

Coverage includes supporting estimates, geometric identifications, negative
results and weighted/cutoff statements asserted in those sources, not just the
four manuscript headlines. Repeated statements may share a proof, but their
specialization must be recorded. Definitions, numerical diagnostics, external
citations, conjectures, and superseded failed arguments must be classified;
they must not be silently counted as theorems or turned into axioms.

**The existing family inventory is not yet a statement-by-statement exhaustive
index.** Each family below therefore needs both an inventory pass and a proof
pass. An equation label alone is not necessarily a theorem, and unnumbered
claims also need accounting. For example, the mixed assembly includes MA11–MA15,
not only the MA1–MA10 limit spine; the general short note also includes S31.
Finishing MA3 does not by itself close either whole note.

Unresolved mathematics remains a separate research queue. In particular, an
unproved sample-wise limit cannot be inferred from the separately proved
Poisson expectation bridge. Universal convergence statements refuted by the
written obstructions require the negative theorem, not a proof of the false
universal statement. No new classification, rate, or variance conjecture is
implicitly added to this finite port programme.

## Definition of done

Completion requires **all** of the following, not a theorem-count percentage:

- [ ] Inventory every asserted result and nonredundant supporting claim in the
  pinned sources, including the earlier written dependencies cited by the
  family table. Record exclusions with reasons; check unnumbered prose too.
- [ ] Map each claim to a compiled theorem with matching quantifiers,
  hypotheses, dimensions, topology, regularity and normalization, or to an
  explicitly proved stronger result and its specialization.
- [ ] Derive physical order, interval volumes, transport, asymptotic estimates
  and independent geometric targets. A structure containing the desired jet,
  area identity, coefficient or limit does not discharge the producer.
- [ ] Preserve the original discrete observable, closed causal order and
  probability law. Prove deterministic results before their separate
  original-law expected results. Include complete complements in obstructions.
- [ ] Supply independently expanded theorem-contract regressions and genuine
  nonvacuous members. A definition, `Goal : Prop`, conditional wrapper or
  selected example is not the quantified family theorem.
- [ ] Account for all written-only and conditional rows in
  [PROOF_COVERAGE.md](PROOF_COVERAGE.md); none may disappear merely because a
  nearby narrower theorem has been proved.
- [ ] Pass the full local warnings-as-errors and transitive-axiom audit on the
  final frozen inputs, retaining the unchanged whitelist and all-source scope;
  attach an input-pinned receipt and check applicable CI on that exact head.
- [ ] Perform a final intended-statement comparison against the pinned written
  sources. Independent human mathematical/physical/literature review remains
  separate; Lean compilation is not a claim that that review occurred.

## Dependency-ordered family queue

Every unchecked row is still open. The order is a port order, not a promise
that every written argument will survive specification unchanged. If a gap or
contradiction is discovered, record it rather than weaken the theorem.

| Batch | Required completion | Status |
| --- | --- | --- |
| Existing checked foundation | Preserve the graph, ellipsoid, null-plane cap, combined/independent two-face, flat 2D/3D, thin 4D torus and probability results listed in the inventory; map their supporting written claims | Proofs checked; exhaustive source correspondence still required |
| Mixed one-tip theorem | Whole smooth MA class; actual radial geometry, induced Lorentzian joint area, actual scalar transport, deterministic limit and separate expected limit | Finite-density reduction checked; geometry and concentration in progress |
| Mixed supporting note closure | MA4 complete frontier/strata and nullity, quantitative MA5, MA7 ancillary geometry, MA9 actual weight representation, MA11 weighted generator/partition response, MA12 uniform tip control, MA13–MA15 specialized probability statements; NM estimates and nonvacuity/calibrations | Open; do not infer from the unweighted limit |
| Shared curved short spine | S1–S8 physical interval/measure, S9–S18 derivative/contact bounds, S19 full cone, S20–S25 face, S26–S29 joint, S30 full assembly and S31 specialization | Open |
| Controlled curved two-face pilot | Actual curved interval, short/long producers, cutoff compensation and independent curvature/joint target for the stated fixed metric | Finite-density expectation checked; limit open in Lean |
| C2 | Every stated curved 2D G-SS member, actual weighted rectangle unions and long remainder, global target and expected limit | Open beyond the checked flat subclass |
| FLAT positive clause | Every stated flat G-SS member in dimensions 2–4, physical lifted unions counted once and complete target restoration | Open beyond restricted coordinate/quotient classes |
| SW and sphere/circle dependencies | Every stated smooth positive conformal factor, actual weighted lenses, both orientations/endpoints and closing-fibre estimates | Measured-order foundation checked; asymptotics open |
| CO | Actual compact-torus geometry, all minimizing paths, CO13 physical model-to-action matching, all complements, negative complete-action growth and independent target | Open; arithmetic model certificate is not completion |
| K/H/O and quotient families | Klein-bottle, reflection-holonomy and 7D focusing obstructions with complete surviving response; thin/first-cut torus families at every stated dimension | Only thin 4D end-to-end theorem checked |
| Higher-dimensional Minkowski | A1–A3, dimension-dependent actual overlap jets and critical remainders, 5D/6D short/long transfer and complete target | Scalar kernels and fixed-regulator wedge checked; geometric assembly open |
| Positive curved long families | RPL/FCDC, Rosen plane wave PW-4 and Hadamard-optical HO-4, including required external geometric inputs at the stated scope | Open |
| Remaining established null/mixed families | All-dimensional ND, selected two-tip TT-A/TT-B, conformal one-cone CC and regular conformal two-tip CT, with whole unions, masks and all extra strata | Open |

The source links and exact scope boundaries for these families are in the
[principal-claim table](PROOF_COVERAGE.md#principal-written-claims-and-the-missing-lean-terms).
No existing issue or historical PR is closed or reinterpreted by this queue.

## First batch: obligations that cannot be hidden

The new `MixedNullContract.lean` restores the original smooth floor assumption
in `AdmissibleMixedNull`, separately from Lipschitz-only `MixedNullData`.
Its radial set, supremum radius, spacetime joint, parameterization and candidate
area are defined without reference to the action. **Definitions alone prove
none of their geometric properties.** In particular:

- [ ] Prove the unique positive radial root, uniform bounds and exact radial
  domain; derive continuity and the smooth regularity needed for joint area.
- [ ] Prove the parameterization reaches exactly the actual spacetime joint,
  with no multiplicity; derive its differential and positive Lorentzian Gram
  determinant, not the ambient Euclidean spacetime-area density.
- [ ] Justify the measure/area interpretation and the independent spatial
  integral identity. The intermediate `mixedNullSpatialLimit` is not itself a
  substitute geometric target.
- [ ] Derive actual finite-density coordinate transport, measurable weights,
  integrable domination and concentration. The one-sided Gaussian helper must
  be instantiated with these producers, not treated as their proof.
- [ ] Assemble the deterministic and original-law expected limits, and check
  the entire smooth class rather than only constants or a sine floor.
- [ ] Close the additional mixed-note statements listed above separately.

## Efficient verification

Use targeted module builds while constructing proofs. Fetch the intended
ancestor and use the incremental checker for integrated edit-loop feedback;
on this stacked branch the base is `origin/lean-coverage-audit`, not an
unrelated or stale branch. Run the full local `formal/check.sh` once the batch's
proof inputs are frozen, before review/handoff. Further changes affecting Lean
validation require another full gate; documentation-only changes do not.

Keep the default two source workers unless memory/swap headroom justifies a
change. Parallel proof work owns disjoint files; do not run duplicate full
audits. Retain the existing visited-set optimization, but never cache proof
acceptance across source edits or shrink the audited source set. The preceding
42-minute warm audit is a measurement, not a timing guarantee for future work.

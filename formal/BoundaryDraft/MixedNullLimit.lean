import BoundaryDraft.MixedNullSurface
import BoundaryDraft.MixedNullConcentration
import BoundaryDraft.MixedNullElementary
import BoundaryDraft.MixedNullFrontier
import BoundaryDraft.MixedNullWeighted

/-!
# The smooth one-tip mixed deterministic and expected limits (MA3)

The scalar transport and singular spatial domination are actual producers.
`MixedNullSurface` independently proves that the globally one-to-one joint
parameterization has positive induced Lorentzian Gram Jacobian equal to its
radius squared. Its finite measure is therefore the parametric induced joint
area, not ambient Euclidean spacetime area or an action-defined measure.

The expectation remains the original finite-Poisson integral. No sample-wise
convergence, weighted asymptotic estimate, density rate or general null/mixed
classification follows from these theorems.
-/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The analytic limit actually needs only Lipschitz data. At this weaker
scope the sphere integral is not being advertised as smooth induced area. -/
theorem MixedNullData.continuumMean_tendsto_area {H : Spatial → ℝ}
    (hH : MixedNullData H) :
    Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      atTop (𝓝 (mixedNullArea H)) := by
  rw [← hH.spatialLimit_eq_area]
  exact hH.continuumMean_tendsto_spatialLimit

/-- MA3 for the entire original smooth mixed class, with the independently
justified induced-area measure as the target. -/
theorem AdmissibleMixedNull.continuumMean_limit {H : Spatial → ℝ}
    (hH : AdmissibleMixedNull H) :
    Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      atTop (𝓝 ((mixedNullJointMeasure H).real univ)) := by
  rw [hH.toMixedNullData.jointMeasure_real_univ]
  exact hH.toMixedNullData.continuumMean_tendsto_area

/-- The separate original-law expectation transfer uses the exact
positive-density equality; it does not interchange a sample-wise limit. -/
theorem AdmissibleMixedNull.expectedBDGAction_limit {H : Spatial → ℝ}
    (hH : AdmissibleMixedNull H) :
    Tendsto (fun ρ : ℝ => expectedBDGAction ρ (mixedNullRegion H))
      atTop (𝓝 ((mixedNullJointMeasure H).real univ)) := by
  apply hH.continuumMean_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hH.toMixedNullData.expectedBDGAction_eq hρ).symm

end BoundaryDraft

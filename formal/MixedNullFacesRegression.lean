import BoundaryDraft.MixedNullFaces
import BoundaryDraft.MixedNullGeometryExamples

/-! Expanded face/normal contracts, including the genuinely nonaffine floor.
These tests do not infer an action limit from face geometry. -/

open Set Filter
open scoped Topology
noncomputable section
namespace MixedNullFacesRegression
open BoundaryDraft

example {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) (x : JointSpace)
    (u : Metric.sphere (0 : JointSpace) 1) :
    let n : Spacetime := (Real.sqrt (1 - ‖graphGradient H x‖ ^ 2))⁻¹ •
      (Fin.cons (1 : ℝ) ((-graphGradient H x : JointSpace) : Spatial) : Spacetime)
    let k : Spacetime := Fin.cons (1 : ℝ) ((-(u : JointSpace)) : Spatial)
    0 < n 0 ∧ minkowskiInner n n = 1 ∧ minkowskiInner k k = 0 ∧
      0 < minkowskiInner n k ∧
      minkowskiInner n k = (1 - inner (𝕜 := ℝ) (graphGradient H x) (u : JointSpace)) /
        Real.sqrt (1 - ‖graphGradient H x‖ ^ 2) := by
  have h : 0 < mixedNullFloorNormal H x 0 ∧
      minkowskiInner (mixedNullFloorNormal H x) (mixedNullFloorNormal H x) = 1 ∧
      minkowskiInner (mixedNullConeNormal u) (mixedNullConeNormal u) = 0 ∧
      0 < minkowskiInner (mixedNullFloorNormal H x) (mixedNullConeNormal u) ∧
      minkowskiInner (mixedNullFloorNormal H x) (mixedNullConeNormal u) =
        (1 - inner (𝕜 := ℝ) (graphGradient H x) (u : JointSpace)) /
          Real.sqrt (1 - ‖graphGradient H x‖ ^ 2) :=
    ⟨(hH.floorNormal_future_unit x).1, (hH.floorNormal_future_unit x).2,
      (mixedNullConeNormal_future_null u).2, hH.normals_inner_pos x u,
      AdmissibleMixedNull.normals_inner x u⟩
  simpa only [mixedNullFloorNormal, mixedNullConeNormal, jointUnitNormal, norm_neg,
    jointVector] using h

example {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) (x v : JointSpace) (hv : v ≠ 0) :
    0 < -minkowskiInner
      (fderiv ℝ (fun y : JointSpace => (Fin.cons (-H y) (y : Spatial) : Spacetime)) x v)
      (fderiv ℝ (fun y : JointSpace => (Fin.cons (-H y) (y : Spatial) : Spacetime)) x v) :=
  hH.lowerParam_spacelike x v hv

example {H : Spatial → ℝ} (hH : AdmissibleMixedNull H) :
    ContDiffAt ℝ ⊤ (fun x : JointSpace => (Fin.cons (-H x) (x : Spatial) : Spacetime)) 0 :=
  hH.lowerParam_smooth.contDiffAt

example (x : JointSpace) (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ (fun y : JointSpace => (Fin.cons (-‖y‖) (y : Spatial) : Spacetime)) x :=
  mixedNullUpperParam_smooth hx

example : ¬DifferentiableAt ℝ
    (fun y : JointSpace => (Fin.cons (-‖y‖) (y : Spatial) : Spacetime)) (0 : JointSpace) :=
  mixedNullUpperParam_not_differentiableAt_zero

example (H : Spatial → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (x : JointSpace) (u : Metric.sphere (0 : JointSpace) 1) :
    1 - k ≤ 1 - fderiv ℝ (fun y : JointSpace => H y) x (u : JointSpace) :=
  mixedNull_radial_derivative_lower_bound H hk hLip x u

example {H : Spatial → ℝ} (hH : MixedNullData H) (u : MixedNullDirection) :
    Tendsto (fun r : ℝ => r - H (r • (u : JointSpace))) atTop atTop :=
  hH.radial_gap_tendsto_atTop u

example {H : Spatial → ℝ} (hH : MixedNullData H) (u : MixedNullDirection) {r : ℝ}
    (hr : 0 ≤ r) :
    r • (u : JointSpace) ∈ closure {x : JointSpace | ‖x‖ < H x} ↔
      r ≤ mixedNullRadius H u :=
  hH.closed_radial_domain u hr

-- The exact admitted sine floor supplies all the nonvacuous geometric inputs.
example : ContDiffAt ℝ ⊤
    (fun x : JointSpace => (Fin.cons (-(1 + (1 / 5) * Real.sin (x 0)))
      (x : Spatial) : Spacetime)) 0 :=
  mixedNull_sine_admissible.lowerParam_smooth.contDiffAt

example (u : MixedNullDirection) :
    fderiv ℝ (fun x : JointSpace => (1 + (1 / 5) * Real.sin (x 0)) - ‖x‖)
      (mixedNullRadius mixedNullSineFloor u • (u : JointSpace)) ≠ 0 :=
  mixedNull_sine_admissible.joint_level_fderiv_ne_zero u

example (x : JointSpace) (u : MixedNullDirection) (a : ℝ) :
    mixedNullFloorNormal mixedNullSineFloor x ≠ a • mixedNullConeNormal u :=
  mixedNull_sine_admissible.normals_not_parallel x u a

end MixedNullFacesRegression

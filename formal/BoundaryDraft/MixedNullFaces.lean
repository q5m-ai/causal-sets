import BoundaryDraft.MixedNullSurface
import BoundaryDraft.MixedNullFrontier
import BoundaryDraft.JointMetric
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-! Actual smooth mixed-face differentials and the future timelike/null normals.
These are graph parameterizations of the faces already identified set-theoretically.
No face derivative, normal pairing or transversality is an admissibility field.
A manifold-with-boundary atlas and generator reparameterization are separate claims. -/

open Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The actual lower graph, including its smooth axis point. -/
def mixedNullLowerParam (H : Spatial → ℝ) (x : JointSpace) : Spacetime :=
  jointVector (-H x) x

/-- The actual upper cone graph. It is smooth away from the spatial origin. -/
def mixedNullUpperParam (x : JointSpace) : Spacetime := jointVector (-‖x‖) x

/-- Differential of a graph with the indicated scalar differential. -/
def mixedNullGraphDifferential (d : JointSpace →L[ℝ] ℝ) : JointSpace →L[ℝ] Spacetime :=
  LinearMap.toContinuousLinearMap
  { toFun := fun v => jointVector (d v) v
    map_add' := by intro v w; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [jointVector]
    map_smul' := by intro c v; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [jointVector] }

theorem hasFDerivAt_mixedNullGraph {f : JointSpace → ℝ} {d : JointSpace →L[ℝ] ℝ}
    {x : JointSpace} (hf : HasFDerivAt f d x) :
    HasFDerivAt (fun y => jointVector (f y) y) (mixedNullGraphDifferential d) x := by
  apply hasFDerivAt_pi'.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt

theorem mixedNullFace_spatialDistance_zero (x : JointSpace) :
    spatialDistance (x : Spatial) 0 = ‖x‖ := by
  simp only [spatialDistance, zero_sub]
  change ‖-x‖ = ‖x‖
  exact norm_neg _

theorem mixedNullLowerParam_mem {H : Spatial → ℝ} {x : JointSpace} (hx : ‖x‖ ≤ H x) :
    mixedNullLowerParam H x ∈ mixedNullLowerFace H := by
  change spatialDistance (x : Spatial) 0 ≤ H x ∧ -H x = -H x
  exact ⟨by rwa [mixedNullFace_spatialDistance_zero], rfl⟩

theorem mixedNullUpperParam_mem {H : Spatial → ℝ} {x : JointSpace} (hx : ‖x‖ ≤ H x) :
    mixedNullUpperParam x ∈ mixedNullUpperFace H := by
  change spatialDistance (x : Spatial) 0 ≤ H x ∧ -‖x‖ = -spatialDistance (x : Spatial) 0
  rw [mixedNullFace_spatialDistance_zero]
  exact ⟨hx, rfl⟩

/-- The null normal is future directed, with its original marking. -/
def mixedNullConeNormal (u : MixedNullDirection) : Spacetime := jointVector 1 (-(u : JointSpace))

/-- The timelike normal uses the actual Euclidean gradient of the floor. -/
def mixedNullFloorNormal (H : Spatial → ℝ) (x : JointSpace) : Spacetime :=
  jointUnitNormal (-graphGradient H x)

theorem mixedNullConeNormal_future_null (u : MixedNullDirection) :
    0 < mixedNullConeNormal u 0 ∧
      minkowskiInner (mixedNullConeNormal u) (mixedNullConeNormal u) = 0 := by
  constructor
  · simp [mixedNullConeNormal, jointVector]
  · rw [mixedNullConeNormal, minkowskiInner_jointVector, real_inner_self_eq_norm_sq,
      norm_neg, mixedNullDirection_norm]
    norm_num

/-- Exact norm differential at a positive radial point, proved from the squared
norm derivative. In particular this is not an assigned cone tangent. -/
theorem mixedNull_norm_hasFDerivAt (u : MixedNullDirection) {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (fun x : JointSpace => ‖x‖) (innerSL ℝ (u : JointSpace))
      (r • (u : JointSpace)) := by
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mixedNullDirection_norm, mul_one]
  have hx : r • (u : JointSpace) ≠ 0 := by
    apply norm_pos_iff.mp
    rwa [hn]
  have hd := (contDiffAt_norm ℝ hx).differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  have he := (hd.hasFDerivAt.mul hd.hasFDerivAt).unique
    (by simpa only [pow_two] using
      (hasStrictFDerivAt_norm_sq (r • (u : JointSpace))).hasFDerivAt)
  have hde : fderiv ℝ (fun x : JointSpace => ‖x‖) (r • (u : JointSpace)) =
      innerSL ℝ (u : JointSpace) := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L : JointSpace →L[ℝ] ℝ => L v) he
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, innerSL_apply, real_inner_smul_left, hn, two_smul] at hv
    change _ = inner (𝕜 := ℝ) (u : JointSpace) v
    nlinarith
  rw [← hde]
  exact hd.hasFDerivAt

theorem mixedNullUpperParam_smooth {x : JointSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ mixedNullUpperParam x := by
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (contDiffAt_norm ℝ hx).neg
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt

/-- Unlike the smooth lower axis point, the upper graph really is singular
at the tip; this is a differential statement, not an inference from null volume. -/
theorem mixedNullUpperParam_not_differentiableAt_zero :
    ¬DifferentiableAt ℝ mixedNullUpperParam (0 : JointSpace) := by
  intro hd
  have ht := (differentiableAt_pi.mp hd) 0
  have hn : DifferentiableAt ℝ (fun x : JointSpace => ‖x‖) 0 := by
    simpa only [mixedNullUpperParam, jointVector, Fin.cons_zero, neg_neg] using ht.neg
  exact not_differentiableAt_norm_zero JointSpace hn

theorem mixedNullUpperParam_fderiv (u : MixedNullDirection) {r : ℝ} (hr : 0 < r)
    (v : JointSpace) :
    fderiv ℝ mixedNullUpperParam (r • (u : JointSpace)) v =
      jointGraphTangent (-(u : JointSpace)) v := by
  unfold mixedNullUpperParam
  rw [(hasFDerivAt_mixedNullGraph (mixedNull_norm_hasFDerivAt u hr).neg).fderiv]
  simp [mixedNullGraphDifferential, jointGraphTangent, inner_neg_left]

theorem mixedNullUpperParam_normal_orthogonal (u : MixedNullDirection) {r : ℝ}
    (hr : 0 < r) (v : JointSpace) :
    minkowskiInner (mixedNullConeNormal u)
      (fderiv ℝ mixedNullUpperParam (r • (u : JointSpace)) v) = 0 := by
  rw [mixedNullUpperParam_fderiv u hr]
  simp [mixedNullConeNormal, jointGraphTangent]

theorem mixedNullUpperParam_radial_null (u : MixedNullDirection) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ mixedNullUpperParam (r • (u : JointSpace)) (u : JointSpace) =
      -mixedNullConeNormal u := by
  rw [mixedNullUpperParam_fderiv u hr]
  simp only [jointGraphTangent, inner_neg_left, real_inner_self_eq_norm_sq,
    mixedNullDirection_norm, one_pow]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [mixedNullConeNormal, jointVector]

/-- MA's quantitative radial derivative bound keeps the specifically supplied
Lipschitz constant, rather than only asserting positivity. -/
theorem mixedNull_radial_derivative_lower_bound (H : Spatial → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (x : JointSpace) (u : MixedNullDirection) :
    1 - k ≤ 1 - fderiv ℝ (fun y : JointSpace => H y) x (u : JointSpace) := by
  have hl : LipschitzWith ⟨k, hk⟩ (fun y : JointSpace => H y) :=
    LipschitzWith.of_dist_le_mul hLip
  have hn := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := x)
  have hb := (fderiv ℝ (fun y : JointSpace => H y) x).le_opNorm (u : JointSpace)
  rw [mixedNullDirection_norm, mul_one, Real.norm_eq_abs] at hb
  have hd := (le_abs_self _).trans (hb.trans hn)
  change _ ≤ k at hd
  linarith

theorem MixedNullData.radial_gap_tendsto_atTop {H : Spatial → ℝ} (hH : MixedNullData H)
    (u : MixedNullDirection) :
    Tendsto (fun r : ℝ => r - H (r • (u : JointSpace))) atTop atTop := by
  obtain ⟨k, _, hk1, hLip⟩ := hH.euclidean_lipschitz
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop (max 0 ((b + H 0) / (1 - k)))] with r hr
  have hr0 : 0 ≤ r := (le_max_left _ _).trans hr
  have hbr := (div_le_iff₀ (sub_pos.mpr hk1)).mp ((le_max_right _ _).trans hr)
  have hb := hLip (r • (u : JointSpace)) 0
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
    mixedNullDirection_norm, mul_one] at hb
  have hu := (le_abs_self _).trans hb
  nlinarith

theorem MixedNullData.closed_radial_domain {H : Spatial → ℝ} (hH : MixedNullData H)
    (u : MixedNullDirection) {r : ℝ} (hr : 0 ≤ r) :
    r • (u : JointSpace) ∈ closure (mixedNullSpatialDomain H) ↔ r ≤ mixedNullRadius H u := by
  rw [hH.closure_spatialDomain]
  simp only [mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    mixedNullDirection_norm, mul_one]
  have hh := (hH.radial_gap_strictMono u).le_iff_le (a := r) (b := mixedNullRadius H u)
  rw [← hH.radius_root u, sub_self] at hh
  simpa only [sub_nonpos] using hh

namespace AdmissibleMixedNull
variable {H : Spatial → ℝ} (hH : AdmissibleMixedNull H)
include hH

theorem gradient_lt_one (x : JointSpace) : ‖graphGradient H x‖ < 1 := by
  obtain ⟨k, hk, hk1, hb⟩ := hH.toMixedNullData.euclidean_lipschitz
  have hl : LipschitzWith ⟨k, hk⟩ (fun y : JointSpace => H y) :=
    LipschitzWith.of_dist_le_mul hb
  rw [← graphSlope, graphSlope_eq_norm_fderiv]
  exact (norm_fderiv_le_of_lipschitz ℝ hl).trans_lt hk1

theorem lowerParam_smooth : ContDiff ℝ ⊤ (mixedNullLowerParam H) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hH.smooth_floor.neg
  · exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

theorem lowerParam_fderiv (x v : JointSpace) :
    fderiv ℝ (mixedNullLowerParam H) x v = jointGraphTangent (-graphGradient H x) v := by
  have hd := ((hH.smooth_floor.differentiable (by simp)) x).hasFDerivAt.neg
  unfold mixedNullLowerParam
  rw [(hasFDerivAt_mixedNullGraph hd).fderiv]
  simp [mixedNullGraphDifferential, jointGraphTangent, graph_differential_eq_inner]

theorem lowerParam_spacelike (x v : JointSpace) (hv : v ≠ 0) :
    0 < -minkowskiInner (fderiv ℝ (mixedNullLowerParam H) x v)
      (fderiv ℝ (mixedNullLowerParam H) x v) := by
  rw [hH.lowerParam_fderiv]
  exact jointGraphTangent_spacelike (by simpa using hH.gradient_lt_one x) hv

theorem floorNormal_future_unit (x : JointSpace) :
    0 < mixedNullFloorNormal H x 0 ∧
      minkowskiInner (mixedNullFloorNormal H x) (mixedNullFloorNormal H x) = 1 :=
  jointUnitNormal_future_unit (by simpa using hH.gradient_lt_one x)

theorem floorNormal_orthogonal (x v : JointSpace) :
    minkowskiInner (mixedNullFloorNormal H x) (fderiv ℝ (mixedNullLowerParam H) x v) = 0 := by
  rw [hH.lowerParam_fderiv]
  exact jointUnitNormal_orthogonal _ _

omit hH in
theorem normals_inner (x : JointSpace) (u : MixedNullDirection) :
    minkowskiInner (mixedNullFloorNormal H x) (mixedNullConeNormal u) =
      (1 - inner (𝕜 := ℝ) (graphGradient H x) (u : JointSpace)) /
        Real.sqrt (1 - ‖graphGradient H x‖ ^ 2) := by
  simp only [mixedNullFloorNormal, mixedNullConeNormal, jointUnitNormal,
    minkowskiInner_smul_left, minkowskiInner_jointVector, inner_neg_left,
    inner_neg_right, neg_neg, norm_neg, mul_one]
  ring

theorem normals_inner_pos (x : JointSpace) (u : MixedNullDirection) :
    0 < minkowskiInner (mixedNullFloorNormal H x) (mixedNullConeNormal u) := by
  rw [normals_inner]
  apply div_pos
  · simpa only [graph_differential_eq_inner] using hH.radial_derivative_pos u x
  · apply Real.sqrt_pos.mpr
    have hg := hH.gradient_lt_one x
    nlinarith [norm_nonneg (graphGradient H x)]

/-- The actual future normals are not parallel; this is stronger than merely
choosing different normal names and follows from their timelike/null norms. -/
theorem normals_not_parallel (x : JointSpace) (u : MixedNullDirection) (a : ℝ) :
    mixedNullFloorNormal H x ≠ a • mixedNullConeNormal u := by
  intro he
  have hn := (hH.floorNormal_future_unit x).2
  rw [he, minkowskiInner_smul_left, minkowskiInner_smul_right,
    (mixedNullConeNormal_future_null u).2] at hn
  norm_num at hn

/-- The actual spatial joint level has nonzero full differential at every joint
parameter point. A regular-level manifold structure is not assumed or supplied. -/
theorem joint_level_fderiv_ne_zero (u : MixedNullDirection) :
    fderiv ℝ (fun x : JointSpace => H x - ‖x‖)
      (mixedNullRadius H u • (u : JointSpace)) ≠ 0 := by
  let x := mixedNullRadius H u • (u : JointSpace)
  have hn := mixedNull_norm_hasFDerivAt u (hH.toMixedNullData.radius_pos u)
  have hh := ((hH.smooth_floor.differentiable (by simp)) x).hasFDerivAt
  rw [(hh.sub hn).fderiv]
  intro hz
  have hv := congrArg (fun L : JointSpace →L[ℝ] ℝ => L (u : JointSpace)) hz
  have hp := hH.radial_derivative_pos u x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    innerSL_apply, real_inner_self_eq_norm_sq, mixedNullDirection_norm, one_pow] at hv
  linarith

end AdmissibleMixedNull
end BoundaryDraft

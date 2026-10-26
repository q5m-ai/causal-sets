import BoundaryDraft.MixedNullCoareaWeighted
import BoundaryDraft.MixedNullSurface
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual weighted cone endpoint and its generator term (NM8 / MA11)

The endpoint is `mixedNullWeightedGlobalWeight H w 0`, not a supplied response.
The general radial theorem permits an arbitrary tip value and only requires
an interior derivative, its weighted integrability, and the actual joint
endpoint limit. The C1 corollary derives these inputs from a spacetime weight.
This file does not identify general absolutely continuous traces with integral
primitives: that wider FTC obligation is not asserted as proved here.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- The actual past-directed generator, in the unchanged spacetime coordinates. -/
def mixedNullGeneratorPoint (u : MixedNullDirection) (r : ℝ) : Spacetime :=
  Fin.cons (-r) (r • (u : JointSpace) : JointSpace)

/-- The radial trace includes the time dependence of the source weight. -/
def mixedNullGeneratorTrace (w : Spacetime → ℝ) (u : MixedNullDirection) (r : ℝ) : ℝ :=
  w (mixedNullGeneratorPoint u r)

/-- Minus the time derivative plus the spatial directional derivative. -/
def mixedNullGeneratorDerivative (w : Spacetime → ℝ) (u : MixedNullDirection) (r : ℝ) : ℝ :=
  -(fderiv ℝ w (mixedNullGeneratorPoint u r)) (timeAxis 1) +
    (fderiv ℝ w (mixedNullGeneratorPoint u r)) (Fin.cons 0 (u : JointSpace))

theorem continuous_mixedNullGeneratorPoint :
    Continuous (fun p : MixedNullDirection × ℝ => mixedNullGeneratorPoint p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_snd.neg
  · exact continuous_snd.mul
      ((EuclideanSpace.proj j).continuous.comp (continuous_subtype_val.comp continuous_fst))

theorem hasDerivAt_mixedNullGeneratorPoint (u : MixedNullDirection) (r : ℝ) :
    HasDerivAt (mixedNullGeneratorPoint u) (Fin.cons (-1) (u : JointSpace)) r := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hasDerivAt_id r).neg
  · simpa using (hasDerivAt_id r).mul_const (u.val j)

theorem contDiff_mixedNullGeneratorPoint (u : MixedNullDirection) :
    ContDiff ℝ 1 (mixedNullGeneratorPoint u) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contDiff_id.neg
  · exact contDiff_id.mul contDiff_const

theorem contDiff_mixedNullGeneratorTrace {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w)
    (u : MixedNullDirection) : ContDiff ℝ 1 (mixedNullGeneratorTrace w u) :=
  hw.comp (contDiff_mixedNullGeneratorPoint u)

/-- The derivative is the total generator derivative, not a spatial derivative. -/
theorem hasDerivAt_mixedNullGeneratorTrace {w : Spacetime → ℝ}
    (u : MixedNullDirection) (r : ℝ) (hw : DifferentiableAt ℝ w (mixedNullGeneratorPoint u r)) :
    HasDerivAt (mixedNullGeneratorTrace w u) (mixedNullGeneratorDerivative w u r) r := by
  have h := hw.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_mixedNullGeneratorPoint u r)
  have hv : (Fin.cons (-1) (u : JointSpace) : Spacetime) =
      -(timeAxis 1) + Fin.cons 0 (u : JointSpace) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  simpa only [mixedNullGeneratorTrace, mixedNullGeneratorDerivative, hv, map_add,
    map_neg, Function.comp_def] using h

theorem continuous_mixedNullGeneratorDerivative {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Continuous (fun p : MixedNullDirection × ℝ => mixedNullGeneratorDerivative w p.1 p.2) := by
  have hf := (hw.continuous_fderiv le_rfl).comp continuous_mixedNullGeneratorPoint
  apply (hf.clm_apply continuous_const).neg.add
  apply hf.clm_apply
  apply continuous_pi
  intro i
  refine Fin.cases continuous_const (fun j => ?_) i
  exact (EuclideanSpace.proj j).continuous.comp (continuous_subtype_val.comp continuous_fst)

/-- Boundedness, not omission of the tip, proves the vanishing endpoint. No
continuity of the trace at zero is assumed. -/
theorem mixedNull_generator_tip_zero {f : ℝ → ℝ} {C : ℝ} (hb : ∀ r, ‖f r‖ ≤ C) :
    Tendsto (fun r => r ^ 2 * f r) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun r : ℝ => r ^ 2 * C)
  · exact Eventually.of_forall fun r => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left (hb r) (sq_nonneg r)
  · simpa using ((continuous_id.pow 2).mul continuous_const).tendsto (0 : ℝ)

/-- A bounded measurable trace has an integrable radial response. -/
theorem mixedNull_intervalIntegrable_radialTrace {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ r, ‖f r‖ ≤ C) (R : ℝ) :
    IntervalIntegrable (fun r => r * f r) volume 0 R := by
  apply IntervalIntegrable.mono_fun' (g := fun r : ℝ => C * |r|)
    ((continuous_const.mul continuous_abs).intervalIntegrable 0 R)
    (measurable_id.mul hf).aestronglyMeasurable
  exact Eventually.of_forall fun r => by
    change ‖r * f r‖ ≤ C * |r|
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hb r) (abs_nonneg r)).trans_eq (mul_comm _ _)

/-- The one-dimensional NM8 identity. The derivative exists on the OPEN
radial interval; the tip is controlled by boundedness, and the joint value
is fixed by a genuine one-sided endpoint limit. This is not advertised as
the general absolutely-continuous-trace FTC. -/
theorem mixedNull_generator_integration_by_parts {f g : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R) (hf : Measurable f) (hb : ∀ r, ‖f r‖ ≤ C)
    (hd : ∀ r ∈ Ioo 0 R, HasDerivAt f (g r) r)
    (hend : Tendsto f (𝓝[<] R) (𝓝 (f R)))
    (hg : IntervalIntegrable (fun r => r ^ 2 * g r) volume 0 R) :
    2 * (∫ r in (0 : ℝ)..R, r * f r) =
      R ^ 2 * f R - ∫ r in (0 : ℝ)..R, r ^ 2 * g r := by
  have hi := mixedNull_intervalIntegrable_radialTrace hf hb R
  have hprod (r : ℝ) (hr : r ∈ Ioo 0 R) :
      HasDerivAt (fun r => r ^ 2 * f r) (2 * (r * f r) + r ^ 2 * g r) r := by
    convert ((hasDerivAt_id r).pow 2).mul (hd r hr) using 1
    simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR hprod
    ((hi.const_mul 2).add hg)
    ((mixedNull_generator_tip_zero hb).mono_left nhdsWithin_le_nhds)
    (((continuous_id.pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hend)
  rw [intervalIntegral.integral_add (hi.const_mul 2) hg,
    intervalIntegral.integral_const_mul, sub_zero] at h
  simp only [id_eq] at h
  linarith

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem integrable_generator_joint_trace {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    Integrable (fun u : MixedNullDirection => mixedNullRadius H u ^ 2 *
      mixedNullGeneratorTrace w u (mixedNullRadius H u)) (volume : Measure JointSpace).toSphere := by
  simpa only [mixedNullGeneratorTrace, mixedNullGeneratorPoint, mixedNullJointParam,
    Function.comp_def, mul_comm] using hH.integrable_radius_sq.bdd_mul'
    (hw.comp hH.continuous_jointParam.measurable).aestronglyMeasurable
    (Eventually.of_forall fun u => hb (mixedNullJointParam H u))

/-- The cone response measure is exactly `2 r dr` at the actual zero endpoint. -/
theorem weightedGlobalWeight_generator_response {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        2 * r * mixedNullGeneratorTrace w u r) ∂(volume : Measure JointSpace).toSphere := by
  simp_rw [mul_assoc (2 : ℝ), intervalIntegral.integral_const_mul, integral_const_mul]
  rw [hH.weightedGlobalWeight_zero hw hb]
  unfold mixedNullGeneratorTrace mixedNullGeneratorPoint
  ring

/-- The actual NM4 endpoint satisfies NM8 for the stated radial derivative
hypotheses. Angular differentiability is not required. The last two inputs
are precisely radial and angular integrability, not an assumed identity. -/
theorem weightedGlobalWeight_generator_of_hasDerivAt {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (g : MixedNullDirection → ℝ → ℝ)
    (hd : ∀ u r, r ∈ Ioo 0 (mixedNullRadius H u) →
      HasDerivAt (mixedNullGeneratorTrace w u) (g u r) r)
    (hend : ∀ u, Tendsto (mixedNullGeneratorTrace w u)
      (𝓝[<] (mixedNullRadius H u)) (𝓝 (mixedNullGeneratorTrace w u (mixedNullRadius H u))))
    (hg : ∀ u, IntervalIntegrable (fun r => r ^ 2 * g u r) volume 0 (mixedNullRadius H u))
    (hgi : Integrable (fun u : MixedNullDirection =>
      ∫ r in (0 : ℝ)..mixedNullRadius H u, r ^ 2 * g u r) (volume : Measure JointSpace).toSphere) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        mixedNullGeneratorTrace w u (mixedNullRadius H u) ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u, r ^ 2 * g u r)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_generator_response hw hb,
    ← integral_sub (hH.integrable_generator_joint_trace hw hb) hgi]
  apply integral_congr_ae
  filter_upwards [] with u
  simp_rw [mul_assoc (2 : ℝ), intervalIntegral.integral_const_mul]
  exact mixedNull_generator_integration_by_parts (hH.radius_pos u)
    (hw.comp (continuous_mixedNullGeneratorPoint.comp
      (continuous_const.prodMk continuous_id)).measurable)
    (fun r => hb (mixedNullGeneratorPoint u r)) (hd u) (hend u) (hg u)

/-- The iterated original response is absolutely integrable for C1 weights. -/
theorem integrable_generator_response {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Integrable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      2 * r * mixedNullGeneratorTrace w u r) (volume : Measure JointSpace).toSphere := by
  have hc : Continuous (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      2 * r * mixedNullGeneratorTrace w u r) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((continuous_const.mul continuous_snd).mul
        (hw.continuous.comp continuous_mixedNullGeneratorPoint)) hH.continuous_radius
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Smooth weights supply the entire angular correction's integrability on the
compact sphere, without any global derivative bound. -/
theorem integrable_generator_correction {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Integrable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      r ^ 2 * mixedNullGeneratorDerivative w u r) (volume : Measure JointSpace).toSphere := by
  have hc : Continuous (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      r ^ 2 * mixedNullGeneratorDerivative w u r) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((continuous_snd.pow 2).mul (continuous_mixedNullGeneratorDerivative hw)) hH.continuous_radius
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Absolute radial derivative integrals are themselves integrable over the
sphere for C1 weights. Thus the iterated correction is not only conditionally
integrable after radial cancellation. -/
theorem integrable_generator_abs_correction {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Integrable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      ‖r ^ 2 * mixedNullGeneratorDerivative w u r‖) (volume : Measure JointSpace).toSphere := by
  have hc : Continuous (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      ‖r ^ 2 * mixedNullGeneratorDerivative w u r‖) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (((continuous_snd.pow 2).mul (continuous_mixedNullGeneratorDerivative hw)).norm)
      hH.continuous_radius
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- C1 NM8 with the actual total time-plus-spatial generator derivative. No
weighted action limit is assumed or concluded by this endpoint identity. -/
theorem weightedGlobalWeight_generator_C1 {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace))
          ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        r ^ 2 * (-(fderiv ℝ w (mixedNullGeneratorPoint u r)) (timeAxis 1) +
          (fderiv ℝ w (mixedNullGeneratorPoint u r)) (Fin.cons 0 (u : JointSpace))))
        ∂(volume : Measure JointSpace).toSphere := by
  apply hH.weightedGlobalWeight_generator_of_hasDerivAt hw.continuous.measurable hb
    (mixedNullGeneratorDerivative w)
  · intro u r _
    exact hasDerivAt_mixedNullGeneratorTrace u r (hw.differentiable le_rfl).differentiableAt
  · intro u
    exact (hw.continuous.comp (continuous_mixedNullGeneratorPoint.comp
      (continuous_const.prodMk continuous_id))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · intro u
    exact ((continuous_id.pow 2).mul ((continuous_mixedNullGeneratorDerivative hw).comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  · exact hH.integrable_generator_correction hw

/-- Generator-constant angular weights require no angular differentiability,
and their value on the axis may be arbitrary. This is the actual endpoint
response, not a definition of a weighted area. -/
theorem weightedGlobalWeight_generator_constant {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) (ψ : MixedNullDirection → ℝ)
    (htrace : ∀ u r, 0 < r → mixedNullGeneratorTrace w u r = ψ u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * ψ u
        ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_generator_response hw hb]
  apply integral_congr_ae
  filter_upwards [] with u
  calc
    (∫ r in (0 : ℝ)..mixedNullRadius H u, 2 * r * mixedNullGeneratorTrace w u r) =
        ∫ r in (0 : ℝ)..mixedNullRadius H u, 2 * r * ψ u := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (hH.radius_pos u).le] at hr
      dsimp only
      by_cases hz : r = 0
      · simp [hz]
      · rw [htrace u r (lt_of_le_of_ne hr.1 (Ne.symm hz))]
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
      ring

/-- The independently defined parametric joint measure supplies the joint-trace
interpretation with unit coefficient. For a smooth floor, `MixedNullSurface`
separately proves that this measure is induced Lorentzian area. -/
theorem weightedGlobalWeight_generator_constant_joint {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) (ψ : MixedNullDirection → ℝ)
    (htrace : ∀ u r, 0 < r → mixedNullGeneratorTrace w u r = ψ u) :
    4 * mixedNullWeightedGlobalWeight H w 0 = ∫ p, w p ∂mixedNullJointMeasure H := by
  rw [hH.weightedGlobalWeight_generator_constant hw hb ψ htrace, hH.integral_jointMeasure w hw]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show w (mixedNullJointParam H u) = ψ u from htrace u _ (hH.radius_pos u)]

end MixedNullData
end BoundaryDraft

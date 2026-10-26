import BoundaryDraft.MixedNullGeneratorTransport
import BoundaryDraft.MixedNullErrorExtension
import BoundaryDraft.MixedNullWeightedContinuity
import BoundaryDraft.MixedNullFrontier
import BoundaryDraft.MixedNullGeometryExamples

/-!
# NM8 and the actual weighted-action limit without global bounds

Every continuous spacetime weight is bounded on the compact region closure.
The local extension theorem therefore applies without changing the original
weight outside the geometry. C1 regularity supplies the generator integration
by parts; clipping is used only for the independently proved scalar limit,
never differentiated. General absolutely continuous traces remain separate.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft
namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- The actual closed vertical fibre lies in the compact region closure. -/
theorem closed_fibre_mem_closure (x : JointSpace) {t : ℝ}
    (ht : t ∈ Icc (-H x) (-‖x‖)) :
    Fin.cons t (x : Spatial) ∈ closure (mixedNullRegion H) := by
  rw [hH.closure_region]
  have hd : spatialDistance (x : Spatial) 0 = ‖x‖ := by
    simp only [spatialDistance, zero_sub]
    change ‖-x‖ = ‖x‖
    exact norm_neg x
  simpa only [mixedNullClosedRegion, mem_setOf_eq, spatialPart_cons, Fin.cons_zero, hd] using ht

/-- Compactness produces the local value bound; no global bound on the
original weight is assumed or inferred. -/
theorem exists_weightBound_of_continuous {w : Spacetime → ℝ} (hw : Continuous w) :
    ∃ M : ℝ, 0 ≤ M ∧ MixedNullWeightBound H w M := by
  obtain ⟨M, hM⟩ := hH.isBounded_region.isCompact_closure.exists_bound_of_continuousOn hw.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x _ t ht
  exact (hM _ (hH.closed_fibre_mem_closure x ht)).trans (le_max_left _ _)

/-- Clipping agrees with the original trace at every positive interior radius. -/
theorem clipWeight_eq_on_generator {w : Spacetime → ℝ} {M : ℝ}
    (hb : MixedNullWeightBound H w M) (u : MixedNullDirection) {r : ℝ}
    (hr : r ∈ Ioo 0 (mixedNullRadius H u)) :
    mixedNullClipWeight M w (mixedNullGeneratorPoint u r) = w (mixedNullGeneratorPoint u r) := by
  have hx := (hH.radial_domain u hr.1.le).mpr hr.2
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr.1]
  have hh : r < H (r • (u : JointSpace)) := by
    change ‖r • (u : JointSpace)‖ < _ at hx
    rwa [hn] at hx
  exact mixedNullClipWeight_eq (hb _ hx (-r) ⟨by linarith, by rw [hn]⟩)

/-- Local boundedness really kills the tip term. The proof transfers the
bounded-trace squeeze on a genuine interval next to zero; no tip value or
continuity of the weight is assumed here. -/
theorem generator_tip_zero_local {w : Spacetime → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : MixedNullWeightBound H w M) (u : MixedNullDirection) :
    Tendsto (fun r => r ^ 2 * w (mixedNullGeneratorPoint u r)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun r => r ^ 2 * mixedNullClipWeight M w (mixedNullGeneratorPoint u r))
      (𝓝[>] 0) (𝓝 0) := (mixedNull_generator_tip_zero
    (fun r => mixedNullClipWeight_bound hM w (mixedNullGeneratorPoint u r))).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (hH.radius_pos u)] with r hr
  rw [hH.clipWeight_eq_on_generator hb u hr]

/-- The local coarea endpoint has the unchanged radial response measure. -/
theorem weightedGlobalWeight_generator_response_local {w : Spacetime → ℝ}
    (hw : Measurable w) {M : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        2 * r * mixedNullGeneratorTrace w u r) ∂(volume : Measure JointSpace).toSphere := by
  simp_rw [mul_assoc (2 : ℝ), intervalIntegral.integral_const_mul, integral_const_mul]
  rw [hH.weightedGlobalWeight_zero_local hw hM hb]
  unfold mixedNullGeneratorTrace mixedNullGeneratorPoint
  ring

/-- Compact angular geometry gives joint-trace integrability for every
continuous weight, even when it is unbounded outside the region. -/
theorem integrable_generator_joint_trace_continuous {w : Spacetime → ℝ} (hw : Continuous w) :
    Integrable (fun u : MixedNullDirection => mixedNullRadius H u ^ 2 *
      w (mixedNullJointParam H u)) (volume : Measure JointSpace).toSphere :=
  ((hH.continuous_radius.pow 2).mul (hw.comp hH.continuous_jointParam)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- NM8 with an explicit local value bound only. No derivative of a clipped
weight is used: the interval ledger differentiates the original C1 trace. -/
theorem weightedGlobalWeight_generator_C1_local {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {M : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * w (mixedNullJointParam H u)
        ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        r ^ 2 * mixedNullGeneratorDerivative w u r) ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_generator_response_local hw.continuous.measurable hM hb,
    ← integral_sub (hH.integrable_generator_joint_trace_continuous hw.continuous)
      (hH.integrable_generator_correction hw)]
  apply integral_congr_ae
  filter_upwards [] with u
  have hd (r : ℝ) : deriv (mixedNullGeneratorTrace w u) r = mixedNullGeneratorDerivative w u r :=
    (hasDerivAt_mixedNullGeneratorTrace u r (hw.differentiable le_rfl _)).deriv
  simpa only [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul, sub_zero, hd, mixedNullGeneratorTrace,
    mixedNullGeneratorPoint, mixedNullJointParam] using
    mixedNull_generator_interval_ledger (contDiff_mixedNullGeneratorTrace hw u) 0 (mixedNullRadius H u)

/-- NM8 for ALL C1 spacetime weights: compactness discharges the local bound.
In particular no bounded-exterior assumption excludes coordinate time. -/
theorem weightedGlobalWeight_generator_C1_unbounded {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * w (mixedNullJointParam H u)
        ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        r ^ 2 * mixedNullGeneratorDerivative w u r) ∂(volume : Measure JointSpace).toSphere := by
  obtain ⟨M, hM, hb⟩ := hH.exists_weightBound_of_continuous hw.continuous
  exact hH.weightedGlobalWeight_generator_C1_local hw hM hb

/-- The actual original weighted action converges for every continuous
spacetime weight. Clipping changes neither its point nor full-partner pair
term, and supplies the hypotheses of the existing continuity producer. -/
theorem weightedContinuumMean_tendsto_globalWeight_continuous {w : Spacetime → ℝ}
    (hw : Continuous w) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (4 * mixedNullWeightedGlobalWeight H w 0)) := by
  obtain ⟨M, hM, hb⟩ := hH.exists_weightBound_of_continuous hw
  have hc : Continuous (mixedNullClipWeight M w) := continuous_const.max (continuous_const.min hw)
  have ht (x : JointSpace) : Continuous (fun t : ℝ => mixedNullClipWeight M w (Fin.cons t (x : Spatial))) := by
    apply hc.comp
    apply continuous_pi
    intro i
    exact Fin.cases continuous_id (fun _ => continuous_const) i
  have hlim := hH.weightedContinuumMean_tendsto_globalWeight hc.measurable
    (mixedNullClipWeight_bound hM w) (fun x _ => (ht x).continuousAt)
  simpa only [hH.weightedContinuumMean_clip_eq hb, weightedGlobalWeight_clip_eq hb] using hlim

/-- MA11 for every C1 spacetime source weight, using the independently proved
weighted action limit and the actual NM8 endpoint identity. -/
theorem weightedContinuumMean_generator_limit_C1 {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w) atTop
      (𝓝 ((∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace))
          ∂(volume : Measure JointSpace).toSphere) -
        ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
          r ^ 2 * (-(fderiv ℝ w (mixedNullGeneratorPoint u r)) (timeAxis 1) +
            (fderiv ℝ w (mixedNullGeneratorPoint u r)) (Fin.cons 0 (u : JointSpace))))
          ∂(volume : Measure JointSpace).toSphere)) := by
  have hlim := hH.weightedContinuumMean_tendsto_globalWeight_continuous hw.continuous
  rw [hH.weightedGlobalWeight_generator_C1_unbounded hw] at hlim
  exact hlim

end MixedNullData

/-- The original coordinate-time weight has total generator derivative -1. -/
theorem mixedNull_generator_coordinateTime_derivative (u : MixedNullDirection) (r : ℝ) :
    mixedNullGeneratorDerivative (fun p : Spacetime => p 0) u r = -1 := by
  have hd := hasDerivAt_mixedNullGeneratorTrace u r
    ((contDiff_apply ℝ ℝ (0 : Fin 4) : ContDiff ℝ 1 (fun p : Spacetime => p 0)).differentiable le_rfl _)
  exact hd.unique (hasDerivAt_id r).neg

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Actual coordinate time, not its clipped extension, has this zero-endpoint
response. The nonzero generator correction is retained in the calculation. -/
theorem weightedGlobalWeight_coordinateTime :
    4 * mixedNullWeightedGlobalWeight H (fun p : Spacetime => p 0) 0 =
      -(2 / 3 : ℝ) * ∫ u : MixedNullDirection, mixedNullRadius H u ^ 3
        ∂(volume : Measure JointSpace).toSphere := by
  have h := hH.weightedGlobalWeight_generator_C1_unbounded
    (contDiff_apply ℝ ℝ (0 : Fin 4))
  have hf (u : MixedNullDirection) :
      (∫ r in (0 : ℝ)..mixedNullRadius H u, r ^ 2 * (-1 : ℝ)) = -(mixedNullRadius H u ^ 3) / 3 := by
    rw [intervalIntegral.integral_mul_const, integral_pow]
    norm_num
    ring
  simp only [mixedNull_generator_coordinateTime_derivative, hf, mixedNullJointParam,
    Fin.cons_zero] at h
  have he (r : ℝ) : r ^ 2 * -r = -(r ^ 3) := by ring
  simp_rw [he, integral_div, integral_neg] at h
  rw [h]
  ring

theorem weightedContinuumMean_coordinateTime_limit :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (fun p : Spacetime => p 0))
      atTop (𝓝 (-(2 / 3 : ℝ) * ∫ u : MixedNullDirection, mixedNullRadius H u ^ 3
        ∂(volume : Measure JointSpace).toSphere)) := by
  have hlim := hH.weightedContinuumMean_tendsto_globalWeight_continuous (continuous_apply 0)
  rw [hH.weightedGlobalWeight_coordinateTime] at hlim
  exact hlim

end MixedNullData

/-- Expanded coordinate-time regression: the unchanged full-partner action,
with a truly unbounded spacetime weight, not a clipped observable. -/
theorem mixedNull_coordinateTime_constant_limit {T : ℝ} (hT : 0 < T) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ p in mixedNullRegion (fun _ : Spatial => T), p 0) -
        ρ * ∫ p in mixedNullRegion (fun _ : Spatial => T), p 0 *
          ∫ q in mixedNullRegion (fun _ : Spatial => T) ∩ causalFuture p,
            bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)))
      atTop (𝓝 (-8 * Real.pi * T ^ 3 / 3)) := by
  have hlim := (mixedNull_constant_admissible hT).toMixedNullData.weightedContinuumMean_coordinateTime_limit
  simp_rw [mixedNullRadius_constant hT] at hlim
  rw [integral_const, smul_eq_mul, jointSphere_area] at hlim
  convert hlim using 1
  congr 1
  ring

/-- This regression cannot accidentally acquire a global boundedness premise. -/
theorem mixedNull_coordinateTime_not_globally_bounded :
    ¬ ∃ M : ℝ, ∀ p : Spacetime, ‖p 0‖ ≤ M := by
  rintro ⟨M, hM⟩
  have h := hM (timeAxis (|M| + 1))
  simp only [timeAxis_zero, Real.norm_eq_abs, abs_of_pos (show 0 < |M| + 1 by positivity)] at h
  linarith [le_abs_self M]

end BoundaryDraft

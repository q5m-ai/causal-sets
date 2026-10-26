import BoundaryDraft.MixedNullGeneratorTransport
import BoundaryDraft.MixedNullGeometryExamples

/-!
Independent NM8 contracts: actual coarea endpoint, full total derivative,
bounded-tip control, nonsmooth angular weights, signed time-dependent terms,
and nonaffine/affine Jacobians with both interval endpoints. The derivative
hypotheses below are not labelled as general absolute continuity.
-/

open MeasureTheory Set Filter BoundaryDraft
open scoped Topology Interval
noncomputable section
namespace MixedNullGeneratorRegression

example {f : ℝ → ℝ} {M : ℝ} (hb : ∀ r, |f r| ≤ M) :
    Tendsto (fun r => r ^ 2 * f r) (𝓝 0) (𝓝 0) :=
  mixedNull_generator_tip_zero (by simpa only [Real.norm_eq_abs] using hb)

-- Tip continuity is deliberately absent; the bounded tip value may jump.
example : Tendsto (fun r : ℝ => r ^ 2 * (if r = 0 then 7 else -1)) (𝓝 0) (𝓝 0) := by
  apply mixedNull_generator_tip_zero (C := 7)
  intro r
  split_ifs <;> norm_num

-- Expanded radial derivative hypotheses, rather than an assumed endpoint identity.
example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : Measurable w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M)
    (d : MixedNullDirection → ℝ → ℝ)
    (hd : ∀ u r, r ∈ Ioo 0 (mixedNullRadius H u) →
      HasDerivAt (fun s => w (Fin.cons (-s) (s • (u : JointSpace) : JointSpace))) (d u r) r)
    (hend : ∀ u : MixedNullDirection, Tendsto (fun r => w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
      (𝓝[<] (mixedNullRadius H u))
      (𝓝 (w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace)))))
    (hi : ∀ u, IntervalIntegrable (fun r => r ^ 2 * d u r) volume 0 (mixedNullRadius H u))
    (hai : Integrable (fun u : MixedNullDirection =>
      ∫ r in (0 : ℝ)..mixedNullRadius H u, r ^ 2 * d u r) (volume : Measure JointSpace).toSphere) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace))
          ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u, r ^ 2 * d u r)
        ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_generator_of_hasDerivAt hw hb d hd hend hi hai

example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace))
          ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius H u,
        r ^ 2 * (-(fderiv ℝ w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace))) (timeAxis 1) +
          (fderiv ℝ w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
            (Fin.cons 0 (u : JointSpace)))) ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_generator_C1 hw hb

example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) :
    Integrable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..mixedNullRadius H u,
      ‖r ^ 2 * (-(fderiv ℝ w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace))) (timeAxis 1) +
        (fderiv ℝ w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
          (Fin.cons 0 (u : JointSpace)))‖) (volume : Measure JointSpace).toSphere :=
  hH.integrable_generator_abs_correction hw

-- A signed, discontinuous angular weight: no angular smoothness is available.
def angularSign (p : Spacetime) : ℝ := if 0 ≤ p 1 then 1 else -1

theorem angularSign_measurable : Measurable angularSign := by
  exact measurable_const.ite (isClosed_le continuous_const (continuous_apply 1)).measurableSet
    measurable_const

theorem angularSign_bound (p : Spacetime) : ‖angularSign p‖ ≤ 1 := by
  unfold angularSign
  split_ifs <;> norm_num

theorem angularSign_trace (u : MixedNullDirection) {r : ℝ} (hr : 0 < r) :
    mixedNullGeneratorTrace angularSign u r = if 0 ≤ u.val 0 then 1 else -1 := by
  change (if 0 ≤ r * u.val 0 then (1 : ℝ) else -1) = if 0 ≤ u.val 0 then 1 else -1
  simp only [mul_nonneg_iff_of_pos_left hr]

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    4 * mixedNullWeightedGlobalWeight H angularSign 0 =
      ∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * (if 0 ≤ u.val 0 then 1 else -1)
        ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_generator_constant angularSign_measurable angularSign_bound _
    (fun u _ hr => angularSign_trace u hr)

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    4 * mixedNullWeightedGlobalWeight H angularSign 0 = ∫ p, angularSign p ∂mixedNullJointMeasure H :=
  hH.weightedGlobalWeight_generator_constant_joint angularSign_measurable angularSign_bound _
    (fun u _ hr => angularSign_trace u hr)

-- The globally bounded extension agrees with the genuine time weight on the
-- whole unit-cap cone trace. It is not falsely claimed to be globally C1.
def clampedTime (p : Spacetime) : ℝ := max (-1) (min 0 (p 0))

theorem clampedTime_continuous : Continuous clampedTime :=
  continuous_const.max (continuous_const.min (continuous_apply 0))

theorem clampedTime_bound (p : Spacetime) : ‖clampedTime p‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) ((min_le_left _ _).trans (by norm_num))

theorem clampedTime_trace (u : MixedNullDirection) {r : ℝ} (hr : r ∈ Icc 0 1) :
    mixedNullGeneratorTrace clampedTime u r = -r := by
  change max (-1 : ℝ) (min 0 (-r)) = -r
  rw [min_eq_right (by linarith [hr.1]), max_eq_right (by linarith [hr.2])]

theorem clampedTime_trace_derivative (u : MixedNullDirection) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    HasDerivAt (mixedNullGeneratorTrace clampedTime u) (-1) r := by
  apply (hasDerivAt_id r).neg.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact clampedTime_trace u ⟨hs.1.le, hs.2.le⟩

private theorem radius_one (u : MixedNullDirection) :
    mixedNullRadius (fun _ : Spatial => (1 : ℝ)) u = 1 :=
  mixedNullRadius_constant (by norm_num) u

private theorem radial_time_correction : (∫ r in (0 : ℝ)..1, r ^ 2 * (-1 : ℝ)) = -1 / 3 := by
  rw [intervalIntegral.integral_mul_const, integral_pow]
  norm_num

/-- The total generator correction is genuinely nonzero and negative. -/
theorem clampedTime_correction :
    (∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius (fun _ : Spatial => (1 : ℝ)) u,
      r ^ 2 * (-1 : ℝ)) ∂(volume : Measure JointSpace).toSphere) = -4 * Real.pi / 3 := by
  simp_rw [radius_one, radial_time_correction]
  rw [integral_const, smul_eq_mul, jointSphere_area]
  ring

theorem clampedTime_joint_trace :
    (∫ u : MixedNullDirection, mixedNullRadius (fun _ : Spatial => (1 : ℝ)) u ^ 2 *
      mixedNullGeneratorTrace clampedTime u (mixedNullRadius (fun _ : Spatial => (1 : ℝ)) u)
        ∂(volume : Measure JointSpace).toSphere) = -4 * Real.pi := by
  simp_rw [radius_one, clampedTime_trace _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
  norm_num only [one_pow, one_mul]
  rw [integral_const, smul_eq_mul, jointSphere_area]
  ring

/-- Actual NM8 calibration: W_t(0) is negative and is not the joint trace / 4. -/
theorem clampedTime_endpoint :
    mixedNullWeightedGlobalWeight (fun _ : Spatial => (1 : ℝ)) clampedTime 0 =
      -2 * Real.pi / 3 := by
  have hH := (mixedNull_constant_admissible (show (0 : ℝ) < 1 by norm_num)).toMixedNullData
  have h := hH.weightedGlobalWeight_generator_of_hasDerivAt
    clampedTime_continuous.measurable clampedTime_bound (fun _ _ => -1)
    (fun u r hr => clampedTime_trace_derivative u (by simpa only [radius_one] using hr))
    (fun u => (clampedTime_continuous.comp (continuous_mixedNullGeneratorPoint.comp
      (continuous_const.prodMk continuous_id))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (fun _ => ((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _)
    (by simpa only [radius_one, radial_time_correction] using
      (integrable_const (-1 / 3 : ℝ) : Integrable (fun _ : MixedNullDirection => (-1 / 3 : ℝ))
        (volume : Measure JointSpace).toSphere))
  rw [clampedTime_joint_trace, clampedTime_correction] at h
  linarith

example : mixedNullWeightedGlobalWeight (fun _ : Spatial => (1 : ℝ)) clampedTime 0 < 0 := by
  rw [clampedTime_endpoint]
  linarith [Real.pi_pos]

example : (-4 * Real.pi / 3 : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]

-- A bounded smooth time-dependent weight also works for the nonaffine floor.
def sineTime (p : Spacetime) : ℝ := Real.sin (p 0)

theorem sineTime_C1 : ContDiff ℝ 1 sineTime := Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (0 : Fin 4))

theorem sineTime_bound (p : Spacetime) : ‖sineTime p‖ ≤ 1 := by
  simpa only [sineTime, Real.norm_eq_abs] using Real.abs_sin_le_one (p 0)

theorem sineTime_total_derivative (u : MixedNullDirection) (r : ℝ) :
    mixedNullGeneratorDerivative sineTime u r = -Real.cos r := by
  have hd := hasDerivAt_mixedNullGeneratorTrace u r (sineTime_C1.differentiable le_rfl _)
  have hs : HasDerivAt (mixedNullGeneratorTrace sineTime u) (-Real.cos r) r := by
    simpa only [id_eq, Real.cos_neg, mul_neg, mul_one, mixedNullGeneratorTrace,
      mixedNullGeneratorPoint, sineTime, Fin.cons_zero] using (hasDerivAt_id r).neg.sin
  exact hd.unique hs

example :
    4 * mixedNullWeightedGlobalWeight mixedNullSineFloor sineTime 0 =
      (∫ u : MixedNullDirection, mixedNullRadius mixedNullSineFloor u ^ 2 *
        Real.sin (-mixedNullRadius mixedNullSineFloor u) ∂(volume : Measure JointSpace).toSphere) +
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius mixedNullSineFloor u,
        r ^ 2 * Real.cos r) ∂(volume : Measure JointSpace).toSphere := by
  have h := mixedNull_sine_admissible.toMixedNullData.weightedGlobalWeight_generator_C1
    sineTime_C1 sineTime_bound
  change 4 * mixedNullWeightedGlobalWeight mixedNullSineFloor sineTime 0 =
    (∫ u : MixedNullDirection, mixedNullRadius mixedNullSineFloor u ^ 2 *
      Real.sin (-mixedNullRadius mixedNullSineFloor u) ∂(volume : Measure JointSpace).toSphere) -
    ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..mixedNullRadius mixedNullSineFloor u,
      r ^ 2 * mixedNullGeneratorDerivative sineTime u r) ∂(volume : Measure JointSpace).toSphere at h
  simpa only [sineTime_total_derivative, mul_neg, intervalIntegral.integral_neg,
    integral_neg, sub_neg_eq_add] using h

-- A genuine nonaffine, increasing radial coordinate, with f(0)=0 and f(1)=2.
def cubicParameter (a : ℝ) : ℝ := a + a ^ 3

theorem cubicParameter_C1 : ContDiff ℝ 1 cubicParameter := contDiff_id.add (contDiff_id.pow 3)

theorem cubicParameter_strictMono : StrictMono cubicParameter :=
  strictMono_id.add (show StrictMono (fun a : ℝ => a ^ 3) from
    (show Odd (3 : ℕ) from ⟨1, by norm_num⟩).strictMono_pow)

theorem cubicParameter_deriv (a : ℝ) : deriv cubicParameter a = 1 + 3 * a ^ 2 := by
  change deriv (fun x : ℝ => x + x ^ 3) a = _
  simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one] using
    ((hasDerivAt_id a).add ((hasDerivAt_id a).pow 3)).deriv

example : cubicParameter 2 ≠ 2 * cubicParameter 1 := by norm_num [cubicParameter]

-- All three terms, and both endpoints, survive a nonlinear pullback.
example (a b : ℝ) :
    (∫ s in a..b, 2 * (s + s ^ 3) * (1 + 3 * s ^ 2) * (-(s + s ^ 3))) =
      (b + b ^ 3) ^ 2 * (-(b + b ^ 3)) - (a + a ^ 3) ^ 2 * (-(a + a ^ 3)) -
        ∫ s in a..b, (s + s ^ 3) ^ 2 * (-(1 + 3 * s ^ 2)) := by
  have h := mixedNull_generator_reparameterized_ledger cubicParameter_C1
    (contDiff_id.neg : ContDiff ℝ 1 (fun r : ℝ => -r)) a b
  have hd (s : ℝ) : deriv (fun a => -cubicParameter a) s = -(1 + 3 * s ^ 2) := by
    rw [deriv.neg, cubicParameter_deriv]
  simp only [id_eq] at h
  simp_rw [cubicParameter_deriv, hd] at h
  simpa only [cubicParameter] using h

example {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (a b c : ℝ) :
    (b ^ 2 * φ b - a ^ 2 * φ a - ∫ r in a..b, r ^ 2 * deriv φ r) +
      (c ^ 2 * φ c - b ^ 2 * φ b - ∫ r in b..c, r ^ 2 * deriv φ r) =
      c ^ 2 * φ c - a ^ 2 * φ a - ∫ r in a..c, r ^ 2 * deriv φ r :=
  mixedNull_generator_cut_ledger hφ a b c

-- The actual mixed endpoint is transported, not merely a scalar test integral.
example {w : Spacetime → ℝ} (hw : ContDiff ℝ 1 w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) :
    4 * mixedNullWeightedGlobalWeight (fun _ : Spatial => (2 : ℝ)) w 0 =
      (∫ u : MixedNullDirection, 4 * w (Fin.cons (-2) ((2 : ℝ) • (u : JointSpace) : JointSpace))
        ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..1,
        (a + a ^ 3) ^ 2 * deriv (fun s =>
          w (Fin.cons (-(s + s ^ 3)) ((s + s ^ 3) • (u : JointSpace) : JointSpace))) a)
        ∂(volume : Measure JointSpace).toSphere := by
  have hH := (mixedNull_constant_admissible (show (0 : ℝ) < 2 by norm_num)).toMixedNullData
  have h := (hH.weightedGlobalWeight_generator_reparameterized hw hb
    (fun _ => cubicParameter) (fun _ => 1) (fun _ => cubicParameter_C1)
    (fun _ => cubicParameter_strictMono) (fun _ => by norm_num [cubicParameter])
    (fun u => by rw [mixedNullRadius_constant (by norm_num)]; norm_num [cubicParameter])).2
  simpa only [cubicParameter, one_pow, one_add_one_eq_two,
    show (2 : ℝ) ^ 2 = 4 by norm_num, mixedNullGeneratorPoint] using h

-- Direction-dependent affine rescaling: no angular regularity premise on α.
example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M)
    (α : MixedNullDirection → ℝ) (hα : ∀ u, 0 < α u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..(mixedNullRadius H u / α u),
        2 * α u ^ 2 * a * w (Fin.cons (-(α u * a)) ((α u * a) • (u : JointSpace) : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_response_affine hw hb α hα

example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M)
    (α : MixedNullDirection → ℝ) (hα : ∀ u, 0 < α u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 *
        w (Fin.cons (-mixedNullRadius H u) (mixedNullRadius H u • (u : JointSpace) : JointSpace))
          ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..(mixedNullRadius H u / α u),
        α u ^ 2 * a ^ 2 * deriv (fun s =>
          w (Fin.cons (-(α u * s)) ((α u * s) • (u : JointSpace) : JointSpace))) a)
        ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_generator_affine hw hb α hα

example (u : MixedNullDirection) (α a : ℝ) :
    HasDerivAt (fun s => (Fin.cons (-(α * s)) ((α * s) • (u : JointSpace) : JointSpace) : Spacetime))
      (-(α • (Fin.cons 1 (-u.val) : Spacetime))) a :=
  mixedNull_generator_affine_marking u α a

end MixedNullGeneratorRegression

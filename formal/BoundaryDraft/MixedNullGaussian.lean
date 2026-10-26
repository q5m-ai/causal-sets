import BoundaryDraft.MixedNullIntegration
import BoundaryDraft.NullGaussianRight
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The actual vertical Gaussian fibre, in proper-time-squared coordinates. -/
open MeasureTheory Filter Set
set_option maxHeartbeats 400000
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- Positive square-root Jacobian on a vertical fibre. The `max` is only a
globally continuous extension to negative parameters and changes no positive
proper-time-squared value. -/
def mixedNullFibreJacobian (r s : ℝ) : ℝ :=
  (2 * Real.sqrt (r ^ 2 + max 0 s))⁻¹

/-- Actual finite upper endpoint; the cutoff is a derived indicator, not an
assumed radial weight or jet. -/
def mixedNullFibreWeight (r L s : ℝ) : ℝ :=
  (Iio (L ^ 2 - r ^ 2)).indicator (mixedNullFibreJacobian r) s

private theorem fibre_sqrt_pos (r : ℝ) (hr : 0 < r) (s : ℝ) :
    0 < Real.sqrt (r ^ 2 + max 0 s) := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_pos_of_pos hr, le_max_left (0 : ℝ) s]

private theorem fibre_jacobian_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (mixedNullFibreJacobian r) := by
  unfold mixedNullFibreJacobian
  apply Continuous.inv₀
  · fun_prop
  · intro s
    exact (mul_ne_zero (by norm_num) (ne_of_gt (fibre_sqrt_pos r hr s)))

private theorem fibre_jacobian_le (r : ℝ) (hr : 0 < r) (s : ℝ) :
    0 ≤ mixedNullFibreJacobian r s ∧ mixedNullFibreJacobian r s ≤ (2 * r)⁻¹ := by
  have hs : 0 ≤ max 0 s := le_max_left _ _
  have hp := fibre_sqrt_pos r hr s
  have hsq : r ≤ Real.sqrt (r ^ 2 + max 0 s) := by
    calc
      r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr.le).symm
      _ ≤ Real.sqrt (r ^ 2 + max 0 s) := Real.sqrt_le_sqrt (by linarith)
  unfold mixedNullFibreJacobian
  refine ⟨inv_nonneg.mpr (by positivity), ?_⟩
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) * r)
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)))

/-- Measurability and a uniform pointwise bound follow from the explicit
Jacobian and the original finite-height cutoff. -/
theorem mixedNullFibreWeight_measurable (r L : ℝ) (hr : 0 < r) :
    Measurable (mixedNullFibreWeight r L) :=
  (fibre_jacobian_continuous r hr).measurable.indicator measurableSet_Iio

theorem mixedNullFibreWeight_bound (r L s : ℝ) (hr : 0 < r) :
    ‖mixedNullFibreWeight r L s‖ ≤ (2 * r)⁻¹ := by
  unfold mixedNullFibreWeight
  by_cases h : s ∈ Iio (L ^ 2 - r ^ 2)
  · rw [Set.indicator_of_mem h, Real.norm_eq_abs,
      abs_of_nonneg (fibre_jacobian_le r hr s).1]
    exact (fibre_jacobian_le r hr s).2
  · rw [Set.indicator_of_not_mem h, norm_zero]
    positivity

/-- At strictly interior spatial points the finite upper cutoff is absent
in a neighborhood of zero, so the actual weight approaches `1/(2r)`. -/
theorem mixedNullFibreWeight_zero (r L : ℝ) (hr : 0 < r) (hrL : r < L) :
    mixedNullFibreWeight r L 0 = (2 * r)⁻¹ := by
  have ha : 0 < L ^ 2 - r ^ 2 := by nlinarith
  simp [mixedNullFibreWeight, mixedNullFibreJacobian, ha, Real.sqrt_sq hr.le]

theorem mixedNullFibreWeight_continuousAt (r L : ℝ) (hr : 0 < r) (hrL : r < L) :
    ContinuousAt (mixedNullFibreWeight r L) 0 := by
  have ha : 0 < L ^ 2 - r ^ 2 := by nlinarith
  exact (fibre_jacobian_continuous r hr).continuousAt.congr_of_eventuallyEq
    (by filter_upwards [Iio_mem_nhds ha] with s hs
        exact Set.indicator_of_mem hs _)


/-- Change variables `s=t²-r²` in the *actual* finite time fibre. The
square-root Jacobian is obtained from a smooth substitution on `r≤t≤L`;
no derivative of `sqrt` at the cone tip is invoked. -/
theorem mixedNull_fibre_substitution (r L ρ : ℝ) (hr : 0 < r) (hrL : r < L) :
    (∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2)) =
      ∫ s in (0 : ℝ)..(L ^ 2 - r ^ 2),
        Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullFibreJacobian r s := by
  let g : ℝ → ℝ := fun s =>
    Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullFibreJacobian r s
  have hg : Continuous g := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.pow 2))).mul
        (fibre_jacobian_continuous r hr)
  have hder (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 - r ^ 2) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).sub_const (r ^ 2) using 1; simp [id_eq, mul_comm]
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := r) (b := L) (g := g)
    (fun t _ => hder t) (by fun_prop) hg
  simp only [Function.comp_def, sub_self] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  have hrt : r ≤ t := by
    have hI : t ∈ Icc r L := by simpa [uIcc_of_le hrL.le] using ht
    exact hI.1
  have htpos : 0 < t := hr.trans_le hrt
  have hnonneg : 0 ≤ t ^ 2 - r ^ 2 := by nlinarith
  have he : mixedNullFibreJacobian r (t ^ 2 - r ^ 2) * (2 * t) = 1 := by
    unfold mixedNullFibreJacobian
    rw [max_eq_right hnonneg, show r ^ 2 + (t ^ 2 - r ^ 2) = t ^ 2 by ring,
      Real.sqrt_sq htpos.le]
    field_simp
  dsimp [g]
  apply Eq.symm
  calc
    _ = Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2) *
        (mixedNullFibreJacobian r (t ^ 2 - r ^ 2) * (2 * t)) := by ring
    _ = _ := by rw [he, mul_one]


/-- The finite fibre equals a Gaussian integral with the explicitly derived
moving cutoff and Jacobian, measured on the fixed positive ray. -/
theorem mixedNull_fibre_as_positive_gaussian (r L ρ : ℝ)
    (hr : 0 < r) (hrL : r < L) :
    (∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullFibreWeight r L s := by
  rw [mixedNull_fibre_substitution r L ρ hr hrL]
  let a := L ^ 2 - r ^ 2
  have ha : 0 ≤ a := by dsimp [a]; nlinarith
  have hset : Iio a ∩ Ioi (0 : ℝ) = Ioo 0 a := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
    tauto
  have hright :
      (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullFibreWeight r L s) =
      ∫ s in Ioo 0 a, Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullFibreJacobian r s := by
    have hfun (s : ℝ) :
        Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullFibreWeight r L s =
        (Iio a).indicator (fun s => Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          mixedNullFibreJacobian r s) s := by
      change _ * (Iio a).indicator (mixedNullFibreJacobian r) s = _
      exact (Set.indicator_mul_right (Iio a)
        (fun s : ℝ => Real.exp (-(Real.pi / 24) * ρ * s ^ 2))
        (mixedNullFibreJacobian r)).symm
    simp_rw [hfun]
    rw [setIntegral_indicator measurableSet_Iio, Set.inter_comm, hset]
  calc
    (∫ s in (0 : ℝ)..a, Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullFibreJacobian r s) =
      ∫ s in Ioo 0 a, Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullFibreJacobian r s := by
          rw [intervalIntegral.integral_of_le ha, integral_Ioc_eq_integral_Ioo]
    _ = _ := hright.symm


/-- The finite vertical fibre has the actual pointwise limit `2/r` at every
strictly interior nonzero spatial point. The upper cutoff was derived from
the region; no radial density limit is assumed. -/
theorem mixedNull_fibre_limit (r L : ℝ) (hr : 0 < r) (hrL : r < L) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      ∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2))
      atTop (𝓝 (2 / r)) := by
  have hlim := nullGaussian_density_limit_right (mixedNullFibreWeight r L)
    (mixedNullFibreWeight_measurable r L hr)
    (mixedNullFibreWeight_continuousAt r L hr hrL).continuousWithinAt
    (2 * r)⁻¹ (fun s _ => mixedNullFibreWeight_bound r L s hr)
  rw [mixedNullFibreWeight_zero r L hr hrL] at hlim
  have he : (4 : ℝ) * (2 * r)⁻¹ = 2 / r := by field_simp; ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  rw [mixedNull_fibre_as_positive_gaussian r L ρ hr hrL]


/-- Uniform finite-density domination by the *spatial* singularity `2/r`,
derived from the actual upper time endpoint and normalized Gaussian mass. -/
theorem mixedNull_fibre_bound (r L ρ : ℝ) (hr : 0 < r) (hrL : r < L)
    (hρ : 0 < ρ) :
    0 ≤ (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2)) ∧
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2)) ≤
        2 / r := by
  let B := mixedNullFibreWeight r L
  let e := (Real.sqrt ρ)⁻¹
  have he : 0 ≤ e := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hi : IntegrableOn (fun u => nullGaussian u * B (e * u)) (Ioi (0 : ℝ)) :=
    integrableOn_nullGaussian_rescaled_right B
      (mixedNullFibreWeight_measurable r L hr) (2 * r)⁻¹
      (fun s _ => mixedNullFibreWeight_bound r L s hr) he
  have hC : IntegrableOn (fun u => nullGaussian u * (2 * r)⁻¹) (Ioi (0 : ℝ)) :=
    integrableOn_nullGaussian.mul_const _
  have hB0 (s : ℝ) : 0 ≤ B s := by
    dsimp [B, mixedNullFibreWeight]
    by_cases hs : s ∈ Iio (L ^ 2 - r ^ 2)
    · rw [Set.indicator_of_mem hs]; exact (fibre_jacobian_le r hr s).1
    · rw [Set.indicator_of_not_mem hs]
  have hn (u : ℝ) :
      0 ≤ nullGaussian u * B (e * u) ∧
      nullGaussian u * B (e * u) ≤ nullGaussian u * (2 * r)⁻¹ := by
    have hg : 0 ≤ nullGaussian u := by unfold nullGaussian; positivity
    have hle : B (e * u) ≤ ‖B (e * u)‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (B (e * u))
    exact ⟨mul_nonneg hg (hB0 _),
      mul_le_mul_of_nonneg_left
        (hle.trans (mixedNullFibreWeight_bound r L _ hr)) hg⟩
  have hlo : 0 ≤ ∫ u in Ioi (0 : ℝ), nullGaussian u * B (e * u) :=
    integral_nonneg fun u => (hn u).1
  have hhi : (∫ u in Ioi (0 : ℝ), nullGaussian u * B (e * u)) ≤ (2 * r)⁻¹ := by
    have hh := integral_mono hi hC (fun u => (hn u).2)
    simpa only [integral_mul_const, integral_nullGaussian, one_mul] using hh
  have hid : (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ t in r..L, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - r ^ 2) ^ 2)) =
      4 * ∫ u in Ioi (0 : ℝ), nullGaussian u * B (e * u) := by
    rw [mixedNull_fibre_as_positive_gaussian r L ρ hr hrL]
    exact nullGaussian_density_rescaling ρ hρ B
  rw [hid]
  have hnorm : (4 : ℝ) * (2 * r)⁻¹ = 2 / r := by field_simp; ring
  constructor
  · exact mul_nonneg (by norm_num) hlo
  · calc
      _ ≤ 4 * (2 * r)⁻¹ := mul_le_mul_of_nonneg_left hhi (by norm_num)
      _ = 2 / r := hnorm

end BoundaryDraft

import BoundaryDraft.MixedNullCoareaPolar

/-! The genuine global MA9 Gaussian action representation. Product
integrability justifies Fubini; the previously proved fibre substitution
is used only after the reciprocal-radius majorant has been checked. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft.MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Absolute integrability of the actual space/sigma integrand. This is a
producer from geometry and positive density, not a Fubini assumption. -/
theorem integrable_coareaGaussian {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : JointSpace × ℝ =>
      Real.exp (-(Real.pi / 24) * ρ * p.2 ^ 2) * mixedNullCoareaKernel H p.2 p.1)
      ((volume : Measure JointSpace).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg : IntegrableOn (fun s : ℝ => Real.exp (-(Real.pi / 24) * ρ * s ^ 2))
      (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (mul_pos (div_pos Real.pi_pos (by norm_num)) hρ)).integrableOn
  have hi := hH.integrable_coareaKernel_zero.mul_prod hg
  apply hi.mono' ((by fun_prop : Measurable (fun p : JointSpace × ℝ =>
      Real.exp (-(Real.pi / 24) * ρ * p.2 ^ 2))).mul
      (hH.measurable_coareaKernel.comp measurable_swap)).aestronglyMeasurable
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hn] with p hp
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (mixedNullCoareaKernel_norm_le H p.2 hp)
    (Real.exp_pos _).le

/-- Absolute integrability of the final global Gaussian integral. -/
theorem integrable_globalWeight_gaussian {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
      mixedNullGlobalWeight H s) (Ioi (0 : ℝ)) := by
  simpa only [integral_const_mul, mixedNullGlobalWeight] using
    (hH.integrable_coareaGaussian hρ).integral_prod_right

/-- The actual vertical integral, changed to sigma and then globally
reordered by Fubini. No origin value or radial cutoff is silently assumed. -/
theorem spatialGaussian_eq_globalWeight {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
      Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullGlobalWeight H s := by
  have hi := hH.integrable_coareaGaussian hρ
  have he : (∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
      Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2)) =
      ∫ x : JointSpace, ∫ s in Ioi (0 : ℝ),
        Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullCoareaKernel H s x := by
    rw [← integral_indicator hH.measurableSet_spatialDomain]
    have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
      apply ae_iff.mpr
      simp
    apply integral_congr_ae
    filter_upwards [hn] with x hx0
    by_cases hx : x ∈ mixedNullSpatialDomain H
    · rw [Set.indicator_of_mem hx, mixedNull_fibre_as_positive_gaussian
        ‖x‖ (H x) ρ (norm_pos_iff.mpr hx0) hx]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact congrArg (fun v => Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * v)
        (coareaKernel_eq_fibreWeight hx hs.le).symm
    · rw [Set.indicator_of_not_mem hx]
      simp only [coareaKernel_eq_zero_of_not_mem hx, mul_zero, integral_zero]
  rw [he, integral_integral_swap hi]
  simp only [integral_const_mul, mixedNullGlobalWeight]

/-- MA9, for the unchanged deterministic action at every positive density. -/
theorem continuumMean_eq_globalWeight {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion H) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          mixedNullGlobalWeight H s := by
  rw [hH.continuumMean_eq_spatialGaussian hρ, hH.spatialGaussian_eq_globalWeight hρ]

/-- MA10's literal `u = sqrt((pi/24)*rho) * sigma` rescaling, with
its displayed coefficient rather than the alternative unit-Gaussian convention. -/
theorem continuumMean_eq_globalWeight_rescaled {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion H) =
      ((4 / Real.sqrt 6) / Real.sqrt (Real.pi / 24)) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2) *
          mixedNullGlobalWeight H (u / Real.sqrt ((Real.pi / 24) * ρ)) := by
  let a := Real.sqrt ((Real.pi / 24) * ρ)
  have hc : 0 < Real.pi / 24 := div_pos Real.pi_pos (by norm_num)
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hc hρ)
  have hs := integral_comp_mul_left_Ioi
    (fun u => Real.exp (-u ^ 2) * mixedNullGlobalWeight H (u / a)) 0 ha
  simp only [mul_zero, smul_eq_mul] at hs
  have he (s : ℝ) : Real.exp (-(a * s) ^ 2) * mixedNullGlobalWeight H (a * s / a) =
      Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullGlobalWeight H s := by
    rw [mul_div_cancel_left₀ s ha.ne', mul_pow,
      show a ^ 2 = (Real.pi / 24) * ρ from Real.sq_sqrt (mul_pos hc hρ).le]
    congr 2
    ring
  simp_rw [he] at hs
  have hcoef : (4 / Real.sqrt 6) * Real.sqrt ρ * a⁻¹ =
      (4 / Real.sqrt 6) / Real.sqrt (Real.pi / 24) := by
    dsimp [a]
    rw [Real.sqrt_mul hc.le, mul_inv_rev]
    have hr : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
    field_simp
    ring
  rw [hH.continuumMean_eq_globalWeight hρ, hs, ← mul_assoc, hcoef]

/-- MA10's common pointwise Gaussian majorant, uniform in the density.
Its spatial coefficient is exactly the written pi*B^2. -/
theorem globalWeight_rescaled_bound {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (ρ u : ℝ) :
    ‖Real.exp (-u ^ 2) * mixedNullGlobalWeight H (u / Real.sqrt ((Real.pi / 24) * ρ))‖ ≤
      Real.pi * (H 0 / (1 - k)) ^ 2 * Real.exp (-u ^ 2) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs, abs_of_nonneg (globalWeight_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hH.globalWeight_bound hk hk1 h _).2 (Real.exp_pos _).le

omit hH in
/-- The MA10 majorant is integrable on the entire fixed positive ray. -/
theorem coareaGaussian_majorant_integrable (B : ℝ) :
    IntegrableOn (fun u : ℝ => Real.pi * B ^ 2 * Real.exp (-u ^ 2)) (Ioi (0 : ℝ)) := by
  simpa only [neg_one_mul] using
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      (Real.pi * B ^ 2)).integrableOn

/-- The coarea route itself now proves the limit, using the actual global
weight and its actual endpoint, rather than wrapping the existing MA3 limit. -/
theorem continuumMean_tendsto_via_globalWeight :
    Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      atTop (𝓝 (mixedNullArea H)) := by
  have hb (s : ℝ) (_hs : 0 ≤ s) :
      ‖mixedNullGlobalWeight H s‖ ≤ mixedNullGlobalWeight H 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (globalWeight_nonneg (H := H) s)]
    exact hH.globalWeight_le_zero s
  have ht := nullGaussian_density_limit_right (mixedNullGlobalWeight H)
    hH.measurable_globalWeight hH.globalWeight_right_continuous
    (mixedNullGlobalWeight H 0) hb
  rw [hH.globalWeight_zero, show 4 * (mixedNullArea H / 4) = mixedNullArea H by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hH.continuumMean_eq_globalWeight hρ).symm

end BoundaryDraft.MixedNullData

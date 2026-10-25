import BoundaryDraft.MixedNullRadial

/-! # Polar evaluation of the actual spatial limiting integral -/
open MeasureTheory Set Filter
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

 theorem lintegral_mixedNull_polar (f : JointSpace → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ∫⁻ u : MixedNullDirection, (∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r ^ 2) * f (r • (u : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere := by
  have hp := (volume : Measure JointSpace).measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : JointSpace)}ᶜ : Set JointSpace), f x.val
        ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p : MixedNullDirection × Ioi (0 : ℝ), f (p.2.val • p.1.val)
        ∂(volume : Measure JointSpace).toSphere.prod (Measure.volumeIoiPow 2) := by
      have ht := hp.symm (homeomorphUnitSphereProd JointSpace).toMeasurableEquiv
      have hh := ht.lintegral_comp (hf.comp measurable_subtype_coe)
      simpa [homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace] using hh.symm
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro u
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      exact lintegral_subtype_comap (μ := volume) measurableSet_Ioi
        (fun r : ℝ => ENNReal.ofReal (r ^ 2) * f (r • (u : JointSpace)))

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

 theorem measurableSet_spatialDomain : MeasurableSet (mixedNullSpatialDomain H) :=
  (isOpen_lt continuous_norm hH.continuous_euclidean).measurableSet

 theorem lintegral_spatialLimit :
    (∫⁻ x in mixedNullSpatialDomain H, ENNReal.ofReal (2 / ‖x‖)) =
      ∫⁻ u : MixedNullDirection, ENNReal.ofReal (mixedNullRadius H u ^ 2)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [← lintegral_indicator hH.measurableSet_spatialDomain,
    lintegral_mixedNull_polar _ ((measurable_const.div continuous_norm.measurable).ennreal_ofReal.indicator
      hH.measurableSet_spatialDomain)]
  apply lintegral_congr
  intro u
  have he : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
      (mixedNullSpatialDomain H).indicator (fun x => ENNReal.ofReal (2 / ‖x‖))
        (r • (u : JointSpace))) = ∫⁻ r in Ioo 0 (mixedNullRadius H u), ENNReal.ofReal (2 * r) := by
    have hcut : (∫⁻ r in Ioi (0 : ℝ),
        (Iio (mixedNullRadius H u)).indicator (fun r => ENNReal.ofReal (2 * r)) r) =
        ∫⁻ r in Ioo 0 (mixedNullRadius H u), ENNReal.ofReal (2 * r) := by
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
      rw [show Iio (mixedNullRadius H u) ∩ Ioi 0 = Ioo 0 (mixedNullRadius H u) by
        ext r; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]]
    rw [← hcut]
    apply setLIntegral_congr_fun measurableSet_Ioi
    filter_upwards [] with r hr
    by_cases hlt : r < mixedNullRadius H u
    · rw [Set.indicator_of_mem ((hH.radial_domain u (le_of_lt hr)).mpr hlt),
        Set.indicator_of_mem (show r ∈ Iio (mixedNullRadius H u) from hlt)]
      have hn : ‖r • (u : JointSpace)‖ = r := by
        rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      rw [hn, ← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 1
      field_simp [(show 0 < r from hr).ne']
      ring
    · rw [Set.indicator_of_not_mem (by simpa only [hH.radial_domain u (le_of_lt hr)]),
        Set.indicator_of_not_mem (show r ∉ Iio (mixedNullRadius H u) from hlt), mul_zero]
  rw [he]
  have hi : IntegrableOn (fun r : ℝ => 2 * r) (Ioo 0 (mixedNullRadius H u)) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_nonneg (by norm_num) hr.1.le)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (hH.radius_pos u).le,
    intervalIntegral.integral_const_mul, integral_id]
  ring

 theorem integrable_spatialLimit : IntegrableOn (fun x : JointSpace => 2 / ‖x‖)
    (mixedNullSpatialDomain H) := by
  refine ⟨(measurable_const.div continuous_norm.measurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity),
    hH.lintegral_spatialLimit]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mp
    hH.integrable_radius_sq.hasFiniteIntegral

/-- Polar identity for the original spatial integral, not a redefined target. -/
 theorem spatialLimit_eq_area : mixedNullSpatialLimit H = mixedNullArea H := by
  unfold mixedNullSpatialLimit mixedNullArea
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
      hH.integrable_spatialLimit.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
      hH.integrable_radius_sq.aestronglyMeasurable,
    hH.lintegral_spatialLimit]

end MixedNullData
end BoundaryDraft

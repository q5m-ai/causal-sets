import BoundaryDraft.MixedNullCoarea

/-! Exact polar identification of the global MA9 weight, with its written
angular/radial normalization and no restriction on positive-sigma slice topology. -/
open MeasureTheory Set Filter
open scoped Topology ENNReal Interval
noncomputable section
namespace BoundaryDraft

/-- Signed polar disintegration, derived from the actual Haar-to-sphere
measure-preserving equivalence. Absolute integrability is an input here;
the geometric coarea kernel supplies it independently. -/
theorem integral_mixedNull_polar {f : JointSpace → ℝ} (hf : Integrable f) :
    (∫ x, f x) = ∫ u : MixedNullDirection, (∫ r in Ioi (0 : ℝ),
      r ^ 2 * f (r • (u : JointSpace))) ∂(volume : Measure JointSpace).toSphere := by
  let p := homeomorphUnitSphereProd JointSpace
  have hp : MeasurePreserving p
      ((volume : Measure JointSpace).comap (fun x : ({0}ᶜ : Set JointSpace) => (x : JointSpace)))
      ((volume : Measure JointSpace).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      (volume : Measure JointSpace).measurePreserving_homeomorphUnitSphereProd
  have ht := hp.symm p.toMeasurableEquiv
  have hs := (integrableOn_iff_comap_subtypeVal
    (measurableSet_singleton (0 : JointSpace)).compl).mp
      (hf.integrableOn (s := ({0}ᶜ : Set JointSpace)))
  have hi : Integrable (fun z : MixedNullDirection × Ioi (0 : ℝ) =>
      f (z.2.val • z.1.val))
      ((volume : Measure JointSpace).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa only [p, homeomorphUnitSphereProd_symm_apply_coe] using
      (ht.integrable_comp_emb p.symm.measurableEmbedding).mpr hs
  calc
    _ = ∫ x : ({(0 : JointSpace)}ᶜ : Set JointSpace), f x.val
        ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ z : MixedNullDirection × Ioi (0 : ℝ), f (z.2.val • z.1.val)
        ∂(volume : Measure JointSpace).toSphere.prod (Measure.volumeIoiPow 2) := by
      simpa only [p, homeomorphUnitSphereProd_symm_apply_coe] using
        (ht.integral_comp p.symm.measurableEmbedding (fun x => f x.val)).symm
    _ = _ := by
      rw [integral_prod _ hi]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul
        (by fun_prop) (by filter_upwards [] with r; exact ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
      exact integral_subtype_comap measurableSet_Ioi
        (fun r : ℝ => r ^ 2 * f (r • (u : JointSpace)))

/-- The exact radial Jacobian, including the factor one half. -/
theorem mixedNullCoareaKernel_radial (H : Spatial → ℝ) {s r : ℝ}
    (hs : 0 ≤ s) (hr : 0 ≤ r) (u : MixedNullDirection) :
    r ^ 2 * mixedNullCoareaKernel H s (r • (u : JointSpace)) =
      if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
        r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) else 0 := by
  rw [mixedNullCoareaKernel_sqrt H hs]
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [hn]
  split_ifs <;> simp [div_eq_mul_inv]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Positive-sigma radial slices lie within `(0,R)`, without connectedness,
monotonicity, or a single moving radial endpoint hypothesis. -/
theorem coarea_radial_slice_subset {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (u : MixedNullDirection)
    (hcut : Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace))) :
    r < mixedNullRadius H u := by
  apply (hH.radial_domain u hr.le).mp
  change ‖r • (u : JointSpace)‖ < H (r • (u : JointSpace))
  rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  exact (show r ≤ Real.sqrt (r ^ 2 + s) by
    calc
      r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right hs)).trans_lt hcut

/-- Polar representation on the fixed positive ray. -/
theorem globalWeight_eq_polar {s : ℝ} (hs : 0 ≤ s) :
    mixedNullGlobalWeight H s =
      ∫ u : MixedNullDirection, (∫ r in Ioi (0 : ℝ),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [mixedNullGlobalWeight, integral_mixedNull_polar (hH.integrable_coareaKernel s)]
  apply integral_congr_ae
  filter_upwards [] with u
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact mixedNullCoareaKernel_radial H hs hr.le u

/-- Exactly MA9's angular/radial formula on `(0,B)`, also valid at zero.
The strict square-root test is never replaced by an unguarded squared height. -/
theorem globalWeight_eq_angular_radial {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : 0 ≤ s) :
    mixedNullGlobalWeight H s =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..(H 0 / (1 - k)),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere := by
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  rw [hH.globalWeight_eq_polar hs]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [intervalIntegral.integral_of_le hB.le, integral_Ioc_eq_integral_Ioo]
  let f : ℝ → ℝ := fun r =>
    if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
      r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) else 0
  have hset : Ioi (0 : ℝ) ∩ Iio B = Ioo 0 B := by ext r; simp
  change (∫ r in Ioi (0 : ℝ), f r) = ∫ r in Ioo 0 B, f r
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  by_cases hb : r < B
  · exact (Set.indicator_of_mem (show r ∈ Iio B from hb) f).symm
  · rw [Set.indicator_of_not_mem (show r ∉ Iio B from hb)]
    apply if_neg
    intro hcut
    have hR := hH.coarea_radial_slice_subset hs hr u hcut
    exact hb (hR.trans_le (hH.radius_bounds hk hk1 h u).2)

end MixedNullData
end BoundaryDraft

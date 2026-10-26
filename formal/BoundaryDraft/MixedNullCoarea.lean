import BoundaryDraft.MixedNullConcentration
import BoundaryDraft.MixedNullGeometryPolar

/-!
# The actual global MA9 coarea weight

The spatial integral below uses the strict square-root cutoff, not a squared
height test that could admit negative exterior heights. Negative sigma is
extended by its zero value via `max 0`; all coordinate identities concern
nonnegative sigma. Integrability precedes removal of the spatial origin.
-/
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal Interval
noncomputable section
namespace BoundaryDraft

/-- Actual spatial Jacobian and cutoff for MA9, with a constant negative-side
extension. In particular the strict cutoff retains the sign of the height. -/
def mixedNullCoareaKernel (H : Spatial → ℝ) (s : ℝ) (x : JointSpace) : ℝ :=
  if Real.sqrt (‖x‖ ^ 2 + max 0 s) < H x then
    (2 * Real.sqrt (‖x‖ ^ 2 + max 0 s))⁻¹ else 0

/-- The global weight is an actual spatial integral, including at sigma zero.
Its value at zero is proved to equal the independently defined area divided
by four, rather than imposed as a field or inferred from an action limit. -/
def mixedNullGlobalWeight (H : Spatial → ℝ) (s : ℝ) : ℝ :=
  ∫ x : JointSpace, mixedNullCoareaKernel H s x

theorem mixedNullCoareaKernel_nonneg (H : Spatial → ℝ) (s : ℝ) (x : JointSpace) :
    0 ≤ mixedNullCoareaKernel H s x := by
  unfold mixedNullCoareaKernel
  split_ifs <;> positivity

theorem mixedNullCoareaKernel_sqrt (H : Spatial → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (x : JointSpace) :
    mixedNullCoareaKernel H s x =
      if Real.sqrt (‖x‖ ^ 2 + s) < H x then
        1 / (2 * Real.sqrt (‖x‖ ^ 2 + s)) else 0 := by
  simp [mixedNullCoareaKernel, max_eq_right hs, one_div]

theorem mixedNullCoareaKernel_zero (H : Spatial → ℝ) (x : JointSpace) :
    mixedNullCoareaKernel H 0 x =
      (mixedNullSpatialDomain H).indicator (fun x => (1 / 4 : ℝ) * (2 / ‖x‖)) x := by
  simp only [mixedNullCoareaKernel, max_self, add_zero, Real.sqrt_sq (norm_nonneg x)]
  by_cases hx : ‖x‖ < H x
  · rw [if_pos hx, Set.indicator_of_mem (show x ∈ mixedNullSpatialDomain H from hx)]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  · rw [if_neg hx, Set.indicator_of_not_mem (show x ∉ mixedNullSpatialDomain H from hx)]

theorem mixedNullCoareaKernel_norm_le (H : Spatial → ℝ) (s : ℝ)
    {x : JointSpace} (hx0 : x ≠ 0) :
    ‖mixedNullCoareaKernel H s x‖ ≤ mixedNullCoareaKernel H 0 x := by
  have hr : ‖x‖ ≤ Real.sqrt (‖x‖ ^ 2 + max 0 s) := by
    calc
      ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (le_max_left _ _))
  rw [Real.norm_eq_abs, abs_of_nonneg (mixedNullCoareaKernel_nonneg H s x)]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  unfold mixedNullCoareaKernel
  simp only [max_self, add_zero, Real.sqrt_sq (norm_nonneg x)]
  split_ifs with hs hx hx
  · simpa only [one_div] using one_div_le_one_div_of_le
      (by positivity : 0 < 2 * ‖x‖)
      (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
  · exact False.elim (hx (hr.trans_lt hs))
  · positivity
  · rfl

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Joint measurability, including the cutoff and its moving upper boundary. -/
theorem measurable_coareaKernel :
    Measurable (fun p : ℝ × JointSpace => mixedNullCoareaKernel H p.1 p.2) := by
  have hs : Measurable (fun p : ℝ × JointSpace =>
      Real.sqrt (‖p.2‖ ^ 2 + max 0 p.1)) := by fun_prop
  exact (measurable_const.mul hs).inv.ite
    (measurableSet_lt hs (hH.continuous_euclidean.measurable.comp measurable_snd))
    measurable_const

/-- Integrability at zero follows from the independently proved polar
reciprocal-radius integral, including its origin treatment. -/
theorem integrable_coareaKernel_zero : Integrable (mixedNullCoareaKernel H 0) := by
  change Integrable (fun x => mixedNullCoareaKernel H 0 x)
  simp_rw [mixedNullCoareaKernel_zero]
  exact (integrable_indicator_iff hH.measurableSet_spatialDomain).mpr
    (hH.integrable_spatialLimit.const_mul (1 / 4))

/-- The singular dominator is proved integrable before invoking origin nullity. -/
theorem integrable_coareaKernel (s : ℝ) : Integrable (mixedNullCoareaKernel H s) := by
  have hi := hH.integrable_coareaKernel_zero
  apply hi.mono' (hH.measurable_coareaKernel.comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [hn] with x hx
  exact mixedNullCoareaKernel_norm_le H s hx

theorem measurable_globalWeight : Measurable (mixedNullGlobalWeight H) :=
  hH.measurable_coareaKernel.stronglyMeasurable.integral_prod_right.measurable

omit hH in
theorem globalWeight_nonneg (s : ℝ) : 0 ≤ mixedNullGlobalWeight H s :=
  integral_nonneg (mixedNullCoareaKernel_nonneg H s)

/-- MA9's assigned endpoint is exactly the actual spatial density at zero.
The area relation used here is independent of all action asymptotics. -/
theorem globalWeight_zero : mixedNullGlobalWeight H 0 = mixedNullArea H / 4 := by
  unfold mixedNullGlobalWeight
  simp_rw [mixedNullCoareaKernel_zero]
  rw [integral_indicator hH.measurableSet_spatialDomain, integral_const_mul]
  change (1 / 4 : ℝ) * mixedNullSpatialLimit H = _
  rw [hH.spatialLimit_eq_area]
  ring

theorem globalWeight_zero_pos : 0 < mixedNullGlobalWeight H 0 := by
  rw [hH.globalWeight_zero]
  exact div_pos hH.area_pos (by norm_num)

theorem globalWeight_le_zero (s : ℝ) :
    mixedNullGlobalWeight H s ≤ mixedNullGlobalWeight H 0 := by
  apply integral_mono_ae (hH.integrable_coareaKernel s) hH.integrable_coareaKernel_zero
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  filter_upwards [hn] with x hx
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using (mixedNullCoareaKernel_norm_le H s hx))

/-- The exact MA9 bound, for the specified Lipschitz constant and B. -/
theorem globalWeight_bound {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (s : ℝ) :
    0 ≤ mixedNullGlobalWeight H s ∧
      mixedNullGlobalWeight H s ≤ Real.pi * (H 0 / (1 - k)) ^ 2 := by
  refine ⟨globalWeight_nonneg (H := H) s, ?_⟩
  have ha := (hH.area_bounds (div_nonneg hH.tip_pos.le (by linarith : 0 ≤ 1 + k))
    (hH.radius_bounds hk hk1 h)).2
  have hw := hH.globalWeight_le_zero s
  rw [hH.globalWeight_zero] at hw
  linarith

omit hH in
/-- The positive-sigma slice stays within the original spatial interior. -/
theorem coareaKernel_eq_zero_of_not_mem {s : ℝ} {x : JointSpace}
    (hx : x ∉ mixedNullSpatialDomain H) : mixedNullCoareaKernel H s x = 0 := by
  have hr : ‖x‖ ≤ Real.sqrt (‖x‖ ^ 2 + max 0 s) := by
    calc
      ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (le_max_left _ _))
  exact if_neg (fun hs => hx (hr.trans_lt hs))

omit hH in
/-- Correct equivalence to the old fibre substitution: the spatial-domain
hypothesis supplies positive H, which cannot be dropped from a squared test. -/
theorem coareaKernel_eq_fibreWeight {x : JointSpace}
    (hx : x ∈ mixedNullSpatialDomain H) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullCoareaKernel H s x = mixedNullFibreWeight ‖x‖ (H x) s := by
  have hHpos : 0 < H x := lt_of_le_of_lt (norm_nonneg x) hx
  have hcut : Real.sqrt (‖x‖ ^ 2 + s) < H x ↔ s < H x ^ 2 - ‖x‖ ^ 2 := by
    rw [Real.sqrt_lt' hHpos]
    constructor <;> intro hh <;> nlinarith
  simp only [mixedNullCoareaKernel, mixedNullFibreWeight, mixedNullFibreJacobian,
    max_eq_right hs, hcut, Set.indicator, mem_Iio]

omit hH in
/-- The two explicit spatial bounds use the specified Lipschitz constant.
There is no positivity premise on H outside the admitted domain. -/
theorem coarea_spatial_bounds {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {x : JointSpace} (hx : x ∈ mixedNullSpatialDomain H) :
    ‖x‖ < H 0 / (1 - k) ∧ H x ≤ H 0 / (1 - k) := by
  let B := H 0 / (1 - k)
  have heq : (1 - k) * B = H 0 := by
    dsimp [B]
    exact mul_div_cancel₀ _ (sub_pos.mpr hk1).ne'
  have he := (le_abs_self (H x - H 0)).trans (h x 0)
  rw [sub_zero] at he
  have hfloor : H x ≤ H 0 + k * ‖x‖ := by linarith
  have hxb : ‖x‖ < B := by
    have hh : ‖x‖ < H x := hx
    nlinarith
  exact ⟨hxb, by nlinarith [mul_nonneg hk (sub_nonneg.mpr hxb.le)]⟩

/-- MA9's upper support endpoint is included in the zero region. -/
theorem globalWeight_eq_zero {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : (H 0 / (1 - k)) ^ 2 ≤ s) :
    mixedNullGlobalWeight H s = 0 := by
  have hB : 0 < H 0 / (1 - k) := div_pos hH.tip_pos (sub_pos.mpr hk1)
  have hs0 : 0 ≤ s := (sq_nonneg _).trans hs
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : x ∈ mixedNullSpatialDomain H
  · have hb := coarea_spatial_bounds hk hk1 h hx
    have hroot : H 0 / (1 - k) ≤ Real.sqrt (‖x‖ ^ 2 + s) := by
      rw [← Real.sqrt_sq hB.le]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])
    rw [mixedNullCoareaKernel_sqrt H hs0]
    exact if_neg (not_lt.mpr (hb.2.trans hroot))
  · exact coareaKernel_eq_zero_of_not_mem hx

omit hH in
/-- Every nonzero spatial fibre is right-continuous, including on the moving
boundary, where its strict cutoff remains zero for all nonnegative sigma. -/
theorem coareaKernel_right_continuous {x : JointSpace} (hx0 : x ≠ 0) :
    ContinuousWithinAt (fun s => mixedNullCoareaKernel H s x) (Ici 0) 0 := by
  by_cases hx : x ∈ mixedNullSpatialDomain H
  · have hc := (mixedNullFibreWeight_continuousAt ‖x‖ (H x)
      (norm_pos_iff.mpr hx0) hx).continuousWithinAt (s := Ici 0)
    rw [ContinuousWithinAt, ← coareaKernel_eq_fibreWeight hx (le_refl 0)] at hc
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (coareaKernel_eq_fibreWeight hx hs).symm
  · have he : (fun s => mixedNullCoareaKernel H s x) = fun _ => (0 : ℝ) := by
      funext s
      exact coareaKernel_eq_zero_of_not_mem hx
    rw [he]
    exact continuousWithinAt_const

/-- MA9's actual global right limit, by the proved integrable reciprocal-radius
majorant. Neither a density limit nor a radial-slice topology is a premise. -/
theorem globalWeight_right_continuous :
    ContinuousWithinAt (mixedNullGlobalWeight H) (Ici 0) 0 := by
  have hi := hH.integrable_coareaKernel_zero
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  apply tendsto_integral_filter_of_dominated_convergence (mixedNullCoareaKernel H 0)
  · exact Eventually.of_forall fun s => (hH.integrable_coareaKernel s).aestronglyMeasurable
  · exact Eventually.of_forall fun s => hn.mono fun x hx => mixedNullCoareaKernel_norm_le H s hx
  · exact hi
  · exact hn.mono fun x hx => coareaKernel_right_continuous hx

theorem globalWeight_tendsto_area_quarter :
    Tendsto (mixedNullGlobalWeight H) (𝓝[≥] (0 : ℝ)) (𝓝 (mixedNullArea H / 4)) := by
  rw [← hH.globalWeight_zero]
  exact hH.globalWeight_right_continuous

end MixedNullData
end BoundaryDraft

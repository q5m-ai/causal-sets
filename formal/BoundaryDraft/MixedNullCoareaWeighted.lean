import BoundaryDraft.MixedNullCoareaAction
import BoundaryDraft.MixedNullWeighted

/-! Signed measurable NM4 weights. These are actual spacetime source weights,
not substituted action-defined quantities. No weighted limit or generator
integration-by-parts claim is made for merely measurable weights. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- Actual source point at a spatial coordinate and nonnegative sigma. -/
def mixedNullCoareaPoint (s : ℝ) (x : JointSpace) : Spacetime :=
  Fin.cons (-Real.sqrt (‖x‖ ^ 2 + max 0 s)) x

/-- NM4's signed global spatial weight, with the same negative-side extension
as the unweighted weight. The endpoint is evaluated separately below. -/
def mixedNullWeightedGlobalWeight (H : Spatial → ℝ) (w : Spacetime → ℝ) (s : ℝ) : ℝ :=
  ∫ x : JointSpace, mixedNullCoareaKernel H s x * w (mixedNullCoareaPoint s x)

theorem continuous_mixedNullCoareaPoint :
    Continuous (fun p : ℝ × JointSpace => mixedNullCoareaPoint p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun p : ℝ × JointSpace => -Real.sqrt (‖p.2‖ ^ 2 + max 0 p.1))
    fun_prop
  · change Continuous (fun p : ℝ × JointSpace => p.2 j)
    exact (EuclideanSpace.proj j).continuous.comp continuous_snd

theorem mixedNullCoareaPoint_radial {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (u : MixedNullDirection) :
    mixedNullCoareaPoint s (r • (u : JointSpace)) =
      Fin.cons (-Real.sqrt (r ^ 2 + s)) (r • (u : JointSpace) : JointSpace) := by
  simp [mixedNullCoareaPoint, max_eq_right hs, norm_smul,
    mixedNullDirection_norm, Real.norm_eq_abs, abs_of_nonneg hr]

@[simp] theorem mixedNullWeightedGlobalWeight_one (H : Spatial → ℝ) (s : ℝ) :
    mixedNullWeightedGlobalWeight H (fun _ => 1) s = mixedNullGlobalWeight H s := by
  simp [mixedNullWeightedGlobalWeight, mixedNullGlobalWeight]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem measurable_weightedCoareaKernel {w : Spacetime → ℝ} (hw : Measurable w) :
    Measurable (fun p : ℝ × JointSpace =>
      mixedNullCoareaKernel H p.1 p.2 * w (mixedNullCoareaPoint p.1 p.2)) :=
  hH.measurable_coareaKernel.mul (hw.comp continuous_mixedNullCoareaPoint.measurable)

theorem integrable_weightedCoareaKernel {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) (s : ℝ) :
    Integrable (fun x : JointSpace =>
      mixedNullCoareaKernel H s x * w (mixedNullCoareaPoint s x)) := by
  have hp := continuous_mixedNullCoareaPoint.measurable.comp
    (show Measurable (fun x : JointSpace => (s, x)) from
      measurable_const.prodMk measurable_id)
  have hm := hw.comp hp
  simpa only [mul_comm] using (hH.integrable_coareaKernel s).bdd_mul'
    hm.aestronglyMeasurable (Eventually.of_forall fun x => hb (mixedNullCoareaPoint s x))

theorem measurable_weightedGlobalWeight {w : Spacetime → ℝ} (hw : Measurable w) :
    Measurable (mixedNullWeightedGlobalWeight H w) :=
  (hH.measurable_weightedCoareaKernel hw).stronglyMeasurable.integral_prod_right.measurable

/-- A signed integral is bounded by the actual nonnegative unweighted one. -/
theorem weightedGlobalWeight_norm_le {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) (s : ℝ) :
    ‖mixedNullWeightedGlobalWeight H w s‖ ≤ C * mixedNullGlobalWeight H s := by
  calc
    _ ≤ ∫ x : JointSpace, ‖mixedNullCoareaKernel H s x * w (mixedNullCoareaPoint s x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : JointSpace, C * mixedNullCoareaKernel H s x := by
      apply integral_mono (hH.integrable_weightedCoareaKernel hw hb s).norm
        ((hH.integrable_coareaKernel s).const_mul C)
      intro x
      dsimp only
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mixedNullCoareaKernel_nonneg H s x), mul_comm]
      exact mul_le_mul_of_nonneg_right (hb _) (mixedNullCoareaKernel_nonneg H s x)
    _ = _ := integral_const_mul _ _

theorem weightedGlobalWeight_bound {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (s : ℝ) :
    ‖mixedNullWeightedGlobalWeight H w s‖ ≤ C * Real.pi * (H 0 / (1 - k)) ^ 2 := by
  have hC : 0 ≤ C := (norm_nonneg (w 0)).trans (hb 0)
  exact (hH.weightedGlobalWeight_norm_le hw hb s).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hH.globalWeight_bound hk hk1 h s).2 hC)

theorem weightedGlobalWeight_eq_zero {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : (H 0 / (1 - k)) ^ 2 ≤ s) :
    mixedNullWeightedGlobalWeight H w s = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hH.globalWeight_eq_zero hk hk1 h hs, mul_zero] using
    hH.weightedGlobalWeight_norm_le hw hb s

/-- NM4 on the fixed positive ray, valid for signed measurable weights. -/
theorem weightedGlobalWeight_eq_polar {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullWeightedGlobalWeight H w s =
      ∫ u : MixedNullDirection, (∫ r in Ioi (0 : ℝ),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 * w (Fin.cons (-Real.sqrt (r ^ 2 + s))
            (r • (u : JointSpace) : JointSpace)) / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [mixedNullWeightedGlobalWeight,
    integral_mixedNull_polar (hH.integrable_weightedCoareaKernel hw hb s)]
  apply integral_congr_ae
  filter_upwards [] with u
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [← mul_assoc, mixedNullCoareaKernel_radial H hs hr.le u,
    mixedNullCoareaPoint_radial hs hr.le u]
  split_ifs <;> ring

/-- Precisely the written fixed `(0,B)` angular/radial weight. -/
theorem weightedGlobalWeight_eq_angular_radial {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullWeightedGlobalWeight H w s =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..(H 0 / (1 - k)),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 * w (Fin.cons (-Real.sqrt (r ^ 2 + s))
            (r • (u : JointSpace) : JointSpace)) / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere := by
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  rw [hH.weightedGlobalWeight_eq_polar hw hb hs]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [intervalIntegral.integral_of_le hB.le, integral_Ioc_eq_integral_Ioo]
  let f : ℝ → ℝ := fun r =>
    if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
      r ^ 2 * w (Fin.cons (-Real.sqrt (r ^ 2 + s))
        (r • (u : JointSpace) : JointSpace)) / (2 * Real.sqrt (r ^ 2 + s)) else 0
  have hset : Ioi (0 : ℝ) ∩ Iio B = Ioo 0 B := by ext r; simp
  change (∫ r in Ioi (0 : ℝ), f r) = ∫ r in Ioo 0 B, f r
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  by_cases hbr : r < B
  · exact (Set.indicator_of_mem (show r ∈ Iio B from hbr) f).symm
  · rw [Set.indicator_of_not_mem (show r ∉ Iio B from hbr)]
    apply if_neg
    intro hcut
    exact hbr ((hH.coarea_radial_slice_subset hs hr u hcut).trans_le
      (hH.radius_bounds hk hk1 h u).2)

/-- NM4's endpoint is the actual integral of the cone trace, including its
factor one half. Measurability does not assert continuity of that trace. -/
theorem weightedGlobalWeight_zero {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    mixedNullWeightedGlobalWeight H w 0 =
      (1 / 2 : ℝ) * ∫ u : MixedNullDirection,
        (∫ r in (0 : ℝ)..mixedNullRadius H u,
          r * w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_eq_polar hw hb (le_refl 0), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [intervalIntegral.integral_of_le (hH.radius_pos u).le,
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  let R := mixedNullRadius H u
  let f : ℝ → ℝ := fun r => (1 / 2 : ℝ) *
    (r * w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
  have hset : Ioi (0 : ℝ) ∩ Iio R = Ioo 0 R := by ext r; simp
  change _ = ∫ r in Ioo 0 R, f r
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [add_zero, Real.sqrt_sq hr.le]
  have hcut : r < H (r • (u : JointSpace)) ↔ r < R := by
    have hd := hH.radial_domain u hr.le
    simpa only [mixedNullSpatialDomain, mem_setOf_eq, norm_smul,
      mixedNullDirection_norm, mul_one, Real.norm_eq_abs,
      abs_of_pos (show 0 < r from hr)] using hd
  simp only [hcut]
  by_cases hlt : r < R
  · rw [if_pos hlt, Set.indicator_of_mem (show r ∈ Iio R from hlt)]
    dsimp [f]
    field_simp [(show 0 < r from hr).ne']
    ring
  · rw [if_neg hlt, Set.indicator_of_not_mem (show r ∉ Iio R from hlt)]

end MixedNullData
end BoundaryDraft

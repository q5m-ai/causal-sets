import BoundaryDraft.MixedNullWeightedContinuity
import BoundaryDraft.MixedNullGeometryExamples

/-!
# Density-uniform NM9 tip control after complete signed cancellation

The cutoff is the actual spatial cylinder in spacetime. Its radius may be
arbitrarily small; no density-dependent geometry and no deletion of the raw
bilocal tip is used. The reciprocal-radius majorant is integrated first.
-/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Genuine Euclidean spatial coordinate, not the sup norm on function space. -/
def mixedNullEuclideanSpatial (p : Spacetime) : JointSpace :=
  (WithLp.equiv 2 _).symm (spatialPart p)

theorem continuous_mixedNullEuclideanSpatial : Continuous mixedNullEuclideanSpatial := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
  unfold spatialPart
  fun_prop

@[simp] theorem mixedNullEuclideanSpatial_coareaPoint (s : ℝ) (x : JointSpace) :
    mixedNullEuclideanSpatial (mixedNullCoareaPoint s x) = x := by
  rfl

/-- Source cutoff only: the full partner domain is unchanged. -/
def mixedNullTipWeight (δ : ℝ) (w : Spacetime → ℝ) (p : Spacetime) : ℝ :=
  if ‖mixedNullEuclideanSpatial p‖ < δ then w p else 0

theorem measurable_mixedNullTipWeight (δ : ℝ) {w : Spacetime → ℝ} (hw : Measurable w) :
    Measurable (mixedNullTipWeight δ w) :=
  hw.ite (measurableSet_lt continuous_mixedNullEuclideanSpatial.norm.measurable
    measurable_const) measurable_const

theorem mixedNullTipWeight_bound (δ : ℝ) {w : Spacetime → ℝ} {M : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) (p : Spacetime) : ‖mixedNullTipWeight δ w p‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  unfold mixedNullTipWeight
  split_ifs
  · exact hb p
  · simpa using hM

/-- The singular pointwise comparison is only used away from the origin;
its constant-cap majorant is independently integrable at the origin. -/
theorem mixedNull_tip_kernel_bound (H : Spatial → ℝ) {δ : ℝ} {w : Spacetime → ℝ}
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (s : ℝ) {x : JointSpace} (hx0 : x ≠ 0) :
    ‖mixedNullCoareaKernel H s x * mixedNullTipWeight δ w (mixedNullCoareaPoint s x)‖ ≤
      M * mixedNullCoareaKernel (fun _ => δ) 0 x := by
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  simp only [mixedNullTipWeight, mixedNullEuclideanSpatial_coareaPoint]
  by_cases hx : ‖x‖ < δ
  · rw [if_pos hx, norm_mul]
    have hk : mixedNullCoareaKernel H 0 x ≤ mixedNullCoareaKernel (fun _ => δ) 0 x := by
      simp only [mixedNullCoareaKernel, max_self, add_zero, Real.sqrt_sq (norm_nonneg x), if_pos hx]
      split_ifs
      · exact le_rfl
      · positivity
    calc
      _ ≤ mixedNullCoareaKernel (fun _ => δ) 0 x * M :=
        mul_le_mul ((mixedNullCoareaKernel_norm_le H s hx0).trans hk) (hb _)
          (norm_nonneg _) (mixedNullCoareaKernel_nonneg _ _ _)
      _ = _ := mul_comm _ _
  · rw [if_neg hx, mul_zero, norm_zero]
    exact mul_nonneg hM (mixedNullCoareaKernel_nonneg _ _ _)

/-- The coarea mass of the genuine tip cylinder is bounded uniformly in sigma,
without a connected-slice hypothesis and without a limit interchange. -/
theorem mixedNull_tip_weight_bound {H : Spatial → ℝ} (hH : MixedNullData H)
    {δ : ℝ} (hδ : 0 < δ) {w : Spacetime → ℝ} (hw : Measurable w) {M : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) (s : ℝ) :
    ‖mixedNullWeightedGlobalWeight H (mixedNullTipWeight δ w) s‖ ≤ M * Real.pi * δ ^ 2 := by
  have hi := hH.integrable_weightedCoareaKernel (measurable_mixedNullTipWeight δ hw)
    (mixedNullTipWeight_bound δ hb) s
  have hδH := (mixedNull_constant_admissible hδ).toMixedNullData
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hb' : ‖mixedNullWeightedGlobalWeight H (mixedNullTipWeight δ w) s‖ ≤
      ∫ x : JointSpace, M * mixedNullCoareaKernel (fun _ => δ) 0 x := by
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono_ae hi.norm (hδH.integrable_coareaKernel_zero.const_mul M)
      (hn.mono fun x hx => mixedNull_tip_kernel_bound H hb s hx)
  rw [integral_const_mul] at hb'
  change ‖mixedNullWeightedGlobalWeight H (mixedNullTipWeight δ w) s‖ ≤
    M * mixedNullGlobalWeight (fun _ => δ) 0 at hb'
  rw [hδH.globalWeight_zero, mixedNullArea_constant hδ] at hb'
  convert hb' using 1
  ring

/-- Mass-four domination for the actual density-scaled Gaussian. -/
theorem mixedNull_gaussian_norm_bound {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ → ℝ) {C : ℝ}
    (hb : ∀ s, 0 ≤ s → ‖B s‖ ≤ C) :
    ‖(4 / Real.sqrt 6) * Real.sqrt ρ *
      ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * B s‖ ≤ 4 * C := by
  rw [nullGaussian_density_rescaling ρ hρ B, norm_mul]
  have hi := integrableOn_nullGaussian.const_mul C
  have hnorm : ‖∫ u in Ioi (0 : ℝ), nullGaussian u * B ((Real.sqrt ρ)⁻¹ * u)‖ ≤ C := by
    have he := norm_integral_le_of_norm_le hi
      (show ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
        ‖nullGaussian u * B ((Real.sqrt ρ)⁻¹ * u)‖ ≤ C * nullGaussian u from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hg : 0 ≤ nullGaussian u := by unfold nullGaussian; positivity
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hg, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (hb _ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg ρ)) hu.le)) hg)
    simpa only [integral_const_mul, integral_nullGaussian, mul_one] using he
  simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
    mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 4)

/-- NM9: every positive density, actual source cylinder, all partners retained.
The bound is independent of density, so no residual point response is hidden. -/
theorem MixedNullData.weightedContinuumMean_tip_bound {H : Spatial → ℝ} (hH : MixedNullData H)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) :
    ‖weightedContinuumMean ρ (mixedNullRegion H) (mixedNullTipWeight δ w)‖ ≤
      4 * M * Real.pi * δ ^ 2 := by
  rw [hH.weightedContinuumMean_eq_globalWeight hρ (measurable_mixedNullTipWeight δ hw)
    (mixedNullTipWeight_bound δ hb)]
  have he := mixedNull_gaussian_norm_bound hρ _
    (fun s _ => mixedNull_tip_weight_bound hH hδ hw hb s)
  convert he using 1
  ring

/-- The spatial cutoff cylinder contains a genuine ambient neighborhood of
the cone tip, not merely the measure-zero tip itself. -/
theorem mixedNull_tipCylinder_mem_nhds {δ : ℝ} (hδ : 0 < δ) :
    {p : Spacetime | ‖mixedNullEuclideanSpatial p‖ < δ} ∈ 𝓝 (0 : Spacetime) := by
  apply (isOpen_lt continuous_mixedNullEuclideanSpatial.norm continuous_const).mem_nhds
  change ‖(0 : JointSpace)‖ < δ
  simpa using hδ

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

omit hH in
/-- The written lower radius bound really puts the full spatial ball in the
admitted region projection. No global positivity of the floor is needed. -/
theorem tip_ball_subset {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {δ : ℝ} (hδ : δ ≤ H 0 / (1 + k)) {x : JointSpace} (hx : ‖x‖ < δ) :
    x ∈ mixedNullSpatialDomain H := by
  have hkpos : 0 < 1 + k := by linarith
  have hd := (le_div_iff₀ hkpos).mp hδ
  have hf := (neg_le_abs (H x - H 0)).trans (h x 0)
  rw [sub_zero] at hf
  change ‖x‖ < H x
  nlinarith [mul_lt_mul_of_pos_right hx hkpos]

omit hH in
/-- The actual endpoint of the unit cylinder below the minimum exit radius
is pi*delta^2. It is nonzero at every fixed positive cutoff. -/
theorem tipWeight_zero {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {δ : ℝ} (hδ : 0 < δ) (hδm : δ ≤ H 0 / (1 + k)) :
    mixedNullWeightedGlobalWeight H (mixedNullTipWeight δ (fun _ => 1)) 0 =
      Real.pi * δ ^ 2 := by
  have he : mixedNullWeightedGlobalWeight H (mixedNullTipWeight δ (fun _ => 1)) 0 =
      mixedNullGlobalWeight (fun _ => δ) 0 := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [mixedNullTipWeight, mixedNullEuclideanSpatial_coareaPoint]
    by_cases hx : ‖x‖ < δ
    · have hxH : ‖x‖ < H x := tip_ball_subset hk h hδm hx
      simp [mixedNullCoareaKernel, hx, hxH, Real.sqrt_sq (norm_nonneg x)]
    · simp [mixedNullCoareaKernel, hx, Real.sqrt_sq (norm_nonneg x)]
  rw [he, (mixedNull_constant_admissible hδ).toMixedNullData.globalWeight_zero,
    mixedNullArea_constant hδ]
  ring

/-- NM9's fixed positive tip-cylinder response is exactly 4*pi*delta^2.
This is an actual full-partner action limit, not a vanishing-cutoff premise. -/
theorem weightedContinuumMean_tip_limit {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {δ : ℝ} (hδ : 0 < δ) (hδm : δ ≤ H 0 / (1 + k)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H)
      (mixedNullTipWeight δ (fun _ => 1))) atTop (𝓝 (4 * Real.pi * δ ^ 2)) := by
  have ht : ∀ x ∈ mixedNullSpatialDomain H,
      ContinuousAt (fun t : ℝ => mixedNullTipWeight δ (fun _ => 1)
        (Fin.cons t (x : Spatial))) (-‖x‖) := by
    intro x _
    change ContinuousAt (fun _ : ℝ => if ‖x‖ < δ then (1 : ℝ) else 0) _
    exact continuousAt_const
  have hl := hH.weightedContinuumMean_tendsto_globalWeight
    (measurable_mixedNullTipWeight δ measurable_const)
    (mixedNullTipWeight_bound δ (show ∀ _p : Spacetime, ‖(1 : ℝ)‖ ≤ 1 by simp)) ht
  rw [tipWeight_zero hk h hδ hδm] at hl
  simpa only [mul_assoc] using hl

end MixedNullData
end BoundaryDraft

import BoundaryDraft.MixedNullCoareaTransport

/-!
# Weighted right continuity without spatial continuity

The first API uses globally bounded measurable spacetime weights and continuity
in time only at the cone trace over the spatial interior. Radial and angular
step cutoffs are therefore admitted. The global bound in this API is explicit;
a locally bounded weight such as the coordinate time is not globally bounded.
-/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft.MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Actual weighted right continuity. Only the time variable is required to
be continuous, and only at the cone trace; no spatial continuity is assumed. -/
theorem weightedGlobalWeight_right_continuous {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (ht : ∀ x ∈ mixedNullSpatialDomain H,
      ContinuousAt (fun t : ℝ => w (Fin.cons t (x : Spatial))) (-‖x‖)) :
    ContinuousWithinAt (mixedNullWeightedGlobalWeight H w) (Ici 0) 0 := by
  have hC : 0 ≤ C := (norm_nonneg (w 0)).trans (hb 0)
  have hi := hH.integrable_coareaKernel_zero.const_mul C
  have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
    apply ae_iff.mpr
    simp
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => C * mixedNullCoareaKernel H 0 x)
  · exact Eventually.of_forall fun s =>
      (hH.integrable_weightedCoareaKernel hw hb s).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    filter_upwards [hn] with x hx
    rw [norm_mul]
    calc
      _ ≤ ‖mixedNullCoareaKernel H s x‖ * C :=
        mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
      _ ≤ C * mixedNullCoareaKernel H 0 x := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (mixedNullCoareaKernel_norm_le H s hx) hC
  · exact hi
  · filter_upwards [hn] with x hx0
    by_cases hx : x ∈ mixedNullSpatialDomain H
    · have harg : ContinuousAt (fun s : ℝ => -Real.sqrt (‖x‖ ^ 2 + max 0 s)) 0 := by
        fun_prop
      have ht' : ContinuousAt (fun t : ℝ => w (Fin.cons t (x : Spatial)))
          (-Real.sqrt (‖x‖ ^ 2 + max 0 (0 : ℝ))) := by
        simpa only [max_self, add_zero, Real.sqrt_sq (norm_nonneg x)] using ht x hx
      have hc := ht'.comp (f := fun s : ℝ => -Real.sqrt (‖x‖ ^ 2 + max 0 s))
        (x := 0) harg
      exact (coareaKernel_right_continuous hx0).mul hc.continuousWithinAt
    · simp only [coareaKernel_eq_zero_of_not_mem hx, zero_mul]
      exact tendsto_const_nhds

/-- The unchanged signed full-partner action converges to four times its
actual coarea endpoint. This is a genuine geometric producer, not a hypothesis
on a supplied limiting weight. -/
theorem weightedContinuumMean_tendsto_globalWeight {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (ht : ∀ x ∈ mixedNullSpatialDomain H,
      ContinuousAt (fun t : ℝ => w (Fin.cons t (x : Spatial))) (-‖x‖)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (4 * mixedNullWeightedGlobalWeight H w 0)) := by
  have hC : 0 ≤ C := (norm_nonneg (w 0)).trans (hb 0)
  have hbound (s : ℝ) (_hs : 0 ≤ s) :
      ‖mixedNullWeightedGlobalWeight H w s‖ ≤ C * mixedNullGlobalWeight H 0 :=
    (hH.weightedGlobalWeight_norm_le hw hb s).trans
      (mul_le_mul_of_nonneg_left (hH.globalWeight_le_zero s) hC)
  have hlim := nullGaussian_density_limit_right (mixedNullWeightedGlobalWeight H w)
    (hH.measurable_weightedGlobalWeight hw)
    (hH.weightedGlobalWeight_right_continuous hw hb ht)
    (C * mixedNullGlobalWeight H 0) hbound
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hH.weightedContinuumMean_eq_globalWeight hρ hw hb).symm

/-- The limiting cone trace is spatially distributed, not merely a joint
value. Its later generator integration by parts is a separate obligation. -/
theorem weightedContinuumMean_tendsto_coneTrace {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (ht : ∀ x ∈ mixedNullSpatialDomain H,
      ContinuousAt (fun t : ℝ => w (Fin.cons t (x : Spatial))) (-‖x‖)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (2 * ∫ u : MixedNullDirection,
        (∫ r in (0 : ℝ)..mixedNullRadius H u,
          r * w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere)) := by
  have hlim := hH.weightedContinuumMean_tendsto_globalWeight hw hb ht
  rw [hH.weightedGlobalWeight_zero hw hb] at hlim
  convert hlim using 1
  congr 1
  ring

end BoundaryDraft.MixedNullData

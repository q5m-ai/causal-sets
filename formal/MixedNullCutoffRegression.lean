import BoundaryDraft.MixedNullCollar
import BoundaryDraft.MixedNullSineGeometry
import BoundaryDraft.MixedNullTipLocal

/-! Expanded NM9/NM10 contracts, including fixed nonzero cutoffs, the original
weighted action, genuine Euclidean radii and a nonplanar floor. -/
open BoundaryDraft MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace MixedNullCutoffRegression

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    {w : Spacetime → ℝ} (hw : Measurable w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) :
    ‖(4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ p in mixedNullRegion H,
          if ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ < δ then w p else 0) -
        ρ * ∫ p in mixedNullRegion H,
          (if ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ < δ then w p else 0) *
            ∫ q in mixedNullRegion H ∩ causalFuture p,
              bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2))‖ ≤
      4 * M * Real.pi * δ ^ 2 := hH.weightedContinuumMean_tip_bound hρ hδ hw hb

-- Exterior values of coordinate time are unbounded; only the actual box
-- bound is used. Clipping in the proof does not change the source observable.
example {H : Spatial → ℝ} (hH : MixedNullData H) {k ρ δ : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hρ : 0 < ρ) (hδ : 0 < δ) :
    ‖weightedContinuumMean ρ (mixedNullRegion H) (mixedNullTipWeight δ (fun p => p 0))‖ ≤
      4 * (H 0 / (1 - k)) * Real.pi * δ ^ 2 := by
  have hB : 0 ≤ H 0 / (1 - k) := div_nonneg hH.tip_pos.le (sub_pos.mpr hk1).le
  apply hH.weightedContinuumMean_tip_bound_local hρ hδ (measurable_pi_apply 0) hB
  apply MixedNullData.weightBound_of_box hk hk1 hLip
  intro p hp
  rw [Real.norm_eq_abs, abs_of_nonpos hp.2.1]
  linarith [hp.1]

-- The original spatial cylinder really contains an ambient tip neighborhood.
example {δ : ℝ} (hδ : 0 < δ) :
    {p : Spacetime | ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ < δ} ∈
      𝓝 (0 : Spacetime) := mixedNull_tipCylinder_mem_nhds hδ

-- Every density, an arbitrarily small fixed source cylinder, and a signed source.
example {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ‖weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor)
      (mixedNullTipWeight δ (fun _ => -(2 : ℝ)))‖ ≤ 8 * Real.pi * δ ^ 2 := by
  have he := mixedNull_sine_admissible.toMixedNullData.weightedContinuumMean_tip_bound
    hρ hδ measurable_const (show ∀ _p : Spacetime, ‖-(2 : ℝ)‖ ≤ 2 by norm_num)
  convert he using 1
  ring

-- The fixed unit cylinder is not claimed to vanish: its limit is pi/4.
example : Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor)
    (mixedNullTipWeight (1 / 4) (fun _ => 1))) atTop (𝓝 (Real.pi / 4)) := by
  let hH := mixedNull_sine_admissible.toMixedNullData
  obtain ⟨k, hk, hk1, hLip⟩ := hH.euclidean_lipschitz
  have hδm : (1 / 4 : ℝ) ≤ mixedNullSineFloor 0 / (1 + k) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + k)).mpr
    norm_num [mixedNullSineFloor]
    linarith
  have he := hH.weightedContinuumMean_tip_limit hk hLip (by norm_num : (0 : ℝ) < 1 / 4) hδm
  convert he using 1
  congr 1
  ring

-- Neither radius bounds nor a cutoff limit are assumed as extra geometric data.
example {H : Spatial → ℝ} (hH : MixedNullData H) {k h : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hh : 0 < h) (hhm : h < H 0 / (1 + k)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (mixedNullCollarWeight H h))
      atTop (𝓝 (∫ u : MixedNullDirection,
        mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2
        ∂(volume : Measure JointSpace).toSphere)) ∧
      Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (fun p => 1 - mixedNullCollarWeight H h p))
        atTop (𝓝 (∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
          ∂(volume : Measure JointSpace).toSphere)) ∧
      (0 ≤ mixedNullCollarResponse H h ∧
        mixedNullCollarResponse H h ≤ 8 * Real.pi * (H 0 / (1 - k)) * h) ∧
      0 < ∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
        ∂(volume : Measure JointSpace).toSphere :=
  hH.collar_response_from_lipschitz hk hk1 hLip hh hhm

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    Tendsto (fun h : ℝ => ∫ u : MixedNullDirection,
      mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2
      ∂(volume : Measure JointSpace).toSphere) (𝓝 0) (𝓝 0) :=
  hH.collarResponse_tendsto_zero

-- Sharp radial membership uses both the actual exit and the inner collar edge.
example (H : Spatial → ℝ) {r : ℝ} (hr : 0 < r) (h t : ℝ) (u : MixedNullDirection) :
    mixedNullCollarWeight H h (Fin.cons t (r • (u : JointSpace) : JointSpace)) =
      if mixedNullRadius H u - h < r ∧ r < mixedNullRadius H u then 1 else 0 :=
  mixedNullCollarWeight_radial H h hr u t

-- A nonconstant floor has a genuinely nonzero complementary action response.
example :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor)
      (mixedNullCollarComplement mixedNullSineFloor (1 / 4))) atTop
      (𝓝 (∫ u : MixedNullDirection, (mixedNullRadius mixedNullSineFloor u - 1 / 4) ^ 2
        ∂(volume : Measure JointSpace).toSphere)) ∧
      0 < ∫ u : MixedNullDirection, (mixedNullRadius mixedNullSineFloor u - 1 / 4) ^ 2
        ∂(volume : Measure JointSpace).toSphere := by
  let hH := mixedNull_sine_admissible.toMixedNullData
  obtain ⟨k, hk, hk1, hLip⟩ := hH.euclidean_lipschitz
  have hhm : (1 / 4 : ℝ) < mixedNullSineFloor 0 / (1 + k) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1 + k)).mpr
    norm_num [mixedNullSineFloor]
    linarith
  have he := hH.collar_response_from_lipschitz hk hk1 hLip (by norm_num : (0 : ℝ) < 1 / 4) hhm
  exact ⟨he.2.1, he.2.2.2⟩

-- Nonaffinity alone is insufficient: this witness lies strictly inside the
-- spatial support of the actual lower face and has a nonzero second derivative.
example :
    (EuclideanSpace.single 0 (Real.pi / 6) : JointSpace) ∈ mixedNullSpatialDomain
      (fun x : Spatial => 1 + (1 / 5 : ℝ) * Real.sin (x 0)) ∧
    deriv (deriv (fun r : ℝ => mixedNullSineFloor (EuclideanSpace.single 0 r : JointSpace)))
      (Real.pi / 6) = -(1 / 10 : ℝ) := mixedNull_sine_interior_second_deriv

example : ∃ u v : MixedNullDirection,
    mixedNullRadius mixedNullSineFloor v < mixedNullRadius mixedNullSineFloor u := by
  obtain ⟨u, v, hu, hv⟩ := mixedNull_sine_radius_nonconstant
  exact ⟨u, v, by rwa [hv]⟩

end MixedNullCutoffRegression

import BoundaryDraft.MixedNullErrorExtension
import BoundaryDraft.MixedNullGeometryExamples

/-! Expanded NM5--NM7 contracts, actual unbounded coordinate-time weights,
nonzero normalization controls, and radial step weights without spatial
continuity. These tests retain the original region and all future partners. -/
open BoundaryDraft MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace MixedNullWeightedErrorRegression

example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : Measurable w) {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M)
    (ht : ∀ x ∈ mixedNullSpatialDomain H,
      ContinuousAt (fun t : ℝ => w (Fin.cons t (x : Spatial))) (-‖x‖)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (4 * mixedNullWeightedGlobalWeight H w 0)) :=
  hH.weightedContinuumMean_tendsto_globalWeight hw hb ht

-- Literal NM5 constants and range; only local value and time bounds.
example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : Measurable w) {M L k s : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : MixedNullWeightBound H w M) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) :
    ‖mixedNullWeightedGlobalWeight H w s - mixedNullWeightedGlobalWeight H w 0‖ ≤
      Real.pi * s * (M * (1 + Real.log ((H 0 / (1 - k)) / Real.sqrt s) +
        2 * (H 0 / (1 - k)) / ((H 0 / (1 + k)) * (1 - k))) + L * (H 0 / (1 - k))) :=
  hH.weightedGlobalWeight_error_local hw hM hb hL ht hk hk1 h hs hsT

-- NM7 with the action and Gaussian tail expanded, not an assumed erfc symbol.
example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : Measurable w) {M L k s ρ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : MixedNullWeightBound H w M) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) (hρ : 0 < ρ) :
    ‖(4 / Real.sqrt 6) * Real.sqrt ρ *
        ((∫ p in mixedNullRegion H, w p) - ρ * ∫ p in mixedNullRegion H,
          w p * ∫ q in mixedNullRegion H ∩ causalFuture p,
            bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) -
      4 * mixedNullWeightedGlobalWeight H w 0‖ ≤
      4 * mixedNullWeightedError (H 0) k M L s + 8 * M * Real.pi * (H 0 / (1 - k)) ^ 2 *
        ((2 / Real.sqrt Real.pi) * ∫ u in Ioi (Real.sqrt ((Real.pi / 24) * ρ) * s), Real.exp (-u ^ 2)) :=
  hH.weightedContinuumMean_error_local hw hM hb hL ht hk hk1 h hs hsT hρ

example {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2)) = 4 :=
  mixedNull_gaussian_mass hρ

example : mixedNullErfc 0 = 1 := mixedNullErfc_zero

example {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ρ : ℝ => mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s)) atTop (𝓝 0) :=
  mixedNullErfc_density_tendsto_zero hs

-- Endpoint sigma=T^2/4 is included in the actual small-sigma estimate.
example {H : Spatial → ℝ} (hH : MixedNullData H) {w : Spacetime → ℝ}
    (hw : Measurable w) {M L k : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : MixedNullWeightBound H w M) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) :
    ‖mixedNullWeightedGlobalWeight H w (H 0 ^ 2 / 4) - mixedNullWeightedGlobalWeight H w 0‖ ≤
      mixedNullWeightedError (H 0) k M L (H 0 ^ 2 / 4) :=
  hH.weightedGlobalWeight_error_local hw hM hb hL ht hk hk1 h
    (div_pos (sq_pos_of_pos hH.tip_pos) (by norm_num)) le_rfl

-- The moving shell proof needs no interval-slice or radial monotonicity premise.
example {H : Spatial → ℝ} (hH : MixedNullData H) {k s r : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) (hr : 0 < r) (hs : 0 ≤ s) (hsT : s ≤ H 0 ^ 2 / 4)
    (hrR : r < mixedNullRadius H u) (hremoved : H (r • (u : JointSpace)) ≤ Real.sqrt (r ^ 2 + s)) :
    mixedNullRadius H u - s / ((H 0 / (1 + k)) * (1 - k)) ≤ r :=
  hH.coarea_removed_shell hk hk1 h u hr hs hsT hrR hremoved

-- The potentially delicate simultaneous endpoints retain strict inclusion.
example {H : Spatial → ℝ} (hH : MixedNullData H) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (u : MixedNullDirection) :
    Real.sqrt (((H 0 / (1 + k)) / 2) ^ 2 + H 0 ^ 2 / 4) <
      H (((H 0 / (1 + k)) / 2) • (u : JointSpace)) :=
  hH.coarea_small_radius_mem hk h u
    (div_nonneg (div_nonneg hH.tip_pos.le (by linarith)) (by norm_num))
    (by positivity) le_rfl le_rfl

/-- Coordinate time satisfies the local box bound, not a global bound. -/
theorem time_weight_bound {H : Spatial → ℝ} {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) :
    MixedNullWeightBound H (fun p => p 0) (H 0 / (1 - k)) := by
  apply MixedNullData.weightBound_of_box hk hk1 h
  intro p hp
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hp.1, hp.2.1.trans (by
    have hh := hp.2.2
    exact (norm_nonneg _).trans hh)⟩

theorem time_weight_lipschitz (H : Spatial → ℝ) :
    MixedNullTimeLipschitz H (fun p => p 0) 1 := by
  intro x _hx t _ht v _hv
  simp only [Fin.cons_zero, Real.norm_eq_abs, one_mul, le_refl]

theorem time_weight_not_globally_bounded : ¬ ∃ M : ℝ, ∀ p : Spacetime, ‖p 0‖ ≤ M := by
  rintro ⟨M, hM⟩
  have hh := hM (Fin.cons (|M| + 1) (0 : Spatial))
  simp only [Fin.cons_zero, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < |M| + 1)] at hh
  linarith [le_abs_self M]

/-- Actual nonzero time-dependent calibration from the independent cone trace. -/
theorem round_time_weight_zero {T : ℝ} (hT : 0 < T) :
    mixedNullWeightedGlobalWeight (fun _ : Spatial => T) (fun p => p 0) 0 =
      -(2 * Real.pi * T ^ 3 / 3) := by
  have hH := (mixedNull_constant_admissible hT).toMixedNullData
  have hb : MixedNullWeightBound (fun _ : Spatial => T) (fun p => p 0) T := by
    simpa using time_weight_bound (H := fun _ : Spatial => T) (k := 0)
      (by norm_num) (by norm_num) (by intro x y; simp)
  rw [hH.weightedGlobalWeight_zero_local (measurable_pi_apply 0) hT.le hb]
  simp_rw [mixedNullRadius_constant hT]
  have hi : (∫ r in (0 : ℝ)..T, r * (-r)) = -(T ^ 3 / 3) := by
    calc
      _ = ∫ r in (0 : ℝ)..T, -(r ^ 2) := by
        apply intervalIntegral.integral_congr
        intro r _hr
        ring
      _ = _ := by rw [intervalIntegral.integral_neg, integral_pow]; norm_num
  simp only [Fin.cons_zero, hi, integral_const, smul_eq_mul, jointSphere_area]
  ring

example : Tendsto (fun ρ : ℝ => weightedContinuumMean ρ
    (mixedNullRegion (fun _ : Spatial => 1)) (fun p => p 0)) atTop (𝓝 (-(8 * Real.pi / 3))) := by
  have hH := (mixedNull_constant_admissible (by norm_num : (0 : ℝ) < 1)).toMixedNullData
  have hb : MixedNullWeightBound (fun _ : Spatial => 1) (fun p => p 0) 1 := by
    simpa using time_weight_bound (H := fun _ : Spatial => 1) (k := 0)
      (by norm_num) (by norm_num) (by intro x y; simp)
  have he := hH.weightedContinuumMean_limit_local (measurable_pi_apply 0)
    (by norm_num : (0 : ℝ) ≤ 1) hb (by norm_num : (0 : ℝ) ≤ 1) (time_weight_lipschitz _)
  rw [round_time_weight_zero (by norm_num : (0 : ℝ) < 1)] at he
  convert he using 1
  congr 1
  ring

-- Nonconstant admitted floor with a genuinely unbounded-in-ambient-time weight.
example : Tendsto (fun ρ : ℝ => weightedContinuumMean ρ
    (mixedNullRegion mixedNullSineFloor) (fun p => p 0))
    atTop (𝓝 (4 * mixedNullWeightedGlobalWeight mixedNullSineFloor (fun p => p 0) 0)) := by
  have hH := mixedNull_sine_admissible.toMixedNullData
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  exact hH.weightedContinuumMean_limit_local (measurable_pi_apply 0)
    (div_nonneg hH.tip_pos.le (sub_nonneg.mpr hk1.le)) (time_weight_bound hk hk1 h)
    (by norm_num) (time_weight_lipschitz _)

/-- Sharp radial step: no spatial continuity is asserted or used. -/
def radialStep (p : Spacetime) : ℝ :=
  if ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ < 1 / 2 then 1 else 0

theorem radialStep_measurable : Measurable radialStep := by
  have hx : Continuous (fun p : Spacetime =>
      ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖) :=
    continuous_norm.comp ((PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
      (by unfold spatialPart; fun_prop))
  exact measurable_const.ite (measurableSet_lt hx.measurable measurable_const) measurable_const

theorem radialStep_bound (p : Spacetime) : ‖radialStep p‖ ≤ 1 := by
  unfold radialStep
  split_ifs <;> norm_num

example : radialStep (Fin.cons (-1 / 2) (0 : Spatial)) = 1 ∧
    radialStep (Fin.cons (-3 / 2) (EuclideanSpace.single 0 1 : JointSpace)) = 0 := by
  constructor
  · norm_num [radialStep, spatialPart_cons]
  · change (if ‖(EuclideanSpace.single 0 1 : JointSpace)‖ < (1 / 2 : ℝ) then (1 : ℝ) else 0) = 0
    norm_num [EuclideanSpace.norm_single]

example : Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor) radialStep)
    atTop (𝓝 (4 * mixedNullWeightedGlobalWeight mixedNullSineFloor radialStep 0)) := by
  apply mixedNull_sine_admissible.toMixedNullData.weightedContinuumMean_tendsto_globalWeight
    radialStep_measurable radialStep_bound
  intro x _hx
  simp only [radialStep, spatialPart_cons]
  exact continuousAt_const

example {H : Spatial → ℝ} (hH : MixedNullData H) {k s : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) :
    ‖mixedNullWeightedGlobalWeight H radialStep s - mixedNullWeightedGlobalWeight H radialStep 0‖ ≤
      mixedNullWeightedError (H 0) k 1 0 s := by
  apply hH.weightedGlobalWeight_error radialStep_measurable radialStep_bound (by norm_num)
    (k := k) _ hk hk1 h hs hsT
  intro x _hx t _ht v _hv
  simp [radialStep, spatialPart_cons]

end MixedNullWeightedErrorRegression

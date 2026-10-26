import BoundaryDraft.MixedNullGeometryExamples
import Mathlib.Data.Real.Pi.Bounds

/-! Actual interior nonzero-curvature and varying-radius witnesses for the
written sine example. Global nonaffinity alone would not prove either claim.
The ambient spacetime is still flat. -/
open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- The first coordinate line of the actual sine floor. -/
theorem mixedNull_sine_line (s : ℝ) :
    mixedNullSineFloor (EuclideanSpace.single 0 s : JointSpace) =
      1 + (1 / 5 : ℝ) * Real.sin s := by
  simp [mixedNullSineFloor]

theorem mixedNull_sine_line_deriv (s : ℝ) :
    deriv (fun r : ℝ => mixedNullSineFloor (EuclideanSpace.single 0 r : JointSpace)) s =
      (1 / 5 : ℝ) * Real.cos s := by
  have he : (fun r : ℝ => mixedNullSineFloor (EuclideanSpace.single 0 r : JointSpace)) =
      fun r => 1 + (1 / 5 : ℝ) * Real.sin r := funext mixedNull_sine_line
  rw [he]
  exact ((Real.hasDerivAt_sin s).const_mul (1 / 5) |>.const_add 1).deriv

/-- A genuine nonzero second directional derivative at an interior spatial
point of the lower face, not a midpoint witness outside the physical domain. -/
theorem mixedNull_sine_interior_second_deriv :
    (EuclideanSpace.single 0 (Real.pi / 6) : JointSpace) ∈ mixedNullSpatialDomain mixedNullSineFloor ∧
      deriv (deriv (fun r : ℝ => mixedNullSineFloor (EuclideanSpace.single 0 r : JointSpace)))
        (Real.pi / 6) = -(1 / 10 : ℝ) := by
  constructor
  · change ‖(EuclideanSpace.single 0 (Real.pi / 6) : JointSpace)‖ < _
    rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < Real.pi / 6),
      mixedNull_sine_line, Real.sin_pi_div_six]
    nlinarith [Real.pi_lt_four]
  · have he : deriv (fun r : ℝ => mixedNullSineFloor (EuclideanSpace.single 0 r : JointSpace)) =
        fun s => (1 / 5 : ℝ) * Real.cos s := funext mixedNull_sine_line_deriv
    rw [he, ((Real.hasDerivAt_cos (Real.pi / 6)).const_mul (1 / 5)).deriv, Real.sin_pi_div_six]
    norm_num

/-- The sine radius varies on the actual joint: along the second axis it is
one, while along the positive first axis it is strictly greater than one. -/
theorem mixedNull_sine_radius_nonconstant :
    ∃ u v : MixedNullDirection,
      1 < mixedNullRadius mixedNullSineFloor u ∧ mixedNullRadius mixedNullSineFloor v = 1 := by
  let u : MixedNullDirection := ⟨EuclideanSpace.single 0 1, by
    simp only [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]⟩
  let v : MixedNullDirection := ⟨EuclideanSpace.single 1 1, by
    simp only [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]⟩
  let hH := mixedNull_sine_admissible.toMixedNullData
  have hsin : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨u, v, ?_, ?_⟩
  · apply (hH.radial_domain u (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖(1 : ℝ) • (u : JointSpace)‖ < mixedNullSineFloor ((1 : ℝ) • (u : JointSpace))
    simp only [one_smul, mixedNullDirection_norm]
    change 1 < 1 + (1 / 5 : ℝ) * Real.sin ((EuclideanSpace.single 0 1 : JointSpace) 0)
    norm_num [EuclideanSpace.single_apply]
    linarith
  · apply Eq.symm
    apply hH.radius_unique v
    norm_num [mixedNullSineFloor, v]

end BoundaryDraft

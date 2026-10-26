import BoundaryDraft.MixedNullWeightedContinuity

/-! Quantitative NM5 geometry: square-root Jacobian estimates and the actual
removed radial shell. No connectedness of positive-sigma slices is assumed. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- NM5's explicit error expression, with the original m and B. -/
def mixedNullWeightedError (T k M L s : ℝ) : ℝ :=
  Real.pi * s * (M * (1 + Real.log ((T / (1 - k)) / Real.sqrt s) +
    2 * (T / (1 - k)) / ((T / (1 + k)) * (1 - k))) + L * (T / (1 - k)))

theorem mixedNull_sqrt_gap {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    0 ≤ Real.sqrt (r ^ 2 + s) - r ∧
    Real.sqrt (r ^ 2 + s) - r ≤ s / (2 * r) := by
  have hq : r ≤ Real.sqrt (r ^ 2 + s) := by
    calc
      r = Real.sqrt (r ^ 2) := (Real.sqrt_sq hr.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right hs)
  have he := Real.sq_sqrt (add_nonneg (sq_nonneg r) hs)
  refine ⟨sub_nonneg.mpr hq, (le_div_iff₀ (by positivity : 0 < 2 * r)).mpr ?_⟩
  nlinarith [sq_nonneg (Real.sqrt (r ^ 2 + s) - r)]

theorem mixedNull_sqrt_gap_eq {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    Real.sqrt (r ^ 2 + s) - r = s / (Real.sqrt (r ^ 2 + s) + r) := by
  have hq := Real.sqrt_nonneg (r ^ 2 + s)
  have he := Real.sq_sqrt (add_nonneg (sq_nonneg r) hs)
  apply (eq_div_iff (by positivity : Real.sqrt (r ^ 2 + s) + r ≠ 0)).mpr
  nlinarith

/-- The two alternative Jacobian bounds that produce the logarithm after
splitting at sqrt(sigma), including nonnegativity. -/
theorem mixedNull_radial_jacobian_difference {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    0 ≤ r / 2 - r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) ∧
    r / 2 - r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) ≤ r / 2 ∧
    r / 2 - r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) ≤ s / (4 * r) := by
  let q := Real.sqrt (r ^ 2 + s)
  have hgap := mixedNull_sqrt_gap hr hs
  have hqr : r ≤ q := by dsimp [q]; linarith [hgap.1]
  have hq : 0 < q := hr.trans_le hqr
  have hJ : 0 ≤ r ^ 2 / (2 * q) := by positivity
  have hJle : r ^ 2 / (2 * q) ≤ r / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * q)).mpr
    nlinarith
  have he : r / 2 - r ^ 2 / (2 * q) = (r / (2 * q)) * (q - r) := by
    field_simp
    ring
  have hcoef : r / (2 * q) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * q)).mpr
    linarith
  refine ⟨sub_nonneg.mpr hJle, by linarith, ?_⟩
  change r / 2 - r ^ 2 / (2 * q) ≤ _
  rw [he]
  calc
    _ ≤ (1 / 2 : ℝ) * (q - r) := mul_le_mul_of_nonneg_right hcoef hgap.1
    _ ≤ (1 / 2 : ℝ) * (s / (2 * r)) := mul_le_mul_of_nonneg_left hgap.2 (by norm_num)
    _ = _ := by ring

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- The quantitative radial slope bound is derived from the original global
Lipschitz hypothesis and the independently proved root equation. -/
theorem radial_gap_lower {k : ℝ}
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) {r : ℝ} (hr : r ≤ mixedNullRadius H u) :
    (1 - k) * (mixedNullRadius H u - r) ≤ H (r • (u : JointSpace)) - r := by
  have he := h (mixedNullRadius H u • (u : JointSpace)) (r • (u : JointSpace))
  rw [← sub_smul, norm_smul, mixedNullDirection_norm, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hr), ← hH.radius_root u] at he
  have hh := (le_abs_self _).trans he
  nlinarith

/-- NM5 Step 1 with both possible endpoints retained: even at r=m/2 and
sigma=T^2/4 the actual square-root cutoff is strict; r=0 is handled separately. -/
theorem coarea_small_radius_mem {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsT : s ≤ H 0 ^ 2 / 4) (hrm : r ≤ (H 0 / (1 + k)) / 2) :
    Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) := by
  have hT := hH.tip_pos
  have he := h (r • (u : JointSpace)) 0
  rw [sub_zero, norm_smul, mixedNullDirection_norm, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hr] at he
  have hfloor := (abs_le.mp he).1
  have hq := Real.sq_sqrt (add_nonneg (sq_nonneg r) hs)
  have hq0 := Real.sqrt_nonneg (r ^ 2 + s)
  have hm : (1 + k) * (H 0 / (1 + k)) = H 0 :=
    mul_div_cancel₀ _ (by linarith : 1 + k ≠ 0)
  have hsmall := mul_le_mul_of_nonneg_left hrm (by linarith : 0 ≤ 1 + k)
  rcases eq_or_lt_of_le hr with rfl | hr'
  · simp only [zero_smul]
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add] at hq hq0 ⊢
    nlinarith
  · have hstrict : Real.sqrt (r ^ 2 + s) < r + H 0 / 2 := by
      nlinarith [mul_pos hr' hT]
    nlinarith

/-- Every removed radius is at least m/2. This uses only the actual failed
square-root cutoff, not a monotone radial slice description. -/
theorem coarea_removed_radius_lower {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsT : s ≤ H 0 ^ 2 / 4)
    (hremoved : H (r • (u : JointSpace)) ≤ Real.sqrt (r ^ 2 + s)) :
    (H 0 / (1 + k)) / 2 ≤ r := by
  have hT := hH.tip_pos
  have he := h (r • (u : JointSpace)) 0
  rw [sub_zero, norm_smul, mixedNullDirection_norm, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hr] at he
  have hfloor := (abs_le.mp he).1
  have hq := Real.sq_sqrt (add_nonneg (sq_nonneg r) hs)
  have hq0 := Real.sqrt_nonneg (r ^ 2 + s)
  have hqb : Real.sqrt (r ^ 2 + s) ≤ r + H 0 / 2 := by
    nlinarith [mul_nonneg hr hT.le]
  have hm : (1 + k) * (H 0 / (1 + k)) = H 0 :=
    mul_div_cancel₀ _ (by linarith : 1 + k ≠ 0)
  apply le_of_not_gt
  intro hlt
  have hh := mul_lt_mul_of_pos_left hlt (by linarith : 0 < 1 + k)
  nlinarith

/-- The removed set lies in the explicit shell of width sigma/(m*(1-k)).
All contacts are retained, including slices with holes or multiple components. -/
theorem coarea_removed_shell {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hsT : s ≤ H 0 ^ 2 / 4) (hrR : r < mixedNullRadius H u)
    (hremoved : H (r • (u : JointSpace)) ≤ Real.sqrt (r ^ 2 + s)) :
    mixedNullRadius H u - s / ((H 0 / (1 + k)) * (1 - k)) ≤ r := by
  let m := H 0 / (1 + k)
  have hm : 0 < m := div_pos hH.tip_pos (by linarith)
  have hl := hH.coarea_removed_radius_lower hk h u hr.le hs hsT hremoved
  have hgap := hH.radial_gap_lower h u hrR.le
  have hsqrt := (mixedNull_sqrt_gap hr hs).2
  have hden : 0 < m * (1 - k) := mul_pos hm (sub_pos.mpr hk1)
  have hquot : s / (2 * r) ≤ s / m :=
    div_le_div_of_nonneg_left hs hm (by dsimp [m]; linarith)
  have hbound : (1 - k) * (mixedNullRadius H u - r) ≤ s / m := by
    linarith
  have hmul := (le_div_iff₀ hm).mp hbound
  have hdiff : mixedNullRadius H u - r ≤ s / (m * (1 - k)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  dsimp [m] at hdiff
  linarith

end MixedNullData
end BoundaryDraft

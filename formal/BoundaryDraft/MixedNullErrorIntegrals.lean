import BoundaryDraft.MixedNullErrorGeometry

/-! The evaluated radial majorants in NM5: the small-radius/logarithmic split
and the complete endpoint shell, before multiplication by sphere area. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- The exact two-piece majorant used in NM5 Step 3. -/
def mixedNullJacobianErrorBound (s r : ℝ) : ℝ :=
  if r ≤ Real.sqrt s then r / 2 else s / (4 * r)

theorem mixedNullJacobianErrorBound_nonneg {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    0 ≤ mixedNullJacobianErrorBound s r := by
  unfold mixedNullJacobianErrorBound
  split_ifs <;> positivity

theorem mixedNullJacobianErrorBound_bounds {s B : ℝ} (hs : 0 < s)
    (hB : Real.sqrt s ≤ B) :
    IntervalIntegrable (mixedNullJacobianErrorBound s) volume 0 B ∧
    (∫ r in (0 : ℝ)..B, mixedNullJacobianErrorBound s r) =
      s / 4 * (1 + Real.log (B / Real.sqrt s)) := by
  let q := Real.sqrt s
  change q ≤ B at hB
  have hq : 0 < q := Real.sqrt_pos.mpr hs
  have hB0 : 0 < B := hq.trans_le hB
  have hlo : IntervalIntegrable (mixedNullJacobianErrorBound s) volume 0 q := by
    apply ((by fun_prop : Continuous (fun r : ℝ => r / 2)).intervalIntegrable 0 q).congr
    rw [uIoc_of_le hq.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (if_pos hr.2).symm
  have hcont : ContinuousOn (fun r : ℝ => s / (4 * r)) (uIcc q B) := by
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro r hr
    have hqr : q ≤ r := by simpa only [min_eq_left hB] using hr.1
    exact mul_ne_zero (by norm_num) (hq.trans_le hqr).ne'
  have hhi : IntervalIntegrable (mixedNullJacobianErrorBound s) volume q B := by
    apply hcont.intervalIntegrable.congr
    rw [uIoc_of_le hB]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (if_neg (not_le.mpr hr.1)).symm
  refine ⟨hlo.trans hhi, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hlo hhi]
  have hl : (∫ r in (0 : ℝ)..q, mixedNullJacobianErrorBound s r) = s / 4 := by
    calc
      _ = ∫ r in (0 : ℝ)..q, r / 2 := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hqr : r ≤ q := by simpa only [max_eq_right hq.le] using hr.2
        exact if_pos hqr
      _ = _ := by
        rw [intervalIntegral.integral_div, integral_id]
        dsimp [q]
        rw [Real.sq_sqrt hs.le]
        ring
  have hh : (∫ r in q..B, mixedNullJacobianErrorBound s r) =
      (s / 4) * Real.log (B / q) := by
    calc
      _ = ∫ r in q..B, (s / 4) * r⁻¹ := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with r hr
        have hqr : q < r := by simpa only [min_eq_left hB] using hr.1
        rw [mixedNullJacobianErrorBound, if_neg (not_le.mpr hqr)]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hq hB0]
  rw [hl, hh]
  ring

/-- The full shell integral, without intersecting it with a presumed
connected positive-sigma slice. -/
theorem mixedNull_shell_integrable (R d A : ℝ) :
    Integrable ((Icc (R - d) R).indicator (fun _ : ℝ => A)) :=
  (integrable_indicator_iff measurableSet_Icc).mpr
    (continuous_const.integrableOn_Icc)

theorem mixedNull_shell_integral {R d A B : ℝ} (hd : 0 ≤ d) (hA : 0 ≤ A) :
    (∫ r in Ioc (0 : ℝ) B, (Icc (R - d) R).indicator (fun _ => A) r) ≤ A * d := by
  calc
    _ ≤ ∫ r : ℝ, (Icc (R - d) R).indicator (fun _ => A) r :=
      setIntegral_le_integral (mixedNull_shell_integrable R d A)
        (Eventually.of_forall fun r => Set.indicator_nonneg (fun _ _ => hA) r)
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith)]
      ring

end BoundaryDraft

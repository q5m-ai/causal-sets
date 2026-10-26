import BoundaryDraft.MixedNullWeightedError
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! The explicit NM5 error tends to zero and is monotone on the original
small-sigma interval. These facts concern the calculated expression, not a
postulated error modulus. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

@[simp] theorem mixedNullWeightedError_zero (T k M L : ℝ) :
    mixedNullWeightedError T k M L 0 = 0 := by simp [mixedNullWeightedError]

private theorem weightedError_normal_form {T k : ℝ} (hT : 0 < T) (hk1 : k < 1)
    (M L : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullWeightedError T k M L s =
      Real.pi * (M * (1 + Real.log (T / (1 - k)) +
        2 * (T / (1 - k)) / ((T / (1 + k)) * (1 - k))) + L * (T / (1 - k))) * s -
        (Real.pi * M / 2) * (s * Real.log s) := by
  by_cases hz : s = 0
  · simp [hz]
  · have hB : 0 < T / (1 - k) := div_pos hT (sub_pos.mpr hk1)
    have hq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hs (Ne.symm hz))).ne'
    rw [mixedNullWeightedError, Real.log_div hB.ne' hq, Real.log_sqrt hs]
    ring

/-- The actual explicit error tends to zero from the right. -/
theorem mixedNullWeightedError_right_continuous {T k : ℝ} (hT : 0 < T) (hk1 : k < 1)
    (M L : ℝ) : ContinuousWithinAt (mixedNullWeightedError T k M L) (Ici 0) 0 := by
  let a := Real.pi * (M * (1 + Real.log (T / (1 - k)) +
    2 * (T / (1 - k)) / ((T / (1 + k)) * (1 - k))) + L * (T / (1 - k)))
  let b := Real.pi * M / 2
  have hc : Continuous (fun s : ℝ => a * s - b * (s * Real.log s)) :=
    (continuous_const.mul continuous_id).sub (continuous_const.mul Real.continuous_mul_log)
  have he : (mixedNullWeightedError T k M L) =ᶠ[𝓝[≥] (0 : ℝ)]
      (fun s : ℝ => a * s - b * (s * Real.log s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact weightedError_normal_form hT hk1 M L hs
  exact hc.continuousWithinAt.congr_of_eventuallyEq he (by simp [a, b])

/-- NM7's monotonicity on the unchanged range 0 <= sigma <= T^2/4. -/
theorem mixedNullWeightedError_monotoneOn {T k M L : ℝ} (hT : 0 < T)
    (hk : 0 ≤ k) (hk1 : k < 1) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    MonotoneOn (mixedNullWeightedError T k M L) (Icc 0 (T ^ 2 / 4)) := by
  let B := T / (1 - k)
  let m := T / (1 + k)
  let a := Real.pi * (M * (1 + Real.log B + 2 * B / (m * (1 - k))) + L * B)
  let b := Real.pi * M / 2
  let f : ℝ → ℝ := fun s => a * s - b * (s * Real.log s)
  have hB : 0 < B := div_pos hT (sub_pos.mpr hk1)
  have hm : 0 < m := div_pos hT (by linarith)
  have hBT : T ≤ B := by
    apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    nlinarith [mul_nonneg hT.le hk]
  have hder {s : ℝ} (hs : 0 < s) : HasDerivAt f (a - b * (Real.log s + 1)) s := by
    convert ((hasDerivAt_id s).const_mul a).sub ((Real.hasDerivAt_mul_log hs.ne').const_mul b) using 1
    simp [f]
  have hc : Continuous f :=
    (continuous_const.mul continuous_id).sub (continuous_const.mul Real.continuous_mul_log)
  have hmono : MonotoneOn f (Icc 0 (T ^ 2 / 4)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc.continuousOn
      (f' := fun s => a - b * (Real.log s + 1))
    · intro s hs
      have hs' : s ∈ Ioo 0 (T ^ 2 / 4) := by simpa only [interior_Icc] using hs
      exact (hder hs'.1).hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 (T ^ 2 / 4) := by simpa only [interior_Icc] using hs
      have hq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs'.1
      have hqB : Real.sqrt s ≤ B := by
        have he := Real.sq_sqrt hs'.1.le
        nlinarith [hs'.2, Real.sqrt_nonneg s]
      have hlog : 0 ≤ Real.log (B / Real.sqrt s) :=
        Real.log_nonneg ((le_div_iff₀ hq).mpr (by simpa using hqB))
      have he : a - b * (Real.log s + 1) =
          Real.pi * (M * ((1 / 2 : ℝ) + Real.log (B / Real.sqrt s) +
            2 * B / (m * (1 - k))) + L * B) := by
        rw [Real.log_div hB.ne' hq.ne', Real.log_sqrt hs'.1.le]
        dsimp [a, b]
        ring
      rw [he]
      have hd : 0 ≤ 2 * B / (m * (1 - k)) :=
        div_nonneg (by positivity) (mul_nonneg hm.le (sub_nonneg.mpr hk1.le))
      positivity
  intro s hs t ht hst
  rw [weightedError_normal_form hT hk1 M L hs.1,
    weightedError_normal_form hT hk1 M L ht.1]
  exact hmono hs ht hst

end BoundaryDraft

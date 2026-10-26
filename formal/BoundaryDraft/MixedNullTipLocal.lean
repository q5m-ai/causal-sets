import BoundaryDraft.MixedNullTip
import BoundaryDraft.MixedNullErrorExtension

/-! NM9 with the written local weight bounds. Clipping is an auxiliary proof
construction only: both original action terms remain unchanged. -/
open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

theorem mixedNullClipWeight_tip_commute {M : ℝ} (hM : 0 ≤ M) (δ : ℝ) (w : Spacetime → ℝ) :
    mixedNullTipWeight δ (mixedNullClipWeight M w) = mixedNullClipWeight M (mixedNullTipWeight δ w) := by
  funext p
  unfold mixedNullTipWeight mixedNullClipWeight
  dsimp only
  split_ifs
  · rfl
  · simp [min_eq_right hM, max_eq_right (neg_nonpos.mpr hM)]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

omit hH in
theorem tip_weightBound {w : Spacetime → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : MixedNullWeightBound H w M) (δ : ℝ) :
    MixedNullWeightBound H (mixedNullTipWeight δ w) M := by
  intro x hx t ht
  unfold mixedNullTipWeight
  split_ifs
  · exact hb x hx t ht
  · simpa using hM

/-- Uniform tip control for the original weight, which may be unbounded away
from the closed geometry box (for example, the coordinate time). -/
theorem weightedContinuumMean_tip_bound_local {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    {w : Spacetime → ℝ} (hw : Measurable w) {M : ℝ} (hM : 0 ≤ M)
    (hb : MixedNullWeightBound H w M) :
    ‖weightedContinuumMean ρ (mixedNullRegion H) (mixedNullTipWeight δ w)‖ ≤
      4 * M * Real.pi * δ ^ 2 := by
  have he := hH.weightedContinuumMean_tip_bound hρ hδ
    (mixedNullClipWeight_measurable hw M) (mixedNullClipWeight_bound hM w)
  rw [mixedNullClipWeight_tip_commute hM,
    hH.weightedContinuumMean_clip_eq (tip_weightBound hM hb δ)] at he
  exact he

end MixedNullData
end BoundaryDraft

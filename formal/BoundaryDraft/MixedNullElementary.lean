import BoundaryDraft.MixedNullReduction

/-! Quantitative causal monotonicity (MA5) and positive finite region volume.
These statements supplement, rather than strengthen the assumptions of, the
previous finite-density producer. -/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

/-- The full MA5 inequality retains the specified Lipschitz constant. -/
theorem mixedNull_floor_increment (H : Spatial → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hLip : ∀ x y, |H x - H y| ≤ κ * spatialDistance x y)
    {p q : Spacetime} (hpq : q ∈ causalFuture p) :
    (q 0 - p 0) - κ * spatialDistance (spatialPart p) (spatialPart q) ≤
        (q 0 + H (spatialPart q)) - (p 0 + H (spatialPart p)) ∧
      (1 - κ) * (q 0 - p 0) ≤
        (q 0 - p 0) - κ * spatialDistance (spatialPart p) (spatialPart q) := by
  have hh := (le_abs_self (H (spatialPart p) - H (spatialPart q))).trans
    (hLip (spatialPart p) (spatialPart q))
  have hd := spatialDistance_le_of_causalFuture p q hpq
  constructor <;> nlinarith

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Every admissible region contains an explicit interior point. -/
theorem timeAxis_in_region : timeAxis (-H 0 / 2) ∈ mixedNullRegion H := by
  have hs : spatialPart (timeAxis (-H 0 / 2)) = 0 := by
    ext i
    simp [spatialPart]
  have hT := hH.tip_pos
  constructor
  · simpa only [hs, timeAxis_zero] using (show -H 0 < -H 0 / 2 by linarith)
  · constructor
    · simpa only [Pi.zero_apply, timeAxis_zero] using
        (show -H 0 / 2 < 0 by linarith)
    · have hsq : 0 < (-H 0 / 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
      simpa [spatialSeparationSq] using hsq

theorem region_nonempty : (mixedNullRegion H).Nonempty :=
  ⟨timeAxis (-H 0 / 2), hH.timeAxis_in_region⟩

theorem region_volume_pos : 0 < volume (mixedNullRegion H) :=
  hH.isOpen_region.measure_pos volume hH.region_nonempty

theorem region_volume_lt_top : volume (mixedNullRegion H) < ⊤ :=
  hH.isBounded_region.measure_lt_top

theorem region_volumeReal_pos : 0 < volume.real (mixedNullRegion H) :=
  ENNReal.toReal_pos hH.region_volume_pos.ne' hH.region_volume_lt_top.ne

/-- The original finite-order observable is integrable before its expectation
is evaluated. The geometric hypotheses have already been discharged. -/
theorem integrable_discrete_action {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (discreteBDGAction ρ)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  hH.boundedCausalRegion.integrable_discreteBDGAction hρ

end MixedNullData
end BoundaryDraft

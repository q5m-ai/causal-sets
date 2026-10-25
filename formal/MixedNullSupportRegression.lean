import BoundaryDraft.MixedNullContract
import BoundaryDraft.MixedNullElementary
import BoundaryDraft.MixedNullWeighted
import BoundaryDraft.NullGaussianRight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independently expanded contracts for geometric and weighted support.
The original smooth class has genuine nonconstant members. The concentration
regression permits a cutoff jump away from zero. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace MixedNullSupportRegression
open BoundaryDraft

def sineFloor (x : Spatial) : ℝ := 1 + (1 / 5 : ℝ) * Real.sin (x 0)

theorem sineFloor_data : AdmissibleMixedNull sineFloor := by
  constructor
  · refine ⟨by norm_num [sineFloor], 1 / 5, by norm_num, by norm_num, ?_⟩
    intro x y
    have hl : LipschitzWith 1 Real.sin :=
      lipschitzWith_of_nnnorm_deriv_le Real.differentiable_sin (by
        intro s
        change ‖deriv Real.sin s‖ ≤ (1 : ℝ)
        rw [Real.deriv_sin, Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos s, Real.cos_le_one s⟩)
    have hs : |Real.sin (x 0) - Real.sin (y 0)| ≤ |x 0 - y 0| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul (x 0) (y 0)
    have hd : |x 0 - y 0| ≤ spatialDistance x y := by
      have he := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (y - x)) (0 : Fin 3)
      change ‖y 0 - x 0‖ ≤ spatialDistance x y at he
      simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    calc
      |sineFloor x - sineFloor y| = (1 / 5 : ℝ) * |Real.sin (x 0) - Real.sin (y 0)| := by
        unfold sineFloor
        rw [show 1 + 1 / 5 * Real.sin (x 0) - (1 + 1 / 5 * Real.sin (y 0)) =
          (1 / 5 : ℝ) * (Real.sin (x 0) - Real.sin (y 0)) by ring, abs_mul]
        norm_num
      _ ≤ (1 / 5 : ℝ) * spatialDistance x y :=
        mul_le_mul_of_nonneg_left (hs.trans hd) (by norm_num)
  · exact contDiff_const.add (contDiff_const.mul
      (Real.contDiff_sin.comp (EuclideanSpace.proj (0 : Fin 3) (𝕜 := ℝ)).contDiff))

example : sineFloor ![Real.pi / 2, 0, 0] ≠
    (sineFloor ![0, 0, 0] + sineFloor ![Real.pi, 0, 0]) / 2 := by
  norm_num [sineFloor, Real.sin_pi_div_two, Real.sin_pi]

-- No positivity outside the spatial domain is imposed on the floor.
def affineFloor (x : Spatial) : ℝ := 1 + (1 / 4 : ℝ) * x 0

theorem affineFloor_data : AdmissibleMixedNull affineFloor := by
  constructor
  · refine ⟨by norm_num [affineFloor], 1 / 4, by norm_num, by norm_num, ?_⟩
    intro x y
    have hd : |x 0 - y 0| ≤ spatialDistance x y := by
      have he := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (y - x)) (0 : Fin 3)
      change ‖y 0 - x 0‖ ≤ spatialDistance x y at he
      simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    calc
      |affineFloor x - affineFloor y| = (1 / 4 : ℝ) * |x 0 - y 0| := by
        unfold affineFloor
        rw [show 1 + 1 / 4 * x 0 - (1 + 1 / 4 * y 0) =
          (1 / 4 : ℝ) * (x 0 - y 0) by ring, abs_mul]
        norm_num
      _ ≤ (1 / 4 : ℝ) * spatialDistance x y :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
  · exact contDiff_const.add (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 3) (𝕜 := ℝ)).contDiff)

example : affineFloor ![-8, 0, 0] < 0 := by norm_num [affineFloor]

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    0 < volume {p : Spacetime | -H (spatialPart p) < p 0 ∧
      p 0 < 0 ∧ spatialSeparationSq p 0 < (0 - p 0) ^ 2} :=
  hH.region_volume_pos

-- The original positive-density law and discrete observable are integrable.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun c => discreteBDGAction ρ c)
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
        {p : Spacetime | -H (spatialPart p) < p 0 ∧
          p 0 < 0 ∧ spatialSeparationSq p 0 < (0 - p 0) ^ 2})) :=
  hH.integrable_discrete_action hρ

-- Expanding both weighted point and pair terms prevents a changed observable
-- or a partner restriction from passing under the weighted wrapper's name.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ}
    (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ p in mixedNullRegion H, w p) - ρ * ∫ p in mixedNullRegion H,
        w p * ∫ q in mixedNullRegion H ∩ causalFuture p,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        w p * Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) :=
  hH.weightedContinuumMean_eq_spacetimeGaussian hρ hw hb

-- A discontinuous cutoff is admissible: global continuity is not required.
def cutoff (s : ℝ) : ℝ := if s ≤ 1 then 1 else 0

example : Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
    (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * cutoff s))
    atTop (𝓝 4) := by
  have hm : Measurable cutoff :=
    measurable_const.ite measurableSet_Iic measurable_const
  have hcont : ContinuousAt cutoff 0 := by
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    simp [cutoff, hs.le]
  have hb (s : ℝ) (_ : 0 ≤ s) : ‖cutoff s‖ ≤ 1 := by
    unfold cutoff
    split <;> norm_num
  simpa [cutoff] using nullGaussian_density_limit_right cutoff hm hcont.continuousWithinAt 1 hb

end MixedNullSupportRegression

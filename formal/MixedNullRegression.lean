import BoundaryDraft.MixedNullReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independent contracts and a genuinely nonaffine floor. No limit or area
claim is smuggled into the finite-density regression. -/
open MeasureTheory Set
noncomputable section
namespace MixedNullRegression
open BoundaryDraft

-- The region is the actual MA1 region, with its strict null-cone boundary.
example (H : Spatial → ℝ) : mixedNullRegion H =
    {p : Spacetime | -H (spatialPart p) < p 0 ∧
      p 0 < 0 ∧ spatialSeparationSq p 0 < (0 - p 0) ^ 2} := rfl

-- The full closed interval is retained, including null pairs and endpoints.
example {H : Spatial → ℝ} (hH : MixedNullData H) {p q z : Spacetime}
    (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H)
    (hpz : z ∈ causalFuture p) (hzq : q ∈ causalFuture z) :
    z ∈ mixedNullRegion H := hH.causallyConvex p hp q hq ⟨hpz, hzq⟩

-- Independently expand the probability law and discrete observable.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) :=
  hH.expectedBDGAction_eq_spacetimeGaussian hρ

example {T : ℝ} (hT : 0 < T) : MixedNullData (fun _ => T) := by
  refine ⟨hT, 0, le_rfl, by norm_num, ?_⟩
  intro x y
  simp

def floor (x : Spatial) : ℝ := 1 + (1 / 4 : ℝ) * Real.sin (x 0)

theorem floor_data : MixedNullData floor := by
  refine ⟨by norm_num [floor], 1 / 4, by norm_num, by norm_num, ?_⟩
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
    |floor x - floor y| = (1 / 4 : ℝ) * |Real.sin (x 0) - Real.sin (y 0)| := by
      unfold floor
      rw [show 1 + 1 / 4 * Real.sin (x 0) - (1 + 1 / 4 * Real.sin (y 0)) =
        (1 / 4 : ℝ) * (Real.sin (x 0) - Real.sin (y 0)) by ring, abs_mul]
      norm_num
    _ ≤ (1 / 4 : ℝ) * spatialDistance x y :=
      mul_le_mul_of_nonneg_left (hs.trans hd) (by norm_num)

example : floor ![Real.pi / 2, 0, 0] ≠
    (floor ![0, 0, 0] + floor ![Real.pi, 0, 0]) / 2 := by
  norm_num [floor, Real.sin_pi_div_two, Real.sin_pi]

example : timeAxis (-1 / 2) ∈ mixedNullRegion floor := by
  have h1 : timeAxis (-(1 / 2)) (1 : Fin 4) = 0 := timeAxis_succ _ 0
  norm_num [mixedNullRegion, floor, spatialPart, chronologicalFuture,
    spatialSeparationSq, h1]

example {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (mixedNullRegion floor) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion floor,
        Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) :=
  floor_data.expectedBDGAction_eq_spacetimeGaussian hρ

end MixedNullRegression

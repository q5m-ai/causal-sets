import BoundaryDraft.ShortRemainderAdapter

/-! Independent scalar contracts and nonzero cutoff controls for S13.
These are not admissible curved spacetimes or a general short-action proof. -/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace ShortRemainderRegression
open BoundaryDraft

/-- A nonzero bounded measurable density with a genuine higher-power remainder. -/
def powerCutoff (p : ℝ) : ℝ → ℝ := (Ioo 0 1).indicator (fun w => w ^ p)

theorem measurable_powerCutoff (p : ℝ) : Measurable (powerCutoff p) :=
  (measurable_id.pow_const p).indicator measurableSet_Ioo

theorem powerCutoff_bound (p : ℝ) (hp : 0 ≤ p) (w : ℝ) :
    ‖powerCutoff p w‖ ≤ 1 := by
  by_cases hw : w ∈ Ioo (0 : ℝ) 1
  · rw [powerCutoff, indicator_of_mem hw, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hw.1.le _)]
    exact Real.rpow_le_one hw.1.le hw.2.le hp
  · simp [powerCutoff, indicator_of_not_mem hw]

theorem powerCutoff_nonzero (p : ℝ) : 0 < powerCutoff p (1 / 2) := by
  rw [powerCutoff, indicator_of_mem (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)]
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem powerCutoff_eventually (p : ℝ) :
    ∀ᶠ w in 𝓝[>] (0 : ℝ), powerCutoff p w = w ^ p := by
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  exact ⟨1, by norm_num, fun w hw => indicator_of_mem hw _⟩

theorem powerCutoff_even_limit (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / ((2 * N : ℕ) : ℝ)) *
      ∫ w : ℝ in Ioi 0, powerCutoff ((N : ℝ) + 1 / 2) w *
        dimensionKernel (2 * N) (c * ρ * w ^ (((2 * N : ℕ) : ℝ) / 2)))
      atTop (𝓝 0) := by
  apply dimensionKernel_short_remainder_even N hN _ (measurable_powerCutoff _) 1
    (fun w _ => powerCutoff_bound _ (by positivity) w) (fun _ => 0) 1 _ c hc
  filter_upwards [powerCutoff_eventually ((N : ℝ) + 1 / 2), self_mem_nhdsWithin]
    with w hw hp
  rw [hw]
  simp only [dimensionJet, zero_mul, Finset.sum_const_zero, sub_zero,
    Real.norm_eq_abs, one_mul]
  exact (abs_of_pos (Real.rpow_pos_of_pos hp ((N : ℝ) + 1 / 2))).le

theorem powerCutoff_odd_limit (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / ((2 * N + 1 : ℕ) : ℝ)) *
      ∫ w : ℝ in Ioi 0, powerCutoff ((N : ℝ) + 1) w *
        dimensionKernel (2 * N + 1) (c * ρ * w ^ (((2 * N + 1 : ℕ) : ℝ) / 2)))
      atTop (𝓝 0) := by
  apply dimensionKernel_short_remainder_odd N hN _ (measurable_powerCutoff _) 1
    (fun w _ => powerCutoff_bound _ (by positivity) w) (fun _ => 0) 1 _ c hc
  filter_upwards [powerCutoff_eventually ((N : ℝ) + 1), self_mem_nhdsWithin]
    with w hw hp
  simp only [dimensionJet, zero_mul, Finset.sum_const_zero, sub_zero, hw,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp ((N : ℝ) + 1)), one_mul]
  nlinarith [abs_nonneg (Real.log w), Real.rpow_pos_of_pos hp ((N : ℝ) + 1)]

-- The dimensions and REAL exponents are expanded independently of the adapter.
example (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (2 : ℝ) * ∫ w : ℝ in Ioi 0,
      powerCutoff (3 / 2) w * dimensionKernel 2 (c * ρ * w)) atTop (𝓝 0) := by
  convert powerCutoff_even_limit 1 (by decide) c hc using 1
  norm_num

example (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (5 / 3 : ℝ) * ∫ w : ℝ in Ioi 0,
      powerCutoff 2 w * dimensionKernel 3 (c * ρ * w ^ (3 / 2 : ℝ)))
      atTop (𝓝 0) := by
  convert powerCutoff_odd_limit 1 (by decide) c hc using 1
  norm_num

example (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (3 / 2 : ℝ) * ∫ w : ℝ in Ioi 0,
      powerCutoff (5 / 2) w * dimensionKernel 4 (c * ρ * w ^ (2 : ℝ)))
      atTop (𝓝 0) := by
  convert powerCutoff_even_limit 2 (by decide) c hc using 1
  norm_num

example (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (7 / 5 : ℝ) * ∫ w : ℝ in Ioi 0,
      powerCutoff 3 w * dimensionKernel 5 (c * ρ * w ^ (5 / 2 : ℝ)))
      atTop (𝓝 0) := by
  convert powerCutoff_odd_limit 2 (by decide) c hc using 1
  norm_num

example (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (4 / 3 : ℝ) * ∫ w : ℝ in Ioi 0,
      powerCutoff (7 / 2) w * dimensionKernel 6 (c * ρ * w ^ (3 : ℝ)))
      atTop (𝓝 0) := by
  convert powerCutoff_even_limit 3 (by decide) c hc using 1
  norm_num

-- The odd estimate retains its logarithm and the critical order 3/2, not 1.
example (R : ℝ → ℝ) (C : ℝ)
    (hR : ∀ᶠ w in 𝓝[>] (0 : ℝ), ‖R w‖ ≤ C * (w ^ (2 : ℝ) * (1 + |Real.log w|))) :
    R =o[𝓝[>] 0] (fun w : ℝ => w ^ (3 / 2 : ℝ)) := by
  have he : ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) := by norm_num
  convert short_odd_remainder_isLittleO 1 R C (by simpa only [he] using hR) using 1
  norm_num

end ShortRemainderRegression

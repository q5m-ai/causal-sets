import BoundaryDraft.DimensionCancellation

/-!
# The scalar implication in S13

The even/odd quantitative remainder bounds in S13 of
`notes/general-metric-short-remainders.md` imply the REAL half-dimensional
little-o hypothesis of `dimensionKernel_transverse_cancellation`.

This is an analytic implication, not a producer of the geometric bounds in
S9--S12, a curved short-action theorem, or a long/complement estimate. The
bounded measurable density and its actual quantitative estimate are explicit
hypotheses, never geometric admissibility fields. Polynomial cancellation is
on the whole positive half-line before domination.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A strictly higher real power is little-o on the positive side of zero. -/
theorem short_rpow_isLittleO {p q : ℝ} (hqp : q < p) :
    (fun w : ℝ => w ^ p) =o[𝓝[>] 0] (fun w => w ^ q) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun hz => ((Real.rpow_pos_of_pos hw q).ne' hz).elim
  · have hlim : Tendsto (fun w : ℝ => w ^ (p - q)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (sub_pos.mpr hqp).ne'] using
        (Real.continuousAt_rpow_const 0 (p - q)
          (Or.inr (sub_pos.mpr hqp).le)).tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact Real.rpow_sub hw p q

/-- The odd-dimensional logarithm still leaves a strictly positive power
margin. Its absolute value and the constant one are both retained. -/
theorem short_rpow_log_isLittleO {p q : ℝ} (hqp : q < p) :
    (fun w : ℝ => w ^ p * (1 + |Real.log w|)) =o[𝓝[>] 0]
      (fun w => w ^ q) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun hz => ((Real.rpow_pos_of_pos hw q).ne' hz).elim
  · have hp : Tendsto (fun w : ℝ => w ^ (p - q)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (sub_pos.mpr hqp).ne'] using
        (Real.continuousAt_rpow_const 0 (p - q)
          (Or.inr (sub_pos.mpr hqp).le)).tendsto.mono_left nhdsWithin_le_nhds
    have hl := (tendsto_log_mul_rpow_nhdsGT_zero (sub_pos.mpr hqp)).abs
    have hlim := hp.add hl
    simp only [abs_zero, add_zero] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hw (p - q)),
      Real.rpow_sub hw p q]
    ring

/-- Even S13: the half-power margin is strictly above the critical order N. -/
theorem short_even_remainder_isLittleO (N : ℕ) (R : ℝ → ℝ) (C : ℝ)
    (hR : ∀ᶠ w in 𝓝[>] (0 : ℝ), ‖R w‖ ≤ C * w ^ ((N : ℝ) + 1 / 2)) :
    R =o[𝓝[>] 0] (fun w : ℝ => w ^ (N : ℝ)) := by
  have hO : R =O[𝓝[>] 0] (fun w : ℝ => w ^ ((N : ℝ) + 1 / 2)) := by
    apply IsBigO.of_bound C
    filter_upwards [hR, self_mem_nhdsWithin] with w hw hp
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)] using hw
  exact hO.trans_isLittleO (short_rpow_isLittleO (by linarith))

/-- Odd S13: the critical order is N+1/2, NOT the integer jet order N. -/
theorem short_odd_remainder_isLittleO (N : ℕ) (R : ℝ → ℝ) (C : ℝ)
    (hR : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      ‖R w‖ ≤ C * (w ^ ((N : ℝ) + 1) * (1 + |Real.log w|))) :
    R =o[𝓝[>] 0] (fun w : ℝ => w ^ ((N : ℝ) + 1 / 2)) := by
  have hO : R =O[𝓝[>] 0] (fun w : ℝ =>
      w ^ ((N : ℝ) + 1) * (1 + |Real.log w|)) := by
    apply IsBigO.of_bound C
    filter_upwards [hR, self_mem_nhdsWithin] with w hw hp
    have hpos : 0 < w ^ ((N : ℝ) + 1) * (1 + |Real.log w|) :=
      mul_pos (Real.rpow_pos_of_pos hp _) (by positivity)
    simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hw
  exact hO.trans_isLittleO (short_rpow_log_isLittleO (by linarith))

/-- The even S13 scalar estimate, with the original density normalization
and no omitted kernel tail, implies signed transverse cancellation. -/
theorem dimensionKernel_short_remainder_even (N : ℕ) (hN : 1 ≤ N)
    (B : ℝ → ℝ) (hB : Measurable B) (M : ℝ)
    (hbound : ∀ w, 0 < w → ‖B w‖ ≤ M) (b : ℕ → ℝ) (C : ℝ)
    (hR : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      ‖B w - dimensionJet (2 * N) b w‖ ≤ C * w ^ ((N : ℝ) + 1 / 2))
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / ((2 * N : ℕ) : ℝ)) *
      ∫ w : ℝ in Ioi 0, B w * dimensionKernel (2 * N)
        (c * ρ * w ^ (((2 * N : ℕ) : ℝ) / 2))) atTop (𝓝 0) := by
  apply dimensionKernel_transverse_cancellation (2 * N) (by omega)
    B hB M hbound b _ c hc
  have hhalf : ((2 * N : ℕ) : ℝ) / 2 = (N : ℝ) := by push_cast; ring
  simpa only [hhalf] using
    short_even_remainder_isLittleO N (fun w => B w - dimensionJet (2 * N) b w) C hR

/-- The odd S13 scalar estimate is sufficient at its genuine fractional
critical order, for every odd physical dimension at least three. -/
theorem dimensionKernel_short_remainder_odd (N : ℕ) (hN : 1 ≤ N)
    (B : ℝ → ℝ) (hB : Measurable B) (M : ℝ)
    (hbound : ∀ w, 0 < w → ‖B w‖ ≤ M) (b : ℕ → ℝ) (C : ℝ)
    (hR : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      ‖B w - dimensionJet (2 * N + 1) b w‖ ≤
        C * (w ^ ((N : ℝ) + 1) * (1 + |Real.log w|)))
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun ρ : ℝ => ρ ^ (1 + 2 / ((2 * N + 1 : ℕ) : ℝ)) *
      ∫ w : ℝ in Ioi 0, B w * dimensionKernel (2 * N + 1)
        (c * ρ * w ^ (((2 * N + 1 : ℕ) : ℝ) / 2))) atTop (𝓝 0) := by
  apply dimensionKernel_transverse_cancellation (2 * N + 1) (by omega)
    B hB M hbound b _ c hc
  have hhalf : ((2 * N + 1 : ℕ) : ℝ) / 2 = (N : ℝ) + 1 / 2 := by push_cast; ring
  simpa only [hhalf] using
    short_odd_remainder_isLittleO N (fun w => B w - dimensionJet (2 * N + 1) b w) C hR

end BoundaryDraft

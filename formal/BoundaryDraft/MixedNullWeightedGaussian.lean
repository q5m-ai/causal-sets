import BoundaryDraft.MixedNullErrorRegularity

/-! NM6--NM7 with the original signed action normalization. The complementary
error function is the actual normalized Gaussian tail integral, not an axiom. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- The conventional complementary error function, defined by its normalized
Gaussian tail. In particular this is an actual integral, not a formal symbol. -/
def mixedNullErfc (t : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ u in Ioi t, Real.exp (-u ^ 2)

theorem mixedNullErfc_nonneg (t : ℝ) : 0 ≤ mixedNullErfc t := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- NM6: the physical positive half-Gaussian has mass four. -/
theorem mixedNull_gaussian_mass {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2)) = 4 := by
  have he := nullGaussian_density_rescaling ρ hρ (fun _ => 1)
  simpa only [mul_one, integral_nullGaussian] using he

private theorem gaussian_scaled_tail {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    (∫ s in Ioi t, Real.exp (-(Real.pi / 24) * ρ * s ^ 2)) =
      (Real.sqrt ((Real.pi / 24) * ρ))⁻¹ *
        ∫ u in Ioi (Real.sqrt ((Real.pi / 24) * ρ) * t), Real.exp (-u ^ 2) := by
  have hc : 0 < (Real.pi / 24) * ρ := mul_pos (div_pos Real.pi_pos (by norm_num)) hρ
  have he := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u ^ 2)) t (Real.sqrt_pos.mpr hc)
  simp only [smul_eq_mul, mul_pow, Real.sq_sqrt hc.le] at he
  convert he using 1
  congr 1
  funext s
  congr 1
  ring

/-- Exact NM7 tail correspondence, including the factor four and the
argument sqrt(c*rho)*s. -/
theorem mixedNull_gaussian_tail {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ s in Ioi t, Real.exp (-(Real.pi / 24) * ρ * s ^ 2)) =
      4 * mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * t) := by
  have hg : (∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi (1 : ℝ)
  have hm := mixedNull_gaussian_mass hρ
  rw [gaussian_scaled_tail hρ 0, mul_zero, hg, ← mul_assoc] at hm
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hcoef : (4 / Real.sqrt 6) * Real.sqrt ρ * (Real.sqrt ((Real.pi / 24) * ρ))⁻¹ =
      4 * (2 / Real.sqrt Real.pi) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hp).mpr
    nlinarith [hm]
  rw [gaussian_scaled_tail hρ t, ← mul_assoc, hcoef, mixedNullErfc]
  ring

/-- The actual tail tends to zero; no asymptotic tail hypothesis is assumed. -/
theorem mixedNullErfc_tendsto_zero : Tendsto mixedNullErfc atTop (𝓝 0) := by
  have hi : Integrable (fun u : ℝ => Real.exp (-u ^ 2)) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have ht : Tendsto (fun t : ℝ => ∫ u : ℝ, (Ioi t).indicator (fun u => Real.exp (-u ^ 2)) u)
      atTop (𝓝 (∫ _u : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => Real.exp (-u ^ 2))
    · exact Eventually.of_forall fun t => (hi.indicator measurableSet_Ioi).aestronglyMeasurable
    · apply Eventually.of_forall
      intro t
      filter_upwards [] with u
      by_cases hu : u ∈ Ioi t
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      · rw [Set.indicator_of_not_mem hu, norm_zero]
        exact (Real.exp_pos _).le
    · exact hi
    · filter_upwards [] with u
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop u] with t ht
      exact (Set.indicator_of_not_mem (show u ∉ Ioi t from not_lt.mpr ht) _).symm
  simp only [integral_indicator measurableSet_Ioi, integral_zero] at ht
  simpa only [mul_zero] using ht.const_mul (2 / Real.sqrt Real.pi)

@[simp] theorem mixedNullErfc_zero : mixedNullErfc 0 = 1 := by
  have hm := mixedNull_gaussian_mass (by norm_num : (0 : ℝ) < 1)
  have ht := mixedNull_gaussian_tail (by norm_num : (0 : ℝ) < 1) 0
  rw [mul_zero] at ht
  linarith

/-- The tail term vanishes with density for each fixed positive split.
Together with the explicit error's right limit this retains NM7's limit order. -/
theorem mixedNullErfc_density_tendsto_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ρ : ℝ => mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s))
      atTop (𝓝 0) := by
  apply mixedNullErfc_tendsto_zero.comp
  apply tendsto_atTop.mpr
  intro b
  have hc : 0 < Real.pi / 24 := div_pos Real.pi_pos (by norm_num)
  filter_upwards [eventually_ge_atTop ((b / s) ^ 2 / (Real.pi / 24))] with ρ hρ
  have hsq : (b / s) ^ 2 ≤ (Real.pi / 24) * ρ := by
    have hh := (div_le_iff₀ hc).mp hρ
    nlinarith
  exact (div_le_iff₀ hs).mp (Real.le_sqrt_of_sq_le hsq)

/-- Analytic Gaussian error consumer. The geometric application below
supplies its local estimate from the actual NM5 producer. -/
theorem mixedNull_gaussian_error (W : ℝ → ℝ) (hW : Measurable W)
    {C E s ρ : ℝ} (hE : 0 ≤ E) (hs : 0 < s) (hρ : 0 < ρ)
    (hb : ∀ t, 0 ≤ t → ‖W t‖ ≤ C)
    (he : ∀ t ∈ Ioc (0 : ℝ) s, ‖W t - W 0‖ ≤ E) :
    ‖(4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ t in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * t ^ 2) * W t) - 4 * W 0‖ ≤
      4 * E + 8 * C * mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s) := by
  let G : ℝ → ℝ := fun t => Real.exp (-(Real.pi / 24) * ρ * t ^ 2)
  let N := (4 / Real.sqrt 6) * Real.sqrt ρ
  have hN : 0 < N := by dsimp [N]; positivity
  have hG (t : ℝ) : 0 ≤ G t := (Real.exp_pos _).le
  have hg : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa only [G, neg_mul] using
      (integrable_exp_neg_mul_sq (mul_pos (div_pos Real.pi_pos (by norm_num)) hρ)).integrableOn
  have hiW : IntegrableOn (fun t => G t * W t) (Ioi (0 : ℝ)) := by
    have hb' : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ‖W t‖ ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht.le
    simpa only [mul_comm] using hg.bdd_mul' hW.aestronglyMeasurable hb'
  have hiTail : IntegrableOn ((Ioi s).indicator G) (Ioi (0 : ℝ)) := hg.indicator measurableSet_Ioi
  have hiE := (hg.const_mul E).add (hiTail.const_mul (2 * C))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖G t * (W t - W 0)‖ ≤ E * G t + (2 * C) * (Ioi s).indicator G t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hG t)]
    by_cases hts : t ≤ s
    · rw [Set.indicator_of_not_mem (show t ∉ Ioi s from not_lt.mpr hts), mul_zero, add_zero, mul_comm]
      exact mul_le_mul_of_nonneg_right (he t ⟨ht, hts⟩) (hG t)
    · rw [Set.indicator_of_mem (show t ∈ Ioi s from lt_of_not_ge hts)]
      have hd : ‖W t - W 0‖ ≤ 2 * C :=
        (norm_sub_le _ _).trans (by linarith [hb t ht.le, hb 0 le_rfl])
      have hh := mul_le_mul_of_nonneg_left hd (hG t)
      nlinarith [mul_nonneg hE (hG t)]
  have hi : N * (∫ t in Ioi (0 : ℝ), G t * (W t - W 0)) =
      N * (∫ t in Ioi (0 : ℝ), G t * W t) - 4 * W 0 := by
    simp_rw [mul_sub]
    rw [integral_sub hiW (hg.mul_const (W 0)), integral_mul_const, mul_sub]
    have hm : N * (∫ t in Ioi (0 : ℝ), G t) = 4 := mixedNull_gaussian_mass hρ
    rw [← mul_assoc, hm]
  have htail : (∫ t in Ioi (0 : ℝ), (Ioi s).indicator G t) = ∫ t in Ioi s, G t := by
    rw [setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (show Ioi s ⊆ Ioi (0 : ℝ) from fun t ht => hs.trans ht)]
  have hscale : N * (∫ t in Ioi (0 : ℝ), E * G t + (2 * C) * (Ioi s).indicator G t) =
      4 * E + 8 * C * mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s) := by
    rw [integral_add (hg.const_mul E) (hiTail.const_mul (2 * C)),
      integral_const_mul, integral_const_mul, htail]
    calc
      _ = E * (N * ∫ t in Ioi (0 : ℝ), G t) +
          (2 * C) * (N * ∫ t in Ioi s, G t) := by ring
      _ = _ := by rw [mixedNull_gaussian_mass hρ, mixedNull_gaussian_tail hρ s]; ring
  change ‖N * (∫ t in Ioi (0 : ℝ), G t * W t) - 4 * W 0‖ ≤ _
  rw [← hi, norm_mul, Real.norm_eq_abs, abs_of_pos hN, ← hscale]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hiE hbound) hN.le

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- NM7 for the actual unchanged weighted action, supplied by the geometric
NM5 estimate. All geometry and cutoffs are fixed as density varies. -/
theorem weightedContinuumMean_error {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s ρ : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) (hρ : 0 < ρ) :
    ‖weightedContinuumMean ρ (mixedNullRegion H) w - 4 * mixedNullWeightedGlobalWeight H w 0‖ ≤
      4 * mixedNullWeightedError (H 0) k M L s +
        8 * M * Real.pi * (H 0 / (1 - k)) ^ 2 *
          mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s) := by
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  have hm := mixedNullWeightedError_monotoneOn hH.tip_pos hk hk1 hM hL
  have hE : 0 ≤ mixedNullWeightedError (H 0) k M L s := by
    have he := hm (show (0 : ℝ) ∈ Icc 0 (H 0 ^ 2 / 4) from ⟨le_rfl, by positivity⟩)
      ⟨hs.le, hsT⟩ hs.le
    simpa only [mixedNullWeightedError_zero] using he
  rw [hH.weightedContinuumMean_eq_globalWeight hρ hw hb]
  have he := mixedNull_gaussian_error (mixedNullWeightedGlobalWeight H w)
    (hH.measurable_weightedGlobalWeight hw) (C := M * Real.pi * (H 0 / (1 - k)) ^ 2)
    hE hs hρ
    (fun t _ => hH.weightedGlobalWeight_bound hw hb hk hk1 h t)
    (fun t ht' => (hH.weightedGlobalWeight_error hw hb hL ht hk hk1 h ht'.1 (ht'.2.trans hsT)).trans
      (hm ⟨ht'.1.le, ht'.2.trans hsT⟩ ⟨hs.le, hsT⟩ ht'.2))
  convert he using 1
  ring

/-- The actual NM5 estimate also supplies weighted right continuity under
only the closed-fibre time Lipschitz assumption, not global time continuity. -/
theorem weightedGlobalWeight_right_continuous_of_timeLipschitz
    {w : Spacetime → ℝ} (hw : Measurable w) {M L : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L) :
    ContinuousWithinAt (mixedNullWeightedGlobalWeight H w) (Ici 0) 0 := by
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  have hlim := mixedNullWeightedError_right_continuous hH.tip_pos hk1 M L
  rw [ContinuousWithinAt, mixedNullWeightedError_zero] at hlim
  have hbound : ∀ᶠ s in 𝓝[≥] (0 : ℝ),
      ‖mixedNullWeightedGlobalWeight H w s - mixedNullWeightedGlobalWeight H w 0‖ ≤
        mixedNullWeightedError (H 0) k M L s := by
    have hpos : 0 < H 0 ^ 2 / 4 := div_pos (sq_pos_of_pos hH.tip_pos) (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with s hs hsT
    have hs0 : 0 ≤ s := hs
    rcases eq_or_lt_of_le hs0 with rfl | hs'
    · simp
    · exact hH.weightedGlobalWeight_error hw hb hL ht hk hk1 h hs' hsT.le
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim)

/-- Weighted scalar limit from the closed-fibre Lipschitz data and the
actual error producer, retaining arbitrary measurable spatial cutoffs. -/
theorem weightedContinuumMean_limit_of_timeLipschitz
    {w : Spacetime → ℝ} (hw : Measurable w) {M L : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (4 * mixedNullWeightedGlobalWeight H w 0)) := by
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  have hlim := nullGaussian_density_limit_right (mixedNullWeightedGlobalWeight H w)
    (hH.measurable_weightedGlobalWeight hw)
    (hH.weightedGlobalWeight_right_continuous_of_timeLipschitz hw hb hL ht)
    (M * mixedNullGlobalWeight H 0) (fun s _ =>
      (hH.weightedGlobalWeight_norm_le hw hb s).trans
        (mul_le_mul_of_nonneg_left (hH.globalWeight_le_zero s) hM))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (hH.weightedContinuumMean_eq_globalWeight hρ hw hb).symm

end MixedNullData
end BoundaryDraft

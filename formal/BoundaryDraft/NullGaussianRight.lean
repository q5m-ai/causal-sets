import BoundaryDraft.NullGaussian

/-! One-sided Gaussian concentration for measurable cutoff weights.
The entire signed BDG action is reduced separately before this positive
Gaussian is used. This module assumes no geometric interval representation. -/

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Positive densities approach zero width from the positive side. -/
theorem tendsto_nullGaussian_width_right :
    Tendsto (fun ρ : ℝ => (Real.sqrt ρ)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_nullGaussian_width, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact inv_pos.mpr (Real.sqrt_pos.mpr hρ)

/-- Cutoffs may jump away from zero; no global continuity is required. -/
theorem integrableOn_nullGaussian_rescaled_right (B : ℝ → ℝ) (hB : Measurable B)
    (C : ℝ) (hbound : ∀ x, 0 ≤ x → ‖B x‖ ≤ C) {ε : ℝ} (hε : 0 ≤ ε) :
    IntegrableOn (fun u => nullGaussian u * B (ε * u)) (Ioi (0 : ℝ)) := by
  apply (integrableOn_nullGaussian.norm.mul_const C).mono'
    (integrableOn_nullGaussian.aestronglyMeasurable.mul
      (hB.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖nullGaussian u * B (ε * u)‖ ≤ ‖nullGaussian u‖ * C
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hbound _ (mul_nonneg hε hu.le)) (norm_nonneg _)

/-- MA concentration only needs right continuity at zero, not continuity of
weights across moving cutoffs or at negative proper-time-square arguments. -/
theorem nullGaussian_density_limit_right (B : ℝ → ℝ) (hB : Measurable B)
    (hB0 : ContinuousWithinAt B (Ici 0) 0)
    (C : ℝ) (hbound : ∀ x, 0 ≤ x → ‖B x‖ ≤ C) :
    Tendsto (fun ρ : ℝ => (4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ σ in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * σ ^ 2) * B σ))
      atTop (𝓝 (4 * B 0)) := by
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hu.le
  have hs := signed_rescaling_limit_right _ nullGaussian B hnonneg
    integrableOn_nullGaussian hB hB0 C hbound
  rw [integral_nullGaussian, one_mul] at hs
  have h := (hs.comp tendsto_nullGaussian_width_right).const_mul 4
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  exact (nullGaussian_density_rescaling ρ hρ B).symm

end BoundaryDraft

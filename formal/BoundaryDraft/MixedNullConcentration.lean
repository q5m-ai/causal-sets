import BoundaryDraft.MixedNullGaussian
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
Three-dimensional spatial domination and its application to the actual
one-tip Gaussian fibre. The origin is null, but its `1/r` singularity is not
discarded: the radial Jacobian makes it locally integrable.
-/
open MeasureTheory Set Filter Metric
set_option maxHeartbeats 1000000
open scoped Topology ENNReal
noncomputable section
namespace BoundaryDraft

/-- Compactly supported radial reciprocal norm in genuine Euclidean 3-space. -/
def mixedNullRadialDominator (B : ℝ) (x : JointSpace) : ℝ :=
  (ball (0 : JointSpace) B).indicator (fun x => 2 / ‖x‖) x

/-- The radial reciprocal-norm dominator is integrable at the origin in three
dimensions. This proof uses the actual Haar-to-sphere product-measure theorem,
not a postulated spatial weight. -/
theorem integrable_mixedNullRadialDominator (B : ℝ) :
    Integrable (mixedNullRadialDominator B) (volume : Measure JointSpace) := by
  let v : Ioi (0 : ℝ) → ℝ := fun r => if (r : ℝ) < B then 2 / (r : ℝ) else 0
  let μ : Measure (Ioi (0 : ℝ)) := Measure.volumeIoiPow 2
  have hline : IntegrableOn (fun r : ℝ => 2 * r) (Ioo 0 B) :=
    (by fun_prop : Continuous (fun r : ℝ => 2 * r)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hline' : Integrable ((Ioo 0 B).indicator (fun r : ℝ => 2 * r)) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hline
  have hcomap : Integrable (fun r : Ioi (0 : ℝ) =>
      if (r : ℝ) < B then 2 * (r : ℝ) else 0)
      ((volume : Measure ℝ).comap (↑)) := by
    convert (integrableOn_iff_comap_subtypeVal (s := Ioi (0 : ℝ))
      measurableSet_Ioi).mp hline'.integrableOn using 1
    funext r
    by_cases hb : (r : ℝ) < B
    · have hp : 0 < (r : ℝ) := r.property
      simp [Set.indicator, hp, hb]
    · simp [Set.indicator, hb]
  have hμ : Integrable v μ := by
    dsimp [μ, Measure.volumeIoiPow]
    apply (integrable_withDensity_iff_integrable_smul'
      (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ 2))
      (by fun_prop) (by filter_upwards [] with r; simp)).mpr
    convert hcomap using 1
    funext r
    simp only [ENNReal.toReal_ofReal (sq_nonneg (r : ℝ)), smul_eq_mul]
    dsimp [v]
    split_ifs with hr
    · have hp := r.property
      have hne : (r : ℝ) ≠ 0 := ne_of_gt r.property
      field_simp
      ring
    · simp
  have hprod : Integrable (fun z : MixedNullDirection × Ioi (0 : ℝ) => v z.2)
      ((volume : Measure JointSpace).toSphere.prod μ) := by
    have hc : Integrable (fun _ : MixedNullDirection => (1 : ℝ))
        ((volume : Measure JointSpace).toSphere) := integrable_const 1
    simpa only [one_mul] using hc.mul_prod hμ
  let p := homeomorphUnitSphereProd JointSpace
  have hpolar : MeasurePreserving p
      ((volume : Measure JointSpace).comap (fun x : ({0}ᶜ : Set JointSpace) => (x : JointSpace)))
      ((volume : Measure JointSpace).toSphere.prod μ) := by
    simpa only [μ, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      ((volume : Measure JointSpace)).measurePreserving_homeomorphUnitSphereProd
  have hsub : Integrable (fun x : ({0}ᶜ : Set JointSpace) =>
      mixedNullRadialDominator B x) ((volume : Measure JointSpace).comap (↑)) := by
    have htmp := (hpolar.integrable_comp_emb p.measurableEmbedding).mpr hprod
    convert htmp using 1
    funext x
    simp [p, mixedNullRadialDominator, v,
      homeomorphUnitSphereProd_apply_snd_coe, Set.indicator, mem_ball, dist_zero_right]
  have haway : IntegrableOn (mixedNullRadialDominator B) ({0}ᶜ : Set JointSpace) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mpr hsub
  have hzero : IntegrableOn (mixedNullRadialDominator B) ({0} : Set JointSpace) := by
    apply integrableOn_singleton_iff.mpr
    left
    simp [mixedNullRadialDominator]
  simpa only [Set.compl_union_self, integrableOn_univ] using haway.union hzero


/-- The actual spatial Gaussian fibre after vertical Fubini. -/
def mixedNullSpatialGaussian (H : Spatial → ℝ) (ρ : ℝ) (x : JointSpace) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ *
    ∫ t in ‖x‖..H x, Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2)

/-- The variable-endpoint fibre is continuous in spatial coordinates at each
fixed density; measurability is not inferred from pointwise asymptotics. -/
theorem mixedNullSpatialGaussian_continuous (H : Spatial → ℝ) (hc : Continuous H)
    (ρ : ℝ) : Continuous (mixedNullSpatialGaussian H ρ) := by
  let f : JointSpace → ℝ → ℝ := fun x t =>
    Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2)
  have hf : Continuous (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    exact Real.continuous_exp.comp
      (continuous_const.mul (((continuous_snd.pow 2).sub
        ((continuous_norm.comp continuous_fst).pow 2)).pow 2))
  have hleft : Continuous (fun x : JointSpace => ∫ t in (0 : ℝ)..‖x‖, f x t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_norm
  have hright : Continuous (fun x : JointSpace => ∫ t in (0 : ℝ)..H x, f x t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
      (hc.comp (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)))
  have heq (x : JointSpace) :
      (∫ t in ‖x‖..H x, f x t) =
        (∫ t in (0 : ℝ)..H x, f x t) - (∫ t in (0 : ℝ)..‖x‖, f x t) := by
    have hfx : Continuous (f x) := by
      dsimp [f]
      exact Real.continuous_exp.comp
        (continuous_const.mul (((continuous_id.pow 2).sub (continuous_const.pow 2)).pow 2))
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hfx.intervalIntegrable 0 ‖x‖) (hfx.intervalIntegrable ‖x‖ (H x))
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hi
  have hh : Continuous (fun x : JointSpace => ∫ t in ‖x‖..H x, f x t) := by
    convert hright.sub hleft using 1
    funext x
    exact heq x
  exact continuous_const.mul hh

/-- The region's spatial projection has a fixed bounded Euclidean support,
from the original strict Lipschitz field (not an extra analytic premise). -/
theorem MixedNullData.spatialDomain_ball {H : Spatial → ℝ} (hH : MixedNullData H) :
    ∃ B : ℝ, 0 < B ∧ mixedNullSpatialDomain H ⊆ ball (0 : JointSpace) B := by
  obtain ⟨k, hk, hk1, hLip⟩ := hH.lipschitz
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  have heq : (1 - k) * B = H 0 := by
    dsimp [B]
    exact mul_div_cancel₀ _ (sub_pos.mpr hk1).ne'
  refine ⟨B, hB, fun x hx => ?_⟩
  have he := hLip x 0
  change |H x - H 0| ≤ k * ‖(0 : JointSpace) - x‖ at he
  rw [zero_sub, norm_neg] at he
  have hfloor : H x ≤ H 0 + k * ‖x‖ := by
    linarith [le_abs_self (H x - H 0)]
  have hn : 0 ≤ ‖x‖ := norm_nonneg _
  have hxb : ‖x‖ < B := by
    have hh : ‖x‖ < H x := hx
    nlinarith
  simpa only [mem_ball, dist_zero_right] using hxb


/-- All spatial integrability, measurability and pointwise limits required by
dominated convergence follow from the actual region and its vertical fibres.
The origin is removed only as a volume-null point, after proving the singular
dominator integrable. -/
theorem MixedNullData.spatialGaussian_limit {H : Spatial → ℝ} (hH : MixedNullData H) :
    Tendsto (fun ρ : ℝ => ∫ x in mixedNullSpatialDomain H,
      mixedNullSpatialGaussian H ρ x) atTop (𝓝 (mixedNullSpatialLimit H)) := by
  obtain ⟨B, hB, hDB⟩ := hH.spatialDomain_ball
  let D := mixedNullSpatialDomain H
  let μ : Measure JointSpace := (volume : Measure JointSpace).restrict D
  have hm : MeasurableSet D := by
    exact (isOpen_lt continuous_norm (hH.continuous.comp
      (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)))).measurableSet
  have hdom : Integrable (mixedNullRadialDominator B) μ :=
    (integrable_mixedNullRadialDominator B).integrableOn
  have hne : ∀ᵐ x : JointSpace ∂μ, x ≠ 0 := by
    apply ae_restrict_of_ae
    apply ae_iff.mpr
    simp
  have hp : ∀ᵐ x : JointSpace ∂μ,
      x ∈ D ∧ x ≠ 0 := by
    filter_upwards [ae_restrict_mem hm, hne] with x hx hx0
    exact ⟨hx, hx0⟩
  have hmeas : ∀ᶠ ρ : ℝ in atTop,
      AEStronglyMeasurable (mixedNullSpatialGaussian H ρ) μ :=
    Filter.Eventually.of_forall fun ρ =>
      (mixedNullSpatialGaussian_continuous H hH.continuous ρ).measurable.aestronglyMeasurable
  have hbnd : ∀ᶠ ρ : ℝ in atTop, ∀ᵐ x : JointSpace ∂μ,
      ‖mixedNullSpatialGaussian H ρ x‖ ≤ mixedNullRadialDominator B x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    filter_upwards [hp] with x ⟨hx, hx0⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hF := mixedNull_fibre_bound ‖x‖ (H x) ρ hr hx hρ
    rw [mixedNullRadialDominator, Set.indicator_of_mem (hDB hx), Real.norm_eq_abs]
    change |(4 / Real.sqrt 6) * Real.sqrt ρ *
      (∫ t in ‖x‖..H x,
        Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2))| ≤ 2 / ‖x‖
    rw [abs_of_nonneg hF.1]
    exact hF.2
  have hlim : ∀ᵐ x : JointSpace ∂μ,
      Tendsto (fun ρ => mixedNullSpatialGaussian H ρ x) atTop (𝓝 (2 / ‖x‖)) := by
    filter_upwards [hp] with x ⟨hx, hx0⟩
    exact mixedNull_fibre_limit ‖x‖ (H x) (norm_pos_iff.mpr hx0) hx
  exact tendsto_integral_filter_of_dominated_convergence
    (mixedNullRadialDominator B) hmeas hbnd hdom hlim

/-- MA8 followed by the actual time-fibre substitution and three-dimensional
spatial dominated convergence proves the deterministic *intermediate* limit.
Identification with induced area is a separate geometry theorem. -/
theorem MixedNullData.continuumMean_tendsto_spatialLimit {H : Spatial → ℝ}
    (hH : MixedNullData H) :
    Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion H))
      atTop (𝓝 (mixedNullSpatialLimit H)) := by
  apply hH.spatialGaussian_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  rw [hH.continuumMean_eq_spatialGaussian hρ]
  simp only [mixedNullSpatialGaussian, integral_const_mul]

end BoundaryDraft

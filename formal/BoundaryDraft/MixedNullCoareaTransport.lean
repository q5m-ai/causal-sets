import BoundaryDraft.MixedNullCoareaWeighted

/-! Measurable signed vertical and proper-time-squared transport for NM4.
The change of variables uses the actual injective polynomial map on each
positive-radius time fibre, so no continuity of the source weight is required. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- General signed time-fibre substitution. The Jacobian theorem handles
measurable signed functions as well as continuous ones; no endpoint derivative
of the square root at the tip is used. -/
theorem mixedNull_fibre_integral_coarea (g : ℝ → ℝ) {r L : ℝ}
    (hr : 0 < r) (hrL : r < L) :
    (∫ t in r..L, g t) = ∫ s in Ioi (0 : ℝ),
      g (Real.sqrt (r ^ 2 + s)) * mixedNullFibreWeight r L s := by
  have hL : 0 < L := hr.trans hrL
  let a := L ^ 2 - r ^ 2
  have ha : 0 < a := by dsimp [a]; nlinarith
  have himage : (fun t : ℝ => t ^ 2 - r ^ 2) '' Ioo r L = Ioo 0 a := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> dsimp [a] <;> nlinarith [ht.1, ht.2]
    · intro hs
      have hsq : 0 ≤ r ^ 2 + s := by nlinarith [hs.1, sq_nonneg r]
      have ht : Real.sqrt (r ^ 2 + s) ∈ Ioo r L := by
        constructor
        · have hp := Real.sqrt_nonneg (r ^ 2 + s)
          have he := Real.sq_sqrt hsq
          nlinarith [hs.1]
        · apply (Real.sqrt_lt' hL).mpr
          have hh : s < L ^ 2 - r ^ 2 := hs.2
          linarith
      exact ⟨Real.sqrt (r ^ 2 + s), ht, by dsimp only; rw [Real.sq_sqrt hsq]; ring⟩
  have hd (t : ℝ) (_ht : t ∈ Ioo r L) :
      HasDerivWithinAt (fun t : ℝ => t ^ 2 - r ^ 2) (2 * t) (Ioo r L) t := by
    convert (((hasDerivAt_id t).pow 2).sub_const (r ^ 2)).hasDerivWithinAt using 1
    simp [id_eq, mul_comm]
  have hinj : InjOn (fun t : ℝ => t ^ 2 - r ^ 2) (Ioo r L) := by
    intro t ht u hu he
    dsimp at he
    nlinarith [ht.1, hu.1]
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun s => g (Real.sqrt (r ^ 2 + s)) * mixedNullFibreJacobian r s)
  rw [himage] at hsub
  have hfinite : (∫ t in r..L, g t) = ∫ s in Ioo 0 a,
      g (Real.sqrt (r ^ 2 + s)) * mixedNullFibreJacobian r s := by
    rw [intervalIntegral.integral_of_le hrL.le, integral_Ioc_eq_integral_Ioo, hsub]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have ht0 : 0 < t := hr.trans ht.1
    have hsig : 0 ≤ t ^ 2 - r ^ 2 := by nlinarith [ht.1]
    dsimp only
    rw [mixedNullFibreJacobian, max_eq_right hsig,
      show r ^ 2 + (t ^ 2 - r ^ 2) = t ^ 2 by ring, Real.sqrt_sq ht0.le,
      abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht0), smul_eq_mul]
    field_simp
  rw [hfinite]
  have hset : Ioi (0 : ℝ) ∩ Iio a = Ioo 0 a := by ext s; simp
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _hs
  exact Set.indicator_mul_right (Iio a)
    (fun s => g (Real.sqrt (r ^ 2 + s))) (mixedNullFibreJacobian r)

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Signed vertical Fubini for an arbitrary integrable source observable,
not just a continuous phase function. -/
theorem coarea_vertical_integral {f : Spacetime → ℝ}
    (hf : IntegrableOn f (mixedNullRegion H)) :
    (∫ p in mixedNullRegion H, f p) =
      ∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
        f (Fin.cons (-t) (x : Spatial)) := by
  let D : Set Spatial := {x | ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x}
  have hm := hH.isOpen_region.measurableSet
  have hD : MeasurableSet D := by
    exact (isOpen_lt (continuous_norm.comp
      (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ))) hH.continuous).measurableSet
  have hfirst : (∫ p in mixedNullRegion H, f p) =
      ∫ x in D, ∫ t in ‖((WithLp.equiv 2 _).symm x : JointSpace)‖..H x,
        f (Fin.cons (-t) x) := by
    rw [← integral_indicator hm, integral_spacetime_fibres _
      ((integrable_indicator_iff hm).mpr hf), ← integral_indicator hD]
    apply integral_congr_ae
    filter_upwards [] with x
    let r := ‖((WithLp.equiv 2 _).symm x : JointSpace)‖
    have he (t : ℝ) : (mixedNullRegion H).indicator f (Fin.cons t x) =
        (Ioo (-H x) (-r)).indicator (fun t => f (Fin.cons t x)) t := by
      simp [Set.indicator, mixedNull_cons_mem_iff, r]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    by_cases hx : r < H x
    · rw [Set.indicator_of_mem (show x ∈ D from hx),
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -H x ≤ -r)]
      have hn := intervalIntegral.integral_comp_neg (a := -H x) (b := -r)
        (fun t => f (Fin.cons (-t) x))
      simpa only [neg_neg, r] using hn
    · rw [Ioo_eq_empty_of_le (by linarith : -r ≤ -H x), setIntegral_empty,
        Set.indicator_of_not_mem (show x ∉ D from hx)]
  rw [hfirst]
  let e : JointSpace ≃ᵐ Spatial :=
    { WithLp.equiv 2 _ with
      measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).measurable }
  have he : MeasurePreserving e := PiLp.volume_preserving_equiv (Fin 3)
  rw [← integral_indicator hD, ← he.integral_comp',
    ← integral_indicator hH.measurableSet_spatialDomain]
  apply integral_congr_ae
  filter_upwards [] with x
  have hd : e x ∈ D ↔ x ∈ mixedNullSpatialDomain H := by
    simp [e, D, mixedNullSpatialDomain]
    rfl
  simp only [Function.comp_def, Set.indicator, hd]
  rfl

/-- The signed weighted space/sigma Gaussian is absolutely integrable before
Fubini. The bound applies to genuine spacetime weights, including time dependence. -/
theorem integrable_weightedCoareaGaussian {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    Integrable (fun p : JointSpace × ℝ =>
      (Real.exp (-(Real.pi / 24) * ρ * p.2 ^ 2) * mixedNullCoareaKernel H p.2 p.1) *
        w (mixedNullCoareaPoint p.2 p.1))
      ((volume : Measure JointSpace).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hp := continuous_mixedNullCoareaPoint.measurable.comp measurable_swap
  have hm := hw.comp hp
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, mul_comm] using
    (hH.integrable_coareaGaussian hρ).bdd_mul'
    hm.aestronglyMeasurable (Eventually.of_forall fun p => hb (mixedNullCoareaPoint p.2 p.1))

theorem integrable_weightedGlobalWeight_gaussian {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    IntegrableOn (fun s : ℝ => Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
      mixedNullWeightedGlobalWeight H w s) (Ioi (0 : ℝ)) := by
  simpa only [mul_assoc, integral_const_mul, mixedNullWeightedGlobalWeight] using
    (hH.integrable_weightedCoareaGaussian hρ hw hb).integral_prod_right

/-- Actual measurable spacetime-weighted coarea, with all Fubini and singular
integrability obligations discharged. This is not the phase-only vertical API. -/
theorem weighted_spacetimeGaussian_eq_globalWeight {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    (∫ p in mixedNullRegion H, w p * Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
        mixedNullWeightedGlobalWeight H w s := by
  have hE : Continuous (fun p : Spacetime => Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2)) := by
    have hs := continuous_intervalSq.comp (continuous_id.prodMk (continuous_const (y := (0 : Spacetime))))
    fun_prop
  have hi := hH.integrable_weightedCoareaGaussian hρ hw hb
  rw [hH.coarea_vertical_integral (hH.integrable_weighted_continuous hw (fun p _ => hb p) hE)]
  have he : (∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
      w (Fin.cons (-t) (x : Spatial)) *
        Real.exp (-(Real.pi / 24) * ρ * intervalSq (Fin.cons (-t) (x : Spatial)) 0 ^ 2)) =
      ∫ x : JointSpace, ∫ s in Ioi (0 : ℝ),
        (Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullCoareaKernel H s x) *
          w (mixedNullCoareaPoint s x) := by
    rw [← integral_indicator hH.measurableSet_spatialDomain]
    have hn : ∀ᵐ x : JointSpace, x ≠ 0 := by
      apply ae_iff.mpr
      simp
    apply integral_congr_ae
    filter_upwards [hn] with x hx0
    by_cases hx : x ∈ mixedNullSpatialDomain H
    · rw [Set.indicator_of_mem hx, mixedNull_fibre_integral_coarea _ (norm_pos_iff.mpr hx0) hx]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs0 : 0 ≤ s := hs.le
      have hsq : 0 ≤ ‖x‖ ^ 2 + s := add_nonneg (sq_nonneg _) hs0
      dsimp only
      rw [mixedNull_intervalSq_cons, neg_sq, Real.sq_sqrt hsq,
        show ‖((WithLp.equiv 2 _).symm (x : Spatial) : JointSpace)‖ = ‖x‖ from rfl,
        add_sub_cancel_left, coareaKernel_eq_fibreWeight hx hs0]
      simp only [mixedNullCoareaPoint, max_eq_right hs0]
      ring
    · rw [Set.indicator_of_not_mem hx]
      simp only [coareaKernel_eq_zero_of_not_mem hx, mul_zero, zero_mul, integral_zero]
  rw [he, integral_integral_swap hi]
  simp only [mul_assoc, integral_const_mul, mixedNullWeightedGlobalWeight]

/-- NM4's exact finite-density identity for the original full-partner signed
weighted action. No regularity, endpoint limit or generator identity is assumed. -/
theorem weightedContinuumMean_eq_globalWeight {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    weightedContinuumMean ρ (mixedNullRegion H) w =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          mixedNullWeightedGlobalWeight H w s := by
  rw [hH.weightedContinuumMean_eq_spacetimeGaussian hρ hw (fun p _ => hb p),
    hH.weighted_spacetimeGaussian_eq_globalWeight hρ hw hb]

end MixedNullData
end BoundaryDraft

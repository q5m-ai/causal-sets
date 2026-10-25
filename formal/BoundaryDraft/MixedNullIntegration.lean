import BoundaryDraft.MixedNullContract
import BoundaryDraft.SpacetimeIntegration

/-!
Actual vertical-coordinate Fubini for the one-tip region. The spatial
coordinate is the original product Lebesgue `Spatial`; Euclidean transport
will be performed separately, not identified by definitional equality.
-/
open MeasureTheory Set
open scoped Topology Interval BigOperators
noncomputable section
namespace BoundaryDraft

private theorem spatial_sq_eq_norm (x : Spatial) :
    (∑ i : Fin 3, x i ^ 2) =
      ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ ^ 2 := by
  simpa [spatialDistance_sq, spatialDistance] using
    (spatialDistance_sq (0 : Spatial) x).symm

/-- Strict chronological source-to-tip condition is exactly the Euclidean
cone inequality in each vertical slice. -/
theorem mixedNull_cons_mem_iff (H : Spatial → ℝ) (t : ℝ) (x : Spatial) :
    Fin.cons t x ∈ mixedNullRegion H ↔
      -H x < t ∧ t < -‖((WithLp.equiv 2 _).symm x : JointSpace)‖ := by
  have hr : 0 ≤ ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ := norm_nonneg _
  have hspace : spatialSeparationSq (Fin.cons t x) 0 =
      ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ ^ 2 := by
    simp [spatialSeparationSq, ← spatial_sq_eq_norm x]
  simp only [mixedNullRegion, mem_setOf_eq, spatialPart_cons,
    chronologicalFuture, Fin.cons_zero, Pi.zero_apply, sub_zero, zero_sub,
    hspace]
  constructor
  · rintro ⟨hh, ht, hs⟩
    have h : ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < -t := by
      apply (sq_lt_sq₀ hr (by linarith : 0 ≤ -t)).mp
      nlinarith
    exact ⟨hh, by linarith⟩
  · rintro ⟨hh, ht⟩
    refine ⟨hh, by linarith [hr], ?_⟩
    nlinarith

/-- The proper-time-squared phase of an actual spacetime point. -/
theorem mixedNull_intervalSq_cons (t : ℝ) (x : Spatial) :
    intervalSq (Fin.cons t x) 0 =
      t ^ 2 - ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ ^ 2 := by
  simp [intervalSq, spatialSeparationSq, spatial_sq_eq_norm]

/-- An exact vertical Fubini formula, before any Gaussian or density limit.
Only absolute integrability of the original spacetime integrand is used. -/
theorem mixedNull_vertical_integral (H : Spatial → ℝ)
    (hc : Continuous H) (hb : Bornology.IsBounded (mixedNullRegion H))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in mixedNullRegion H, f (intervalSq p 0)) =
      ∫ x in {x : Spatial |
        ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x}, ∫ t in
        (‖((WithLp.equiv 2 _).symm x : JointSpace)‖)..H x,
          f (t ^ 2 - ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ ^ 2) := by
  let F : Spacetime → ℝ := fun p => f (intervalSq p 0)
  have hF : Continuous F := by
    unfold F intervalSq spatialSeparationSq
    fun_prop
  have hm : MeasurableSet (mixedNullRegion H) := by
    have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
    have hp : IsOpen {p : Spacetime | (0 : Spacetime) ∈ chronologicalFuture p} :=
      (isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt
          (continuous_spatialSeparationSq.comp (continuous_id.prodMk continuous_const))
          ((continuous_const.sub (continuous_apply 0)).pow 2))
    exact ((isOpen_lt (hc.comp hs).neg (continuous_apply 0)).inter hp).measurableSet
  have hi : IntegrableOn F (mixedNullRegion H) :=
    (hF.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hD : MeasurableSet {x : Spatial |
      ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x} := by
    exact (isOpen_lt (continuous_norm.comp
      (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ))) hc).measurableSet
  rw [← integral_indicator hm,
    integral_spacetime_fibres _ ((integrable_indicator_iff hm).mpr hi),
    ← integral_indicator hD]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    let r := ‖((WithLp.equiv 2 _).symm x : JointSpace)‖
    have he (t : ℝ) : (mixedNullRegion H).indicator F (Fin.cons t x) =
        (Ioo (-H x) (-r)).indicator (fun t => f (t ^ 2 - r ^ 2)) t := by
      simp [Set.indicator, mixedNull_cons_mem_iff, F, mixedNull_intervalSq_cons, r]
    simp_rw [he]
    rw [integral_indicator measurableSet_Ioo]
    by_cases hx : r < H x
    · have hx' : x ∈ {x : Spatial |
          ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x} := hx
      rw [Set.indicator_of_mem hx',
        ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -H x ≤ -r)]
      have hn := intervalIntegral.integral_comp_neg (a := -H x) (b := -r)
        (fun t => f (t ^ 2 - r ^ 2))
      simpa only [neg_sq, neg_neg, r] using hn
    · have hx' : x ∉ {x : Spatial |
          ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x} := hx
      rw [Ioo_eq_empty_of_le (by linarith : -r ≤ -H x), setIntegral_empty,
        Set.indicator_of_not_mem hx']


/-- Lebesgue transport from the actual three-coordinate product to the
Euclidean normed space; the isometry and measure preservation are explicit. -/
theorem mixedNull_vertical_euclidean (H : Spatial → ℝ)
    (hc : Continuous H) (hb : Bornology.IsBounded (mixedNullRegion H))
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ p in mixedNullRegion H, f (intervalSq p 0)) =
      ∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
        f (t ^ 2 - ‖x‖ ^ 2) := by
  rw [mixedNull_vertical_integral H hc hb f hf]
  let e : JointSpace ≃ᵐ Spatial :=
    { WithLp.equiv 2 _ with
      measurable_toFun := (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).measurable }
  have he : MeasurePreserving e := PiLp.volume_preserving_equiv (Fin 3)
  let D : Set Spatial := {x | ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ < H x}
  have hm : MeasurableSet D := by
    exact (isOpen_lt (continuous_norm.comp
      (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ))) hc).measurableSet
  rw [← integral_indicator hm, ← he.integral_comp']
  have hd (x : JointSpace) : e x ∈ D ↔ x ∈ mixedNullSpatialDomain H := by
    simp [e, D, mixedNullSpatialDomain]
    rfl
  have hm' : MeasurableSet (mixedNullSpatialDomain H) := by
    exact (isOpen_lt continuous_norm (hc.comp
      (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)))).measurableSet
  rw [← integral_indicator hm']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Function.comp_def, Set.indicator, hd]
    rfl

/-- Finite-density exact Gaussian integration in genuine Euclidean spatial
coordinates, with neither a postulated radial weight nor a jet. -/
theorem MixedNullData.continuumMean_eq_spatialGaussian {H : Spatial → ℝ}
    (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion H) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ x in mixedNullSpatialDomain H, ∫ t in ‖x‖..H x,
          Real.exp (-(Real.pi / 24) * ρ * (t ^ 2 - ‖x‖ ^ 2) ^ 2) := by
  rw [hH.continuumMean_eq_spacetimeGaussian hρ,
    mixedNull_vertical_euclidean H hH.continuous hH.isBounded_region
      (fun s => Real.exp (-(Real.pi / 24) * ρ * s ^ 2)) (by fun_prop)]

end BoundaryDraft

import BoundaryDraft.MixedNullCoareaTransport
import BoundaryDraft.MixedNullGeometryExamples

/-! Expanded MA9/NM4 contracts: actual global integrals, original full-partner
action, both support endpoints, nonconstant admitted floors, signed and
time-dependent measurable weights, and the non-negligible pointwise origin. -/
open BoundaryDraft MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace MixedNullCoareaRegression

-- The actual spatial integral, not a fibre weight or an assigned limit.
example {H : Spatial → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    mixedNullGlobalWeight H s = ∫ x : JointSpace,
      if Real.sqrt (‖x‖ ^ 2 + s) < H x then
        1 / (2 * Real.sqrt (‖x‖ ^ 2 + s)) else 0 := by
  unfold mixedNullGlobalWeight
  apply integral_congr_ae
  exact Eventually.of_forall (mixedNullCoareaKernel_sqrt H hs)

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    Measurable (fun p : ℝ × JointSpace =>
      if Real.sqrt (‖p.2‖ ^ 2 + max 0 p.1) < H p.2 then
        (2 * Real.sqrt (‖p.2‖ ^ 2 + max 0 p.1))⁻¹ else 0) :=
  hH.measurable_coareaKernel

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    (∫ x : JointSpace, if ‖x‖ < H x then (2 * ‖x‖)⁻¹ else 0) =
      (1 / 4 : ℝ) * ∫ u : MixedNullDirection, mixedNullRadius H u ^ 2
        ∂(volume : Measure JointSpace).toSphere := by
  have he := hH.globalWeight_zero
  simpa only [mixedNullGlobalWeight, mixedNullCoareaKernel, max_self, add_zero,
    Real.sqrt_sq (norm_nonneg _), mixedNullArea, div_eq_mul_inv, mul_comm, one_mul] using he

example {H : Spatial → ℝ} (hH : MixedNullData H) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : 0 ≤ s) :
    mixedNullGlobalWeight H s =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..(H 0 / (1 - k)),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere :=
  hH.globalWeight_eq_angular_radial hk hk1 h hs

-- No topology of the positive-sigma slices appears in this contract.
example {H : Spatial → ℝ} (hH : MixedNullData H) {s r : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (u : MixedNullDirection)
    (hc : Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace))) :
    r < mixedNullRadius H u := hH.coarea_radial_slice_subset hs hr u hc

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    Tendsto (mixedNullGlobalWeight H) (𝓝[≥] (0 : ℝ))
      (𝓝 ((∫ u : MixedNullDirection, mixedNullRadius H u ^ 2
        ∂(volume : Measure JointSpace).toSphere) / 4)) :=
  hH.globalWeight_tendsto_area_quarter

-- Both sides are expanded to the original point-minus-full-partner action
-- and the independently defined spatial coarea integral.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ _p in {p : Spacetime | -H (spatialPart p) < p 0 ∧
        (0 : Spacetime) ∈ chronologicalFuture p}, (1 : ℝ)) -
       ρ * ∫ p in {p : Spacetime | -H (spatialPart p) < p 0 ∧
        (0 : Spacetime) ∈ chronologicalFuture p},
         ∫ q in {p : Spacetime | -H (spatialPart p) < p 0 ∧
           (0 : Spacetime) ∈ chronologicalFuture p} ∩ causalFuture p,
           bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          (∫ x : JointSpace, if Real.sqrt (‖x‖ ^ 2 + max 0 s) < H x then
            (2 * Real.sqrt (‖x‖ ^ 2 + max 0 s))⁻¹ else 0) :=
  hH.continuumMean_eq_globalWeight hρ

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion H) =
      ((4 / Real.sqrt 6) / Real.sqrt (Real.pi / 24)) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u ^ 2) *
          mixedNullGlobalWeight H (u / Real.sqrt ((Real.pi / 24) * ρ)) :=
  hH.continuumMean_eq_globalWeight_rescaled hρ

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun p : JointSpace × ℝ =>
      Real.exp (-(Real.pi / 24) * ρ * p.2 ^ 2) * mixedNullCoareaKernel H p.2 p.1)
      ((volume : Measure JointSpace).prod (volume.restrict (Ioi (0 : ℝ)))) :=
  hH.integrable_coareaGaussian hρ

example {H : Spatial → ℝ} (hH : MixedNullData H) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (s : ℝ) :
    0 ≤ mixedNullGlobalWeight H s ∧
      mixedNullGlobalWeight H s ≤ Real.pi * (H 0 / (1 - k)) ^ 2 :=
  hH.globalWeight_bound hk hk1 h s

example {H : Spatial → ℝ} (hH : MixedNullData H) {k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) :
    mixedNullGlobalWeight H ((H 0 / (1 - k)) ^ 2) = 0 ∧
      0 < mixedNullGlobalWeight H 0 :=
  ⟨hH.globalWeight_eq_zero hk hk1 h le_rfl, hH.globalWeight_zero_pos⟩

-- Round calibration: the endpoint is pi*T^2, not the diamond normalization.
example {T : ℝ} (hT : 0 < T) :
    mixedNullGlobalWeight (fun _ : Spatial => T) 0 = Real.pi * T ^ 2 := by
  rw [(mixedNull_constant_admissible hT).toMixedNullData.globalWeight_zero,
    mixedNullArea_constant hT]
  ring

example {T s : ℝ} (hT : 0 < T) (hs : T ^ 2 ≤ s) :
    mixedNullGlobalWeight (fun _ : Spatial => T) s = 0 := by
  apply (mixedNull_constant_admissible hT).toMixedNullData.globalWeight_eq_zero
    (k := 0) (by norm_num) (by norm_num) (by intro x y; simp)
  simpa using hs

-- A genuinely nonplanar admitted floor, with the new producer route.
example {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion mixedNullSineFloor) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          mixedNullGlobalWeight mixedNullSineFloor s :=
  mixedNull_sine_admissible.toMixedNullData.continuumMean_eq_globalWeight hρ

example : Tendsto (fun ρ : ℝ => continuumMean ρ (mixedNullRegion mixedNullSineFloor))
    atTop (𝓝 (mixedNullArea mixedNullSineFloor)) :=
  mixedNull_sine_admissible.toMixedNullData.continuumMean_tendsto_via_globalWeight

-- The admitted affine control retains negative exterior heights.
example : AdmissibleMixedNull (mixedNullAffineFloor (1 / 2) 1) ∧
    mixedNullAffineFloor (1 / 2) 1 ![-4, 0, 0] < 0 :=
  ⟨mixedNull_affine_admissible (by norm_num)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num),
    mixedNull_affine_exterior_negative⟩

example : mixedNullCoareaKernel (mixedNullAffineFloor (1 / 2) 1) 1
    ((WithLp.equiv 2 _).symm ![-4, 0, 0]) = 0 := by
  apply if_neg
  have hh := mixedNull_affine_exterior_negative
  exact not_lt.mpr (hh.le.trans (Real.sqrt_nonneg _))

-- An admitted positive-sigma slice has a genuine hole at the axis: it
-- contains radius one but neither radius zero nor the joint radius two.
example :
    ¬ Real.sqrt (9 / 8 : ℝ) < mixedNullAffineFloor (1 / 2) 1 0 ∧
    Real.sqrt (1 ^ 2 + 9 / 8 : ℝ) < mixedNullAffineFloor (1 / 2) 1
      (EuclideanSpace.single 0 1 : JointSpace) ∧
    ¬ Real.sqrt (2 ^ 2 + 9 / 8 : ℝ) < mixedNullAffineFloor (1 / 2) 1
      (EuclideanSpace.single 0 2 : JointSpace) := by
  have hzero : (1 : ℝ) ≤ Real.sqrt (9 / 8) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 9 / 8)
  have hone : Real.sqrt (1 ^ 2 + 9 / 8 : ℝ) < 3 / 2 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)).mpr (by norm_num)
  have htwo : (2 : ℝ) ≤ Real.sqrt (2 ^ 2 + 9 / 8) := by
    simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] using
      Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ^ 2 ≤ 2 ^ 2 + 9 / 8)
  constructor
  · simpa [mixedNullAffineFloor] using not_lt.mpr hzero
  constructor
  · convert hone using 1
    norm_num [mixedNullAffineFloor]
  · apply not_lt.mpr
    convert htwo using 1
    norm_num [mixedNullAffineFloor]

-- A negative height must not be accepted by the raw squared test, even
-- when the coarea definitions are used on a profile outside admissibility.
example : (-2 : ℝ) ^ 2 > ‖(0 : JointSpace)‖ ^ 2 + 1 ∧
    mixedNullCoareaKernel (fun _ : Spatial => -2) 1 0 = 0 := by
  norm_num [mixedNullCoareaKernel]

-- The positive-sigma origin value is not zero. Only its integral may be
-- ignored, after establishing the integrable reciprocal-radius majorant.
example : mixedNullCoareaKernel (fun _ : Spatial => 2) 1 0 = 1 / 2 ∧
    mixedNullCoareaKernel (fun _ : Spatial => 2) 0 0 = 0 := by
  norm_num [mixedNullCoareaKernel]

-- The full signed weighted action, with partners still in the original region.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ p in mixedNullRegion H, w p) - ρ * ∫ p in mixedNullRegion H,
        w p * ∫ q in mixedNullRegion H ∩ causalFuture p,
          bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          (∫ x : JointSpace, mixedNullCoareaKernel H s x *
            w (Fin.cons (-Real.sqrt (‖x‖ ^ 2 + max 0 s)) (x : Spatial))) :=
  hH.weightedContinuumMean_eq_globalWeight hρ hw hb

example {H : Spatial → ℝ} (hH : MixedNullData H)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C) :
    mixedNullWeightedGlobalWeight H w 0 =
      (1 / 2 : ℝ) * ∫ u : MixedNullDirection,
        (∫ r in (0 : ℝ)..mixedNullRadius H u,
          r * w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere := hH.weightedGlobalWeight_zero hw hb

example {H : Spatial → ℝ} (hH : MixedNullData H)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullWeightedGlobalWeight H w s =
      ∫ u : MixedNullDirection, (∫ r in (0 : ℝ)..(H 0 / (1 - k)),
        if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
          r ^ 2 * w (Fin.cons (-Real.sqrt (r ^ 2 + s))
            (r • (u : JointSpace) : JointSpace)) / (2 * Real.sqrt (r ^ 2 + s)) else 0)
        ∂(volume : Measure JointSpace).toSphere :=
  hH.weightedGlobalWeight_eq_angular_radial hw hb hk hk1 h hs

example {H : Spatial → ℝ} (hH : MixedNullData H)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) (s : ℝ) :
    ‖mixedNullWeightedGlobalWeight H w s‖ ≤ C * Real.pi * (H 0 / (1 - k)) ^ 2 ∧
      mixedNullWeightedGlobalWeight H w ((H 0 / (1 - k)) ^ 2) = 0 :=
  ⟨hH.weightedGlobalWeight_bound hw hb hk hk1 h s,
    hH.weightedGlobalWeight_eq_zero hw hb hk hk1 h le_rfl⟩

example {H : Spatial → ℝ} (hH : MixedNullData H) :
    mixedNullWeightedGlobalWeight H (fun _ => -1) 0 = -(mixedNullArea H / 4) := by
  simp only [mixedNullWeightedGlobalWeight, mul_neg_one, integral_neg]
  exact congrArg Neg.neg hH.globalWeight_zero

/-- Discontinuous, signed, genuinely time-dependent source weight. -/
def stepWeight (p : Spacetime) : ℝ := if p 0 < -1 / 2 then -1 else 2

theorem stepWeight_measurable : Measurable stepWeight :=
  measurable_const.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const) measurable_const

theorem stepWeight_bound (p : Spacetime) : ‖stepWeight p‖ ≤ 2 := by
  unfold stepWeight
  split_ifs <;> norm_num

example {ρ : ℝ} (hρ : 0 < ρ) :
    weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor) stepWeight =
      (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ s in Ioi (0 : ℝ), Real.exp (-(Real.pi / 24) * ρ * s ^ 2) *
          mixedNullWeightedGlobalWeight mixedNullSineFloor stepWeight s :=
  mixedNull_sine_admissible.toMixedNullData.weightedContinuumMean_eq_globalWeight
    hρ stepWeight_measurable stepWeight_bound

end MixedNullCoareaRegression

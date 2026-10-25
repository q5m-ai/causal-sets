import BoundaryDraft.MixedNullTip

/-!
# The actual NM10 collar and its nonzero complement

The collar is a measurable source weight on the original mixed region, with
all partners retained. Its radius uses the proved exit radius on each ray.
This is not the action of a newly restricted spacetime region.
-/
open MeasureTheory Set Filter
open scoped Topology Interval Classical
noncomputable section
namespace BoundaryDraft

/-- Exit radius of the actual spatial ray; the unused axis value is fixed to
zero. Measurability is proved from the genuine polar homeomorphism. -/
def mixedNullExitRadius (H : Spatial → ℝ) (x : JointSpace) : ℝ :=
  if hx : x ∈ ({0}ᶜ : Set JointSpace) then
    mixedNullRadius H ((homeomorphUnitSphereProd JointSpace) ⟨x, hx⟩).1 else 0

/-- Sharp collar of radial width h, with no partner cutoff. -/
def mixedNullCollarWeight (H : Spatial → ℝ) (h : ℝ) (p : Spacetime) : ℝ :=
  let x := mixedNullEuclideanSpatial p
  if mixedNullExitRadius H x - h < ‖x‖ ∧ ‖x‖ < mixedNullExitRadius H x then 1 else 0

/-- The complementary source observable is not assumed to vanish. -/
def mixedNullCollarComplement (H : Spatial → ℝ) (h : ℝ) (p : Spacetime) : ℝ :=
  1 - mixedNullCollarWeight H h p

/-- Independent radial expression for the collar response. -/
def mixedNullCollarResponse (H : Spatial → ℝ) (h : ℝ) : ℝ :=
  ∫ u : MixedNullDirection,
    mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2
    ∂(volume : Measure JointSpace).toSphere

theorem mixedNullExitRadius_radial (H : Spatial → ℝ) {r : ℝ} (hr : 0 < r)
    (u : MixedNullDirection) : mixedNullExitRadius H (r • (u : JointSpace)) = mixedNullRadius H u := by
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hx : r • (u : JointSpace) ∈ ({0}ᶜ : Set JointSpace) := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (norm_pos_iff.mp (by simpa only [hn] using hr))
  rw [mixedNullExitRadius, dif_pos hx]
  congr 1
  apply Subtype.ext
  simp only [homeomorphUnitSphereProd_apply_fst_coe, hn, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

theorem mixedNullCollarWeight_radial (H : Spatial → ℝ) (h : ℝ) {r : ℝ}
    (hr : 0 < r) (u : MixedNullDirection) (t : ℝ) :
    mixedNullCollarWeight H h (Fin.cons t (r • (u : JointSpace) : JointSpace)) =
      if mixedNullRadius H u - h < r ∧ r < mixedNullRadius H u then 1 else 0 := by
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  change (if mixedNullExitRadius H (r • (u : JointSpace)) - h < ‖r • (u : JointSpace)‖ ∧
    ‖r • (u : JointSpace)‖ < mixedNullExitRadius H (r • (u : JointSpace)) then 1 else 0) = _
  rw [mixedNullExitRadius_radial H hr u, hn]

theorem mixedNullCollarWeight_bounds (H : Spatial → ℝ) (h : ℝ) (p : Spacetime) :
    0 ≤ mixedNullCollarWeight H h p ∧ mixedNullCollarWeight H h p ≤ 1 := by
  unfold mixedNullCollarWeight
  dsimp only
  split_ifs <;> norm_num

theorem mixedNullCollarWeight_norm_le (H : Spatial → ℝ) (h : ℝ) (p : Spacetime) :
    ‖mixedNullCollarWeight H h p‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mixedNullCollarWeight_bounds H h p).1]
  exact (mixedNullCollarWeight_bounds H h p).2

theorem mixedNullCollarComplement_norm_le (H : Spatial → ℝ) (h : ℝ) (p : Spacetime) :
    ‖mixedNullCollarComplement H h p‖ ≤ 1 := by
  rw [mixedNullCollarComplement, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (mixedNullCollarWeight_bounds H h p).2)]
  linarith [(mixedNullCollarWeight_bounds H h p).1]

/-- The elementary radial primitive, including both artificial endpoints. -/
theorem mixedNull_integral_radial_collar {R h : ℝ} (hh : 0 < h) (hhR : h < R) :
    (∫ r in (0 : ℝ)..R, r * (if R - h < r ∧ r < R then (1 : ℝ) else 0)) =
      (R ^ 2 - (R - h) ^ 2) / 2 := by
  have hR : 0 < R := hh.trans hhR
  have he : (fun r : ℝ => r * (if R - h < r ∧ r < R then (1 : ℝ) else 0)) =
      (Ioo (R - h) R).indicator (fun r => r) := by
    funext r
    simp only [Set.indicator, mem_Ioo]
    split_ifs <;> simp
  rw [he, intervalIntegral.integral_of_le hR.le, setIntegral_indicator measurableSet_Ioo]
  have hs : Ioc 0 R ∩ Ioo (R - h) R = Ioo (R - h) R := by
    apply inter_eq_right.mpr
    intro r hr
    exact ⟨(sub_pos.mpr hhR).trans hr.1, hr.2.le⟩
  rw [hs, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : R - h ≤ R), integral_id]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem measurable_exitRadius : Measurable (mixedNullExitRadius H) := by
  exact Measurable.dite
    (hH.continuous_radius.measurable.comp (homeomorphUnitSphereProd JointSpace).measurable.fst)
    measurable_const (measurableSet_singleton (0 : JointSpace)).compl

theorem measurable_collarWeight (h : ℝ) : Measurable (mixedNullCollarWeight H h) := by
  have hr := hH.measurable_exitRadius.comp continuous_mixedNullEuclideanSpatial.measurable
  have hn := continuous_mixedNullEuclideanSpatial.norm.measurable
  exact measurable_const.ite ((measurableSet_lt (hr.sub measurable_const) hn).inter
    (measurableSet_lt hn hr)) measurable_const

theorem measurable_collarComplement (h : ℝ) : Measurable (mixedNullCollarComplement H h) :=
  measurable_const.sub (hH.measurable_collarWeight h)

/-- Actual cone trace at zero; sharp radial cutoffs are not replaced by smooth
surrogates with a silently lost generator term. -/
theorem collarWeight_zero {h : ℝ} (hh : 0 < h) (hhR : ∀ u, h < mixedNullRadius H u) :
    4 * mixedNullWeightedGlobalWeight H (mixedNullCollarWeight H h) 0 =
      mixedNullCollarResponse H h := by
  rw [hH.weightedGlobalWeight_zero (hH.measurable_collarWeight h)
    (mixedNullCollarWeight_norm_le H h)]
  have he (u : MixedNullDirection) :
      (∫ r in (0 : ℝ)..mixedNullRadius H u,
        r * mixedNullCollarWeight H h
          (Fin.cons (-r) (r • (u : JointSpace) : JointSpace))) =
      (mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2) / 2 := by
    rw [← mixedNull_integral_radial_collar hh (hhR u),
      intervalIntegral.integral_of_le (hH.radius_pos u).le,
      intervalIntegral.integral_of_le (hH.radius_pos u).le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [mixedNullCollarWeight_radial H h hr.1 u (-r)]
  simp_rw [he]
  rw [integral_div]
  unfold mixedNullCollarResponse
  ring

/-- NM10's fixed-collar response for the actual original-region observable. -/
theorem weightedContinuumMean_collar_limit {h : ℝ} (hh : 0 < h)
    (hhR : ∀ u, h < mixedNullRadius H u) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (mixedNullCollarWeight H h))
      atTop (𝓝 (mixedNullCollarResponse H h)) := by
  have ht : ∀ x ∈ mixedNullSpatialDomain H, ContinuousAt
      (fun t : ℝ => mixedNullCollarWeight H h (Fin.cons t (x : Spatial))) (-‖x‖) := by
    intro x _
    change ContinuousAt (fun _ : ℝ => if mixedNullExitRadius H x - h < ‖x‖ ∧
      ‖x‖ < mixedNullExitRadius H x then (1 : ℝ) else 0) _
    exact continuousAt_const
  have hl := hH.weightedContinuumMean_tendsto_globalWeight (hH.measurable_collarWeight h)
    (mixedNullCollarWeight_norm_le H h) ht
  rw [hH.collarWeight_zero hh hhR] at hl
  exact hl

theorem integrable_radius_sub_sq (h : ℝ) :
    Integrable (fun u : MixedNullDirection => (mixedNullRadius H u - h) ^ 2)
      (volume : Measure JointSpace).toSphere :=
  ((hH.continuous_radius.sub continuous_const).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Quantitative NM10 response bound with a specified uniform upper radius. -/
theorem collarResponse_bound {h B : ℝ} (hh : 0 < h)
    (hhR : ∀ u, h < mixedNullRadius H u) (hB : ∀ u, mixedNullRadius H u ≤ B) :
    0 ≤ mixedNullCollarResponse H h ∧ mixedNullCollarResponse H h ≤ 8 * Real.pi * B * h := by
  have hi := hH.integrable_radius_sq.sub (hH.integrable_radius_sub_sq h)
  constructor
  · apply integral_nonneg
    intro u
    change 0 ≤ mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2
    nlinarith [hhR u]
  · have he := integral_mono hi (integrable_const (2 * B * h)) (fun u => by
      change mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2 ≤ 2 * B * h
      nlinarith [hB u, sq_nonneg h])
    simp only [integral_const, smul_eq_mul, jointSphere_area] at he
    change mixedNullCollarResponse H h ≤ _ at he
    convert he using 1
    ring

/-- The complete complementary source, not an independently chosen region,
has the written positive response. -/
theorem weightedContinuumMean_collarComplement_limit {h : ℝ} (hh : 0 < h)
    (hhR : ∀ u, h < mixedNullRadius H u) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (mixedNullCollarComplement H h))
      atTop (𝓝 (∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
        ∂(volume : Measure JointSpace).toSphere)) := by
  have ht : ∀ x ∈ mixedNullSpatialDomain H, ContinuousAt
      (fun t : ℝ => mixedNullCollarComplement H h (Fin.cons t (x : Spatial))) (-‖x‖) := by
    intro x _
    change ContinuousAt (fun _ : ℝ => 1 -
      (if mixedNullExitRadius H x - h < ‖x‖ ∧ ‖x‖ < mixedNullExitRadius H x then (1 : ℝ) else 0)) _
    exact continuousAt_const
  have hl := hH.weightedContinuumMean_tendsto_globalWeight (hH.measurable_collarComplement h)
    (mixedNullCollarComplement_norm_le H h) ht
  have he : mixedNullWeightedGlobalWeight H (mixedNullCollarComplement H h) 0 =
      mixedNullGlobalWeight H 0 - mixedNullWeightedGlobalWeight H (mixedNullCollarWeight H h) 0 := by
    unfold mixedNullWeightedGlobalWeight mixedNullCollarComplement mixedNullGlobalWeight
    simp_rw [mul_sub, mul_one]
    exact integral_sub hH.integrable_coareaKernel_zero
      (hH.integrable_weightedCoareaKernel (hH.measurable_collarWeight h)
        (mixedNullCollarWeight_norm_le H h) 0)
  rw [he, mul_sub, hH.collarWeight_zero hh hhR, hH.globalWeight_zero,
    show 4 * (mixedNullArea H / 4) = mixedNullArea H by ring] at hl
  have htarget : mixedNullArea H - mixedNullCollarResponse H h =
      ∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
        ∂(volume : Measure JointSpace).toSphere := by
    rw [mixedNullCollarResponse, integral_sub hH.integrable_radius_sq (hH.integrable_radius_sub_sq h)]
    change mixedNullArea H - (mixedNullArea H - _) = _
    ring
  rwa [htarget] at hl

/-- A fixed collar's complement has a strictly positive limiting response;
discarding it is therefore a false localization route on the actual action. -/
theorem collarComplement_response_pos {h m : ℝ} (hhm : h < m)
    (hm : ∀ u, m ≤ mixedNullRadius H u) :
    0 < ∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
      ∂(volume : Measure JointSpace).toSphere := by
  have he := integral_mono (integrable_const ((m - h) ^ 2)) (hH.integrable_radius_sub_sq h)
    (fun u => pow_le_pow_left₀ (sub_pos.mpr hhm).le (sub_le_sub_right (hm u) h) 2)
  simp only [integral_const, smul_eq_mul, jointSphere_area] at he
  have hmpos : 0 < m - h := sub_pos.mpr hhm
  exact (by positivity : 0 < 4 * Real.pi * (m - h) ^ 2).trans_le he

/-- The response coefficient is an actual polynomial in collar width after
integrating the fixed radius. This does not vary the spacetime geometry. -/
theorem collarResponse_eq (h : ℝ) :
    mixedNullCollarResponse H h = 2 * h *
      (∫ u : MixedNullDirection, mixedNullRadius H u ∂(volume : Measure JointSpace).toSphere) -
        4 * Real.pi * h ^ 2 := by
  have hi : Integrable (mixedNullRadius H) (volume : Measure JointSpace).toSphere :=
    hH.continuous_radius.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (u : MixedNullDirection) :
      mixedNullRadius H u ^ 2 - (mixedNullRadius H u - h) ^ 2 =
        2 * h * mixedNullRadius H u - h ^ 2 := by ring
  unfold mixedNullCollarResponse
  simp_rw [he]
  rw [integral_sub (hi.const_mul (2 * h)) (integrable_const (h ^ 2)), integral_const_mul,
    integral_const, smul_eq_mul, jointSphere_area]

/-- The second, sequential NM10 limit shrinks the collar only after the
fixed-width action response has been computed. -/
theorem collarResponse_tendsto_zero : Tendsto (mixedNullCollarResponse H) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun h : ℝ => 2 * h *
      (∫ u : MixedNullDirection, mixedNullRadius H u ∂(volume : Measure JointSpace).toSphere) -
        4 * Real.pi * h ^ 2) := by fun_prop
  have ht := hc.tendsto 0
  simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at ht
  exact ht.congr' (Eventually.of_forall fun h => (hH.collarResponse_eq h).symm)

/-- Literal written geometric hypotheses produce all fixed-collar outputs;
no desired radius bounds, action limit or complement smallness is a field. -/
theorem collar_response_from_lipschitz {k h : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hh : 0 < h) (hhm : h < H 0 / (1 + k)) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (mixedNullCollarWeight H h))
        atTop (𝓝 (mixedNullCollarResponse H h)) ∧
      Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) (mixedNullCollarComplement H h))
        atTop (𝓝 (∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
          ∂(volume : Measure JointSpace).toSphere)) ∧
      (0 ≤ mixedNullCollarResponse H h ∧
        mixedNullCollarResponse H h ≤ 8 * Real.pi * (H 0 / (1 - k)) * h) ∧
      0 < ∫ u : MixedNullDirection, (mixedNullRadius H u - h) ^ 2
        ∂(volume : Measure JointSpace).toSphere := by
  have hb := hH.radius_bounds hk hk1 hLip
  have hhR : ∀ u, h < mixedNullRadius H u := fun u => hhm.trans_le (hb u).1
  exact ⟨hH.weightedContinuumMean_collar_limit hh hhR,
    hH.weightedContinuumMean_collarComplement_limit hh hhR,
    hH.collarResponse_bound hh hhR (fun u => (hb u).2),
    hH.collarComplement_response_pos hhm (fun u => (hb u).1)⟩

end MixedNullData
end BoundaryDraft

import BoundaryDraft.MixedNullWeightedGaussian

/-!
# Local closed-fibre and bounding-box hypotheses

Value clipping constructs a globally bounded measurable extension that agrees
with the original weight at every active coarea source and throughout the
original region. Thus a weight such as coordinate time need not be globally
bounded. No spatial or time cutoff is inserted into the original observable.
-/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- A local bound on the actual closed vertical fibres. -/
def MixedNullWeightBound (H : Spatial → ℝ) (w : Spacetime → ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ mixedNullSpatialDomain H, ∀ t ∈ Icc (-H x) (-‖x‖),
    ‖w (Fin.cons t (x : Spatial))‖ ≤ M

/-- The closed bounding box is expressed with the actual Euclidean spatial
norm. Its cylindrical spatial section is contained in the coordinate box. -/
def mixedNullWeightBox (B : ℝ) : Set Spacetime :=
  {p | -B ≤ p 0 ∧ p 0 ≤ 0 ∧ ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ ≤ B}

def mixedNullClipWeight (M : ℝ) (w : Spacetime → ℝ) (p : Spacetime) : ℝ :=
  max (-M) (min M (w p))

theorem mixedNullClipWeight_measurable {w : Spacetime → ℝ} (hw : Measurable w) (M : ℝ) :
    Measurable (mixedNullClipWeight M w) := measurable_const.max (measurable_const.min hw)

theorem mixedNullClipWeight_bound {M : ℝ} (hM : 0 ≤ M) (w : Spacetime → ℝ) (p : Spacetime) :
    ‖mixedNullClipWeight M w p‖ ≤ M := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem mixedNullClipWeight_eq {M : ℝ} {w : Spacetime → ℝ} {p : Spacetime}
    (hb : ‖w p‖ ≤ M) : mixedNullClipWeight M w p = w p := by
  have hh := abs_le.mp (show |w p| ≤ M from hb)
  simp [mixedNullClipWeight, min_eq_right hh.2, max_eq_right hh.1]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

omit hH in
/-- Closed-box bounds imply the weaker bounds on actual closed fibres. -/
theorem weightBound_of_box {w : Spacetime → ℝ} {M k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hb : ∀ p ∈ mixedNullWeightBox (H 0 / (1 - k)), ‖w p‖ ≤ M) :
    MixedNullWeightBound H w M := by
  intro x hx t ht
  have hbounds := coarea_spatial_bounds hk hk1 h hx
  apply hb
  simp only [mixedNullWeightBox, mem_setOf_eq, Fin.cons_zero, spatialPart_cons]
  change -(H 0 / (1 - k)) ≤ t ∧ t ≤ 0 ∧ ‖x‖ ≤ H 0 / (1 - k)
  exact ⟨by linarith [ht.1], by linarith [ht.2, norm_nonneg x], hbounds.1.le⟩

omit hH in
/-- Box-local time Lipschitz control implies the exact closed-fibre contract. -/
theorem timeLipschitz_of_box {w : Spacetime → ℝ} {L k : ℝ}
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (ht : ∀ x : JointSpace, ‖x‖ ≤ H 0 / (1 - k) →
      ∀ t ∈ Icc (-(H 0 / (1 - k))) 0, ∀ v ∈ Icc (-(H 0 / (1 - k))) 0,
        ‖w (Fin.cons t (x : Spatial)) - w (Fin.cons v (x : Spatial))‖ ≤ L * |t - v|) :
    MixedNullTimeLipschitz H w L := by
  intro x hx t ht' v hv
  have hh := coarea_spatial_bounds hk hk1 h hx
  exact ht x hh.1.le t ⟨by linarith [ht'.1], by linarith [ht'.2, norm_nonneg x]⟩
    v ⟨by linarith [hv.1], by linarith [hv.2, norm_nonneg x]⟩

omit hH in
/-- Value clipping changes no active coarea contribution, including sigma=0. -/
theorem weightedCoareaKernel_clip_eq {w : Spacetime → ℝ} {M : ℝ}
    (hb : MixedNullWeightBound H w M) (s : ℝ) (x : JointSpace) :
    mixedNullCoareaKernel H s x * mixedNullClipWeight M w (mixedNullCoareaPoint s x) =
      mixedNullCoareaKernel H s x * w (mixedNullCoareaPoint s x) := by
  have hq : ‖x‖ ≤ Real.sqrt (‖x‖ ^ 2 + max 0 s) := by
    calc
      ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (le_max_left _ _))
  by_cases hc : Real.sqrt (‖x‖ ^ 2 + max 0 s) < H x
  · have hx : x ∈ mixedNullSpatialDomain H := hq.trans_lt hc
    dsimp only [mixedNullCoareaPoint]
    rw [mixedNullClipWeight_eq (hb x hx (-Real.sqrt (‖x‖ ^ 2 + max 0 s)) ⟨by linarith, by linarith⟩)]
  · simp [mixedNullCoareaKernel, hc]

omit hH in
theorem weightedGlobalWeight_clip_eq {w : Spacetime → ℝ} {M : ℝ}
    (hb : MixedNullWeightBound H w M) (s : ℝ) :
    mixedNullWeightedGlobalWeight H (mixedNullClipWeight M w) s = mixedNullWeightedGlobalWeight H w s := by
  apply integral_congr_ae
  exact Eventually.of_forall (weightedCoareaKernel_clip_eq hb s)

omit hH in
theorem timeLipschitz_clip {w : Spacetime → ℝ} {M L : ℝ}
    (hb : MixedNullWeightBound H w M) (ht : MixedNullTimeLipschitz H w L) :
    MixedNullTimeLipschitz H (mixedNullClipWeight M w) L := by
  intro x hx t ht' v hv
  rw [mixedNullClipWeight_eq (hb x hx t ht'), mixedNullClipWeight_eq (hb x hx v hv)]
  exact ht x hx t ht' v hv

omit hH in
theorem clipWeight_eq_on_region {w : Spacetime → ℝ} {M : ℝ}
    (hb : MixedNullWeightBound H w M) {p : Spacetime} (hp : p ∈ mixedNullRegion H) :
    mixedNullClipWeight M w p = w p := by
  let x : JointSpace := (WithLp.equiv 2 _).symm (spatialPart p)
  have he : Fin.cons (p 0) (x : Spatial) = p := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hp' := (mixedNull_cons_mem_iff H (p 0) (x : Spatial)).mp (he.symm ▸ hp)
  change -H x < p 0 ∧ p 0 < -‖x‖ at hp'
  have hx : x ∈ mixedNullSpatialDomain H := by change ‖x‖ < H x; linarith [hp'.1, hp'.2]
  have hh := hb x hx (p 0) ⟨hp'.1.le, hp'.2.le⟩
  rw [he] at hh
  exact mixedNullClipWeight_eq hh

/-- Equality of the original point and full-partner pair terms, before any
Gaussian reduction or limit. The extension is not a change of observable. -/
theorem weightedContinuumMean_clip_eq {w : Spacetime → ℝ} {M : ℝ}
    (hb : MixedNullWeightBound H w M) (ρ : ℝ) :
    weightedContinuumMean ρ (mixedNullRegion H) (mixedNullClipWeight M w) =
      weightedContinuumMean ρ (mixedNullRegion H) w := by
  unfold weightedContinuumMean
  congr 1
  congr 1
  · apply setIntegral_congr_fun hH.isOpen_region.measurableSet
    intro p hp
    exact clipWeight_eq_on_region hb hp
  · congr 1
    apply setIntegral_congr_fun hH.isOpen_region.measurableSet
    intro p hp
    dsimp only
    rw [clipWeight_eq_on_region hb hp]

/-- Local value bounds already give absolute spatial integrability, including
at sigma zero, by equality with the genuinely integrable bounded extension. -/
theorem integrable_weightedCoareaKernel_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M) (s : ℝ) :
    Integrable (fun x : JointSpace => mixedNullCoareaKernel H s x * w (mixedNullCoareaPoint s x)) :=
  (hH.integrable_weightedCoareaKernel (mixedNullClipWeight_measurable hw M)
    (mixedNullClipWeight_bound hM w) s).congr
      (Eventually.of_forall (weightedCoareaKernel_clip_eq hb s))

/-- Actual finite-density NM4 with local bounds only. -/
theorem weightedContinuumMean_eq_globalWeight_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M) {ρ : ℝ} (hρ : 0 < ρ) :
    weightedContinuumMean ρ (mixedNullRegion H) w =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ s in Ioi (0 : ℝ),
        Real.exp (-(Real.pi / 24) * ρ * s ^ 2) * mixedNullWeightedGlobalWeight H w s := by
  have he := hH.weightedContinuumMean_eq_globalWeight hρ (mixedNullClipWeight_measurable hw M)
    (mixedNullClipWeight_bound hM w)
  simpa only [hH.weightedContinuumMean_clip_eq hb, weightedGlobalWeight_clip_eq hb] using he

/-- The actual cone-trace endpoint for locally bounded weights. Radial
endpoints are removed only inside already integrable bounded extensions. -/
theorem weightedGlobalWeight_zero_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M) :
    mixedNullWeightedGlobalWeight H w 0 =
      (1 / 2 : ℝ) * ∫ u : MixedNullDirection,
        (∫ r in (0 : ℝ)..mixedNullRadius H u,
          r * w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace)))
        ∂(volume : Measure JointSpace).toSphere := by
  rw [← weightedGlobalWeight_clip_eq hb 0,
    hH.weightedGlobalWeight_zero (mixedNullClipWeight_measurable hw M) (mixedNullClipWeight_bound hM w)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [intervalIntegral.integral_of_le (hH.radius_pos u).le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (hH.radius_pos u).le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr.1]
  have hx := (hH.radial_domain u hr.1.le).mpr hr.2
  have hh : r < H (r • (u : JointSpace)) := by
    change ‖r • (u : JointSpace)‖ < _ at hx
    rwa [hn] at hx
  dsimp only
  rw [mixedNullClipWeight_eq (hb _ hx (-r) ⟨by linarith, by rw [hn]⟩)]

/-- NM5 with only local closed-fibre bounds; box bounds suffice by the two
preceding box-specialization lemmas. In particular coordinate time is allowed. -/
theorem weightedGlobalWeight_error_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M)
    (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) :
    ‖mixedNullWeightedGlobalWeight H w s - mixedNullWeightedGlobalWeight H w 0‖ ≤
      mixedNullWeightedError (H 0) k M L s := by
  have he := hH.weightedGlobalWeight_error (mixedNullClipWeight_measurable hw M)
    (mixedNullClipWeight_bound hM w) hL (timeLipschitz_clip hb ht) hk hk1 h hs hsT
  simpa only [weightedGlobalWeight_clip_eq hb] using he

/-- NM7 under the source's local, rather than global, boundedness contract. -/
theorem weightedContinuumMean_error_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M)
    (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s ρ : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) (hρ : 0 < ρ) :
    ‖weightedContinuumMean ρ (mixedNullRegion H) w - 4 * mixedNullWeightedGlobalWeight H w 0‖ ≤
      4 * mixedNullWeightedError (H 0) k M L s +
        8 * M * Real.pi * (H 0 / (1 - k)) ^ 2 *
          mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s) := by
  have he := hH.weightedContinuumMean_error (mixedNullClipWeight_measurable hw M)
    (mixedNullClipWeight_bound hM w) hL (timeLipschitz_clip hb ht) hk hk1 h hs hsT hρ
  simpa only [hH.weightedContinuumMean_clip_eq hb, weightedGlobalWeight_clip_eq hb] using he

/-- Weighted right continuity under the original local time and value bounds. -/
theorem weightedGlobalWeight_right_continuous_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M L : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M)
    (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L) :
    ContinuousWithinAt (mixedNullWeightedGlobalWeight H w) (Ici 0) 0 := by
  have he := hH.weightedGlobalWeight_right_continuous_of_timeLipschitz
    (mixedNullClipWeight_measurable hw M) (mixedNullClipWeight_bound hM w) hL (timeLipschitz_clip hb ht)
  simpa only [show mixedNullWeightedGlobalWeight H (mixedNullClipWeight M w) =
    mixedNullWeightedGlobalWeight H w from funext (weightedGlobalWeight_clip_eq hb)] using he

/-- The original action's weighted scalar limit with box-local data only. -/
theorem weightedContinuumMean_limit_local {w : Spacetime → ℝ} (hw : Measurable w)
    {M L : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M)
    (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L) :
    Tendsto (fun ρ : ℝ => weightedContinuumMean ρ (mixedNullRegion H) w)
      atTop (𝓝 (4 * mixedNullWeightedGlobalWeight H w 0)) := by
  have he := hH.weightedContinuumMean_limit_of_timeLipschitz
    (mixedNullClipWeight_measurable hw M) (mixedNullClipWeight_bound hM w) hL (timeLipschitz_clip hb ht)
  simpa only [hH.weightedContinuumMean_clip_eq hb, weightedGlobalWeight_clip_eq hb] using he

end MixedNullData
end BoundaryDraft

import BoundaryDraft.MixedNullErrorIntegrals

/-! NM5 for the actual signed global weight. The time Lipschitz hypothesis
is required only on closed vertical fibres over the admitted spatial domain.
The bound on the weight in the initial API is global and explicit. -/
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

def mixedNullErrorRadialIntegrand (H : Spatial → ℝ) (w : Spacetime → ℝ)
    (s : ℝ) (u : MixedNullDirection) (r : ℝ) : ℝ :=
  if Real.sqrt (r ^ 2 + s) < H (r • (u : JointSpace)) then
    (r ^ 2 / (2 * Real.sqrt (r ^ 2 + s))) *
      w (Fin.cons (-Real.sqrt (r ^ 2 + s)) (r • (u : JointSpace) : JointSpace)) else 0

/-- Time Lipschitz control only on the actual closed vertical fibres.
This permits discontinuous spatial cutoffs. -/
def MixedNullTimeLipschitz (H : Spatial → ℝ) (w : Spacetime → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ mixedNullSpatialDomain H, ∀ t ∈ Icc (-H x) (-‖x‖),
    ∀ v ∈ Icc (-H x) (-‖x‖),
      ‖w (Fin.cons t (x : Spatial)) - w (Fin.cons v (x : Spatial))‖ ≤ L * |t - v|

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem measurable_errorRadialIntegrand {w : Spacetime → ℝ} (hw : Measurable w) (s : ℝ) :
    Measurable (fun p : MixedNullDirection × ℝ => mixedNullErrorRadialIntegrand H w s p.1 p.2) := by
  have hx : Continuous (fun p : MixedNullDirection × ℝ => p.2 • (p.1 : JointSpace)) := by fun_prop
  have hp : Continuous (fun p : MixedNullDirection × ℝ =>
      (Fin.cons (-Real.sqrt (p.2 ^ 2 + s)) (p.2 • (p.1 : JointSpace) : JointSpace) : Spacetime)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun p : MixedNullDirection × ℝ => -Real.sqrt (p.2 ^ 2 + s))
      fun_prop
    · change Continuous (fun p : MixedNullDirection × ℝ => (p.2 • (p.1 : JointSpace)) j)
      exact (EuclideanSpace.proj j).continuous.comp hx
  have hq : Measurable (fun p : MixedNullDirection × ℝ => Real.sqrt (p.2 ^ 2 + s)) := by fun_prop
  exact (((measurable_snd.pow_const 2).div (measurable_const.mul hq)).mul
    (hw.comp hp.measurable)).ite
      (measurableSet_lt hq (hH.continuous_euclidean.measurable.comp hx.measurable)) measurable_const

omit hH in
theorem errorRadialIntegrand_norm_le {w : Spacetime → ℝ} {M : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (u : MixedNullDirection) : ‖mixedNullErrorRadialIntegrand H w s u r‖ ≤ M * (r / 2) := by
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  have hj := mixedNull_radial_jacobian_difference hr hs
  unfold mixedNullErrorRadialIntegrand
  split_ifs
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (r ^ 2 / (2 * Real.sqrt (r ^ 2 + s))) * M :=
        mul_le_mul_of_nonneg_left (hb _) (by positivity)
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith [hj.1]) hM
  · simp only [norm_zero]
    positivity

/-- The actual per-radius NM5 error is dominated by the logarithmic Jacobian
majorant, the proved removed shell, and the time-variation cost. -/
theorem errorRadialIntegrand_difference_bound {w : Spacetime → ℝ} {M L k : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s r : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4)
    (hr : 0 < r) (hrB : r ≤ H 0 / (1 - k)) (u : MixedNullDirection) :
    ‖mixedNullErrorRadialIntegrand H w s u r - mixedNullErrorRadialIntegrand H w 0 u r‖ ≤
      M * mixedNullJacobianErrorBound s r +
      M * (Icc (mixedNullRadius H u - s / ((H 0 / (1 + k)) * (1 - k)))
        (mixedNullRadius H u)).indicator (fun _ => (H 0 / (1 - k)) / 2) r + L * s / 4 := by
  let q := Real.sqrt (r ^ 2 + s)
  let B := H 0 / (1 - k)
  let R := mixedNullRadius H u
  let d := s / ((H 0 / (1 + k)) * (1 - k))
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  have hgap := mixedNull_sqrt_gap hr hs.le
  have hqr : r ≤ q := by dsimp [q]; linarith [hgap.1]
  have hq : 0 < q := hr.trans_le hqr
  have hj := mixedNull_radial_jacobian_difference hr hs.le
  have hJ0 : 0 ≤ mixedNullJacobianErrorBound s r := mixedNullJacobianErrorBound_nonneg hs.le hr.le
  have hJ : r / 2 - r ^ 2 / (2 * q) ≤ mixedNullJacobianErrorBound s r := by
    unfold mixedNullJacobianErrorBound
    split_ifs
    · exact hj.2.1
    · exact hj.2.2
  have hnorm : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hdom : r < H (r • (u : JointSpace)) ↔ r < R := by
    simpa only [mixedNullSpatialDomain, mem_setOf_eq, hnorm] using hH.radial_domain u hr.le
  have hS0 : 0 ≤ (Icc (R - d) R).indicator (fun _ : ℝ => B / 2) r :=
    Set.indicator_nonneg (fun _ _ => by positivity) _
  change _ ≤ M * mixedNullJacobianErrorBound s r +
    M * (Icc (R - d) R).indicator (fun _ => B / 2) r + L * s / 4
  unfold mixedNullErrorRadialIntegrand
  rw [add_zero, Real.sqrt_sq hr.le]
  have hbase : r ^ 2 / (2 * r) = r / 2 := by field_simp; ring
  rw [hbase]
  by_cases hc : q < H (r • (u : JointSpace))
  · have hc0 : r < H (r • (u : JointSpace)) := hqr.trans_lt hc
    rw [if_pos hc, if_pos hc0]
    let ws := w (Fin.cons (-q) (r • (u : JointSpace) : JointSpace))
    let w0 := w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace))
    have hwtime : ‖ws - w0‖ ≤ L * (q - r) := by
      have hx : r • (u : JointSpace) ∈ mixedNullSpatialDomain H := by
        change ‖r • (u : JointSpace)‖ < _
        rwa [hnorm]
      have he := ht _ hx (-q) ⟨by linarith, by rw [hnorm]; linarith⟩
        (-r) ⟨by linarith, by rw [hnorm]⟩
      simpa only [show -q - -r = -(q - r) by ring, abs_neg,
        abs_of_nonneg (sub_nonneg.mpr hqr)] using he
    have htime : (r ^ 2 / (2 * q)) * ‖ws - w0‖ ≤ L * s / 4 := by
      calc
        _ ≤ (r ^ 2 / (2 * q)) * (L * (q - r)) :=
          mul_le_mul_of_nonneg_left hwtime (by positivity)
        _ ≤ (r / 2) * (L * (q - r)) :=
          mul_le_mul_of_nonneg_right (by linarith [hj.1]) (mul_nonneg hL (sub_nonneg.mpr hqr))
        _ ≤ (r / 2) * (L * (s / (2 * r))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap.2 hL) (by positivity)
        _ = _ := by field_simp; ring
    have hweight : ‖(r ^ 2 / (2 * q) - r / 2) * w0‖ ≤
        M * mixedNullJacobianErrorBound s r := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hj.1])]
      have hn : -(r ^ 2 / (2 * q) - r / 2) = r / 2 - r ^ 2 / (2 * q) := by ring
      rw [hn]
      calc
        _ ≤ (r / 2 - r ^ 2 / (2 * q)) * M :=
          mul_le_mul_of_nonneg_left (hb _) hj.1
        _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hJ hM
    have he : ‖(r ^ 2 / (2 * q)) * ws - (r / 2) * w0‖ ≤
        M * mixedNullJacobianErrorBound s r + L * s / 4 := by
      calc
        _ = ‖(r ^ 2 / (2 * q) - r / 2) * w0 + (r ^ 2 / (2 * q)) * (ws - w0)‖ := by
          congr 1; ring
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add hweight (by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact htime))
    exact he.trans (by linarith [mul_nonneg hM hS0])
  · rw [if_neg hc]
    by_cases hc0 : r < H (r • (u : JointSpace))
    · rw [if_pos hc0, zero_sub, norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hrR : r < R := hdom.mp hc0
      have hshell : R - d ≤ r := hH.coarea_removed_shell hk hk1 h u hr hs.le hsT hrR (le_of_not_gt hc)
      rw [Set.indicator_of_mem (show r ∈ Icc (R - d) R from ⟨hshell, hrR.le⟩)]
      have he : (r / 2) * ‖w (Fin.cons (-r) (r • (u : JointSpace) : JointSpace))‖ ≤ M * (B / 2) := by
        calc
          _ ≤ (r / 2) * M := mul_le_mul_of_nonneg_left (hb _) (by positivity)
          _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by dsimp [B]; linarith) hM
      exact he.trans (by linarith [mul_nonneg hM hJ0, mul_nonneg hL hs.le])
    · rw [if_neg hc0, sub_zero, norm_zero]
      positivity

theorem errorRadialIntegrand_integrable {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) {s B : ℝ} (hs : 0 ≤ s) (hB : 0 < B)
    (u : MixedNullDirection) : IntervalIntegrable (mixedNullErrorRadialIntegrand H w s u) volume 0 B := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hB.le).mpr
  have hi : IntegrableOn (fun r : ℝ => M * (r / 2)) (Ioc 0 B) :=
    (by fun_prop : Continuous (fun r : ℝ => M * (r / 2))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hm := (hH.measurable_errorRadialIntegrand hw s).comp
    (show Measurable (fun r : ℝ => (u, r)) from measurable_const.prodMk measurable_id)
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact errorRadialIntegrand_norm_le hb hs hr.1 u

omit hH in
theorem errorRadialIntegral_norm_le {w : Spacetime → ℝ} {M : ℝ}
    (hb : ∀ p, ‖w p‖ ≤ M) {s B : ℝ} (hs : 0 ≤ s) (hB : 0 < B)
    (u : MixedNullDirection) :
    ‖∫ r in (0 : ℝ)..B, mixedNullErrorRadialIntegrand H w s u r‖ ≤ M * B ^ 2 / 4 := by
  rw [intervalIntegral.integral_of_le hB.le]
  have hi : IntegrableOn (fun r : ℝ => M * (r / 2)) (Ioc 0 B) :=
    (by fun_prop : Continuous (fun r : ℝ => M * (r / 2))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc
    _ ≤ ∫ r in Ioc (0 : ℝ) B, M * (r / 2) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact errorRadialIntegrand_norm_le hb hs hr.1 u
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hB.le, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, integral_id]
      ring

theorem errorRadialIntegral_integrable {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) {s B : ℝ} (hs : 0 ≤ s) (hB : 0 < B) :
    Integrable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..B,
      mixedNullErrorRadialIntegrand H w s u r) (volume : Measure JointSpace).toSphere := by
  have hm : Measurable (fun u : MixedNullDirection => ∫ r in (0 : ℝ)..B,
      mixedNullErrorRadialIntegrand H w s u r) := by
    simp_rw [intervalIntegral.integral_of_le hB.le]
    exact (hH.measurable_errorRadialIntegrand hw s).stronglyMeasurable.integral_prod_right.measurable
  exact (integrable_const (M * B ^ 2 / 4)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun u => errorRadialIntegral_norm_le hb hs hB u)

theorem globalWeight_eq_errorRadialIntegral {w : Spacetime → ℝ} (hw : Measurable w)
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖) {s : ℝ} (hs : 0 ≤ s) :
    mixedNullWeightedGlobalWeight H w s = ∫ u : MixedNullDirection,
      (∫ r in (0 : ℝ)..(H 0 / (1 - k)), mixedNullErrorRadialIntegrand H w s u r)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_eq_angular_radial hw hb hk hk1 h hs]
  apply integral_congr_ae
  filter_upwards [] with u
  apply intervalIntegral.integral_congr
  intro r _hr
  dsimp only
  unfold mixedNullErrorRadialIntegrand
  split_ifs <;> ring

/-- The complete integrated radial error, with the actual moving shell and
all three evaluated costs. -/
theorem errorRadialIntegral_difference_bound {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) (u : MixedNullDirection) :
    let B := H 0 / (1 - k)
    let m := H 0 / (1 + k)
    ‖(∫ r in (0 : ℝ)..B, mixedNullErrorRadialIntegrand H w s u r) -
      (∫ r in (0 : ℝ)..B, mixedNullErrorRadialIntegrand H w 0 u r)‖ ≤
      M * (s / 4 * (1 + Real.log (B / Real.sqrt s))) +
        M * ((B / 2) * (s / (m * (1 - k)))) + (L * s / 4) * B := by
  dsimp only
  let B := H 0 / (1 - k)
  let m := H 0 / (1 + k)
  let d := s / (m * (1 - k))
  let shell := (Icc (mixedNullRadius H u - d) (mixedNullRadius H u)).indicator
    (fun _ : ℝ => B / 2)
  have hM : 0 ≤ M := (norm_nonneg (w 0)).trans (hb 0)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  have hm : 0 < m := div_pos hH.tip_pos (by linarith)
  have hd : 0 ≤ d := div_nonneg hs.le (mul_nonneg hm.le (sub_nonneg.mpr hk1.le))
  have hBT : H 0 ≤ B := by
    apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    nlinarith [mul_nonneg hH.tip_pos.le hk]
  have hroot : Real.sqrt s ≤ B := by
    have he := Real.sq_sqrt hs.le
    have hn := Real.sqrt_nonneg s
    nlinarith [hH.tip_pos]
  have hJ := mixedNullJacobianErrorBound_bounds hs hroot
  have hiJ : IntegrableOn (mixedNullJacobianErrorBound s) (Ioc 0 B) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hB.le).mp hJ.1
  have hiS : IntegrableOn shell (Ioc 0 B) :=
    (mixedNull_shell_integrable (mixedNullRadius H u) d (B / 2)).integrableOn
  have hiC : IntegrableOn (fun _ : ℝ => L * s / 4) (Ioc 0 B) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiE := ((hiJ.const_mul M).add (hiS.const_mul M)).add hiC
  rw [← intervalIntegral.integral_sub
    (hH.errorRadialIntegrand_integrable hw hb hs.le hB u)
    (hH.errorRadialIntegrand_integrable hw hb (le_refl 0) hB u),
    intervalIntegral.integral_of_le hB.le]
  calc
    _ ≤ ∫ r in Ioc (0 : ℝ) B,
        M * mixedNullJacobianErrorBound s r + M * shell r + L * s / 4 := by
      apply norm_integral_le_of_norm_le hiE
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hH.errorRadialIntegrand_difference_bound hb hL ht hk hk1 h hs hsT hr.1 hr.2 u
    _ ≤ _ := by
      rw [integral_add (f := fun r => M * mixedNullJacobianErrorBound s r + M * shell r)
          ((hiJ.const_mul M).add (hiS.const_mul M)) hiC,
        integral_add (hiJ.const_mul M) (hiS.const_mul M), integral_const_mul, integral_const_mul,
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hB.le, sub_zero,
        ← intervalIntegral.integral_of_le hB.le, hJ.2]
      have he := mul_le_mul_of_nonneg_left
        (mixedNull_shell_integral (R := mixedNullRadius H u) (B := B) hd (by positivity : 0 ≤ B / 2)) hM
      dsimp [shell] at *
      nlinarith

/-- NM5, with its literal constants and original sigma range, for the actual
global spacetime-weighted coarea density. No desired estimate is assumed. -/
theorem weightedGlobalWeight_error {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) :
    ‖mixedNullWeightedGlobalWeight H w s - mixedNullWeightedGlobalWeight H w 0‖ ≤
      mixedNullWeightedError (H 0) k M L s := by
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  rw [hH.globalWeight_eq_errorRadialIntegral hw hb hk hk1 h hs.le,
    hH.globalWeight_eq_errorRadialIntegral hw hb hk hk1 h (le_refl 0),
    ← integral_sub (hH.errorRadialIntegral_integrable hw hb hs.le hB)
      (hH.errorRadialIntegral_integrable hw hb (le_refl 0) hB)]
  have he := norm_integral_le_of_norm_le (integrable_const (μ := (volume : Measure JointSpace).toSphere)
    (M * (s / 4 * (1 + Real.log (B / Real.sqrt s))) +
      M * ((B / 2) * (s / ((H 0 / (1 + k)) * (1 - k)))) + (L * s / 4) * B))
    (Eventually.of_forall fun u => hH.errorRadialIntegral_difference_bound hw hb hL ht hk hk1 h hs hsT u)
  rw [integral_const, smul_eq_mul, jointSphere_area] at he
  convert he using 1
  unfold mixedNullWeightedError
  dsimp [B]
  ring

end MixedNullData
end BoundaryDraft

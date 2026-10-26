import BoundaryDraft.MixedNullErrorExtension

/-!
# The actual NM11 partner-cutoff ledger

The point term occurs once. Both pair integrals retain the original region and
closed causal order; a cutoff multiplies their integrands, not their domains.
Absolute integrability is proved before splitting the signed kernel. No term
is asserted to vanish separately, uniformly or in a density limit.
-/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace BoundaryDraft

/-- Pair term with an actual measurable partner cutoff. -/
def mixedNullCutoffPair (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ)
    (χ : Spacetime → Spacetime → ℝ) : ℝ :=
  ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H ∩ causalFuture p,
    w p * χ p q * bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)

/-- The short ledger entry contains the single original point term. -/
def mixedNullCutoffShort (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ)
    (χ : Spacetime → Spacetime → ℝ) : ℝ :=
  (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ p in mixedNullRegion H, w p) - ρ * mixedNullCutoffPair H ρ w χ)

/-- The complementary entry is the omitted signed pair term, not a new
region action. The coefficient is exactly `-C * rho * sqrt rho`. -/
def mixedNullCutoffLong (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ)
    (χ : Spacetime → Spacetime → ℝ) : ℝ :=
  -(4 / Real.sqrt 6) * ρ * Real.sqrt ρ *
    mixedNullCutoffPair H ρ w (fun p q => 1 - χ p q)

/-- The actual assembly remainder; neither term of the ledger is dropped. -/
def mixedNullCutoffRemainder (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ)
    (χ : Spacetime → Spacetime → ℝ) : ℝ :=
  mixedNullCutoffShort H ρ w χ + mixedNullCutoffLong H ρ w χ -
    4 * mixedNullWeightedGlobalWeight H w 0

@[simp] theorem mixedNullCutoffLong_one (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ) :
    mixedNullCutoffLong H ρ w (fun _ _ => 1) = 0 := by
  simp [mixedNullCutoffLong, mixedNullCutoffPair]

@[simp] theorem mixedNullCutoffShort_zero (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ) :
    mixedNullCutoffShort H ρ w (fun _ _ => 0) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H, w p := by
  simp [mixedNullCutoffShort, mixedNullCutoffPair]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- General signed, bounded cutoff integrability on the genuine pair domain. -/
theorem integrable_cutoff_bilocal (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    {D : ℝ} (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      ‖χ p q‖ ≤ D) :
    IntegrableOn (fun p : Spacetime × Spacetime =>
      w p.1 * χ p.1 p.2 * bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      {p | p.1 ∈ mixedNullRegion H ∧ p.2 ∈ mixedNullRegion H ∧ p.2 ∈ causalFuture p.1} := by
  have hm := hH.isOpen_region.measurableSet
  have hS := (hm.preimage measurable_fst).inter
    ((hm.preimage measurable_snd).inter measurableSet_causalRelation)
  have he : (fun p : Spacetime × Spacetime =>
      w p.1 * χ p.1 p.2 * bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2)) =
      (fun p => χ p.1 p.2 * (w p.1 * bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))) := by
    funext p
    ring
  rw [he]
  apply (hH.integrable_weighted_bilocal ρ hw hb).bdd_mul' hχ.aestronglyMeasurable
    (c := D)
  filter_upwards [ae_restrict_mem hS] with p hp
  exact hχb p.1 hp.1 p.2 hp.2

/-- Every actual section is integrable, including null-related partners. -/
theorem integrable_cutoff_section (ρ : ℝ) (w : Spacetime → ℝ)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    {D : ℝ} (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      ‖χ p q‖ ≤ D) {p : Spacetime} (hp : p ∈ mixedNullRegion H) :
    IntegrableOn (fun q => w p * χ p q *
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2))
      (mixedNullRegion H ∩ causalFuture p) := by
  have hm := hH.isOpen_region.measurableSet.inter (isClosed_causalFuture p).measurableSet
  have hi := (integrableOn_bdg_future_of_bounded hH.isBounded_region ρ p).bdd_mul'
    (hχ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (show ∀ᵐ q ∂volume.restrict (mixedNullRegion H ∩ causalFuture p), ‖χ p q‖ ≤ D from by
      filter_upwards [ae_restrict_mem hm] with q hq
      exact hχb p hp q hq)
  simpa only [mul_assoc] using hi.const_mul (w p)

/-- Fubini integrability of the full cutoff outer integral. -/
theorem integrable_cutoff_outer (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    {D : ℝ} (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      ‖χ p q‖ ≤ D) :
    IntegrableOn (fun p => ∫ q in mixedNullRegion H ∩ causalFuture p,
      w p * χ p q * bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2))
      (mixedNullRegion H) := by
  classical
  let M := mixedNullRegion H
  let S : Set (Spacetime × Spacetime) := {p | p.1 ∈ M ∧ p.2 ∈ M ∧ p.2 ∈ causalFuture p.1}
  let K : Spacetime × Spacetime → ℝ := S.indicator (fun p =>
    w p.1 * χ p.1 p.2 * bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
  have hm : MeasurableSet M := hH.isOpen_region.measurableSet
  have hS : MeasurableSet S := (hm.preimage measurable_fst).inter
    ((hm.preimage measurable_snd).inter measurableSet_causalRelation)
  have hi : Integrable K (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrable_indicator_iff hS).mpr (hH.integrable_cutoff_bilocal ρ hw hb hχ hχb)
  apply (integrable_indicator_iff hm).mp
  apply hi.integral_prod_left.congr
  filter_upwards [] with p
  by_cases hp : p ∈ M
  · rw [indicator_of_mem hp, ← integral_indicator (hm.inter (isClosed_causalFuture p).measurableSet)]
    congr 1
    ext q
    simp [K, S, Set.indicator, hp]
  · simp [K, S, Set.indicator, hp]

/-- Exact complement identity for a bounded measurable partner cutoff.
Bounds need hold only on the real full causal pair domain. -/
theorem cutoffPair_add_complement (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    mixedNullCutoffPair H ρ w χ + mixedNullCutoffPair H ρ w (fun p q => 1 - χ p q) =
      ∫ p in mixedNullRegion H, w p * ∫ q in mixedNullRegion H ∩ causalFuture p,
        bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2) := by
  have hbχ : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      ‖χ p q‖ ≤ 1 := by
    intro p hp q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (hχb p hp q hq).1]
    exact (hχb p hp q hq).2
  have hbχ' : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      ‖1 - χ p q‖ ≤ 1 := by
    intro p hp q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hχb p hp q hq).2)]
    linarith [(hχb p hp q hq).1]
  unfold mixedNullCutoffPair
  rw [← integral_add (hH.integrable_cutoff_outer ρ hw hb hχ hbχ)
    (hH.integrable_cutoff_outer ρ hw hb (measurable_const.sub hχ) hbχ')]
  apply setIntegral_congr_fun hH.isOpen_region.measurableSet
  intro p hp
  dsimp only
  rw [← integral_add (hH.integrable_cutoff_section ρ w hχ hbχ hp)
    (hH.integrable_cutoff_section ρ w (measurable_const.sub hχ) hbχ' hp),
    ← integral_const_mul]
  apply setIntegral_congr_fun (hH.isOpen_region.measurableSet.inter
    (isClosed_causalFuture p).measurableSet)
  intro q _
  ring

/-- NM11's original short-plus-long ledger, with the point contribution once.
This finite-density identity does not even need density positivity. -/
theorem cutoff_ledger (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    mixedNullCutoffShort H ρ w χ + mixedNullCutoffLong H ρ w χ =
      weightedContinuumMean ρ (mixedNullRegion H) w := by
  have he := hH.cutoffPair_add_complement ρ hw hb hχ hχb
  unfold mixedNullCutoffShort mixedNullCutoffLong weightedContinuumMean
  rw [← he]
  ring

/-- The exact signed Gaussian is obtained only after restoring the entire
partner complement. No smallness estimate for the long entry is a premise. -/
theorem cutoff_ledger_eq_gaussian {ρ : ℝ} (hρ : 0 < ρ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    mixedNullCutoffShort H ρ w χ + mixedNullCutoffLong H ρ w χ =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        w p * Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) := by
  rw [hH.cutoff_ledger ρ hw hb hχ hχb,
    hH.weightedContinuumMean_eq_spacetimeGaussian hρ hw hb]

/-- The full remainder is exactly the weighted scalar error, independently
of the chosen partner cutoff. A quantitative bound must be proved separately. -/
theorem cutoff_remainder_eq (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    mixedNullCutoffRemainder H ρ w χ = weightedContinuumMean ρ (mixedNullRegion H) w -
      4 * mixedNullWeightedGlobalWeight H w 0 := by
  rw [mixedNullCutoffRemainder, hH.cutoff_ledger ρ hw hb hχ hχb]

/-- Finite overlapping source partitions are restored with their own actual
partner cutoffs. This is not a sum of actions on disjoint chart regions. -/
theorem cutoff_ledger_partition {ι : Type*} (s : Finset ι) {ρ : ℝ} (hρ : 0 < ρ)
    (w : ι → Spacetime → ℝ) (C : ι → ℝ) (χ : ι → Spacetime → Spacetime → ℝ)
    (hw : ∀ i ∈ s, Measurable (w i))
    (hb : ∀ i ∈ s, ∀ p ∈ mixedNullRegion H, ‖w i p‖ ≤ C i)
    (hχ : ∀ i ∈ s, Measurable (fun p : Spacetime × Spacetime => χ i p.1 p.2))
    (hχb : ∀ i ∈ s, ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ i p q ∧ χ i p q ≤ 1)
    (hs : ∀ p ∈ mixedNullRegion H, ∑ i ∈ s, w i p = 1) :
    (∑ i ∈ s, (mixedNullCutoffShort H ρ (w i) (χ i) +
      mixedNullCutoffLong H ρ (w i) (χ i))) = continuumMean ρ (mixedNullRegion H) := by
  calc
    _ = ∑ i ∈ s, weightedContinuumMean ρ (mixedNullRegion H) (w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hH.cutoff_ledger ρ (hw i hi) (hb i hi) (hχ i hi) (hχb i hi)
    _ = _ := hH.weightedContinuumMean_partition s hρ w C hw hb hs

/-- The actual full-ledger remainder satisfies NM7, with only the written
local value/time bounds. No estimate for the long entry alone is claimed. -/
theorem cutoff_remainder_bound {w : Spacetime → ℝ} (hw : Measurable w)
    {M L k s ρ : ℝ} (hM : 0 ≤ M) (hb : MixedNullWeightBound H w M)
    (hL : 0 ≤ L) (ht : MixedNullTimeLipschitz H w L)
    (hk : 0 ≤ k) (hk1 : k < 1)
    (hLip : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (hs : 0 < s) (hsT : s ≤ H 0 ^ 2 / 4) (hρ : 0 < ρ)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    ‖mixedNullCutoffRemainder H ρ w χ‖ ≤
      4 * mixedNullWeightedError (H 0) k M L s + 8 * M * Real.pi * (H 0 / (1 - k)) ^ 2 *
        mixedNullErfc (Real.sqrt ((Real.pi / 24) * ρ) * s) := by
  have hbM : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ M := by
    intro p hp
    rw [← clipWeight_eq_on_region hb hp]
    exact mixedNullClipWeight_bound hM w p
  rw [hH.cutoff_remainder_eq ρ hw hbM hχ hχb]
  exact hH.weightedContinuumMean_error_local hw hM hb hL ht hk hk1 hLip hs hsT hρ

end MixedNullData
end BoundaryDraft

import BoundaryDraft.MixedNullReduction
import BoundaryDraft.WeightedGraphAction

/-!
# Mixed-region source weights retain every partner

The finite-density partition assertion preceding MA11 holds for signed,
bounded measurable weights, not merely smooth ones. No weighted asymptotic
formula or assertion that a source complement vanishes is made here.
-/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace BoundaryDraft.MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem integrable_weighted_continuous {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {f : Spacetime → ℝ} (hf : Continuous f) :
    IntegrableOn (fun p => w p * f p) (mixedNullRegion H) := by
  have hi : IntegrableOn f (mixedNullRegion H) :=
    (hf.continuousOn.integrableOn_compact hH.isBounded_region.isCompact_closure).mono_set
      subset_closure
  apply hi.bdd_mul' hw.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hH.isOpen_region.measurableSet] with p hp
  exact hb p hp

/-- Absolute integrability before cancellation also holds for merely
measurable, signed source weights. No cross-region pair is discarded. -/
theorem integrable_weighted_bilocal (ρ : ℝ) {w : Spacetime → ℝ}
    (hw : Measurable w) {C : ℝ}
    (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C) :
    IntegrableOn (fun p : Spacetime × Spacetime => w p.1 *
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      {p | p.1 ∈ mixedNullRegion H ∧ p.2 ∈ mixedNullRegion H ∧
        p.2 ∈ causalFuture p.1} := by
  have hm := hH.isOpen_region.measurableSet
  have hS := (hm.preimage measurable_fst).inter
    ((hm.preimage measurable_snd).inter measurableSet_causalRelation)
  apply (integrableOn_bilocal_bdg hH.isBounded_region ρ).bdd_mul'
    (hw.comp measurable_fst).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hS] with p hp
  exact hb p.1 hp.1

/-- The weight is on the first endpoint only; the actual inner action still
includes all partners in the original region, with its signed BDG kernel. -/
theorem weightedContinuumMean_eq_spacetimeGaussian {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w)
    {C : ℝ} (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C) :
    weightedContinuumMean ρ (mixedNullRegion H) w =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        w p * Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) := by
  let M := mixedNullRegion H
  let E := fun p : Spacetime => Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2)
  let Q := fun p : Spacetime => ∫ q in M ∩ causalFuture p,
    bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)
  have hm : MeasurableSet M := hH.isOpen_region.measurableSet
  have hE : Continuous E := by
    have hs := continuous_intervalSq.comp (continuous_id.prodMk (continuous_const (y := (0 : Spacetime))))
    dsimp [E]
    fun_prop
  have hiw : IntegrableOn w M := by
    simpa only [mul_one] using hH.integrable_weighted_continuous hw hb
      (continuous_const : Continuous (fun _ : Spacetime => (1 : ℝ)))
  have hiE : IntegrableOn (fun p => w p * E p) M :=
    hH.integrable_weighted_continuous hw hb hE
  have hinner : (∫ p in M, w p * Q p) = ∫ p in M, (w p - w p * E p) / ρ := by
    apply setIntegral_congr_fun hm
    intro p hp
    have he : ρ * Q p = 1 - E p := hH.future_kernel_identity hρ p hp
    apply (eq_div_iff hρ.ne').mpr
    calc
      (w p * Q p) * ρ = w p * (ρ * Q p) := by ring
      _ = w p - w p * E p := by rw [he]; ring
  have hrho : ρ * (∫ p in M, (w p - w p * E p) / ρ) =
      ∫ p in M, w p - w p * E p := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro p _
    field_simp
  change (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ p in M, w p) - ρ * ∫ p in M, w p * Q p) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in M, w p * E p
  rw [hinner, hrho, integral_sub hiw hiE]
  ring

/-- Signed, overlapping source partitions sum to the full original action.
This is not additivity for actions of separately restricted chart regions. -/
theorem weightedContinuumMean_partition {ι : Type*} (s : Finset ι)
    {ρ : ℝ} (hρ : 0 < ρ) (w : ι → Spacetime → ℝ) (C : ι → ℝ)
    (hw : ∀ i ∈ s, Measurable (w i))
    (hb : ∀ i ∈ s, ∀ p ∈ mixedNullRegion H, ‖w i p‖ ≤ C i)
    (hs : ∀ p ∈ mixedNullRegion H, ∑ i ∈ s, w i p = 1) :
    (∑ i ∈ s, weightedContinuumMean ρ (mixedNullRegion H) (w i)) =
      continuumMean ρ (mixedNullRegion H) := by
  let E := fun p : Spacetime => Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2)
  have hE : Continuous E := by
    have hi := continuous_intervalSq.comp (continuous_id.prodMk (continuous_const (y := (0 : Spacetime))))
    dsimp [E]
    fun_prop
  calc
    _ = ∑ i ∈ s, (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ p in mixedNullRegion H, w i p * E p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hH.weightedContinuumMean_eq_spacetimeGaussian hρ (hw i hi) (hb i hi)
    _ = (4 / Real.sqrt 6) * Real.sqrt ρ *
        ∫ p in mixedNullRegion H, ∑ i ∈ s, w i p * E p := by
      rw [← Finset.mul_sum]
      congr 1
      exact (integral_finset_sum s (fun i hi =>
        hH.integrable_weighted_continuous (hw i hi) (hb i hi) hE)).symm
    _ = (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H, E p := by
      congr 1
      apply setIntegral_congr_fun hH.isOpen_region.measurableSet
      intro p hp
      change (∑ i ∈ s, w i p * E p) = E p
      rw [← Finset.sum_mul, hs p hp, one_mul]
    _ = _ := (hH.continuumMean_eq_spacetimeGaussian hρ).symm

end BoundaryDraft.MixedNullData

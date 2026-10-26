import BoundaryDraft.MixedNullProbabilityGeometry

/-!
# Expanded original-law Campbell--Mecke formulas for MA14

Both endpoint intensities are expanded to the factor `ρ²`. The first formula
uses the actual endpoint-excluded restricted interval rate. Closed containment
then identifies it with the original Minkowski phase. No chart replaces the
partner region, and every layer retains its Poisson factorial denominator.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- MA14's actual restricted-rate integrand, defined without assuming convexity. -/
def mixedNullLayerIntegrand (H : Spatial → ℝ) (ρ : ℝ) (k : ℕ) (p q : Spacetime) : ℝ :=
  if q ∈ causalFuture p ∧ p ≠ q then
    Real.exp (-(ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})))) *
      (ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q}))) ^ k /
        k.factorial
  else 0

/-- The original Minkowski-rate integrand still uses closed causal order and
unequal endpoints. Null pairs have not been deleted from this definition. -/
def mixedNullMinkowskiLayerIntegrand (ρ : ℝ) (k : ℕ) (p q : Spacetime) : ℝ :=
  if q ∈ causalFuture p ∧ p ≠ q then
    Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
      ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ k / k.factorial
  else 0

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ}
include hH

/-- Expanding the actual Poisson PMF and restricted intensity, not postulating
an expectation or changing the interval counts. -/
theorem poissonLayerMean_eq_restricted (hρ : 0 < ρ) (k : ℕ) :
    poissonLayerMean (hH.boundedCausalRegion.sprinkling ρ hρ) k =
      mixedNullLayerIntegrand H ρ k := by
  funext p q
  unfold poissonLayerMean mixedNullLayerIntegrand
  split_ifs
  · rw [show (poissonPMF
        ((hH.boundedCausalRegion.sprinkling ρ hρ).intensity
          (causalIntervalInterior p q)).toNNReal k).toReal =
        poissonPMFReal ((hH.boundedCausalRegion.sprinkling ρ hρ).intensity
          (causalIntervalInterior p q)).toNNReal k from
      ENNReal.toReal_ofReal poissonPMFReal_nonneg]
    simp only [poissonPMFReal, ENNReal.coe_toNNReal_eq_toReal,
      FiniteSprinkling.intensity_toReal _ (measurableSet_causalIntervalInterior p q)]
    rw [inter_comm]
    rfl
  · rfl

/-- Pointwise rate identification on the entire original partner region,
including null-related distinct endpoints. -/
theorem poisson_layer_integrand_eq_minkowski (hρ : 0 < ρ) (k : ℕ)
    {p q : Spacetime} (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H) :
    mixedNullLayerIntegrand H ρ k p q = mixedNullMinkowskiLayerIntegrand ρ k p q := by
  unfold mixedNullLayerIntegrand mixedNullMinkowskiLayerIntegrand
  split_ifs with hpq
  · rw [hH.poisson_restricted_interval_rate hρ hp hq hpq.1]
  · rfl

theorem poisson_layer_integrand_measurable (hρ : 0 < ρ) (k : ℕ) :
    Measurable (fun p : Spacetime × Spacetime => mixedNullLayerIntegrand H ρ k p.1 p.2) := by
  rw [← hH.poissonLayerMean_eq_restricted hρ k]
  exact measurable_poissonLayerMean _ k

/-- The actual restricted layer integrand is everywhere between zero and one. -/
theorem poisson_layer_integrand_bounds (hρ : 0 < ρ) (k : ℕ) (p q : Spacetime) :
    0 ≤ mixedNullLayerIntegrand H ρ k p q ∧ mixedNullLayerIntegrand H ρ k p q ≤ 1 := by
  rw [← hH.poissonLayerMean_eq_restricted hρ k]
  exact ⟨poissonLayerMean_nonneg _ k p q, poissonLayerMean_le_one _ k p q⟩

theorem poisson_integrable_layer (hρ : 0 < ρ) (k : ℕ) :
    Integrable (fun c : Multiset Spacetime => (intervalLayer k c : ℝ))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  integrable_intervalLayer (hH.boundedCausalRegion.sprinkling ρ hρ) k

/-- Integrability is in unscaled original product volume, before the factor
`ρ²` is placed outside the integral. -/
theorem poisson_integrable_layer_integrand (hρ : 0 < ρ) (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime => mixedNullLayerIntegrand H ρ k p.1 p.2)
      ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H))) := by
  letI : IsFiniteMeasure (volume.restrict (mixedNullRegion H)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hH.region_volume_lt_top⟩
  apply (integrable_const (1 : ℝ)).mono'
    (hH.poisson_layer_integrand_measurable hρ k).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hH.poisson_layer_integrand_bounds hρ k p.1 p.2).1]
    exact (hH.poisson_layer_integrand_bounds hρ k p.1 p.2).2

theorem poisson_integrable_layer_section (hρ : 0 < ρ) (k : ℕ) (p : Spacetime) :
    Integrable (mixedNullLayerIntegrand H ρ k p) (volume.restrict (mixedNullRegion H)) := by
  letI : IsFiniteMeasure (volume.restrict (mixedNullRegion H)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hH.region_volume_lt_top⟩
  apply (integrable_const (1 : ℝ)).mono'
    ((hH.poisson_layer_integrand_measurable hρ k).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    change ‖mixedNullLayerIntegrand H ρ k p q‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hH.poisson_layer_integrand_bounds hρ k p q).1]
    exact (hH.poisson_layer_integrand_bounds hρ k p q).2

/-- MA14 with both intensity factors and the genuine restricted rate fully
expanded. It is an expectation under the original law for each natural layer. -/
theorem poisson_integral_layer_restricted (hρ : 0 < ρ) (k : ℕ) :
    (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H,
        if q ∈ causalFuture p ∧ p ≠ q then
          Real.exp (-(ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})))) *
            (ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q}))) ^ k /
              k.factorial
        else 0 := by
  rw [show (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ∫ p, ∫ q, poissonLayerMean (hH.boundedCausalRegion.sprinkling ρ hρ) k p q
        ∂(hH.boundedCausalRegion.sprinkling ρ hρ).intensity
        ∂(hH.boundedCausalRegion.sprinkling ρ hρ).intensity from
    integral_intervalLayer (hH.boundedCausalRegion.sprinkling ρ hρ) k]
  rw [hH.poissonLayerMean_eq_restricted hρ k]
  simp only [FiniteSprinkling.intensity, BoundedCausalRegion.sprinkling,
    integral_smul_measure, ENNReal.toReal_ofReal hρ.le, smul_eq_mul, integral_const_mul]
  rw [← mul_assoc, ← pow_two]
  rfl

/-- The same expectation with the actual Minkowski interval phase, still
retaining the closed causal condition and distinct endpoints. -/
theorem poisson_integral_layer_minkowski (hρ : 0 < ρ) (k : ℕ) :
    (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H,
        if q ∈ causalFuture p ∧ p ≠ q then
          Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
            ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ k / k.factorial
        else 0 := by
  rw [hH.poisson_integral_layer_restricted hρ k]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hH.isOpen_region.measurableSet] with p hp
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hH.isOpen_region.measurableSet] with q hq
  exact hH.poisson_layer_integrand_eq_minkowski hρ k hp hq

/-- The Minkowski integrand is also bounded between zero and one on the full
region product, as a consequence of the actual restricted Poisson rate. -/
theorem poisson_minkowski_layer_bounds (hρ : 0 < ρ) (k : ℕ)
    {p q : Spacetime} (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H) :
    0 ≤ mixedNullMinkowskiLayerIntegrand ρ k p q ∧
      mixedNullMinkowskiLayerIntegrand ρ k p q ≤ 1 := by
  rw [← hH.poisson_layer_integrand_eq_minkowski hρ k hp hq]
  exact hH.poisson_layer_integrand_bounds hρ k p q

theorem poisson_integrable_minkowski_layer (hρ : 0 < ρ) (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime => mixedNullMinkowskiLayerIntegrand ρ k p.1 p.2)
      ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H))) := by
  apply (hH.poisson_integrable_layer_integrand hρ k).congr
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (hH.isOpen_region.measurableSet.prod hH.isOpen_region.measurableSet)] with p hp
  exact hH.poisson_layer_integrand_eq_minkowski hρ k hp.1 hp.2

theorem poisson_integrable_minkowski_section (hρ : 0 < ρ) (k : ℕ)
    {p : Spacetime} (hp : p ∈ mixedNullRegion H) :
    Integrable (mixedNullMinkowskiLayerIntegrand ρ k p) (volume.restrict (mixedNullRegion H)) := by
  apply (hH.poisson_integrable_layer_section hρ k p).congr
  filter_upwards [ae_restrict_mem hH.isOpen_region.measurableSet] with q hq
  exact hH.poisson_layer_integrand_eq_minkowski hρ k hp hq

/-- Only in the continuous integral may the distinct-endpoint condition be
removed. Null/diagonal pairs are discarded by the proved a.e. cone statement,
not by altering the finite-order observable. -/
theorem poisson_integral_layer_future (hρ : 0 < ρ) (k : ℕ) :
    (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H ∩ causalFuture p,
        Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
          ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ k / k.factorial := by
  rw [hH.poisson_integral_layer_minkowski hρ k]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  rw [inter_comm, ← Measure.restrict_restrict (isClosed_causalFuture p).measurableSet,
    ← integral_indicator (isClosed_causalFuture p).measurableSet]
  apply integral_congr_ae
  filter_upwards [(ae_causalFuture_chronological p).filter_mono ae_restrict_le] with q hq
  by_cases hpq : q ∈ causalFuture p
  · simp only [hpq, (hq hpq).2, ne_eq, not_false_eq_true, and_self, if_true,
      indicator_of_mem hpq]
  · simp [hpq]

/-- MA15 in the note's normalization, with the actual law and both intensities
visible. This is a finite-layer consequence, not an exponential-series swap. -/
theorem poisson_integral_action (hρ : 0 < ρ) :
    (∫ c, discreteBDGAction ρ c
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      4 / Real.sqrt (6 * ρ) *
        (ρ * volume.real (mixedNullRegion H) -
          ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H ∩ causalFuture p,
            (1 - 9 * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) +
              8 * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 2 -
              (4 / 3) * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 3) *
                Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2))) := by
  let S := hH.boundedCausalRegion.sprinkling ρ hρ
  change (∫ c, discreteBDGAction S.density c ∂S.probability) = _
  rw [S.integral_discreteBDGAction, S.integral_poissonBDGMean hH.causallyConvex,
    mixedNull_bdgNormalization]
  rfl

end MixedNullData
end BoundaryDraft

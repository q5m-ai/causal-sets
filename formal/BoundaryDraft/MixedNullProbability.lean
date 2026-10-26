import BoundaryDraft.MixedNullElementary

/-!
# Original-law probability and factorial moments for MA13

The measure in every conclusion is the constructed finite Poisson law on the
whole mixed region. No expectation, moment, or support assertion is a field of
`MixedNullData`. Closed causal order and the two excluded marked endpoints
remain those of `DiscreteBDG`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Real falling factorial, including the empty configuration. -/
theorem mixedNull_pairCard_cast (n : ℕ) :
    ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n <;> simp [Nat.cast_mul, Nat.cast_add]

/-- The note's square-root convention is the existing normalization. -/
theorem mixedNull_bdgNormalization (ρ : ℝ) :
    bdgNormalization ρ = 4 / Real.sqrt (6 * ρ) := by
  rw [bdgNormalization, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]

/-- MA13's coefficient is 16, not the sum of the four absolute coefficients. -/
theorem mixedNull_abs_discreteBDGAction_le {ρ : ℝ} (hρ : 0 < ρ)
    (c : Multiset Spacetime) :
    |discreteBDGAction ρ c| ≤ 4 / Real.sqrt (6 * ρ) *
      ((c.card : ℝ) + 16 * ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  have hb := abs_discreteBDGAction_le ρ c
  rw [abs_of_pos (bdgNormalization_pos hρ), mixedNull_bdgNormalization,
    mixedNull_pairCard_cast] at hb
  exact hb

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ}
include hH

/-- The literal original mixed law is a probability measure. -/
theorem poisson_isProbabilityMeasure (hρ : 0 < ρ) :
    IsProbabilityMeasure
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  inferInstanceAs (IsProbabilityMeasure (hH.boundedCausalRegion.sprinkling ρ hρ).probability)

theorem poisson_ae_supported (hρ : 0 < ρ) :
    ∀ᵐ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H)),
      ∀ x ∈ c, x ∈ mixedNullRegion H :=
  (hH.boundedCausalRegion.sprinkling ρ hρ).ae_supported

theorem poisson_ae_nodup (hρ : 0 < ρ) :
    ∀ᵐ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H)),
      c.Nodup :=
  (hH.boundedCausalRegion.sprinkling ρ hρ).ae_nodup

/-- The supported simple sample has the genuine finite-order action. The
layer-pair finsets use closed causality, unequal endpoints, and only the two
marked endpoints removed from each interval. -/
theorem poisson_ae_finite_order (hρ : 0 < ρ) :
    ∀ᵐ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H)),
      (∀ x ∈ c, x ∈ mixedNullRegion H) ∧ c.Nodup ∧
      discreteBDGAction ρ c = 4 / Real.sqrt (6 * ρ) *
        ((Fintype.card (CausalPoint c) : ℝ) - (causalLayerPairs 0 c).card +
          9 * (causalLayerPairs 1 c).card - 16 * (causalLayerPairs 2 c).card +
          8 * (causalLayerPairs 3 c).card) := by
  filter_upwards [hH.poisson_ae_supported hρ, hH.poisson_ae_nodup hρ] with c hs hc
  exact ⟨hs, hc, by simpa only [mixedNull_bdgNormalization] using
    discreteBDGAction_eq_finite_order ρ hc⟩

/-- The count distribution has mean density times the original four-volume. -/
theorem poisson_card_probability (hρ : 0 < ρ) (n : ℕ) :
    FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))
      {c : Multiset Spacetime | c.card = n} =
      ENNReal.ofReal (Real.exp (-(ρ * volume.real (mixedNullRegion H))) *
        (ρ * volume.real (mixedNullRegion H)) ^ n / n.factorial) := by
  simpa only [FiniteConfiguration.count_univ, univ_inter, measureReal_def] using
    (hH.boundedCausalRegion.sprinkling ρ hρ).count_probability MeasurableSet.univ n

theorem poisson_integrable_card (hρ : 0 < ρ) :
    Integrable (fun c : Multiset Spacetime => (c.card : ℝ))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  FinitePoisson.integrable_card (hH.boundedCausalRegion.sprinkling ρ hρ).intensity

/-- First real factorial moment, with no bounded-cardinality assumption. -/
theorem poisson_integral_card (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (c.card : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ * volume.real (mixedNullRegion H) :=
  (hH.boundedCausalRegion.sprinkling ρ hρ).integral_card

theorem poisson_integrable_pairCard (hρ : 0 < ρ) :
    Integrable (fun c : Multiset Spacetime => (c.card : ℝ) * ((c.card : ℝ) - 1))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) := by
  simpa only [mixedNull_pairCard_cast] using
    FinitePoisson.integrable_pairCard (hH.boundedCausalRegion.sprinkling ρ hρ).intensity

/-- Second real factorial moment: distinct ordered occurrences, not `N²`. -/
theorem poisson_integral_pairCard (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (c.card : ℝ) * ((c.card : ℝ) - 1)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      (ρ * volume.real (mixedNullRegion H)) ^ 2 := by
  let S := hH.boundedCausalRegion.sprinkling ρ hρ
  change (∫ c : Multiset Spacetime, (c.card : ℝ) * ((c.card : ℝ) - 1)
    ∂FinitePoisson.law S.intensity) = _
  simp_rw [← mixedNull_pairCard_cast]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun c : Multiset Spacetime =>
      Nat.cast_nonneg (c.card * (c.card - 1)))
    (FinitePoisson.integrable_pairCard S.intensity).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, FinitePoisson.lintegral_pairCard,
    ENNReal.toReal_mul]
  rw [S.intensity_toReal MeasurableSet.univ, univ_inter]
  exact (pow_two _).symm

/-- MA13 supplies an integrable quadratic dominator in exactly the note's
normalization; the original discrete observable is already absolutely
integrable by `integrable_discrete_action`. -/
theorem poisson_integrable_action_bound (hρ : 0 < ρ) :
    Integrable (fun c : Multiset Spacetime => 4 / Real.sqrt (6 * ρ) *
      ((c.card : ℝ) + 16 * ((c.card : ℝ) * ((c.card : ℝ) - 1))))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  ((hH.poisson_integrable_card hρ).add
    ((hH.poisson_integrable_pairCard hρ).const_mul 16)).const_mul _

end MixedNullData
end BoundaryDraft

import BoundaryDraft.MixedNullProbabilityLayers
import BoundaryDraft.MixedNullGeometryExamples

/-!
Independent original-law contracts for MA13--MA15. The probability measure,
real falling factorial, intensity factors, interval rate, and factorial
weights are expanded below. The nonaffine floor and a supported null chain
prevent a planar-only or chronological-order replacement.
-/

open MeasureTheory Set BoundaryDraft
open scoped ENNReal Classical BigOperators
noncomputable section
namespace MixedNullProbabilityRegression

-- Only the original geometric inputs, not any probability identity, are used.
example (H : Spatial → ℝ) (hT : 0 < H 0) (κ : ℝ) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (hLip : ∀ x y, |H x - H y| ≤ κ * spatialDistance x y) {ρ : ℝ} (hρ : 0 < ρ) :
    IsProbabilityMeasure (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
      {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
        spatialSeparationSq p 0 < (0 - p 0) ^ 2})) :=
  (show MixedNullData H from ⟨hT, κ, hκ, hκ1, hLip⟩).poisson_isProbabilityMeasure hρ

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
      {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
        spatialSeparationSq p 0 < (0 - p 0) ^ 2}),
      c.Nodup ∧ ∀ p ∈ c, -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
        spatialSeparationSq p 0 < (0 - p 0) ^ 2 := by
  filter_upwards [hH.poisson_ae_nodup hρ, hH.poisson_ae_supported hρ] with c hc hs
  exact ⟨hc, hs⟩

-- The finite-order layer is an actual finset of distinct closed-causal pairs.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ c ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H)),
      let L := fun k : ℕ => ((c.toFinset ×ˢ c.toFinset).filter fun p =>
        p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2 ∧
          (c.toFinset.filter fun z => z ∈ causalInterval p.1 p.2 \ {p.1, p.2}).card = k).card
      (∀ p ∈ c, p ∈ mixedNullRegion H) ∧ c.Nodup ∧
        discreteBDGAction ρ c = 4 / Real.sqrt (6 * ρ) *
          ((Fintype.card (CausalPoint c) : ℝ) - L 0 + 9 * L 1 - 16 * L 2 + 8 * L 3) := by
  filter_upwards [hH.poisson_ae_finite_order hρ] with c hc
  dsimp only
  have hi (p q : Spacetime) :
      (c.toFinset.filter fun z => z ∈ causalInterval p q \ {p, q}).card =
        (configurationInterval c p q).card := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro z _
    rfl
  simp_rw [hi]
  exact hc

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun c : Multiset Spacetime => (c.card : ℝ))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) ∧
    Integrable (fun c : Multiset Spacetime => (c.card : ℝ) * ((c.card : ℝ) - 1))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) :=
  ⟨hH.poisson_integrable_card hρ, hH.poisson_integrable_pairCard hρ⟩

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (c.card : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
        {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
          spatialSeparationSq p 0 < (0 - p 0) ^ 2})) =
      ρ * volume.real {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
        spatialSeparationSq p 0 < (0 - p 0) ^ 2} :=
  hH.poisson_integral_card hρ

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (c.card : ℝ) * ((c.card : ℝ) - 1)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict
        {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
          spatialSeparationSq p 0 < (0 - p 0) ^ 2})) =
      (ρ * volume.real {p : Spacetime | -H (spatialPart p) < p 0 ∧ p 0 < 0 ∧
        spatialSeparationSq p 0 < (0 - p 0) ^ 2}) ^ 2 :=
  hH.poisson_integral_pairCard hρ

example {ρ : ℝ} (hρ : 0 < ρ) (c : Multiset Spacetime) :
    |discreteBDGAction ρ c| ≤ 4 / Real.sqrt (6 * ρ) *
      ((c.card : ℝ) + 16 * ((c.card : ℝ) * ((c.card : ℝ) - 1))) :=
  mixedNull_abs_discreteBDGAction_le hρ c

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun c => 4 / Real.sqrt (6 * ρ) *
      ((c.card : ℝ) - intervalLayer 0 c + 9 * intervalLayer 1 c -
        16 * intervalLayer 2 c + 8 * intervalLayer 3 c))
      (FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) := by
  rw [← mixedNull_bdgNormalization]
  exact hH.integrable_discrete_action hρ

-- Both endpoint factors, the true punctured closed interval, and k! are visible.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H,
        if q ∈ causalFuture p ∧ p ≠ q then
          Real.exp (-(ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})))) *
            (ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q}))) ^ k /
              k.factorial
        else 0 :=
  hH.poisson_integral_layer_restricted hρ k

-- No full partner region has been replaced by a source chart or future-tip interval.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    (∫ c : Multiset Spacetime, (intervalLayer k c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H,
        if q ∈ causalFuture p ∧ p ≠ q then
          Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
            ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ k / k.factorial
        else 0 :=
  hH.poisson_integral_layer_minkowski hρ k

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime =>
      if p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2 then
        Real.exp (-(ρ * volume.real
          (mixedNullRegion H ∩ (causalInterval p.1 p.2 \ {p.1, p.2})))) *
          (ρ * volume.real (mixedNullRegion H ∩ (causalInterval p.1 p.2 \ {p.1, p.2}))) ^ k /
            k.factorial
      else (0 : ℝ))
      ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H))) :=
  hH.poisson_integrable_layer_integrand hρ k

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ)
    (p q : Spacetime) :
    let f := if q ∈ causalFuture p ∧ p ≠ q then
      Real.exp (-(ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})))) *
        (ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q}))) ^ k /
          k.factorial else 0
    0 ≤ f ∧ f ≤ 1 :=
  hH.poisson_layer_integrand_bounds hρ k p q

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    Integrable (fun p : Spacetime × Spacetime =>
      if p.2 ∈ causalFuture p.1 ∧ p.1 ≠ p.2 then
        Real.exp (-((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2)) *
          ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2) ^ k / k.factorial
      else (0 : ℝ))
      ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H))) :=
  hH.poisson_integrable_minkowski_layer hρ k

-- The exact rate is calculated from the actual intensity; endpoint membership
-- and positive density are supplied, rather than an assumed rate identity.
example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    {p q : Spacetime} (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H)
    (hpq : p 0 ≤ q 0 ∧ spatialSeparationSq p q ≤ (q 0 - p 0) ^ 2) :
    ((ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))
      ({z | z ∈ causalFuture p ∧ q ∈ causalFuture z} \ {p, q})).toReal =
      (Real.pi / 24) * ρ * ((q 0 - p 0) ^ 2 - spatialSeparationSq p q) ^ 2 :=
  hH.poisson_intensity_interval_rate hρ hp hq hpq

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    {p q : Spacetime} (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H)
    (hpq : p 0 < q 0 ∧ spatialSeparationSq p q < (q 0 - p 0) ^ 2) :
    ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})) =
      (Real.pi / 24) * ρ * intervalSq p q ^ 2 :=
  hH.poisson_restricted_interval_rate hρ hp hq ⟨hpq.1.le, hpq.2.le⟩

example {p q : Spacetime} (hpq : (q 0 - p 0) ^ 2 - spatialSeparationSq p q = 0) :
    volume {z | z ∈ causalFuture p ∧ q ∈ causalFuture z} = 0 :=
  mixedNull_volume_nullInterval hpq

example : volume {p : Spacetime × Spacetime |
    (p.2 0 - p.1 0) ^ 2 - spatialSeparationSq p.1 p.2 = 0} = 0 :=
  mixedNull_volume_nullPairs

example : volume {p : Spacetime × Spacetime | p.1 = p.2} = 0 :=
  mixedNull_volume_diagonal

example (H : Spatial → ℝ) :
    ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H)))
      {p : Spacetime × Spacetime | intervalSq p.1 p.2 = 0} = 0 :=
  mixedNull_restricted_nullPairs H

-- Finite signed generating polynomial, with the actual factorials retained.
example (z : ℝ) :
    Real.exp (-z) * (1 - 9 * z + 16 * z ^ 2 / (2 : ℕ).factorial -
      8 * z ^ 3 / (3 : ℕ).factorial) =
      (1 - 9 * z + 8 * z ^ 2 - (4 / 3) * z ^ 3) * Real.exp (-z) := by
  norm_num [Nat.factorial]
  ring

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c, 4 / Real.sqrt (6 * ρ) *
      ((c.card : ℝ) - intervalLayer 0 c + 9 * intervalLayer 1 c -
        16 * intervalLayer 2 c + 8 * intervalLayer 3 c)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))) =
      4 / Real.sqrt (6 * ρ) * (ρ * volume.real (mixedNullRegion H) -
        ρ ^ 2 * ∫ p in mixedNullRegion H, ∫ q in mixedNullRegion H ∩ causalFuture p,
          (1 - 9 * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) +
            8 * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 2 -
            (4 / 3) * ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 3) *
              Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2))) := by
  simpa only [discreteBDGAction, mixedNull_bdgNormalization] using hH.poisson_integral_action hρ

-- A genuine nonaffine floor, with the source's amplitude, not a planar surrogate.
def sineFloor (x : Spatial) : ℝ := 1 + (1 / 5 : ℝ) * Real.sin (x 0)

theorem sineFloor_data : MixedNullData sineFloor :=
  mixedNull_sine_admissible.toMixedNullData

example : sineFloor ![Real.pi / 2, 0, 0] ≠
    (sineFloor ![0, 0, 0] + sineFloor ![Real.pi, 0, 0]) / 2 := by
  norm_num [sineFloor, Real.sin_pi_div_two, Real.sin_pi]

example {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (c.card : ℝ) * ((c.card : ℝ) - 1)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion sineFloor))) =
      (ρ * volume.real (mixedNullRegion sineFloor)) ^ 2 :=
  sineFloor_data.poisson_integral_pairCard hρ

-- Layer two has denominator 2, not 1; the cubic layer's denominator is 6.
example {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (intervalLayer 2 c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion sineFloor))) =
      ρ ^ 2 * ∫ p in mixedNullRegion sineFloor, ∫ q in mixedNullRegion sineFloor,
        if q ∈ causalFuture p ∧ p ≠ q then
          Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
            ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 2 / 2
        else 0 := by
  simpa only [Nat.factorial, Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one] using
    sineFloor_data.poisson_integral_layer_minkowski hρ 2

example {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ c : Multiset Spacetime, (intervalLayer 3 c : ℝ)
      ∂FinitePoisson.law (ENNReal.ofReal ρ • volume.restrict (mixedNullRegion sineFloor))) =
      ρ ^ 2 * ∫ p in mixedNullRegion sineFloor, ∫ q in mixedNullRegion sineFloor ∩ causalFuture p,
        Real.exp (-((Real.pi / 24) * ρ * intervalSq p q ^ 2)) *
          ((Real.pi / 24) * ρ * intervalSq p q ^ 2) ^ 3 / 6 := by
  simpa only [Nat.factorial, Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one] using
    sineFloor_data.poisson_integral_layer_future hρ 3

example {ρ : ℝ} (hρ : 0 < ρ) {p q : Spacetime}
    (hp : p ∈ mixedNullRegion sineFloor) (hq : q ∈ mixedNullRegion sineFloor)
    (hpq : q ∈ chronologicalFuture p) :
    ((ENNReal.ofReal ρ • volume.restrict (mixedNullRegion sineFloor))
      (causalInterval p q \ {p, q})).toReal =
      (Real.pi / 24) * ρ * intervalSq p q ^ 2 :=
  sineFloor_data.poisson_intensity_interval_rate hρ hp hq ⟨hpq.1.le, hpq.2.le⟩

-- Three null-collinear points strictly inside the constant-floor mixed region.
def nullChain : Multiset Spacetime :=
  (![-3 / 4, 0, 0, 0] : Spacetime) ::ₘ ![-5 / 8, 1 / 8, 0, 0] ::ₘ
    ![-1 / 2, 1 / 4, 0, 0] ::ₘ 0

private theorem planarEvent_eq_iff (t x s y : ℝ) :
    (![t, x, 0, 0] : Spacetime) = ![s, y, 0, 0] ↔ t = s ∧ x = y := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

example : ∀ p ∈ nullChain, p ∈ mixedNullRegion (fun _ => (1 : ℝ)) := by
  simp only [nullChain, Multiset.mem_cons, Multiset.not_mem_zero, or_false]
  intro p hp
  rcases hp with rfl | rfl | rfl <;>
    norm_num [mixedNullRegion, chronologicalFuture, spatialSeparationSq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three]

example : intervalLayer 0 nullChain = 2 ∧ intervalLayer 1 nullChain = 1 := by
  norm_num [intervalLayer, intervalPairSum_eq_sum, nullChain, causalFuture,
    spatialSeparationSq, Fin.sum_univ_three, intervalCount, FiniteConfiguration.count_cons,
    causalIntervalInterior, causalInterval, causalPast, planarEvent_eq_iff,
    Matrix.cons_val_two, Matrix.cons_val_three]

example (ρ : ℝ) :
    mixedNullMinkowskiLayerIntegrand ρ 0 ![-3 / 4, 0, 0, 0] ![-1 / 2, 1 / 4, 0, 0] = 1 := by
  norm_num [mixedNullMinkowskiLayerIntegrand, causalFuture, intervalSq, spatialSeparationSq,
    Fin.sum_univ_three, planarEvent_eq_iff, Matrix.cons_val_two, Matrix.cons_val_three]

example (ρ : ℝ) (p : Spacetime) : mixedNullMinkowskiLayerIntegrand ρ 0 p p = 0 := by
  simp [mixedNullMinkowskiLayerIntegrand]

example : volume (causalInterval (![-3 / 4, 0, 0, 0] : Spacetime)
    ![-1 / 2, 1 / 4, 0, 0]) = 0 := by
  apply mixedNull_volume_nullInterval
  norm_num [intervalSq, spatialSeparationSq, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.cons_val_three]

end MixedNullProbabilityRegression

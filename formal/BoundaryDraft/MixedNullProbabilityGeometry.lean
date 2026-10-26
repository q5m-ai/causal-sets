import BoundaryDraft.MixedNullProbability
import BoundaryDraft.DimensionIntervalCompatibility

/-!
# Original-coordinate interval volumes and null sets for MA14

The dimension-indexed theorems are transported through the actual
volume-preserving coordinate equivalence. Null and diagonal pairs remain in
the discrete order. The null-set conclusions here concern continuous product
volume only.
-/

open MeasureTheory Set
open scoped ENNReal Classical
noncomputable section
namespace BoundaryDraft

/-- Closed causal intervals in the original four coordinates, including null
and diagonal endpoints, have the usual Alexandrov volume. -/
theorem mixedNull_volume_causalInterval {p q : Spacetime} (hpq : q ∈ causalFuture p) :
    volume (causalInterval p q) =
      ENNReal.ofReal ((Real.pi / 24) * intervalSq p q ^ 2) := by
  obtain ⟨x, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective p
  obtain ⟨y, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective q
  rw [volume_oldCausalInterval_eq_dimension,
    volume_dimensionCausalInterval_four x y
      ((dimensionSpacetimeCoordinates_causal x y).mp hpq),
    dimensionSpacetimeCoordinates_intervalSq]

/-- A zero-phase interval itself has zero four-volume; this is not inferred
from the measure of the set of endpoint pairs. -/
theorem mixedNull_volume_nullInterval {p q : Spacetime} (hpq : intervalSq p q = 0) :
    volume (causalInterval p q) = 0 := by
  obtain ⟨x, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective p
  obtain ⟨y, rfl⟩ := (dimensionSpacetimeCoordinates 3).surjective q
  rw [dimensionSpacetimeCoordinates_intervalSq] at hpq
  rw [volume_oldCausalInterval_eq_dimension]
  exact volume_dimensionCausalInterval_null (by norm_num : 0 < 3) x y hpq

/-- All zero-phase endpoint pairs form a null set in original product volume. -/
theorem mixedNull_volume_nullPairs :
    volume {p : Spacetime × Spacetime | intervalSq p.1 p.2 = 0} = 0 := by
  let e := (dimensionSpacetimeCoordinates 3).prodCongr (dimensionSpacetimeCoordinates 3)
  have he : MeasurePreserving e := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact (dimensionSpacetimeCoordinates_measurePreserving 3).prod
      (dimensionSpacetimeCoordinates_measurePreserving 3)
  rw [← he.measure_preimage_emb e.measurableEmbedding]
  change volume {p : DimensionSpacetime 3 × DimensionSpacetime 3 |
    intervalSq (dimensionSpacetimeCoordinates 3 p.1)
      (dimensionSpacetimeCoordinates 3 p.2) = 0} = 0
  simp_rw [dimensionSpacetimeCoordinates_intervalSq]
  exact volume_dimensionNullPairs (by norm_num : 0 < 3)

/-- The original-coordinate diagonal is product-volume-null as well. -/
theorem mixedNull_volume_diagonal :
    volume {p : Spacetime × Spacetime | p.1 = p.2} = 0 := by
  let e := (dimensionSpacetimeCoordinates 3).prodCongr (dimensionSpacetimeCoordinates 3)
  have he : MeasurePreserving e := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact (dimensionSpacetimeCoordinates_measurePreserving 3).prod
      (dimensionSpacetimeCoordinates_measurePreserving 3)
  rw [← he.measure_preimage_emb e.measurableEmbedding]
  change volume {p : DimensionSpacetime 3 × DimensionSpacetime 3 |
    dimensionSpacetimeCoordinates 3 p.1 = dimensionSpacetimeCoordinates 3 p.2} = 0
  simpa only [(dimensionSpacetimeCoordinates 3).injective.eq_iff] using
    (volume_dimensionDiagonal (n := 3))

/-- In particular the full mixed partner product, not a chart, has no null
endpoint pairs in its continuous integration measure. -/
theorem mixedNull_restricted_nullPairs (H : Spatial → ℝ) :
    ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H)))
      {p : Spacetime × Spacetime | intervalSq p.1 p.2 = 0} = 0 := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq mixedNull_volume_nullPairs)
    (zero_le _)

theorem mixedNull_restricted_diagonal (H : Spatial → ℝ) :
    ((volume.restrict (mixedNullRegion H)).prod (volume.restrict (mixedNullRegion H)))
      {p : Spacetime × Spacetime | p.1 = p.2} = 0 := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq mixedNull_volume_diagonal)
    (zero_le _)

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Closed containment and removal of the marked endpoints identify the
actual restricted interval volume before any proper-time calculation. -/
theorem poisson_restricted_interval_volume {p q : Spacetime}
    (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H) :
    volume (mixedNullRegion H ∩ (causalInterval p q \ {p, q})) =
      volume (causalInterval p q) := by
  rw [inter_eq_right.mpr (fun _ hz => hH.causallyConvex p hp q hq hz.1)]
  exact volume_causalIntervalInterior p q

/-- The genuine restricted rate equals the original Minkowski rate for every
closed causal pair in the mixed region, not just almost every timelike pair. -/
theorem poisson_restricted_interval_rate {ρ : ℝ} (_hρ : 0 < ρ) {p q : Spacetime}
    (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H)
    (hpq : q ∈ causalFuture p) :
    ρ * volume.real (mixedNullRegion H ∩ (causalInterval p q \ {p, q})) =
      (Real.pi / 24) * ρ * intervalSq p q ^ 2 := by
  rw [measureReal_def, hH.poisson_restricted_interval_volume hp hq,
    mixedNull_volume_causalInterval hpq,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (sq_nonneg _))]
  ring

/-- The intensity measure itself, evaluated on the endpoint-excluded interval,
has exactly the same real rate. -/
theorem poisson_intensity_interval_rate {ρ : ℝ} (hρ : 0 < ρ) {p q : Spacetime}
    (hp : p ∈ mixedNullRegion H) (hq : q ∈ mixedNullRegion H)
    (hpq : q ∈ causalFuture p) :
    ((ENNReal.ofReal ρ • volume.restrict (mixedNullRegion H))
      (causalInterval p q \ {p, q})).toReal =
      (Real.pi / 24) * ρ * intervalSq p q ^ 2 := by
  change ((hH.boundedCausalRegion.sprinkling ρ hρ).intensity
    (causalIntervalInterior p q)).toReal = _
  rw [(hH.boundedCausalRegion.sprinkling ρ hρ).intensity_toReal
    (measurableSet_causalIntervalInterior p q), inter_comm]
  exact hH.poisson_restricted_interval_rate hρ hp hq hpq

omit hH in
/-- Null intervals have zero restricted volume, even without endpoint membership. -/
theorem poisson_restricted_null_interval {p q : Spacetime} (hpq : intervalSq p q = 0) :
    volume (mixedNullRegion H ∩ (causalInterval p q \ {p, q})) = 0 :=
  measure_mono_null (fun _ hz => hz.2.1) (mixedNull_volume_nullInterval hpq)

end MixedNullData
end BoundaryDraft

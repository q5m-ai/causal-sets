import BoundaryDraft.ExpectationBridge
import BoundaryDraft.NullBoundary

/-!
# Exact finite-density reduction for the one-tip mixed class

This ports MA5, MA6 and MA8 and the finite-density equalities of MA3 in
`notes/null-mixed-assembly.md`. The input is only a globally strictly
Euclidean-Lipschitz floor with positive height at the origin. Smoothness is
not needed for these results. No area formula or density limit is asserted.
The original action, causal order, kernel and Poisson law are unchanged.
-/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace BoundaryDraft

/-- The region above the floor and strictly below the future cone at zero. -/
def mixedNullRegion (H : Spatial → ℝ) : Set Spacetime :=
  {p | -H (spatialPart p) < p 0 ∧ (0 : Spacetime) ∈ chronologicalFuture p}

/-- Geometric assumptions only; the norm is Euclidean, not the coordinate sup norm. -/
structure MixedNullData (H : Spatial → ℝ) : Prop where
  tip_pos : 0 < H 0
  lipschitz : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ ∀ x y,
    |H x - H y| ≤ κ * spatialDistance x y

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem continuous : Continuous H := by
  obtain ⟨κ, hκ, _, hLip⟩ := hH.lipschitz
  have hl : LipschitzWith ⟨κ, hκ⟩ (fun x : EuclideanSpace ℝ (Fin 3) => H x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |H x - H y| ≤ κ * ‖x - y‖
    have he := hLip x y
    change |H x - H y| ≤ κ * ‖y - x‖ at he
    simpa only [norm_sub_rev] using he
  exact hl.continuous.comp (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ))

theorem isOpen_region : IsOpen (mixedNullRegion H) := by
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  have hp : IsOpen {p : Spacetime | (0 : Spacetime) ∈ chronologicalFuture p} := by
    exact (isOpen_lt (continuous_apply 0) continuous_const).inter
      (isOpen_lt
        (continuous_spatialSeparationSq.comp (continuous_id.prodMk continuous_const))
        ((continuous_const.sub (continuous_apply 0)).pow 2))
  exact (isOpen_lt (hH.continuous.comp hs).neg (continuous_apply 0)).inter hp

/-- MA5 includes null displacements and needs no differentiability. -/
theorem floor_future {p q : Spacetime}
    (hp : -H (spatialPart p) < p 0) (hpq : q ∈ causalFuture p) :
    -H (spatialPart q) < q 0 := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hH.lipschitz
  have hd := spatialDistance_le_of_causalFuture p q hpq
  have hnonneg := spatialDistance_nonneg (spatialPart p) (spatialPart q)
  have hdiff := (le_abs_self (H (spatialPart p) - H (spatialPart q))).trans
    (hLip (spatialPart p) (spatialPart q))
  have hmul : κ * spatialDistance (spatialPart p) (spatialPart q) ≤
      spatialDistance (spatialPart p) (spatialPart q) := by nlinarith
  linarith

/-- MA6: the entire future interval is retained, not a local cone approximation. -/
theorem complete_future (p : Spacetime) (hp : p ∈ mixedNullRegion H) :
    mixedNullRegion H ∩ causalFuture p = causalFuture p ∩ chronologicalPast 0 := by
  ext q
  constructor
  · intro hq
    exact ⟨hq.2, hq.1.2⟩
  · rintro ⟨hpq, hq⟩
    exact ⟨⟨hH.floor_future hp.1 hpq, hq⟩, hpq⟩

theorem causallyConvex : CausallyConvex (mixedNullRegion H) := by
  intro p hp q hq z hz
  exact ⟨hH.floor_future hp.1 hz.1, causal_chronologicalFuture_trans hz.2 hq.2⟩

/-- The spatial and temporal bounds are derived, not added to admissibility. -/
theorem isBounded_region : Bornology.IsBounded (mixedNullRegion H) := by
  obtain ⟨κ, hκ, hκ1, hLip⟩ := hH.lipschitz
  let B := H 0 / (1 - κ)
  have hden : 0 < 1 - κ := sub_pos.mpr hκ1
  have hB : 0 < B := div_pos hH.tip_pos hden
  have hBeq : (1 - κ) * B = H 0 := by dsimp [B]; field_simp
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin 4 => -B) (fun _ => B))).isBounded.subset
  intro p hp
  let r := spatialDistance (spatialPart p) 0
  have hr : 0 ≤ r := spatialDistance_nonneg _ _
  have htime : p 0 < 0 := hp.2.1
  have hrsq : r ^ 2 = spatialSeparationSq p 0 := by
    simp [r, spatialDistance_sq, spatialSeparationSq, spatialPart]
  have hrt : r < -p 0 := by
    apply (sq_lt_sq₀ hr (by linarith : 0 ≤ -p 0)).mp
    rw [hrsq]
    simpa using hp.2.2
  have hheight : H (spatialPart p) ≤ H 0 + κ * r := by
    have := (le_abs_self (H (spatialPart p) - H 0)).trans (hLip (spatialPart p) 0)
    change H (spatialPart p) - H 0 ≤ κ * r at this
    linarith
  have hrB : r < B := by nlinarith [hp.1]
  have htB : -B < p 0 := by nlinarith [hp.1]
  have hcoord (i : Fin 3) : |p i.succ| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs, hrsq]
    have hi := Finset.single_le_sum (fun j : Fin 3 => fun _ => sq_nonneg (p j.succ))
      (Finset.mem_univ i)
    simpa [spatialSeparationSq] using hi
  constructor <;> intro i
  · refine Fin.cases htB.le (fun j => ?_) i
    change -B ≤ p j.succ
    have := (abs_le.mp (hcoord j)).1
    linarith
  · refine Fin.cases (htime.le.trans hB.le) (fun j => ?_) i
    exact (abs_le.mp (hcoord j)).2.trans hrB.le

theorem boundedCausalRegion : BoundedCausalRegion (mixedNullRegion H) :=
  ⟨hH.isOpen_region.measurableSet, hH.isBounded_region, hH.causallyConvex⟩

/-- MA8: exact signed cancellation before the outer integration. -/
theorem future_kernel_identity {ρ : ℝ} (hρ : 0 < ρ) (p : Spacetime)
    (hp : p ∈ mixedNullRegion H) :
    ρ * (∫ q in mixedNullRegion H ∩ causalFuture p,
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) =
      1 - Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) := by
  rw [hH.complete_future p hp, integral_future_chronologicalPast_eq_causalInterval]
  exact causalInterval_kernel_identity ρ p 0 hρ hp.2

/-- The finite-density deterministic part of MA3; not its asymptotic assertion. -/
theorem continuumMean_eq_spacetimeGaussian {ρ : ℝ} (hρ : 0 < ρ) :
    continuumMean ρ (mixedNullRegion H) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) := by
  let M := mixedNullRegion H
  let E := fun p : Spacetime => Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2)
  let Q := fun p : Spacetime => ∫ q in M ∩ causalFuture p,
    bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)
  have hm : MeasurableSet M := hH.isOpen_region.measurableSet
  have hE : Continuous E := by
    have hs := continuous_intervalSq.comp (continuous_id.prodMk (continuous_const (y := (0 : Spacetime))))
    dsimp [E]
    fun_prop
  have hi1 : IntegrableOn (fun _ : Spacetime => (1 : ℝ)) M :=
    (continuous_const.continuousOn.integrableOn_compact hH.isBounded_region.isCompact_closure).mono_set subset_closure
  have hiE : IntegrableOn E M :=
    (hE.continuousOn.integrableOn_compact hH.isBounded_region.isCompact_closure).mono_set subset_closure
  have hinner : (∫ p in M, Q p) = ∫ p in M, (1 - E p) / ρ := by
    apply setIntegral_congr_fun hm
    intro p hp
    apply (eq_div_iff hρ.ne').mpr
    have hi := hH.future_kernel_identity hρ p hp
    dsimp only [Q, E, M]
    linarith
  have hrho : ρ * (∫ p in M, (1 - E p) / ρ) = ∫ p in M, 1 - E p := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro p _
    field_simp
  change continuumMean ρ M = (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in M, E p
  unfold continuumMean
  change (4 / Real.sqrt 6) * Real.sqrt ρ *
    ((∫ _p in M, (1 : ℝ)) - ρ * ∫ p in M, Q p) = _
  rw [hinner, hrho, integral_sub hi1 hiE]
  ring

/-- Separate original-law expectation transfer, with geometry discharged above. -/
theorem expectedBDGAction_eq {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (mixedNullRegion H) = continuumMean ρ (mixedNullRegion H) :=
  hH.boundedCausalRegion.expectedBDGAction_eq hρ

theorem expectedBDGAction_eq_spacetimeGaussian {ρ : ℝ} (hρ : 0 < ρ) :
    expectedBDGAction ρ (mixedNullRegion H) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) := by
  rw [hH.expectedBDGAction_eq hρ, hH.continuumMean_eq_spacetimeGaussian hρ]

end MixedNullData
end BoundaryDraft

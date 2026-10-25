import BoundaryDraft.MixedNullPartnerLedger
import BoundaryDraft.MixedNullGeometryExamples

/-! The NM11 ledger is expanded with its signed kernel, full partner domain,
point term once, signed source weight and an actual two-endpoint cutoff. -/
open BoundaryDraft MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace MixedNullPartnerLedgerRegression

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    {w : Spacetime → ℝ} (hw : Measurable w) {C : ℝ}
    (hb : ∀ p ∈ mixedNullRegion H, ‖w p‖ ≤ C)
    {χ : Spacetime → Spacetime → ℝ}
    (hχ : Measurable (fun p : Spacetime × Spacetime => χ p.1 p.2))
    (hχb : ∀ p ∈ mixedNullRegion H, ∀ q ∈ mixedNullRegion H ∩ causalFuture p,
      0 ≤ χ p q ∧ χ p q ≤ 1) :
    (4 / Real.sqrt 6) * Real.sqrt ρ *
      ((∫ p in mixedNullRegion H, w p) - ρ * ∫ p in mixedNullRegion H,
        ∫ q in mixedNullRegion H ∩ causalFuture p,
          w p * χ p q * bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) +
      (-(4 / Real.sqrt 6) * ρ * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        ∫ q in mixedNullRegion H ∩ causalFuture p,
          w p * (1 - χ p q) * bdgKernel ((Real.pi / 24) * ρ * intervalSq p q ^ 2)) =
      (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H,
        w p * Real.exp (-(Real.pi / 24) * ρ * intervalSq p 0 ^ 2) :=
  hH.cutoff_ledger_eq_gaussian hρ hw hb hχ hχb

/-- A genuinely pair-dependent sharp coordinate-distance cutoff. -/
def pairCutoff (ε : ℝ) (p q : Spacetime) : ℝ := if dist p q < ε then 1 else 0

theorem pairCutoff_measurable (ε : ℝ) :
    Measurable (fun p : Spacetime × Spacetime => pairCutoff ε p.1 p.2) :=
  measurable_const.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const

theorem pairCutoff_bounds (ε : ℝ) (p q : Spacetime) :
    0 ≤ pairCutoff ε p q ∧ pairCutoff ε p q ≤ 1 := by
  unfold pairCutoff
  split_ifs <;> norm_num

/-- Signed, discontinuous and time-dependent; no positivity is silently used. -/
def signedSource (p : Spacetime) : ℝ := if p 0 < -1 / 2 then -1 else 2

theorem signedSource_measurable : Measurable signedSource :=
  measurable_const.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const) measurable_const

theorem signedSource_bound (p : Spacetime) : ‖signedSource p‖ ≤ 2 := by
  unfold signedSource
  split_ifs <;> norm_num

example (ε ρ : ℝ) :
    mixedNullCutoffShort mixedNullSineFloor ρ signedSource (pairCutoff ε) +
      mixedNullCutoffLong mixedNullSineFloor ρ signedSource (pairCutoff ε) =
        weightedContinuumMean ρ (mixedNullRegion mixedNullSineFloor) signedSource :=
  mixedNull_sine_admissible.toMixedNullData.cutoff_ledger ρ signedSource_measurable
    (fun p _ => signedSource_bound p) (pairCutoff_measurable ε)
    (fun p _ q _ => pairCutoff_bounds ε p q)

example (ε ρ : ℝ) :
    IntegrableOn (fun p : Spacetime × Spacetime => signedSource p.1 * pairCutoff ε p.1 p.2 *
      bdgKernel ((Real.pi / 24) * ρ * intervalSq p.1 p.2 ^ 2))
      {p | p.1 ∈ mixedNullRegion mixedNullSineFloor ∧ p.2 ∈ mixedNullRegion mixedNullSineFloor ∧
        p.2 ∈ causalFuture p.1} := by
  apply mixedNull_sine_admissible.toMixedNullData.integrable_cutoff_bilocal ρ
    signedSource_measurable (fun p _ => signedSource_bound p) (pairCutoff_measurable ε)
    (D := 1)
  intro p _ q _
  rw [Real.norm_eq_abs, abs_of_nonneg (pairCutoff_bounds ε p q).1]
  exact (pairCutoff_bounds ε p q).2

example (H : Spatial → ℝ) (ρ : ℝ) (w : Spacetime → ℝ) :
    mixedNullCutoffLong H ρ w (fun _ _ => 1) = 0 ∧
      mixedNullCutoffShort H ρ w (fun _ _ => 0) =
        (4 / Real.sqrt 6) * Real.sqrt ρ * ∫ p in mixedNullRegion H, w p :=
  ⟨mixedNullCutoffLong_one H ρ w, mixedNullCutoffShort_zero H ρ w⟩

example {H : Spatial → ℝ} (hH : MixedNullData H) {ρ : ℝ} (hρ : 0 < ρ)
    (s : Finset ℕ) (w : ℕ → Spacetime → ℝ) (C : ℕ → ℝ) (ε : ℕ → ℝ)
    (hw : ∀ i ∈ s, Measurable (w i))
    (hb : ∀ i ∈ s, ∀ p ∈ mixedNullRegion H, ‖w i p‖ ≤ C i)
    (hs : ∀ p ∈ mixedNullRegion H, ∑ i ∈ s, w i p = 1) :
    (∑ i ∈ s, (mixedNullCutoffShort H ρ (w i) (pairCutoff (ε i)) +
      mixedNullCutoffLong H ρ (w i) (pairCutoff (ε i)))) = continuumMean ρ (mixedNullRegion H) :=
  hH.cutoff_ledger_partition s hρ w C (fun i => pairCutoff (ε i)) hw hb
    (fun i _ => pairCutoff_measurable (ε i))
    (fun i _ p _ q _ => pairCutoff_bounds (ε i) p q) hs

end MixedNullPartnerLedgerRegression

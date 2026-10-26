import BoundaryDraft.MixedNullGenerator

/-!
# The complete generator ledger under affine and nonaffine coordinates

Both the response Jacobian and the derivative term are transported, including
both endpoints of an arbitrary subinterval. The mixed-region corollaries
specialize the actual radius at the joint. Coordinate changes need only be C1
along each generator; no angular smoothness is imposed. Sphere statements are
iterated integral identities, not claims of a jointly measurable product
coordinate transformation for arbitrary angular parameter dependence.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
namespace BoundaryDraft

/-- Transport of the full response measure: `2 r dr` becomes `2 f f' da`.
This oriented-interval form also retains nonzero artificial lower endpoints. -/
theorem mixedNull_generator_response_transport {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hφ : Continuous φ) (a b : ℝ) :
    (∫ r in f a..f b, 2 * r * φ r) =
      ∫ s in a..b, 2 * f s * deriv f s * φ (f s) := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b)
    (g := fun r => 2 * r * φ r)
    (fun s _ => (hf.differentiable le_rfl s).hasDerivAt)
    (hf.continuous_deriv le_rfl).continuousOn
    ((continuous_const.mul continuous_id).mul hφ)
  calc
    _ = ∫ s in a..b, (2 * f s * φ (f s)) * deriv f s := h.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      ring

/-- The transported derivative includes the pullback Jacobian. -/
theorem mixedNull_generator_deriv_comp {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    deriv (fun a => φ (f a)) s = deriv φ (f s) * deriv f s :=
  ((hφ.differentiable le_rfl (f s)).hasDerivAt.comp s
    (hf.differentiable le_rfl s).hasDerivAt).deriv

/-- Transport of the correction is not just transport of the joint value. -/
theorem mixedNull_generator_correction_transport {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (a b : ℝ) :
    (∫ r in f a..f b, r ^ 2 * deriv φ r) =
      ∫ s in a..b, f s ^ 2 * deriv (fun a => φ (f a)) s := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := a) (b := b)
    (g := fun r => r ^ 2 * deriv φ r)
    (fun s _ => (hf.differentiable le_rfl s).hasDerivAt)
    (hf.continuous_deriv le_rfl).continuousOn
    ((continuous_id.pow 2).mul (hφ.continuous_deriv le_rfl))
  calc
    _ = ∫ s in a..b, (f s ^ 2 * deriv φ (f s)) * deriv f s := h.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [mixedNull_generator_deriv_comp hf hφ]
      ring

/-- The full signed interval ledger retains both artificial boundaries. -/
theorem mixedNull_generator_interval_ledger {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (a b : ℝ) :
    (∫ r in a..b, 2 * r * φ r) = b ^ 2 * φ b - a ^ 2 * φ a -
      ∫ r in a..b, r ^ 2 * deriv φ r := by
  have h1 : IntervalIntegrable (fun r => 2 * r * φ r) volume a b :=
    ((continuous_const.mul continuous_id).mul hφ.continuous).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun r => r ^ 2 * deriv φ r) volume a b :=
    ((continuous_id.pow 2).mul (hφ.continuous_deriv le_rfl)).intervalIntegrable a b
  have hd (r : ℝ) : HasDerivAt (fun r => r ^ 2 * φ r)
      (2 * r * φ r + r ^ 2 * deriv φ r) r := by
    convert ((hasDerivAt_id r).pow 2).mul (hφ.differentiable le_rfl r).hasDerivAt using 1
    simp only [id_eq, Nat.cast_ofNat, pow_one, mul_one]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) (h1.add h2)
  rw [intervalIntegral.integral_add h1 h2] at h
  linarith

/-- Artificial radial endpoint terms cancel exactly after the two neighboring
interval ledgers are summed; neither correction integral is discarded. -/
theorem mixedNull_generator_cut_ledger {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (a b c : ℝ) :
    (b ^ 2 * φ b - a ^ 2 * φ a - ∫ r in a..b, r ^ 2 * deriv φ r) +
      (c ^ 2 * φ c - b ^ 2 * φ b - ∫ r in b..c, r ^ 2 * deriv φ r) =
      c ^ 2 * φ c - a ^ 2 * φ a - ∫ r in a..c, r ^ 2 * deriv φ r := by
  have hc : Continuous (fun r : ℝ => r ^ 2 * deriv φ r) :=
    (continuous_id.pow 2).mul (hφ.continuous_deriv le_rfl)
  have hi : (∫ r in a..b, r ^ 2 * deriv φ r) + (∫ r in b..c, r ^ 2 * deriv φ r) =
      ∫ r in a..c, r ^ 2 * deriv φ r :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a b) (hc.intervalIntegrable b c)
  rw [← hi]
  ring

/-- Invariance of all three terms together, not just `f(b)^2`. This theorem
applies in particular to every increasing C1 change of generator coordinate. -/
theorem mixedNull_generator_reparameterized_ledger {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hφ : ContDiff ℝ 1 φ) (a b : ℝ) :
    (∫ s in a..b, 2 * f s * deriv f s * φ (f s)) =
      f b ^ 2 * φ (f b) - f a ^ 2 * φ (f a) -
        ∫ s in a..b, f s ^ 2 * deriv (fun a => φ (f a)) s := by
  rw [← mixedNull_generator_response_transport hf hφ.continuous,
    ← mixedNull_generator_correction_transport hf hφ]
  exact mixedNull_generator_interval_ledger hφ _ _

/-- Affine normal marking corresponds to the derivative of the actual
spacetime generator, with its past-directed sign explicit. -/
theorem mixedNull_generator_affine_marking (u : MixedNullDirection) (α a : ℝ) :
    HasDerivAt (fun s => mixedNullGeneratorPoint u (α * s))
      (-(α • (Fin.cons 1 (-u.val) : Spacetime))) a := by
  have ha : HasDerivAt (fun s : ℝ => α * s) α a := by
    simpa using (hasDerivAt_id a).const_mul α
  have h := (hasDerivAt_mixedNullGeneratorPoint u (α * a)).scomp a ha
  convert h using 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [smul_eq_mul]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

/-- Transport of the actual zero-endpoint response, keeping the complete
pullback Jacobian and the actual upper coordinate endpoint. -/
theorem weightedGlobalWeight_response_reparameterized {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (f : MixedNullDirection → ℝ → ℝ) (A : MixedNullDirection → ℝ)
    (hf : ∀ u, ContDiff ℝ 1 (f u)) (hf0 : ∀ u, f u 0 = 0)
    (hfA : ∀ u, f u (A u) = mixedNullRadius H u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..A u,
        2 * f u a * deriv (f u) a * w (mixedNullGeneratorPoint u (f u a)))
        ∂(volume : Measure JointSpace).toSphere := by
  rw [hH.weightedGlobalWeight_generator_response hw.continuous.measurable hb]
  apply integral_congr_ae
  filter_upwards [] with u
  simpa only [hf0, hfA, mixedNullGeneratorTrace] using
    mixedNull_generator_response_transport (hf u) (contDiff_mixedNullGeneratorTrace hw u).continuous
      0 (A u)

/-- Integrability of the whole transformed response is inherited through the
proved radial change of variables, with no angular smoothness premise. -/
theorem integrable_generator_reparameterized_response {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) (f : MixedNullDirection → ℝ → ℝ) (A : MixedNullDirection → ℝ)
    (hf : ∀ u, ContDiff ℝ 1 (f u)) (hf0 : ∀ u, f u 0 = 0)
    (hfA : ∀ u, f u (A u) = mixedNullRadius H u) :
    Integrable (fun u : MixedNullDirection => ∫ a in (0 : ℝ)..A u,
      2 * f u a * deriv (f u) a * w (mixedNullGeneratorPoint u (f u a)))
        (volume : Measure JointSpace).toSphere := by
  apply (hH.integrable_generator_response hw).congr
  filter_upwards [] with u
  simpa only [hf0, hfA, mixedNullGeneratorTrace] using
    mixedNull_generator_response_transport (hf u) (contDiff_mixedNullGeneratorTrace hw u).continuous
      0 (A u)

/-- The transported correction's iterated angular integral is absolutely
integrable. This follows from equality with the original correction, without
angular differentiability assumptions on the coordinate changes. -/
theorem integrable_generator_reparameterized_correction {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) (f : MixedNullDirection → ℝ → ℝ) (A : MixedNullDirection → ℝ)
    (hf : ∀ u, ContDiff ℝ 1 (f u)) (hf0 : ∀ u, f u 0 = 0)
    (hfA : ∀ u, f u (A u) = mixedNullRadius H u) :
    Integrable (fun u : MixedNullDirection => ∫ a in (0 : ℝ)..A u,
      f u a ^ 2 * deriv (fun s => w (mixedNullGeneratorPoint u (f u s))) a)
        (volume : Measure JointSpace).toSphere := by
  apply (hH.integrable_generator_correction hw).congr
  filter_upwards [] with u
  have hd (r : ℝ) : deriv (mixedNullGeneratorTrace w u) r = mixedNullGeneratorDerivative w u r :=
    (hasDerivAt_mixedNullGeneratorTrace u r (hw.differentiable le_rfl _)).deriv
  simpa only [hf0, hfA, hd, mixedNullGeneratorTrace] using
    mixedNull_generator_correction_transport (hf u) (contDiff_mixedNullGeneratorTrace hw u) 0 (A u)

/-- NM8 under a nonaffine increasing C1 radial reparameterization. The actual
endpoint is positive, the joint term is transported, and the indispensable
correction retains the total derivative of the pulled-back trace. -/
theorem weightedGlobalWeight_generator_reparameterized {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (f : MixedNullDirection → ℝ → ℝ) (A : MixedNullDirection → ℝ)
    (hf : ∀ u, ContDiff ℝ 1 (f u)) (hmono : ∀ u, StrictMono (f u))
    (hf0 : ∀ u, f u 0 = 0) (hfA : ∀ u, f u (A u) = mixedNullRadius H u) :
    (∀ u, 0 < A u) ∧
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, f u (A u) ^ 2 * w (mixedNullGeneratorPoint u (f u (A u)))
        ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..A u,
        f u a ^ 2 * deriv (fun s => w (mixedNullGeneratorPoint u (f u s))) a)
        ∂(volume : Measure JointSpace).toSphere := by
  constructor
  · intro u
    apply (hmono u).lt_iff_lt.mp
    rw [hf0, hfA]
    exact hH.radius_pos u
  · rw [hH.weightedGlobalWeight_generator_C1 hw hb]
    congr 1
    · apply integral_congr_ae
      filter_upwards [] with u
      rw [hfA]
      rfl
    · apply integral_congr_ae
      filter_upwards [] with u
      have hd (r : ℝ) : deriv (mixedNullGeneratorTrace w u) r = mixedNullGeneratorDerivative w u r :=
        (hasDerivAt_mixedNullGeneratorTrace u r (hw.differentiable le_rfl _)).deriv
      simpa only [hf0, hfA, hd, mixedNullGeneratorTrace, mixedNullGeneratorDerivative] using
        mixedNull_generator_correction_transport (hf u) (contDiff_mixedNullGeneratorTrace hw u) 0 (A u)

/-- Affine marking, with the actual endpoint `R/α` and both powers of α in
the response measure. α may vary with direction without angular smoothness. -/
theorem weightedGlobalWeight_response_affine {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (α : MixedNullDirection → ℝ) (hα : ∀ u, 0 < α u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..(mixedNullRadius H u / α u),
        2 * α u ^ 2 * a * w (mixedNullGeneratorPoint u (α u * a)))
        ∂(volume : Measure JointSpace).toSphere := by
  have he := hH.weightedGlobalWeight_response_reparameterized hw hb
    (fun u a => α u * a) (fun u => mixedNullRadius H u / α u)
    (fun _ => contDiff_const.mul contDiff_id) (fun _ => mul_zero _)
    (fun u => mul_div_cancel₀ _ (hα u).ne')
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with u
  apply intervalIntegral.integral_congr
  intro a _
  dsimp only
  rw [show deriv (fun s => α u * s) a = α u by simpa using ((hasDerivAt_id a).const_mul (α u)).deriv]
  ring

/-- Affine NM8 transports the derivative term as well as the joint endpoint. -/
theorem weightedGlobalWeight_generator_affine {w : Spacetime → ℝ}
    (hw : ContDiff ℝ 1 w) {C : ℝ} (hb : ∀ p, ‖w p‖ ≤ C)
    (α : MixedNullDirection → ℝ) (hα : ∀ u, 0 < α u) :
    4 * mixedNullWeightedGlobalWeight H w 0 =
      (∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * w (mixedNullJointParam H u)
        ∂(volume : Measure JointSpace).toSphere) -
      ∫ u : MixedNullDirection, (∫ a in (0 : ℝ)..(mixedNullRadius H u / α u),
        α u ^ 2 * a ^ 2 * deriv (fun s => w (mixedNullGeneratorPoint u (α u * s))) a)
        ∂(volume : Measure JointSpace).toSphere := by
  have he := (hH.weightedGlobalWeight_generator_reparameterized hw hb
    (fun u a => α u * a) (fun u => mixedNullRadius H u / α u)
    (fun _ => contDiff_const.mul contDiff_id)
    (fun u _ _ hab => mul_lt_mul_of_pos_left hab (hα u))
    (fun _ => mul_zero _) (fun u => mul_div_cancel₀ _ (hα u).ne')).2
  have hcancel (u : MixedNullDirection) : α u * (mixedNullRadius H u / α u) = mixedNullRadius H u :=
    mul_div_cancel₀ _ (hα u).ne'
  simpa only [hcancel, mul_pow, mixedNullGeneratorPoint, mixedNullJointParam] using he

end MixedNullData
end BoundaryDraft

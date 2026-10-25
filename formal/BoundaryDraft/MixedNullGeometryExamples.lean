import BoundaryDraft.MixedNullSurface
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Nonvacuity and normalization controls for the mixed geometry producer -/
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace BoundaryDraft

 theorem mixedNull_constant_admissible {T : ℝ} (hT : 0 < T) :
    AdmissibleMixedNull (fun _ : Spatial => T) where
  tip_pos := hT
  lipschitz := ⟨0, le_rfl, by norm_num, by intro x y; simp⟩
  smooth_floor := contDiff_const

 theorem mixedNullRadius_constant {T : ℝ} (hT : 0 < T) (u : MixedNullDirection) :
    mixedNullRadius (fun _ : Spatial => T) u = T :=
  ((mixedNull_constant_admissible hT).toMixedNullData.radius_unique u rfl).symm

/-- The cone cap has area `4πT²`, not the diamond's `πT²`. -/
 theorem mixedNullArea_constant {T : ℝ} (hT : 0 < T) :
    mixedNullArea (fun _ : Spatial => T) = 4 * Real.pi * T ^ 2 := by
  unfold mixedNullArea
  simp_rw [mixedNullRadius_constant hT]
  rw [integral_const, smul_eq_mul, jointSphere_area]

/-- A genuine affine member may take negative values far outside its domain. -/
def mixedNullAffineFloor (a T : ℝ) (x : Spatial) : ℝ := T + a * x 0

 theorem mixedNull_affine_admissible {a T : ℝ} (hT : 0 < T) (ha : |a| < 1) :
    AdmissibleMixedNull (mixedNullAffineFloor a T) where
  tip_pos := by simpa [mixedNullAffineFloor] using hT
  lipschitz := by
    refine ⟨|a|, abs_nonneg a, ha, fun x y => ?_⟩
    have hd : |x 0 - y 0| ≤ spatialDistance x y := by
      have he := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (y - x)) (0 : Fin 3)
      change ‖y 0 - x 0‖ ≤ spatialDistance x y at he
      simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    calc
      |mixedNullAffineFloor a T x - mixedNullAffineFloor a T y| = |a| * |x 0 - y 0| := by
        simp only [mixedNullAffineFloor, add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (abs_nonneg a)
  smooth_floor := contDiff_const.add (contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff)

 theorem mixedNullRadius_affine {a T : ℝ} (hT : 0 < T) (ha : |a| < 1)
    (u : MixedNullDirection) :
    mixedNullRadius (mixedNullAffineFloor a T) u = T / (1 - a * u.val 0) := by
  have hu : |u.val 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs, mixedNullDirection_norm] using PiLp.norm_apply_le u.val (0 : Fin 3)
  have hden : 0 < 1 - a * u.val 0 := by
    have hb : a * u.val 0 ≤ |a| := calc
      _ ≤ |a * u.val 0| := le_abs_self _
      _ = |a| * |u.val 0| := abs_mul _ _
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left hu (abs_nonneg a)
      _ = |a| := mul_one _
    linarith
  apply Eq.symm
  apply (mixedNull_affine_admissible hT ha).toMixedNullData.radius_unique u
  change T / (1 - a * u.val 0) = T + a * (T / (1 - a * u.val 0) * u.val 0)
  field_simp [hden.ne']
  ring

/-- The admitted geometry is genuinely non-round: two exact unequal radii. -/
 theorem mixedNull_affine_radius_nonconstant :
    ∃ u v : MixedNullDirection,
      mixedNullRadius (mixedNullAffineFloor (1 / 2) 1) u = 2 ∧
      mixedNullRadius (mixedNullAffineFloor (1 / 2) 1) v = 2 / 3 := by
  let u : MixedNullDirection := ⟨EuclideanSpace.single 0 1, by
    simp only [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]⟩
  let v : MixedNullDirection := ⟨EuclideanSpace.single 0 (-1), by
    simp only [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_neg, norm_one]⟩
  have ha : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num
  refine ⟨u, v, ?_, ?_⟩ <;>
    rw [mixedNullRadius_affine (a := (1 / 2 : ℝ)) (T := 1) (by norm_num) ha] <;>
    norm_num [u, v]

 theorem mixedNull_affine_exterior_negative :
    mixedNullAffineFloor (1 / 2) 1 ![-4, 0, 0] < 0 := by
  norm_num [mixedNullAffineFloor]

 def mixedNullSineFloor (x : Spatial) : ℝ := 1 + (1 / 5 : ℝ) * Real.sin (x 0)

 theorem mixedNull_sine_admissible : AdmissibleMixedNull mixedNullSineFloor where
  tip_pos := by norm_num [mixedNullSineFloor]
  lipschitz := by
    have hl : LipschitzWith 1 Real.sin :=
      lipschitzWith_of_nnnorm_deriv_le Real.differentiable_sin (by
        intro x
        change ‖deriv Real.sin x‖ ≤ (1 : ℝ)
        rw [Real.deriv_sin, Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
    refine ⟨1 / 5, by norm_num, by norm_num, fun x y => ?_⟩
    have hd : |x 0 - y 0| ≤ spatialDistance x y := by
      have he := PiLp.norm_apply_le ((WithLp.equiv 2 _).symm (y - x)) (0 : Fin 3)
      change ‖y 0 - x 0‖ ≤ spatialDistance x y at he
      simpa only [Real.norm_eq_abs, abs_sub_comm] using he
    have hs : |Real.sin (x 0) - Real.sin (y 0)| ≤ |x 0 - y 0| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul (x 0) (y 0)
    calc
      |mixedNullSineFloor x - mixedNullSineFloor y| =
          (1 / 5 : ℝ) * |Real.sin (x 0) - Real.sin (y 0)| := by
        simp only [mixedNullSineFloor, add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.trans hd) (by norm_num)
  smooth_floor := contDiff_const.add (contDiff_const.mul
    (Real.contDiff_sin.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff))

/-- An explicit failed affine midpoint identity prevents a planar-only reading. -/
 theorem mixedNull_sine_nonplanar :
    mixedNullSineFloor ![Real.pi / 2, 0, 0] ≠
      (mixedNullSineFloor ![0, 0, 0] + mixedNullSineFloor ![Real.pi, 0, 0]) / 2 := by
  norm_num [mixedNullSineFloor, Real.sin_pi_div_two, Real.sin_pi]

end BoundaryDraft

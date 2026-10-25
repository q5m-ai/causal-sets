import BoundaryDraft.MixedNullGeometrySmooth
import BoundaryDraft.MixedNullGeometryPolar

/-!
# Parametric induced Lorentzian area of the actual one-tip mixed joint

The shared measure is justified by the differential of a smooth extension of
the actual global parameterization. Its positive Gram Jacobian is exactly the
shared radius squared. This is parametric induced area, as in
`EllipsoidSurface`; no canonical Hausdorff identification is asserted here.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section
namespace BoundaryDraft

/-- Ambient extension of the cone parameterization for a scalar radial function. -/
def mixedNullParamExtension (f : JointSpace → ℝ) (x : JointSpace) : Spacetime :=
  Fin.cons (-f x) (f x • x : JointSpace)

/-- The linear map obtained by differentiating the actual parameterization. -/
def mixedNullParamDifferential (R : ℝ) (u : JointSpace) (d : JointSpace →L[ℝ] ℝ) :
    JointSpace →L[ℝ] Spacetime :=
  LinearMap.toContinuousLinearMap
  { toFun := fun v => Fin.cons (-d v) (d v • u + R • v : JointSpace)
    map_add' := by
      intro v w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp <;> ring
    map_smul' := by
      intro c v
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp; ring }

 theorem hasFDerivAt_mixedNullParamExtension {f : JointSpace → ℝ} {u : JointSpace}
    {d : JointSpace →L[ℝ] ℝ} (hf : HasFDerivAt f d u) :
    HasFDerivAt (mixedNullParamExtension f) (mixedNullParamDifferential (f u) u d) u := by
  apply hasFDerivAt_pi'.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf.neg
  · have hd := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt).comp u (hf.smul (hasFDerivAt_id u))
    convert hd using 1
    apply ContinuousLinearMap.ext
    intro v
    change d v * u j + f u * v j = f u * v j + d v * u j
    ring

 theorem contDiffAt_mixedNullParamExtension {f : JointSpace → ℝ} {u : JointSpace}
    (hf : ContDiffAt ℝ ⊤ f u) : ContDiffAt ℝ ⊤ (mixedNullParamExtension f) u := by
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf.neg
  · exact hf.mul (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt

 theorem minkowskiInner_cons_euclidean (t s : ℝ) (x y : JointSpace) :
    minkowskiInner (Fin.cons t (x : Spatial)) (Fin.cons s (y : Spatial)) =
      t * s - inner (𝕜 := ℝ) x y := by
  simp [minkowskiInner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Every parameter point has a genuine two-dimensional unit tangent frame. -/
 theorem mixedNullDirection_tangent_frame (u : MixedNullDirection) :
    ∃ v w : JointSpace, inner (𝕜 := ℝ) (u : JointSpace) v = 0 ∧
      inner (𝕜 := ℝ) (u : JointSpace) w = 0 ∧
      ‖v‖ = 1 ∧ ‖w‖ = 1 ∧ inner (𝕜 := ℝ) v w = 0 := by
  have hu : (u : JointSpace) ≠ 0 := by
    intro hz
    have hn := mixedNullDirection_norm u
    rw [hz, norm_zero] at hn
    norm_num at hn
  letI : Fact (Module.finrank ℝ JointSpace = 2 + 1) := ⟨by simp [JointSpace]⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 hu
  exact ⟨b 0, b 1,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 1).property,
    b.orthonormal.1 0, b.orthonormal.1 1, b.orthonormal.inner_eq_zero (by decide)⟩

/-- Radial derivative products really cancel in the negative Lorentz metric. -/
 theorem mixedNullParamDifferential_metric (R : ℝ) (u : MixedNullDirection)
    (d : JointSpace →L[ℝ] ℝ) (v w : JointSpace)
    (hv : inner (𝕜 := ℝ) (u : JointSpace) v = 0)
    (hw : inner (𝕜 := ℝ) (u : JointSpace) w = 0) :
    -minkowskiInner (mixedNullParamDifferential R u d v)
      (mixedNullParamDifferential R u d w) = R ^ 2 * inner (𝕜 := ℝ) v w := by
  change -minkowskiInner (Fin.cons (-d v) (d v • (u : JointSpace) + R • v : JointSpace))
    (Fin.cons (-d w) (d w • (u : JointSpace) + R • w : JointSpace)) = _
  rw [minkowskiInner_cons_euclidean]
  have huv : inner (𝕜 := ℝ) v (u : JointSpace) = 0 := by rw [real_inner_comm, hv]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hv, hw, huv, real_inner_self_eq_norm_sq, mixedNullDirection_norm, one_pow, mul_zero,
    add_zero, zero_add]
  ring

namespace AdmissibleMixedNull
variable {H : Spatial → ℝ} (hH : AdmissibleMixedNull H)
include hH

/-- A smooth ambient extension of the actual joint parameterization, with its
actual differential and induced tangent metric. No tangent identity is input. -/
 theorem jointParam_smooth_metric (u : MixedNullDirection) :
    ∃ Ψ : JointSpace → Spacetime,
      ContDiffAt ℝ ⊤ Ψ (u : JointSpace) ∧
      Ψ u = mixedNullJointParam H u ∧
      (∀ᶠ v : MixedNullDirection in 𝓝 u, Ψ v = mixedNullJointParam H v) ∧
      ∀ v w : JointSpace,
        inner (𝕜 := ℝ) (u : JointSpace) v = 0 →
        inner (𝕜 := ℝ) (u : JointSpace) w = 0 →
        -minkowskiInner (fderiv ℝ Ψ (u : JointSpace) v) (fderiv ℝ Ψ (u : JointSpace) w) =
          mixedNullRadius H u ^ 2 * inner (𝕜 := ℝ) v w := by
  obtain ⟨f, hf, he, _, hagree⟩ := hH.exists_smooth_radius_extension u
  refine ⟨mixedNullParamExtension f, contDiffAt_mixedNullParamExtension hf, ?_, ?_, ?_⟩
  · simp only [mixedNullParamExtension, mixedNullJointParam, he]
  · filter_upwards [hagree] with v hv
    simp only [mixedNullParamExtension, mixedNullJointParam, hv]
  · intro v w hv hw
    rw [(hasFDerivAt_mixedNullParamExtension (hf.differentiableAt (by simp)).hasFDerivAt).fderiv, he]
    exact mixedNullParamDifferential_metric _ u _ v w hv hw

/-- The squared radius is the positive square root of the actual induced
Gram determinant on every orthonormal tangent frame. -/
 theorem jointParam_induced_area (u : MixedNullDirection) :
    ∃ Ψ : JointSpace → Spacetime,
      ContDiffAt ℝ ⊤ Ψ (u : JointSpace) ∧
      Ψ u = mixedNullJointParam H u ∧
      (∀ᶠ v : MixedNullDirection in 𝓝 u, Ψ v = mixedNullJointParam H v) ∧
      (∀ v : JointSpace, inner (𝕜 := ℝ) (u : JointSpace) v = 0 → v ≠ 0 →
        0 < -minkowskiInner (fderiv ℝ Ψ (u : JointSpace) v) (fderiv ℝ Ψ (u : JointSpace) v)) ∧
      ∀ v w : JointSpace,
        inner (𝕜 := ℝ) (u : JointSpace) v = 0 →
        inner (𝕜 := ℝ) (u : JointSpace) w = 0 →
        ‖v‖ = 1 → ‖w‖ = 1 → inner (𝕜 := ℝ) v w = 0 →
        mixedNullRadius H u ^ 2 = Real.sqrt
          ((-minkowskiInner (fderiv ℝ Ψ (u : JointSpace) v) (fderiv ℝ Ψ (u : JointSpace) v)) *
           (-minkowskiInner (fderiv ℝ Ψ (u : JointSpace) w) (fderiv ℝ Ψ (u : JointSpace) w)) -
           (-minkowskiInner (fderiv ℝ Ψ (u : JointSpace) v) (fderiv ℝ Ψ (u : JointSpace) w)) ^ 2) := by
  obtain ⟨Ψ, hΨ, he, ha, hm⟩ := hH.jointParam_smooth_metric u
  refine ⟨Ψ, hΨ, he, ha, ?_, ?_⟩
  · intro v hv hv0
    rw [hm v v hv hv, real_inner_self_eq_norm_sq]
    exact mul_pos (sq_pos_of_pos (hH.toMixedNullData.radius_pos u)) (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  · intro v w hv hw hv1 hw1 hvw
    rw [hm v v hv hv, hm w w hw hw, hm v w hv hw, hvw,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv1, hw1]
    simp only [one_pow, mul_one, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    rw [← pow_two, Real.sqrt_sq (sq_nonneg _)]

end AdmissibleMixedNull

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

 theorem jointMeasure_univ : mixedNullJointMeasure H univ = ENNReal.ofReal (mixedNullArea H) := by
  rw [mixedNullJointMeasure, Measure.map_apply hH.continuous_jointParam.measurable MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hH.integrable_radius_sq
    (Eventually.of_forall fun _ => sq_nonneg _)).symm

 theorem finite_jointMeasure : IsFiniteMeasure (mixedNullJointMeasure H) := by
  constructor
  rw [hH.jointMeasure_univ]
  exact ENNReal.ofReal_lt_top

 theorem jointMeasure_pos : 0 < mixedNullJointMeasure H univ := by
  rw [hH.jointMeasure_univ]
  exact ENNReal.ofReal_pos.mpr hH.area_pos

 theorem integral_jointMeasure (f : Spacetime → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂mixedNullJointMeasure H) =
      ∫ u : MixedNullDirection, mixedNullRadius H u ^ 2 * f (mixedNullJointParam H u)
        ∂(volume : Measure JointSpace).toSphere := by
  rw [mixedNullJointMeasure, integral_map hH.continuous_jointParam.measurable.aemeasurable
    hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (hH.continuous_radius.pow 2).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    rw [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

 theorem jointMeasure_real_univ : (mixedNullJointMeasure H).real univ = mixedNullArea H := by
  rw [Measure.real, hH.jointMeasure_univ, ENNReal.toReal_ofReal hH.area_pos.le]

 theorem jointMeasure_supported : mixedNullJointMeasure H (mixedNullJoint H)ᶜ = 0 := by
  rw [mixedNullJointMeasure, Measure.map_apply hH.continuous_jointParam.measurable
    hH.isCompact_joint.isClosed.measurableSet.compl]
  have he : mixedNullJointParam H ⁻¹' (mixedNullJoint H)ᶜ = ∅ := by
    ext u
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not.mpr (hH.jointParam_mem u)
  rw [he, measure_empty]

 theorem spatialLimit_eq_jointMeasure : mixedNullSpatialLimit H = (mixedNullJointMeasure H).real univ := by
  rw [hH.spatialLimit_eq_area, hH.jointMeasure_real_univ]

end MixedNullData
end BoundaryDraft

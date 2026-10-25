import BoundaryDraft.MixedNullContract
import BoundaryDraft.EllipsoidSurface

/-! # Actual radial roots for the one-tip mixed joint -/

open MeasureTheory Set Filter
open scoped Topology NNReal
noncomputable section
namespace BoundaryDraft

@[simp] theorem mixedNullDirection_norm (u : MixedNullDirection) : ‖(u : JointSpace)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp u.property

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

 theorem continuous_euclidean : Continuous (fun x : JointSpace => H x) :=
  hH.continuous.comp (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ))

 theorem euclidean_lipschitz : ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
    ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖ := by
  obtain ⟨k, hk, hk1, h⟩ := hH.lipschitz
  refine ⟨k, hk, hk1, fun x y => ?_⟩
  have he := h x y
  change |H x - H y| ≤ k * ‖y - x‖ at he
  simpa only [norm_sub_rev] using he

 theorem radial_gap_strictMono (u : MixedNullDirection) :
    StrictMono (fun r : ℝ => r - H (r • (u : JointSpace))) := by
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  intro a b hab
  have he := h (b • (u : JointSpace)) (a • (u : JointSpace))
  rw [← sub_smul, norm_smul, mixedNullDirection_norm, mul_one,
    Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] at he
  have hd := (le_abs_self _).trans he
  have := mul_lt_mul_of_pos_right hk1 (sub_pos.mpr hab)
  dsimp only
  linarith

 theorem exists_radial_root (u : MixedNullDirection) :
    ∃ R : ℝ, 0 < R ∧ R = H (R • (u : JointSpace)) := by
  classical
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (sub_pos.mpr hk1)
  have heq : (1 - k) * B = H 0 := by
    dsimp [B]; exact mul_div_cancel₀ _ (sub_pos.mpr hk1).ne'
  have he := h (B • (u : JointSpace)) 0
  simp only [sub_zero, norm_smul, mixedNullDirection_norm, mul_one,
    Real.norm_eq_abs, abs_of_pos hB] at he
  have hcont : Continuous (fun r : ℝ => r - H (r • (u : JointSpace))) :=
    continuous_id.sub (hH.continuous_euclidean.comp (continuous_id.smul continuous_const))
  obtain ⟨R, hR, hr⟩ := intermediate_value_Icc hB.le hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (0 - H ((0 : ℝ) • (u : JointSpace)))
      (B - H (B • (u : JointSpace))) from ⟨by simpa using hH.tip_pos.le,
        by have := (le_abs_self _).trans he; dsimp [B] at *; nlinarith⟩)
  have hRp : 0 < R := by
    by_contra hn
    have : R = 0 := le_antisymm (le_of_not_gt hn) hR.1
    subst R
    simp only [zero_smul, zero_sub, neg_eq_zero] at hr
    exact hH.tip_pos.ne' hr
  exact ⟨R, hRp, sub_eq_zero.mp hr⟩

 theorem radius_spec (u : MixedNullDirection) :
    0 < mixedNullRadius H u ∧
      mixedNullRadius H u = H (mixedNullRadius H u • (u : JointSpace)) := by
  obtain ⟨R, hR, he⟩ := hH.exists_radial_root u
  have hs : mixedNullRadialSet H u = Ico 0 R := by
    ext r
    change (0 ≤ r ∧ r < H (r • (u : JointSpace))) ↔ (0 ≤ r ∧ r < R)
    have hg := hH.radial_gap_strictMono u
    have hr : r < H (r • (u : JointSpace)) ↔ r < R := by
      have ht := hg.lt_iff_lt (a := r) (b := R)
      rw [← he, sub_self] at ht
      simpa only [sub_neg] using ht
    exact and_congr_right fun _ => hr
  rw [mixedNullRadius, hs, csSup_Ico hR]
  exact ⟨hR, he⟩

 theorem radius_pos (u : MixedNullDirection) : 0 < mixedNullRadius H u :=
  (hH.radius_spec u).1

 theorem radius_root (u : MixedNullDirection) :
    mixedNullRadius H u = H (mixedNullRadius H u • (u : JointSpace)) :=
  (hH.radius_spec u).2

 theorem radius_unique (u : MixedNullDirection) {r : ℝ}
    (hr : r = H (r • (u : JointSpace))) : r = mixedNullRadius H u := by
  apply (hH.radial_gap_strictMono u).injective
  change r - H (r • (u : JointSpace)) =
    mixedNullRadius H u - H (mixedNullRadius H u • (u : JointSpace))
  rw [← hr, ← hH.radius_root u, sub_self, sub_self]

 theorem radial_support (u : MixedNullDirection) (r : ℝ) :
    r ∈ mixedNullRadialSet H u ↔ 0 ≤ r ∧ r < mixedNullRadius H u := by
  have hg := (hH.radial_gap_strictMono u).lt_iff_lt (a := r) (b := mixedNullRadius H u)
  rw [← hH.radius_root u, sub_self] at hg
  exact and_congr_right fun _ => by simpa only [sub_neg] using hg

 theorem radialSet_eq (u : MixedNullDirection) :
    mixedNullRadialSet H u = Ico 0 (mixedNullRadius H u) :=
  Set.ext (hH.radial_support u)

 theorem radial_domain (u : MixedNullDirection) {r : ℝ} (hr : 0 ≤ r) :
    r • (u : JointSpace) ∈ mixedNullSpatialDomain H ↔ r < mixedNullRadius H u := by
  have hn : ‖r • (u : JointSpace)‖ = r := by
    rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
  have := hH.radial_support u r
  simpa only [mixedNullRadialSet, mem_setOf_eq, hr, true_and, mixedNullSpatialDomain,
    hn] using this

 theorem radius_bounds {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (h : ∀ x y : JointSpace, |H x - H y| ≤ k * ‖x - y‖)
    (u : MixedNullDirection) :
    H 0 / (1 + k) ≤ mixedNullRadius H u ∧
      mixedNullRadius H u ≤ H 0 / (1 - k) := by
  have hp := hH.radius_pos u
  have he := h (mixedNullRadius H u • (u : JointSpace)) 0
  rw [sub_zero, norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs,
    abs_of_pos hp, ← hH.radius_root u] at he
  constructor
  · apply (div_le_iff₀ (by linarith : 0 < 1 + k)).mpr
    have := (abs_le.mp he).1
    nlinarith
  · apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    have := (abs_le.mp he).2
    nlinarith

 theorem uniform_radius_bounds : ∃ m B : ℝ, 0 < m ∧ 0 < B ∧
    ∀ u : MixedNullDirection, m ≤ mixedNullRadius H u ∧ mixedNullRadius H u ≤ B := by
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  exact ⟨H 0 / (1 + k), H 0 / (1 - k), div_pos hH.tip_pos (by linarith),
    div_pos hH.tip_pos (by linarith), hH.radius_bounds hk hk1 h⟩

 theorem radius_lipschitz : ∃ K : ℝ≥0, LipschitzWith K (mixedNullRadius H) := by
  obtain ⟨k, hk, hk1, h⟩ := hH.euclidean_lipschitz
  let B := H 0 / (1 - k)
  have hB : 0 < B := div_pos hH.tip_pos (by linarith)
  let K := k * B / (1 - k)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hk hB.le) (by linarith)
  refine ⟨⟨K, hK⟩, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  change |mixedNullRadius H u - mixedNullRadius H v| ≤ K * ‖(u : JointSpace) - v‖
  have he := h (mixedNullRadius H u • (u : JointSpace))
    (mixedNullRadius H v • (v : JointSpace))
  rw [← hH.radius_root u, ← hH.radius_root v] at he
  have hv := (hH.radius_bounds hk hk1 h v).2
  have hn : ‖mixedNullRadius H u • (u : JointSpace) - mixedNullRadius H v • (v : JointSpace)‖ ≤
      |mixedNullRadius H u - mixedNullRadius H v| + B * ‖(u : JointSpace) - v‖ := by
    calc
      _ = ‖(mixedNullRadius H u - mixedNullRadius H v) • (u : JointSpace) +
        mixedNullRadius H v • ((u : JointSpace) - v)‖ := by congr 1; module
      _ ≤ ‖(mixedNullRadius H u - mixedNullRadius H v) • (u : JointSpace)‖ +
        ‖mixedNullRadius H v • ((u : JointSpace) - v)‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_smul, norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (hH.radius_pos v)]
        exact add_le_add_left (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) _
  have he' := he.trans (mul_le_mul_of_nonneg_left hn hk)
  have hd : (1 - k) * |mixedNullRadius H u - mixedNullRadius H v| ≤
      k * B * ‖(u : JointSpace) - v‖ := by nlinarith
  have hd' := (le_div_iff₀ (sub_pos.mpr hk1)).mpr (by nlinarith :
    |mixedNullRadius H u - mixedNullRadius H v| * (1 - k) ≤ k * B * ‖(u : JointSpace) - v‖)
  convert hd' using 1
  dsimp [K]
  ring

 theorem continuous_radius : Continuous (mixedNullRadius H) :=
  let ⟨_, h⟩ := hH.radius_lipschitz; h.continuous

 theorem continuous_jointParam : Continuous (mixedNullJointParam H) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hH.continuous_radius.neg
  · exact hH.continuous_radius.mul
      ((EuclideanSpace.proj j).continuous.comp continuous_subtype_val)

 theorem jointParam_mem (u : MixedNullDirection) : mixedNullJointParam H u ∈ mixedNullJoint H := by
  have hn : spatialDistance (mixedNullRadius H u • (u : JointSpace)) 0 = mixedNullRadius H u := by
    change ‖(0 : JointSpace) - mixedNullRadius H u • (u : JointSpace)‖ = _
    rw [zero_sub, norm_neg, norm_smul, mixedNullDirection_norm, mul_one,
      Real.norm_eq_abs, abs_of_pos (hH.radius_pos u)]
  constructor
  · simpa only [mixedNullJointParam, spatialPart_cons, hn] using (hH.radius_root u).symm
  · simpa only [mixedNullJointParam, Fin.cons_zero, spatialPart_cons] using congrArg Neg.neg hn.symm

 theorem joint_spatial_ne_zero {p : Spacetime} (hp : p ∈ mixedNullJoint H) :
    spatialPart p ≠ 0 := by
  intro he
  have hz := hp.1
  rw [he] at hz
  have : H 0 = 0 := by simpa [spatialDistance] using hz
  exact hH.tip_pos.ne' this

 theorem jointParam_surjective : ∀ p ∈ mixedNullJoint H, ∃ u, mixedNullJointParam H u = p := by
  intro p hp
  let x : JointSpace := (WithLp.equiv 2 _).symm (spatialPart p)
  have hx : x ≠ 0 := by
    intro hz
    apply hH.joint_spatial_ne_zero hp
    exact congrArg (WithLp.equiv 2 _) hz
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : MixedNullDirection := ⟨‖x‖⁻¹ • x, by
    simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']⟩
  have he : ‖x‖ • (u : JointSpace) = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hd : spatialDistance (spatialPart p) 0 = ‖x‖ := by
    change ‖(0 : JointSpace) - x‖ = ‖x‖
    rw [zero_sub, norm_neg]
  have hr : mixedNullRadius H u = ‖x‖ := (hH.radius_unique u (by
    rw [he]; exact hd.symm.trans hp.1.symm)).symm
  refine ⟨u, ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change -mixedNullRadius H u = p 0
    rw [hr, ← hd]
    exact hp.2.symm
  · change (mixedNullRadius H u • (u : JointSpace)) j = p j.succ
    rw [hr, he]
    rfl

 theorem jointParam_injective : Function.Injective (mixedNullJointParam H) := by
  intro u v he
  have hr : mixedNullRadius H u = mixedNullRadius H v := by
    have ht := congrFun he 0
    change -mixedNullRadius H u = -mixedNullRadius H v at ht
    exact neg_injective ht
  apply Subtype.ext
  have hs : mixedNullRadius H u • (u : JointSpace) = mixedNullRadius H u • (v : JointSpace) := by
    ext i
    have ht := congrFun he i.succ
    change mixedNullRadius H u * u.val i = mixedNullRadius H v * v.val i at ht
    simpa only [hr] using ht
  exact (smul_right_injective _ (hH.radius_pos u).ne') hs

 theorem range_jointParam : Set.range (mixedNullJointParam H) = mixedNullJoint H := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩; exact hH.jointParam_mem u
  · exact hH.jointParam_surjective p

 theorem isCompact_joint : IsCompact (mixedNullJoint H) := by
  rw [← hH.range_jointParam]
  exact isCompact_range hH.continuous_jointParam

/-- Radial projection is an actual inverse, including its nonzero denominator. -/
 theorem jointParam_radial_inverse (u : MixedNullDirection) :
    let x : JointSpace := (WithLp.equiv 2 _).symm (spatialPart (mixedNullJointParam H u))
    ‖x‖⁻¹ • x = (u : JointSpace) := by
  change ‖mixedNullRadius H u • (u : JointSpace)‖⁻¹ •
    (mixedNullRadius H u • (u : JointSpace)) = (u : JointSpace)
  rw [norm_smul, mixedNullDirection_norm, mul_one, Real.norm_eq_abs,
    abs_of_pos (hH.radius_pos u), smul_smul, inv_mul_cancel₀ (hH.radius_pos u).ne', one_smul]

/-- A global homeomorphism onto the actual joint, with no covering multiplicity. -/
 def jointHomeomorph : MixedNullDirection ≃ₜ mixedNullJoint H := by
  let f : MixedNullDirection → mixedNullJoint H := fun u => ⟨mixedNullJointParam H u, hH.jointParam_mem u⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v he
      exact hH.jointParam_injective (congrArg Subtype.val he)
    · intro p
      obtain ⟨u, hu⟩ := hH.jointParam_surjective p p.property
      exact ⟨u, Subtype.ext hu⟩
  let e := Equiv.ofBijective f hf
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (hH.continuous_jointParam.subtype_mk (fun u => hH.jointParam_mem u))

 theorem jointHomeomorph_apply (u : MixedNullDirection) :
    (hH.jointHomeomorph u : Spacetime) = mixedNullJointParam H u := rfl

 theorem integrable_radius_sq : Integrable (fun u : MixedNullDirection => mixedNullRadius H u ^ 2)
    (volume : Measure JointSpace).toSphere :=
  (hH.continuous_radius.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem area_bounds {m B : ℝ} (hm : 0 ≤ m)
    (hb : ∀ u : MixedNullDirection, m ≤ mixedNullRadius H u ∧ mixedNullRadius H u ≤ B) :
    4 * Real.pi * m ^ 2 ≤ mixedNullArea H ∧ mixedNullArea H ≤ 4 * Real.pi * B ^ 2 := by
  have hl := integral_mono (integrable_const (m ^ 2)) hH.integrable_radius_sq
    (fun u => pow_le_pow_left₀ hm (hb u).1 2)
  have hu := integral_mono hH.integrable_radius_sq (integrable_const (B ^ 2))
    (fun u => pow_le_pow_left₀ (hH.radius_pos u).le (hb u).2 2)
  simpa only [mixedNullArea, integral_const, smul_eq_mul, jointSphere_area] using And.intro hl hu

 theorem area_pos : 0 < mixedNullArea H := by
  obtain ⟨m, B, hm, _, hb⟩ := hH.uniform_radius_bounds
  exact (by positivity : 0 < 4 * Real.pi * m ^ 2).trans_le (hH.area_bounds hm.le hb).1

end MixedNullData
end BoundaryDraft

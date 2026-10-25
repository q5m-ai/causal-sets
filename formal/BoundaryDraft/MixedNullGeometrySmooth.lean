import BoundaryDraft.MixedNullRadial
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Smooth implicit radial roots, obtained from the actual floor -/
open Set Filter
open scoped Topology NNReal
noncomputable section
namespace BoundaryDraft

/-- Invertible triangular differential of the actual root equation. -/
def mixedNullRootLinear (L : JointSpace →L[ℝ] ℝ) (u : JointSpace) (R : ℝ)
    (ha : 1 - L u ≠ 0) : (JointSpace × ℝ) ≃L[ℝ] (JointSpace × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p => (p.1, (1 - L u) * p.2 - R * L p.1)
    invFun := fun p => (p.1, (p.2 + R * L p.1) / (1 - L u))
    left_inv := by intro p; ext <;> dsimp; field_simp
    right_inv := by intro p; ext <;> dsimp; field_simp
    map_add' := by intro p q; ext <;> simp; ring
    map_smul' := by intro c p; ext <;> simp; ring }

namespace AdmissibleMixedNull
variable {H : Spatial → ℝ} (hH : AdmissibleMixedNull H)
include hH

 theorem radial_derivative_pos (u : MixedNullDirection) (x : JointSpace) :
    0 < 1 - fderiv ℝ (fun y : JointSpace => H y) x (u : JointSpace) := by
  obtain ⟨k, hk, hk1, h⟩ := hH.toMixedNullData.euclidean_lipschitz
  have hl : LipschitzWith ⟨k, hk⟩ (fun y : JointSpace => H y) :=
    LipschitzWith.of_dist_le_mul fun y z => h y z
  have hn := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := x)
  have hb := (fderiv ℝ (fun y : JointSpace => H y) x).le_opNorm (u : JointSpace)
  rw [mixedNullDirection_norm, mul_one, Real.norm_eq_abs] at hb
  have := (le_abs_self _).trans (hb.trans hn)
  change _ ≤ k at this
  linarith

/-- The radial root has a strictly positive actual scalar derivative. -/
 theorem radial_gap_hasDerivAt (u : MixedNullDirection) (r : ℝ) :
    HasDerivAt (fun t : ℝ => t - H (t • (u : JointSpace)))
      (1 - fderiv ℝ (fun x : JointSpace => H x) (r • (u : JointSpace)) (u : JointSpace)) r := by
  have hd := ((hH.smooth_floor.differentiable (by simp)) (r • (u : JointSpace))).hasFDerivAt
  simpa using (hasDerivAt_id r).sub
    (hd.comp_hasDerivAt r ((hasDerivAt_id r).smul_const (u : JointSpace)))

/-- A genuine smooth ambient extension of the radius around every sphere point.
The extension solves the actual floor equation on an ambient neighborhood;
on the sphere it agrees with the fixed supremum-defined shared radius. -/
 theorem exists_smooth_radius_extension (u : MixedNullDirection) :
    ∃ f : JointSpace → ℝ, ContDiffAt ℝ ⊤ f (u : JointSpace) ∧
      f u = mixedNullRadius H u ∧
      (∀ᶠ x in 𝓝 (u : JointSpace), f x = H (f x • x)) ∧
      (∀ᶠ v : MixedNullDirection in 𝓝 u, f (v : JointSpace) = mixedNullRadius H v) := by
  let R := mixedNullRadius H u
  let L := fderiv ℝ (fun y : JointSpace => H y) (R • (u : JointSpace))
  have ha : 1 - L u ≠ 0 := (hH.radial_derivative_pos u _).ne'
  let eL := mixedNullRootLinear L u R ha
  let F : JointSpace × ℝ → JointSpace × ℝ := fun p => (p.1, p.2 - H (p.2 • p.1))
  let a : JointSpace × ℝ := (u, R)
  have hF : ContDiff ℝ ⊤ F :=
    contDiff_fst.prodMk (contDiff_snd.sub (hH.smooth_floor.comp (contDiff_snd.smul contDiff_fst)))
  have hd : HasFDerivAt F (eL : (JointSpace × ℝ) →L[ℝ] (JointSpace × ℝ)) a := by
    have hh := ((hH.smooth_floor.differentiable (by simp)) (R • (u : JointSpace))).hasFDerivAt
    have he := (hasFDerivAt_fst (𝕜 := ℝ) (p := a)).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := a)).sub
      (hh.comp a ((hasFDerivAt_snd (𝕜 := ℝ) (p := a)).smul
        (hasFDerivAt_fst (𝕜 := ℝ) (p := a)))))
    convert he using 1
    apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    · dsimp [eL, mixedNullRootLinear, a, L]
      simp only [map_add, map_smul, smul_eq_mul]
      ring
  have hsd : HasStrictFDerivAt F (eL : (JointSpace × ℝ) →L[ℝ] (JointSpace × ℝ)) a := by
    rw [← hd.fderiv]
    exact hF.contDiffAt.hasStrictFDerivAt (by simp)
  let e := hsd.toPartialHomeomorph F
  have haE : a ∈ e.source := hsd.mem_toPartialHomeomorph_source
  have hFa : F a = ((u : JointSpace), (0 : ℝ)) := by
    simp only [F, a, ← hH.toMixedNullData.radius_root u, R, sub_self]
  have hinv : ContDiffAt ℝ ⊤ e.symm (F a) := by
    apply e.contDiffAt_symm (e.map_source haE)
    · simpa only [e.left_inv haE] using hd
    · simpa only [e.left_inv haE] using hF.contDiffAt (x := a)
  let f : JointSpace → ℝ := fun x => (e.symm (x, 0)).2
  have hf : ContDiffAt ℝ ⊤ f (u : JointSpace) := by
    apply contDiffAt_snd.comp (u : JointSpace)
    rw [hFa] at hinv
    exact hinv.comp (u : JointSpace) (contDiffAt_id.prodMk contDiffAt_const)
  have he0 : e.symm ((u : JointSpace), 0) = a := by
    rw [← hFa]; exact e.left_inv haE
  have hroot : ∀ᶠ x in 𝓝 (u : JointSpace), f x = H (f x • x) := by
    have ht : ∀ᶠ x in 𝓝 (u : JointSpace), (x, (0 : ℝ)) ∈ e.target :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (e.open_target.mem_nhds (by
          change ((u : JointSpace), 0) ∈ e.target
          rw [← hFa]
          exact e.map_source haE))
    filter_upwards [ht] with x hx
    have he := e.right_inv hx
    have he1 : (e.symm (x, 0)).1 = x := congrArg Prod.fst he
    have he2 : (e.symm (x, 0)).2 - H ((e.symm (x, 0)).2 • (e.symm (x, 0)).1) = 0 :=
      congrArg Prod.snd he
    rw [he1] at he2
    exact sub_eq_zero.mp he2
  refine ⟨f, hf, congrArg Prod.snd he0, hroot, ?_⟩
  filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hroot] with v hv
  exact hH.toMixedNullData.radius_unique v hv

/-- The differential of the constructed root is derived by differentiating
its actual equation; it is not supplied as geometric data. -/
 theorem exists_smooth_radius_differential (u : MixedNullDirection) :
    ∃ f : JointSpace → ℝ, ContDiffAt ℝ ⊤ f (u : JointSpace) ∧
      f u = mixedNullRadius H u ∧
      (∀ᶠ v : MixedNullDirection in 𝓝 u, f v = mixedNullRadius H v) ∧
      ∀ v : JointSpace, fderiv ℝ f (u : JointSpace) v =
        mixedNullRadius H u *
          fderiv ℝ (fun x : JointSpace => H x) (mixedNullRadius H u • (u : JointSpace)) v /
        (1 - fderiv ℝ (fun x : JointSpace => H x)
          (mixedNullRadius H u • (u : JointSpace)) (u : JointSpace)) := by
  obtain ⟨f, hf, he, hr, hag⟩ := hH.exists_smooth_radius_extension u
  have hd := (hf.differentiableAt (by simp)).hasFDerivAt
  have hh := ((hH.smooth_floor.differentiable (by simp)) (f u • (u : JointSpace))).hasFDerivAt
  have hc := hh.comp (f := fun x => f x • x) (u : JointSpace)
    (hd.smul (hasFDerivAt_id (u : JointSpace)))
  have heq := hd.unique (hc.congr_of_eventuallyEq hr)
  refine ⟨f, hf, he, hag, fun v => ?_⟩
  have hv := congrArg (fun d : JointSpace →L[ℝ] ℝ => d v) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul, he] at hv
  apply (eq_div_iff (hH.radial_derivative_pos u _).ne').mpr
  nlinarith

end AdmissibleMixedNull
end BoundaryDraft

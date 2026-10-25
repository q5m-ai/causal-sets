import BoundaryDraft.MixedNullContract
import BoundaryDraft.SpacetimeIntegration

/-! The complete closed region and its two bounding graphs (MA4).
The reverse closure inclusion is proved by actual inward perturbations,
including the spatial axis and the joint; there is no extra lateral wall. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace BoundaryDraft

/-- Both time endpoints are retained in the closed candidate. -/
def mixedNullClosedRegion (H : Spatial → ℝ) : Set Spacetime :=
  {p | -H (spatialPart p) ≤ p 0 ∧ p 0 ≤ -spatialDistance (spatialPart p) 0}

def mixedNullLowerFace (H : Spatial → ℝ) : Set Spacetime :=
  {p | spatialDistance (spatialPart p) 0 ≤ H (spatialPart p) ∧ p 0 = -H (spatialPart p)}

def mixedNullUpperFace (H : Spatial → ℝ) : Set Spacetime :=
  {p | spatialDistance (spatialPart p) 0 ≤ H (spatialPart p) ∧
    p 0 = -spatialDistance (spatialPart p) 0}

private theorem distance_zero_norm (x : Spatial) :
    spatialDistance x 0 = ‖((WithLp.equiv 2 _).symm x : JointSpace)‖ := by
  simp only [spatialDistance, zero_sub]
  change ‖-((WithLp.equiv 2 _).symm x : JointSpace)‖ = _
  exact norm_neg _

@[simp] private theorem euclidean_roundtrip (x : JointSpace) :
    ((WithLp.equiv 2 _).symm (x : Spatial) : JointSpace) = x := by
  ext i
  rfl

private theorem continuous_radius : Continuous (fun p : Spacetime =>
    spatialDistance (spatialPart p) 0) := by
  simp_rw [distance_zero_norm]
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact ((PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp hs).norm

private theorem continuous_cons {a : ℝ → ℝ} {b : ℝ → Spatial}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun s => (Fin.cons (a s) (b s) : Spacetime)) := by
  apply continuous_pi
  intro i
  exact Fin.cases ha (fun j => (continuous_apply j).comp hb) i

private theorem distance_smul {s : ℝ} (hs : 0 ≤ s) (x : Spatial) :
    spatialDistance (s • x) 0 = s * spatialDistance x 0 := by
  rw [distance_zero_norm, distance_zero_norm]
  change ‖s • ((WithLp.equiv 2 _).symm x : JointSpace)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]

/-- The chronological condition is exactly the strict cone inequality. -/
theorem mem_mixedNullRegion_iff (H : Spatial → ℝ) (p : Spacetime) :
    p ∈ mixedNullRegion H ↔
      -H (spatialPart p) < p 0 ∧ p 0 < -spatialDistance (spatialPart p) 0 := by
  have hr := spatialDistance_nonneg (spatialPart p) 0
  have he : spatialDistance (spatialPart p) 0 ^ 2 = spatialSeparationSq p 0 := by
    simp [spatialDistance_sq, spatialSeparationSq, spatialPart]
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    have ht : p 0 < 0 := hp.2.1
    have hh : spatialDistance (spatialPart p) 0 < -p 0 := by
      apply (sq_lt_sq₀ hr (by linarith : 0 ≤ -p 0)).mp
      rw [he]
      simpa using hp.2.2
    linarith
  · rintro ⟨hf, ht⟩
    refine ⟨hf, ?_, ?_⟩
    · change p 0 < 0
      linarith
    · change spatialSeparationSq p 0 < (0 - p 0) ^ 2
      rw [← he, zero_sub]
      exact (sq_lt_sq₀ hr (by linarith : 0 ≤ -p 0)).mpr (by linarith)

/-- The spatial domain is the actual projection of the open spacetime region. -/
theorem mixedNullSpatialDomain_eq_image (H : Spatial → ℝ) :
    mixedNullSpatialDomain H =
      (fun p => ((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)) '' mixedNullRegion H := by
  ext x
  constructor
  · intro hx
    refine ⟨Fin.cons (-(H x + ‖x‖) / 2) (x : Spatial), ?_, ?_⟩
    · rw [mem_mixedNullRegion_iff]
      simp only [spatialPart_cons, Fin.cons_zero, distance_zero_norm, euclidean_roundtrip]
      have hh : ‖x‖ < H x := hx
      constructor <;> dsimp only <;> linarith
    · simp
  · rintro ⟨p, hp, rfl⟩
    have hh := (mem_mixedNullRegion_iff H p).mp hp
    change ‖((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ < H (spatialPart p)
    rw [← distance_zero_norm]
    linarith [hh.1, hh.2]

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem isClosed_closedRegion : IsClosed (mixedNullClosedRegion H) := by
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  exact (isClosed_le (hH.continuous.comp hs).neg (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_radius.neg)

/-- The closure contains the floor, complete cone and their entire joint. -/
theorem closure_region : closure (mixedNullRegion H) = mixedNullClosedRegion H := by
  apply subset_antisymm
  · apply closure_minimal _ hH.isClosed_closedRegion
    intro p hp
    have hp' := (mem_mixedNullRegion_iff H p).mp hp
    exact ⟨hp'.1.le, hp'.2.le⟩
  · intro p hp
    have hr := spatialDistance_nonneg (spatialPart p) 0
    obtain ⟨κ, hκ, hκ1, hLip⟩ := hH.lipschitz
    by_cases hzero : spatialDistance (spatialPart p) 0 = 0
    · have hx : spatialPart p = 0 := by
        have hz := norm_eq_zero.mp ((distance_zero_norm (spatialPart p)).symm.trans hzero)
        exact congrArg (WithLp.equiv 2 _) hz
      have hlo : -H 0 ≤ p 0 := by simpa [hx] using hp.1
      have hup : p 0 ≤ 0 := by simpa [hzero] using hp.2
      let f : ℝ → Spacetime := fun s => Fin.cons (s * p 0 + (1 - s) * (-H 0 / 2)) (0 : Spatial)
      have hc : Continuous f := by
        apply continuous_cons <;> fun_prop
      have he : f 1 = p := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · have hj := congrFun hx j
          simpa [f, spatialPart] using hj.symm
      have hl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 p) := by
        simpa only [he] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hl
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with s hs hs0
      rw [mem_mixedNullRegion_iff]
      simp only [f, spatialPart_cons, Fin.cons_zero]
      have hT := hH.tip_pos
      have hs1 : s < 1 := hs
      have hd : spatialDistance (0 : Spatial) 0 = 0 := by simp [distance_zero_norm]
      rw [hd]
      constructor <;> nlinarith
    · have hrpos : 0 < spatialDistance (spatialPart p) 0 := lt_of_le_of_ne hr (Ne.symm hzero)
      let r := spatialDistance (spatialPart p) 0
      let a := (1 + κ) / 2
      let f : ℝ → Spacetime := fun s => Fin.cons (p 0 + (1 - s) * a * r) (s • spatialPart p)
      have hc : Continuous f := by
        apply continuous_cons <;> fun_prop
      have he : f 1 = p := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · simp [f, spatialPart]
      have hl : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 p) := by
        simpa only [he] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hl
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with s hs hs0
      have hs1 : s < 1 := hs
      have hd : spatialDistance (s • spatialPart p) (spatialPart p) = (1 - s) * r := by
        unfold spatialDistance
        rw [show spatialPart p - s • spatialPart p = (1 - s) • spatialPart p by
          ext i; simp; ring]
        change ‖(1 - s) • ((WithLp.equiv 2 _).symm (spatialPart p) : JointSpace)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs1)]
        rw [← distance_zero_norm]
      have hh := (le_abs_self (H (spatialPart p) - H (s • spatialPart p))).trans
        (hLip (spatialPart p) (s • spatialPart p))
      rw [spatialDistance_symm, hd] at hh
      have hpositive : 0 < (1 - s) * (1 - κ) * r :=
        mul_pos (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hκ1)) hrpos
      rw [mem_mixedNullRegion_iff]
      simp only [f, spatialPart_cons, Fin.cons_zero]
      rw [distance_smul hs0.le]
      have hlo := hp.1
      have hup := hp.2
      dsimp [a, r] at *
      constructor <;> nlinarith

/-- Exact spatial closure, including every radial endpoint. -/
theorem closure_spatialDomain : closure (mixedNullSpatialDomain H) =
    {x : JointSpace | ‖x‖ ≤ H x} := by
  apply subset_antisymm
  · apply closure_minimal (fun (x : JointSpace) hx => (show ‖x‖ < H x from hx).le)
    exact isClosed_le continuous_norm
      (hH.continuous.comp (PiLp.continuous_equiv 2 (fun _ : Fin 3 => ℝ)))
  · intro x hx
    let p : Spacetime := Fin.cons (-‖x‖) (x : Spatial)
    have hp : p ∈ closure (mixedNullRegion H) := by
      rw [hH.closure_region]
      change -H (spatialPart p) ≤ p 0 ∧ p 0 ≤ -spatialDistance (spatialPart p) 0
      simp only [p, spatialPart_cons, Fin.cons_zero, distance_zero_norm, euclidean_roundtrip]
      exact ⟨neg_le_neg hx, le_rfl⟩
    have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
    have hc := (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp hs
    have he := mem_closure_image hc.continuousAt hp
    simp only [Function.comp_def] at he
    rw [← mixedNullSpatialDomain_eq_image] at he
    simpa [p] using he

/-- No lateral component is missing from the frontier. -/
theorem frontier_region : frontier (mixedNullRegion H) =
    mixedNullLowerFace H ∪ mixedNullUpperFace H := by
  rw [frontier, hH.closure_region, hH.isOpen_region.interior_eq]
  ext p
  simp only [mem_diff, mixedNullClosedRegion, mem_setOf_eq, mem_mixedNullRegion_iff,
    mem_union, mixedNullLowerFace, mixedNullUpperFace]
  constructor
  · rintro ⟨⟨hlo, hup⟩, hn⟩
    have hd : spatialDistance (spatialPart p) 0 ≤ H (spatialPart p) := by linarith
    by_cases hf : -H (spatialPart p) < p 0
    · right
      exact ⟨hd, le_antisymm hup (le_of_not_gt (fun h => hn ⟨hf, h⟩))⟩
    · left
      exact ⟨hd, le_antisymm (le_of_not_gt hf) hlo⟩
  · rintro (⟨hd, he⟩ | ⟨hd, he⟩)
    · refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rintro ⟨hh, _⟩
      linarith
    · refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rintro ⟨_, hh⟩
      linarith

end MixedNullData

/-- The intersection of the two actual boundary faces is exactly MA1's joint. -/
theorem mixedNull_faces_inter (H : Spatial → ℝ) :
    mixedNullLowerFace H ∩ mixedNullUpperFace H = mixedNullJoint H := by
  ext p
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨by have := hl.2; have := hu.2; linarith, hu.2⟩
  · intro hp
    exact ⟨⟨hp.1.ge, by rw [hp.1]; exact hp.2⟩, ⟨hp.1.ge, hp.2⟩⟩

/-- A time graph has zero original four-volume, derived by coordinate
transport and spatial-first Tonelli, not by an area convention. -/
theorem volume_timeGraph_zero (f : Spatial → ℝ) (hf : Continuous f) :
    volume {p : Spacetime | p 0 = f (spatialPart p)} = 0 := by
  let e : ℝ × Spatial ≃ᵐ Spacetime :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm
  have he (t : ℝ) (x : Spatial) : e (t, x) = Fin.cons t x := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  have hm : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm _
  have hc : Continuous spatialPart := by unfold spatialPart; fun_prop
  have hS : MeasurableSet {p : Spacetime | p 0 = f (spatialPart p)} :=
    (isClosed_eq (continuous_apply 0) (hf.comp hc)).measurableSet
  rw [← hm.measure_preimage hS.nullMeasurableSet]
  have hp : e ⁻¹' {p : Spacetime | p 0 = f (spatialPart p)} =
      {p : ℝ × Spatial | p.1 = f p.2} := by
    ext p
    simp [he]
  have hprod : MeasurableSet {p : ℝ × Spatial | p.1 = f p.2} :=
    (isClosed_eq continuous_fst (hf.comp continuous_snd)).measurableSet
  rw [hp, Measure.volume_eq_prod, Measure.prod_apply_symm hprod]
  simp

namespace MixedNullData
variable {H : Spatial → ℝ} (hH : MixedNullData H)
include hH

theorem lowerFace_volume_zero : volume (mixedNullLowerFace H) = 0 :=
  measure_mono_null (fun _ hp => hp.2) (volume_timeGraph_zero (fun x => -H x) hH.continuous.neg)

omit hH in
theorem upperFace_volume_zero : volume (mixedNullUpperFace H) = 0 := by
  have hc : Continuous (fun x : Spatial => -spatialDistance x 0) := by
    simp_rw [distance_zero_norm]
    exact (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).norm.neg
  exact measure_mono_null (fun _ hp => hp.2) (volume_timeGraph_zero _ hc)

/-- Volume-nullity is not used to discard a density-normalized boundary term. -/
theorem frontier_volume_zero : volume (frontier (mixedNullRegion H)) = 0 := by
  rw [hH.frontier_region]
  apply le_antisymm _ bot_le
  calc
    _ ≤ volume (mixedNullLowerFace H) + volume (mixedNullUpperFace H) := measure_union_le _ _
    _ = 0 := by rw [hH.lowerFace_volume_zero, upperFace_volume_zero, zero_add]

theorem compact_faces : IsCompact (mixedNullLowerFace H) ∧ IsCompact (mixedNullUpperFace H) := by
  have hs : Continuous spatialPart := by unfold spatialPart; fun_prop
  have hD := isClosed_le continuous_radius (hH.continuous.comp hs)
  constructor
  · apply hH.isBounded_region.isCompact_closure.of_isClosed_subset
      (hD.inter (isClosed_eq (continuous_apply 0) (hH.continuous.comp hs).neg))
    intro p hp
    rw [hH.closure_region]
    have hh := hp.1
    have ht := hp.2
    dsimp only [mem_setOf_eq, Function.comp_apply] at hh ht
    constructor <;> dsimp only <;> linarith
  · apply hH.isBounded_region.isCompact_closure.of_isClosed_subset
      (hD.inter (isClosed_eq (continuous_apply 0) continuous_radius.neg))
    intro p hp
    rw [hH.closure_region]
    have hh := hp.1
    have ht := hp.2
    dsimp only [mem_setOf_eq, Function.comp_apply] at hh ht
    constructor <;> dsimp only <;> linarith

end MixedNullData
end BoundaryDraft

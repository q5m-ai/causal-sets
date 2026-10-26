import BoundaryDraft.MixedNullReduction
import BoundaryDraft.EllipsoidJoint
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Independent geometry and targets for the smooth one-tip mixed theorem

These definitions follow MA1 and MA7. The smoothness field is restored for
induced joint geometry; no action identity, radial-root conclusion, integral
formula, asymptotic estimate or limit is an admissibility field. The radial
area density must be justified from the actual Lorentzian tangent metric by
the subsequent geometry producer, not by action asymptotics.
-/

open MeasureTheory Set
noncomputable section
namespace BoundaryDraft

abbrev MixedNullDirection := Metric.sphere (0 : JointSpace) 1

/-- The original smooth MA floor contract, distinct from finite-density data. -/
structure AdmissibleMixedNull (H : Spatial → ℝ) : Prop extends MixedNullData H where
  smooth_floor : ContDiff ℝ ⊤ (fun x : JointSpace => H x)

/-- Spatial interior, independently of any limiting observable. -/
def mixedNullSpatialDomain (H : Spatial → ℝ) : Set JointSpace :=
  {x | ‖x‖ < H x}

/-- Radial support is defined for all profiles; its boundedness and exact
endpoint characterization are theorems, not fields. -/
def mixedNullRadialSet (H : Spatial → ℝ) (u : MixedNullDirection) : Set ℝ :=
  {r | 0 ≤ r ∧ r < H (r • (u : JointSpace))}

noncomputable def mixedNullRadius (H : Spatial → ℝ) (u : MixedNullDirection) : ℝ :=
  sSup (mixedNullRadialSet H u)

/-- Actual spacetime intersection of floor and future cone. -/
def mixedNullJoint (H : Spatial → ℝ) : Set Spacetime :=
  {p | H (spatialPart p) = spatialDistance (spatialPart p) 0 ∧
    p 0 = -spatialDistance (spatialPart p) 0}

/-- The proposed global joint parameterization. Its image, inverse and
Lorentzian differential must be proved from admissible geometry. -/
def mixedNullJointParam (H : Spatial → ℝ) (u : MixedNullDirection) : Spacetime :=
  Fin.cons (-mixedNullRadius H u)
    (mixedNullRadius H u • (u : JointSpace) : JointSpace)

/-- Parametric candidate area; its induced-metric interpretation is a
separate required theorem, not part of this definition. -/
def mixedNullJointMeasure (H : Spatial → ℝ) : Measure Spacetime :=
  Measure.map (mixedNullJointParam H)
    ((volume : Measure JointSpace).toSphere.withDensity
      (fun u => ENNReal.ofReal (mixedNullRadius H u ^ 2)))

/-- MA7's sphere-integral target, independent of the action. -/
def mixedNullArea (H : Spatial → ℝ) : ℝ :=
  ∫ u : MixedNullDirection, mixedNullRadius H u ^ 2
    ∂(volume : Measure JointSpace).toSphere

/-- An intermediate spatial integral, NOT a replacement for induced area. -/
def mixedNullSpatialLimit (H : Spatial → ℝ) : ℝ :=
  ∫ x in mixedNullSpatialDomain H, 2 / ‖x‖

end BoundaryDraft

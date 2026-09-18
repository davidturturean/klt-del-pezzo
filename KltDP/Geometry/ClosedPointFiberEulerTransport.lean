import KltDP.Geometry.ClosedPoints
import KltDP.Geometry.CohomologyFieldIsoTransport
import KltDP.Geometry.SchemeIsoEulerTransport
import Mathlib.AlgebraicGeometry.Fiber

/-! The full original residue-field fiber and the constructed k-valued
closed-point fiber have the same native Euler characteristic. Both the
scheme isomorphism and the native scalar change use the same original
base-to-residue-field isomorphism. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.ClosedPointFiberEulerTransport
open ModuleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  (π : X ⟶ Y) (f : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  (x : Y) (hx : IsClosed ({x} : Set Y))

private theorem residuePoint_comp_section :
    Spec.map (closedPointResidueFieldIso f x hx).hom ≫ closedPointSection f x hx =
      Y.fromSpecResidueField x := by
  rw [closedPointSection, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- The actual map of full original fiber schemes. -/
def residueToSection : π.fiber x ⟶ pullback π (closedPointSection f x hx) :=
  pullback.map π (Y.fromSpecResidueField x) π (closedPointSection f x hx)
    (𝟙 _) (Spec.map (closedPointResidueFieldIso f x hx).hom) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (residuePoint_comp_section f x hx).symm)

instance residueToSection_isIso : IsIso (residueToSection π f x hx) := by
  letI : IsIso (Spec.map (closedPointResidueFieldIso f x hx).hom) := by infer_instance
  dsimp only [residueToSection]
  infer_instance

/-- The original residue-field structure map is preserved after scalar change. -/
theorem residueToSection_snd :
    residueToSection π f x hx ≫ pullback.snd π (closedPointSection f x hx) =
      π.fiberToSpecResidueField x ≫ Spec.map (closedPointResidueFieldIso f x hx).hom := by
  exact pullback.lift_snd _ _ _

/-- Equality for the exact residue-field Euler function occurring in the
flat-family theorem and the actual k-point fiber used by surface RR. -/
theorem eulerCharacteristic_eq :
    eulerCharacteristic (π.fiberToSpecResidueField x)
        (_root_.SheafOfModules.unit (π.fiber x).ringCatSheaf) =
      eulerCharacteristic (pullback.snd π (closedPointSection f x hx))
        (_root_.SheafOfModules.unit (pullback π (closedPointSection f x hx)).ringCatSheaf) := by
  have he := eulerCharacteristic_unit_eq (asIso (residueToSection π f x hx))
    (π.fiberToSpecResidueField x ≫ Spec.map (closedPointResidueFieldIso f x hx).hom)
    (pullback.snd π (closedPointSection f x hx)) (residueToSection_snd π f x hx)
  have hc := eulerCharacteristic_comp_specIso (π.fiberToSpecResidueField x)
    (closedPointResidueFieldEquiv f x hx)
    (_root_.SheafOfModules.unit (π.fiber x).ringCatSheaf)
  exact hc.symm.trans he

end KltDP.Geometry.ClosedPointFiberEulerTransport

#check @KltDP.Geometry.ClosedPointFiberEulerTransport.eulerCharacteristic_eq
#print axioms KltDP.Geometry.ClosedPointFiberEulerTransport.eulerCharacteristic_eq

import KltDP.Geometry.RationalSurfaceStructureCohomologyConditional
import KltDP.Literature.Hartshorne.RuledSurfaceGenus

/-!
# Native structure cohomology of an original rational regular surface

The complete reviewed Hartshorne V.2.5 statement supplies the product
model computation. Original rationality and regularity give the actual
common-resolution comparison. No source or cohomology premise remains
in this public theorem.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A rational regular original projective surface has chi(O)=1 and h1=h2=0. -/
theorem structureCohomology_of_rational
    (S : NormalProjectiveSurface k)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hrational : Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    eulerCharacteristic S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) = 1 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 1 = 0 ∧
      cohomologyDimension S.structureMorphism
        (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) 2 = 0 :=
  S.structureCohomology_of_rational_conditional
    KltDP.Literature.Hartshorne.ruled_surface_genus_literal hS hrational

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.structureCohomology_of_rational
#print axioms KltDP.Geometry.NormalProjectiveSurface.structureCohomology_of_rational

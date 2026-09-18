import KltDP.Geometry.GenericFiberStalkIso
import KltDP.Geometry.RegularLocalEquiv

/-! Regularity of the actual generic-fiber local rings follows through
the literal stalk maps of its original inclusion. This does not assert
geometric regularity or smoothness over the generic residue field. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.GenericFiberRegular

variable {X Y : Scheme.{u}} [IsIntegral Y]

theorem regularPoint (f : X ⟶ Y) (x : f.fiber (genericPoint Y))
    (hx : RegularPoint X ((f.fiberι (genericPoint Y)).base x)) :
    RegularPoint (f.fiber (genericPoint Y)) x :=
  regularLocal_of_ringEquiv
    (GenericFiberStalkIso.stalkIso f x).commRingCatIsoToRingEquiv hx

theorem regularPoints (f : X ⟶ Y) (hX : ∀ x : X, RegularPoint X x) :
    ∀ x : f.fiber (genericPoint Y), RegularPoint (f.fiber (genericPoint Y)) x :=
  fun x => regularPoint f x (hX _)

#print axioms regularPoints

end KltDP.Geometry.GenericFiberRegular

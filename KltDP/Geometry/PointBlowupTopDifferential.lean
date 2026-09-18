import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportIsIso
import KltDP.Geometry.SchemeModulePullbackTensorInclusion

/-!
# Original top-differential objects on the whole point blowup

All four objects and arrows below use the actual glued point blowup,
its original projection, its actual center-fiber kernel and the existing
intrinsic exterior differential. No canonical divisor is chosen here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.PointBlowupTopDifferential

open PointBlowupGluing SchemeKaehlerSheaf

local instance pointTopModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k R : Type u} [CommRing k] [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X)) (n : ℕ)

abbrev sourceSheaf : X.Modules := SchemeExteriorPower.sheaf (baseRingSheaf f) n

abbrev topSheaf : (scheme j q hclosed).Modules :=
  SchemeExteriorPower.sheaf (baseRingSheaf (projection j q hclosed ≫ f)) n

/-- The original exterior differential of the actual whole blowdown. -/
def blowdownMap :
    (schemeModulePullback (projection j q hclosed)).obj (sourceSheaf f n) ⟶
      topSheaf f j q hclosed n :=
  SchemeKaehlerExteriorPullbackTransport.map f (projection j q hclosed)
    (projection j q hclosed ≫ f) rfl n

/-- The literal original global center-fiber kernel tensored with the actual top sheaf. -/
abbrev exceptionalTensor : (scheme j q hclosed).Modules :=
  schemeKernelIdeal (globalCenterFiberι j q hclosed) ⊗ topSheaf f j q hclosed n

/-- The original exceptional inclusion acts on the original top-differential sheaf. -/
def exceptionalInclusion : exceptionalTensor f j q hclosed n ⟶ topSheaf f j q hclosed n :=
  schemeStructureTensorInclusion (schemeKernelIdealι (globalCenterFiberι j q hclosed))
    (topSheaf f j q hclosed n)

end KltDP.Geometry.PointBlowupTopDifferential

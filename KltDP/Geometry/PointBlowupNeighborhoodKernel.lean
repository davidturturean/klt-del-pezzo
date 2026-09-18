import KltDP.Geometry.PointBlowupClosedCenterIso
import KltDP.Geometry.PointBlowupNeighborhoodIndependence
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# The actual exceptional fiber and kernel under neighborhood change

The original neighborhood isomorphism is over the original surface. The
proved isomorphism of the actual reduced quotient centers completes the
original pullback diagram. Its induced isomorphism of the actual whole
center fibers preserves their inclusions, so the existing kernel transport
isomorphism applies without any support-to-ideal inference.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.PointBlowupGluing

open SchemeKernelIdealIsoTransport

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) [qR.asIdeal.IsMaximal]
    (qS : PrimeSpectrum S) [qS.asIdeal.IsMaximal]
    (hR : IsClosed ({jR.base qR} : Set X))
    (hS : IsClosed ({jS.base qS} : Set X))
    (hpoint : jR.base qR = jS.base qS)

/-- The original pullback map on the two actual global center fibers. -/
def globalCenterFiberNeighborhoodMap : globalCenterFiber jR qR hR ⟶
    globalCenterFiber jS qS hS :=
  pullback.map (projection jR qR hR) (closedCenterInclusion jR qR)
    (projection jS qS hS) (closedCenterInclusion jS qS)
    (neighborhoodIso jR jS qR qS hR hS hpoint).hom
    (closedCenterIso jR jS qR qS hR hS hpoint).hom (𝟙 X)
    (by rw [Category.comp_id, neighborhoodIso_over_base])
    (by rw [Category.comp_id, closedCenterIso_hom_comp])

instance globalCenterFiberNeighborhoodMap_isIso :
    IsIso (globalCenterFiberNeighborhoodMap jR jS qR qS hR hS hpoint) := by
  unfold globalCenterFiberNeighborhoodMap
  infer_instance

/-- The actual exceptional fiber is carried by the original neighborhood isomorphism. -/
def globalCenterFiberNeighborhoodIso : globalCenterFiber jR qR hR ≅
    globalCenterFiber jS qS hS :=
  asIso (globalCenterFiberNeighborhoodMap jR jS qR qS hR hS hpoint)

theorem globalCenterFiberNeighborhoodIso_hom_ι :
    (globalCenterFiberNeighborhoodIso jR jS qR qS hR hS hpoint).hom ≫
        globalCenterFiberι jS qS hS =
      globalCenterFiberι jR qR hR ≫ (neighborhoodIso jR jS qR qS hR hS hpoint).hom := by
  simp only [globalCenterFiberNeighborhoodIso, asIso_hom,
    globalCenterFiberNeighborhoodMap, globalCenterFiberι, pullback.map, pullback.lift_fst]

/-- The kernel on the new neighborhood is the pullback of the original actual kernel. -/
def globalCenterFiberKernelNeighborhoodIso :
    schemeKernelIdeal (globalCenterFiberι jS qS hS) ≅
      (schemeModulePullback (neighborhoodIso jR jS qR qS hR hS hpoint).inv).obj
        (schemeKernelIdeal (globalCenterFiberι jR qR hR)) :=
  schemeKernelTransportIso (globalCenterFiberι jR qR hR)
    (neighborhoodIso jR jS qR qS hR hS hpoint) (globalCenterFiberι jS qS hS)
    (globalCenterFiberNeighborhoodIso jR jS qR qS hR hS hpoint)
    (globalCenterFiberNeighborhoodIso_hom_ι jR jS qR qS hR hS hpoint)

/-- The same kernel comparison preserves the literal inclusions into the structure sheaf. -/
theorem globalCenterFiberKernelNeighborhoodIso_hom_inclusion :
    (globalCenterFiberKernelNeighborhoodIso jR jS qR qS hR hS hpoint).hom ≫
        pulledKernelInclusion (globalCenterFiberι jR qR hR)
          (neighborhoodIso jR jS qR qS hR hS hpoint).inv =
      schemeKernelIdealι (globalCenterFiberι jS qS hS) :=
  schemeKernelTransportIso_hom_inclusion (globalCenterFiberι jR qR hR)
    (neighborhoodIso jR jS qR qS hR hS hpoint) (globalCenterFiberι jS qS hS)
    (globalCenterFiberNeighborhoodIso jR jS qR qS hR hS hpoint)
    (globalCenterFiberNeighborhoodIso_hom_ι jR jS qR qS hR hS hpoint)

end KltDP.Geometry.PointBlowupGluing

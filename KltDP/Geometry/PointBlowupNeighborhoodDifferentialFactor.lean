import KltDP.Geometry.PointBlowupNeighborhoodKernel
import KltDP.Geometry.PointBlowupTopDifferential
import KltDP.Geometry.SchemeTopDifferentialFactorSquare
import KltDP.Geometry.SchemeModuleIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Original whole differential factors under actual neighborhood change

The original pullback along a scheme isomorphism is an equivalence: this
follows from its original adjunction and the already proved pushforward
equivalence. The normalized original square transports a proved factor to
that pullback, and the pinned fully faithful preimage returns it to the
original whole point blowup. No new global gluing or smoothness input is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.PointBlowupTopDifferential

open PointBlowupGluing

local instance neighborhoodFactorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance neighborhoodPullbackEquivalence {X Y : Scheme.{u}} (e : Y ⟶ X) [IsIso e] :
    (schemeModulePullback e).IsEquivalence :=
  (schemeModulePullbackPushforwardAdjunction e).isEquivalence_left_of_isEquivalence_right

private theorem preimageIso_factor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {M N Q : C}
    (e : F.obj M ≅ F.obj N) (b : N ⟶ Q) (a : M ⟶ Q)
    (he : e.hom ≫ F.map b = F.map a) : (F.preimageIso e).hom ≫ b = a := by
  apply F.map_injective
  simpa only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage] using he

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (jR : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion jR]
    (jS : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion jS]
    (qR : PrimeSpectrum R) [qR.asIdeal.IsMaximal]
    (qS : PrimeSpectrum S) [qS.asIdeal.IsMaximal]
    (hR : IsClosed ({jR.base qR} : Set X))
    (hS : IsClosed ({jS.base qS} : Set X))
    (hpoint : jR.base qR = jS.base qS) (n : ℕ)

private theorem neighborhoodFactor_square :
    (neighborhoodIso jR jS qR qS hR hS hpoint).inv ≫ projection jR qR hR =
      projection jS qS hS ≫ 𝟙 X := by
  rw [Category.comp_id, neighborhoodIso_inv_over_base]

private theorem neighborhoodFactor_structure :
    (neighborhoodIso jR jS qR qS hR hS hpoint).inv ≫ (projection jR qR hR ≫ f) =
      projection jS qS hS ≫ f := by
  rw [← Category.assoc, neighborhoodIso_inv_over_base]

variable (eS : (schemeModulePullback (projection jS qS hS)).obj (sourceSheaf f n) ≅
    exceptionalTensor f jS qS hS n)

/-- The actual normalized square produces the factor after the original inverse-neighborhood pullback. -/
def neighborhoodChartFactorIso :
    (schemeModulePullback (neighborhoodIso jR jS qR qS hR hS hpoint).inv).obj
        ((schemeModulePullback (projection jR qR hR)).obj (sourceSheaf f n)) ≅
      (schemeModulePullback (neighborhoodIso jR jS qR qS hR hS hpoint).inv).obj
        (exceptionalTensor f jR qR hR n) :=
  SchemeTopDifferentialFactorSquare.factorIso
    (f := f) (π := projection jR qR hR)
    (l := (neighborhoodIso jR jS qR qS hR hS hpoint).inv)
    (c := 𝟙 X) (b := projection jS qS hS)
    (hsq := neighborhoodFactor_square jR jS qR qS hR hS hpoint)
    (g := projection jR qR hR ≫ f) (p := f) (hp := Category.id_comp f)
    (q := projection jS qS hS ≫ f)
    (hl := neighborhoodFactor_structure f jR jS qR qS hR hS hpoint) (n := n)
    (eJ := globalCenterFiberKernelNeighborhoodIso jR jS qR qS hR hS hpoint) (e := eS)

/-- The original fully faithful pullback recovers the factor on the original whole point blowup. -/
def neighborhoodFactorIso :
    (schemeModulePullback (projection jR qR hR)).obj (sourceSheaf f n) ≅
      exceptionalTensor f jR qR hR n :=
  (schemeModulePullback (neighborhoodIso jR jS qR qS hR hS hpoint).inv).preimageIso
    (neighborhoodChartFactorIso f jR jS qR qS hR hS hpoint n eS)

variable (heS : eS.hom ≫ exceptionalInclusion f jS qS hS n = blowdownMap f jS qS hS n)

include heS in
/-- The recovered factor retains the same original whole exterior differential. -/
theorem neighborhoodFactorIso_comp :
    (neighborhoodFactorIso f jR jS qR qS hR hS hpoint n eS).hom ≫
        exceptionalInclusion f jR qR hR n = blowdownMap f jR qR hR n := by
  apply preimageIso_factor
    (schemeModulePullback (neighborhoodIso jR jS qR qS hR hS hpoint).inv)
    (neighborhoodChartFactorIso f jR jS qR qS hR hS hpoint n eS)
    (exceptionalInclusion f jR qR hR n) (blowdownMap f jR qR hR n)
  exact SchemeTopDifferentialFactorSquare.factorIso_comp
    (f := f) (π := projection jR qR hR)
    (l := (neighborhoodIso jR jS qR qS hR hS hpoint).inv)
    (c := 𝟙 X) (b := projection jS qS hS)
    (hsq := neighborhoodFactor_square jR jS qR qS hR hS hpoint)
    (g := projection jR qR hR ≫ f) (hg := rfl) (p := f) (hp := Category.id_comp f)
    (q := projection jS qS hS ≫ f)
    (hl := neighborhoodFactor_structure f jR jS qR qS hR hS hpoint) (hb := rfl) (n := n)
    (i := schemeKernelIdealι (globalCenterFiberι jR qR hR))
    (j := schemeKernelIdealι (globalCenterFiberι jS qS hS))
    (eJ := globalCenterFiberKernelNeighborhoodIso jR jS qR qS hR hS hpoint)
    (hJ := globalCenterFiberKernelNeighborhoodIso_hom_inclusion jR jS qR qS hR hS hpoint)
    (e := eS) (he := heS)

end KltDP.Geometry.PointBlowupTopDifferential

import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.CurveDegreeZeroNotBig

/-!
The original degree-one line pullback gives a degree-one effective
Cartier zero scheme, using the actual signed Cartier pullback. Its
identification with the original point fiber is a separate geometric
comparison, not a premise of this degree computation.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry.ModuleCohomology
universe u

namespace KltDP.Geometry.DegreeOneCartierPullback

/-- The actual Cartier pullback has original zero-scheme H0 dimension one. -/
theorem effectiveCartierDegree_eq_one
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (π : X ⟶ Y) [GenericPointPreserving π]
    (L : InvertibleSheaf Y) (D : CartierDivisor Y)
    (hD : HasRegularCartierEquations Y D)
    (eD : cartierDivisorModule Y D ≅ L.obj)
    (hdegree : eulerCharacteristic f (pullbackInvertibleSheaf π L).obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit X.ringCatSheaf) = 1) :
    effectiveCartierDegree X (DominantCartierPullback.pullbackHom π D)
      (DominantCartierPullback.pullbackHom_hasRegularEquations π D hD) f = 1 := by
  let e : cartierDivisorModule X (DominantCartierPullback.pullbackHom π D) ≅
      (pullbackInvertibleSheaf π L).obj :=
    (DominantCartierPullback.modulePullbackIso π D).symm ≪≫
      (schemeModulePullback π).mapIso eD
  have hχ := eulerCharacteristic_eq_of_iso f e
  have h := CurveDegreeZeroNotBig.eulerDifference_cartier_eq_effectiveDegree
    f hdim (DominantCartierPullback.pullbackHom π D)
      (DominantCartierPullback.pullbackHom_hasRegularEquations π D hD)
  rw [hχ, hdegree] at h
  exact_mod_cast h.symm

#check KltDP.Geometry.DegreeOneCartierPullback.effectiveCartierDegree_eq_one
#print axioms KltDP.Geometry.DegreeOneCartierPullback.effectiveCartierDegree_eq_one

end KltDP.Geometry.DegreeOneCartierPullback

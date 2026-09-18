import KltDP.Geometry.SchemeKaehlerPullbackMap
import KltDP.Examples.FrobeniusGraphClosed
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The original global differential map on the projective product

Each component is the existing differential map of the original scheme
projection. The second component uses only the proved fiber-product square
to identify its structure morphism with the original product structure map.
Their categorical sum is the global comparison to be checked on the
original product atlas. No isomorphism or canonical-class formula is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalDifferentials

open SchemeKaehlerSheaf
open KltDP.Examples.FrobeniusProjectivePoints KltDP.Examples.FrobeniusGraphClosed

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (k : Type u) [Field k]

/-- The original first pulled-back differential sheaf. -/
abbrev firstFactor : (projectiveProduct k).Modules :=
  (schemeModulePullback (firstProjection (k := k))).obj
    (baseRingSheaf (projectiveSpaceToSpec k 1))

/-- The original second pulled-back differential sheaf. -/
abbrev secondFactor : (projectiveProduct k).Modules :=
  (schemeModulePullback (secondProjection (k := k))).obj
    (baseRingSheaf (projectiveSpaceToSpec k 1))

/-- The actual second projection has the original product structure morphism. -/
theorem secondProjection_structure :
    secondProjection (k := k) ≫ projectiveSpaceToSpec k 1 = projectiveProductToSpec :=
  pullback.condition.symm

/-- The original differential along the original first projection. -/
def firstDifferential : firstFactor k ⟶ baseRingSheaf (projectiveProductToSpec (k := k)) :=
  SchemeKaehlerPullbackMap.map (projectiveSpaceToSpec k 1) firstProjection

/-- The original differential along the original second projection, with the actual
fiber-product structure-map equality. -/
def secondDifferential : secondFactor k ⟶ baseRingSheaf (projectiveProductToSpec (k := k)) :=
  SchemeKaehlerPullbackMap.map (projectiveSpaceToSpec k 1) secondProjection ≫
    eqToHom (congrArg (fun f => baseRingSheaf f) (secondProjection_structure k))

/-- The first component retains the original pullback-unit normalization on every section. -/
theorem firstDifferential_unit_d (U : (projectiveSpace k 1).Opens)
    (s : Γ(projectiveSpace k 1, U)) :
    (firstDifferential k).val.app (op (firstProjection ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction firstProjection).unit.app
          (baseRingSheaf (projectiveSpaceToSpec k 1))).val.app (op U)
            ((baseRingDerivation (projectiveSpaceToSpec k 1)).d s)) =
      (baseRingDerivation (projectiveProductToSpec (k := k))).d
        (firstProjection.app U s) :=
  SchemeKaehlerPullbackMap.map_unit_d (projectiveSpaceToSpec k 1) firstProjection U s

/-- The global categorical sum of the two original projection differentials. -/
def comparison : firstFactor k ⊞ secondFactor k ⟶
    baseRingSheaf (projectiveProductToSpec (k := k)) :=
  biprod.desc (firstDifferential k) (secondDifferential k)

/-- Its first component is exactly the original first projection differential. -/
@[reassoc]
theorem inl_comparison :
    biprod.inl ≫ comparison k = firstDifferential k :=
  biprod.inl_desc _ _

/-- Its second component is exactly the original second projection differential. -/
@[reassoc]
theorem inr_comparison :
    biprod.inr ≫ comparison k = secondDifferential k :=
  biprod.inr_desc _ _

end KltDP.Geometry.ProjectiveProductCanonicalDifferentials

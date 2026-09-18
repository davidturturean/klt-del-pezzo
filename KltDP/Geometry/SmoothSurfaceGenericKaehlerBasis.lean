import KltDP.Geometry.SmoothSurfaceKaehlerAtlas
import KltDP.Geometry.KaehlerLocalizedFrame
import KltDP.Geometry.RationalTreePicardIntrinsicNode
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A native generic Kähler basis from the original smooth surface map

Choose the existing actual smooth affine chart at the generic point and
localize its proved two-element differential basis along its original
generic germ. The field algebra is exactly IntrinsicNodal.stalkAlgebra
for the original structure morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SmoothSurfaceGenericKaehlerBasis

open IntrinsicNodal SmoothSurfaceKaehlerAtlas

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]

include hSmooth in
/-- The native generic basis comes from a genuine smooth affine chart,
with no basis, coordinate or generic-rank hypothesis. -/
def basis :
    letI := stalkAlgebra f (genericPoint X)
    Basis (Fin 2) X.functionField (KaehlerDifferential k X.functionField) := by
  let U : X.Opens := atlasOpen f (genericPoint X)
  let hU : IsAffineOpen U := atlasOpen_isAffineOpen f (genericPoint X)
  have hmem : genericPoint X ∈ U := atlasOpen_mem f (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X, hmem⟩⟩
  letI := affineSectionsAlgebra f hU
  letI := stalkAlgebra f (genericPoint X)
  letI : IsScalarTower k Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (fun g : CommRingCat.of k ⟶ X.functionField => g.hom a)
        (baseToAffineSectionsMap_germ f hU (genericPoint X) hmem).symm
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  exact KaehlerLocalizedFrame.localizedFrame k Γ(X, U) X.functionField
    (nonZeroDivisors Γ(X, U)) (atlasFrame f (genericPoint X))

include hSmooth in
/-- The same original function field has native Kähler dimension two. -/
theorem finrank_eq_two :
    letI := stalkAlgebra f (genericPoint X)
    Module.finrank X.functionField (KaehlerDifferential k X.functionField) = 2 := by
  letI := stalkAlgebra f (genericPoint X)
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (basis f)

end KltDP.Geometry.SmoothSurfaceGenericKaehlerBasis

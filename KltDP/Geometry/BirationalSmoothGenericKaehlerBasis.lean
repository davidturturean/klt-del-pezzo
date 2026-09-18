import KltDP.Geometry.BirationalFunctionFieldStalkAlgebra
import KltDP.Geometry.SmoothSurfaceGenericKaehlerBasis
import KltDP.Geometry.KaehlerBasisAlgEquiv

/-!
# Native generic Kähler rank two from an actual smooth birational source

The source basis is derived from its actual smooth affine chart. Transport
through the inverse of the original birational function-field algebra map
gives a genuine native basis on the target function field. Both ground
actions are the original IntrinsicNodal.stalkAlgebra actions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalSmoothGenericKaehlerBasis

open IntrinsicNodal

variable {k : Type u} [Field k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (f : S ⟶ Spec (CommRingCat.of k)) [hSmooth : IsSmoothOfRelativeDimension 2 f]
    (σ : X ⟶ Spec (CommRingCat.of k)) (π : S ⟶ X) (hπ : π ≫ σ = f)
    (hbir : IsBirationalScheme π)

include hSmooth hπ hbir in
/-- The target generic basis is derived from the original smooth birational source. -/
def basis :
    letI := stalkAlgebra σ (genericPoint X)
    Basis (Fin 2) X.functionField (KaehlerDifferential k X.functionField) := by
  letI := stalkAlgebra σ (genericPoint X)
  letI := stalkAlgebra f (genericPoint S)
  exact KaehlerBasisAlgEquiv.basis
    (BirationalFunctionFieldStalkAlgebra.equiv f σ π hπ hbir).symm
    (SmoothSurfaceGenericKaehlerBasis.basis f)

include hSmooth hπ hbir in
/-- The original target function field has native Kähler dimension two. -/
theorem finrank_eq_two :
    letI := stalkAlgebra σ (genericPoint X)
    Module.finrank X.functionField (KaehlerDifferential k X.functionField) = 2 := by
  letI := stalkAlgebra σ (genericPoint X)
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (basis f σ π hπ hbir)

end KltDP.Geometry.BirationalSmoothGenericKaehlerBasis

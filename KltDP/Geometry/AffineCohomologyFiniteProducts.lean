/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The finite-product argument is adapted from Vilin97/MazurTheorem
9327963d4ec14fba49c7b14b004fd00707ffc2e9,
MazurTorsion/Upstream/SchemeModuleCohomologyAffineCover.lean:40-59.
It uses the project's original tilde and counit, and the pinned biproduct
comparison, instead of the newer essential-image object-property API.
-/
import KltDP.Geometry.AffineQuasicoherentKernels
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Finite products of original affine quasicoherent modules

The original tilde left adjoint preserves finite coproducts. In preadditive
categories these give finite products. The original quasicoherent counits
then identify the ambient product with a tilde sheaf. This is a source port
draft; VM elaboration and the compiled dependency audit remain pending.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.AffineCohomologyPort

open AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R]

/-- The existing tilde left adjoint preserves finite products. -/
theorem tilde_preservesFiniteProducts : PreservesFiniteProducts (functor R) := by
  constructor
  intro n
  letI : PreservesBiproductsOfShape (Fin n) (functor R) :=
    preservesBiproductsOfShape_of_preservesCoproductsOfShape (functor R)
  exact preservesProductsOfShape_of_preservesBiproductsOfShape (functor R)

/-- The actual product is the tilde of the product of original global sections. -/
def quasicoherentProductIso {I : Type u} [Finite I]
    (M : I → (Spec (.of R)).Modules) [∀ i, (M i).IsQuasicoherent] :
    (∏ᶜ fun i => (globalSectionsFunctor R).obj (M i)).tilde ≅ ∏ᶜ M := by
  letI := tilde_preservesFiniteProducts (R := R)
  letI (i : I) : IsIso (counit (M i)) := counit_isIso_of_isQuasicoherent (M i)
  exact PreservesProduct.iso (functor R) (fun i => (globalSectionsFunctor R).obj (M i)) ≪≫
    Pi.mapIso (fun i => asIso (counit (M i)))

/-- A finite ambient product of original affine quasicoherent modules is quasicoherent. -/
theorem product_isQuasicoherent {I : Type u} [Finite I]
    (M : I → (Spec (.of R)).Modules) [∀ i, (M i).IsQuasicoherent] :
    (∏ᶜ M).IsQuasicoherent := by
  letI := tilde_isQuasicoherent (∏ᶜ fun i => (globalSectionsFunctor R).obj (M i))
  exact _root_.SheafOfModules.isQuasicoherent_of_isIso
    (R := (Spec (.of R)).ringCatSheaf)
    (M := (∏ᶜ fun i => (globalSectionsFunctor R).obj (M i)).tilde)
    (N := ∏ᶜ M) (quasicoherentProductIso M).hom

end KltDP.Geometry.AffineCohomologyPort

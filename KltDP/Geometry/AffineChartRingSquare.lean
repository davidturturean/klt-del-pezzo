import KltDP.Geometry.AffineFiniteType

/-!
# Original scalar maps on an affine chart square

The actual section map of a scheme morphism respects the two ground
algebras defined by the original structure maps. Both the scalar tower
and the spectrum square follow from the pinned actual affine-chart square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffineChartRingSquare

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (π : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (hπ : π ≫ f = g)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ π ⁻¹ᵁ U)

include hπ in
/-- The actual chart section map preserves the original base-ring maps. -/
theorem baseMap_comp :
    baseToAffineSectionsMap f hU ≫ π.appLE U V hVU =
      baseToAffineSectionsMap g hV := by
  apply Spec.map_injective
  calc
    Spec.map (baseToAffineSectionsMap f hU ≫ π.appLE U V hVU) =
        Spec.map (π.appLE U V hVU) ≫ Spec.map (baseToAffineSectionsMap f hU) :=
      Spec.map_comp _ _
    _ = Spec.map (π.appLE U V hVU) ≫ hU.fromSpec ≫ f := by
      rw [Spec_map_baseToAffineSectionsMap]
    _ = hV.fromSpec ≫ π ≫ f := by
      rw [IsAffineOpen.Spec_map_appLE_fromSpec_assoc]
    _ = Spec.map (baseToAffineSectionsMap g hV) := by
      rw [hπ, Spec_map_baseToAffineSectionsMap]

/-- The original affine section map, regarded as its own scalar action. -/
abbrev chartAlgebra : Algebra Γ(X, U) Γ(Y, V) :=
  (π.appLE U V hVU).hom.toAlgebra

/-- The two original ground actions form the actual scalar tower. -/
def scalarTower :
    letI := affineSectionsAlgebra f hU
    letI := affineSectionsAlgebra g hV
    letI := chartAlgebra π hVU
    IsScalarTower k Γ(X, U) Γ(Y, V) := by
  letI := affineSectionsAlgebra f hU
  letI := affineSectionsAlgebra g hV
  letI := chartAlgebra π hVU
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg (fun r : CommRingCat.of k ⟶ Γ(Y, V) => r.hom)
    (baseMap_comp π f g hπ hU hV hVU).symm

/-- The spectrum map of that same scalar action is the original chart square. -/
theorem chartMap_square :
    letI := chartAlgebra π hVU
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(Y, V))) ≫ hU.fromSpec =
      hV.fromSpec ≫ π := by
  letI := chartAlgebra π hVU
  exact IsAffineOpen.Spec_map_appLE_fromSpec π hU hV hVU

end KltDP.Geometry.AffineChartRingSquare

#check @KltDP.Geometry.AffineChartRingSquare.scalarTower
#print axioms KltDP.Geometry.AffineChartRingSquare.scalarTower

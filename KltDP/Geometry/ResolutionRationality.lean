import KltDP.Geometry.RationalityBirationalMorphism

/-!
# Rationality along the original resolution morphism

Properness follows from the original projective structure maps. The
existing birational-open theorem then supplies an actual partial
isomorphism over the same base field. No rationality theorem is assumed.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

variable {k : Type u} [Field k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

/-- A resolution gives an actual birational equivalence over its original field. -/
theorem IsResolution.birationalOver (hπ : IsResolution S X π) :
    Scheme.BirationalOver S.structureMorphism X.structureMorphism := by
  letI : IsProper π := hπ.isProper
  exact birationalOver_of_isBirationalScheme π S.structureMorphism X.structureMorphism
    hπ.over_base ((isBirational_iff_isBirationalScheme π).mp hπ.birational)

/-- The whole source of the original resolution is birational to the same affine plane. -/
theorem IsResolution.birationalOver_affinePlane (hπ : IsResolution S X π)
    (hX : Scheme.BirationalOver X.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :
    Scheme.BirationalOver S.structureMorphism
      (𝔸(Fin 2; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) :=
  hπ.birationalOver.trans hX

end KltDP.Geometry

#check @KltDP.Geometry.IsResolution.birationalOver
#print axioms KltDP.Geometry.IsResolution.birationalOver
#print axioms KltDP.Geometry.IsResolution.birationalOver_affinePlane

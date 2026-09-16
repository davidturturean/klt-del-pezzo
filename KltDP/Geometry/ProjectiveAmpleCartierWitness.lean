import KltDP.Geometry.ProjectiveAmpleWitness
import KltDP.Geometry.GloballyGeneratedEffectiveCartier
import KltDP.Geometry.AmpleNefUnconditional

/-!
# Actual ample Cartier divisors on original integral projective schemes

The actual projective ample line sheaf has an original Cartier-divisor
representative. Its original Picard class retains Serre ampleness, supplying
an actual ample and nef Cartier divisor on every original normal projective surface.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance ampleCartierOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance ampleCartierOverLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

local instance ampleCartierMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- An original integral scheme projective over a field has an actual
Cartier divisor whose associated original line sheaf is Serre ample. -/
theorem IsProjectiveOverField.exists_isAmple_cartier {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveOverField f) :
    ∃ D : CartierDivisor X, AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X D) := by
  obtain ⟨L, hL⟩ := hf.exists_isAmple
  letI : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  obtain ⟨D, ⟨e⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  refine ⟨D, AmplePositivity.isAmple_of_toPic_eq ?_ hL⟩
  apply Units.ext
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨e⟩

/-- Every original normal projective surface has an actual ample Cartier divisor. -/
theorem NormalProjectiveSurface.exists_isAmple_cartier {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) :
    ∃ D : CartierDivisor X.toScheme,
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) :=
  X.projective.exists_isAmple_cartier

/-- An actual Cartier witness simultaneously satisfies the existing ample
and nef predicates on the original normal projective surface. -/
theorem NormalProjectiveSurface.exists_isAmple_isNef_cartier {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) :
    ∃ D : CartierDivisor X.toScheme,
      AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D) ∧
      Positivity.IsNef X.structureMorphism (cartierDivisorInvertibleSheaf X.toScheme D) := by
  obtain ⟨D, hD⟩ := X.exists_isAmple_cartier
  exact ⟨D, hD, AmpleNefUnconditional.isNef_of_isAmple X _ hD⟩

end KltDP.Geometry

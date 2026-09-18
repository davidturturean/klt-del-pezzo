import KltDP.Geometry.SemiampleProjectiveMap
import KltDP.Geometry.LinearSystemDegreeOnePullback
import KltDP.Geometry.LinearSystemProper
import KltDP.Geometry.SchemeKernelIdealIsoTransport

/-!
# Projective realization of an actual semiample power

The finite power system constructed from semiampleness defines a morphism
over the original field. Its pullback of the original degree-one sheaf is
the actual tensor power, and properness follows from the original source.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.SemiampleProjectiveMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowers ProjectiveSpaceDegreeOneSheaf SchemeKernelIdealIsoTransport

variable {k : Type u} [Field k] {X : Scheme.{u}} (L : InvertibleSheaf X)
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The original projective morphism realizes the actual positive tensor power. -/
def PowerSystem.toProjective_pullbackDegreeOneIso (D : PowerSystem L) :
    (pullbackInvertibleSheaf (PowerSystem.toProjective L f D)
      (degreeOne k D.dimension)).obj ≅ (power L D.exponent).obj :=
  LinearSystemPullback.pullbackDegreeOneIso
    (power L D.exponent) D.sections f D.covers

/-- The same actual pullback yields the expected equality of original Picard classes. -/
theorem PowerSystem.toProjective_picard (D : PowerSystem L) :
    schemePicardPullbackHom (PowerSystem.toProjective L f D)
      (degreeOne k D.dimension).toPic = L.toPic ^ D.exponent := by
  rw [schemePicardPullbackHom_toPic]
  exact (toPic_eq_of_iso _ _
    (PowerSystem.toProjective_pullbackDegreeOneIso L f D)).trans
      (power_toPic L D.exponent)

/-- A proper original source gives a proper projective realization. -/
instance PowerSystem.toProjective_isProper [IsProper f] (D : PowerSystem L) :
    IsProper (PowerSystem.toProjective L f D) := by
  change IsProper (LinearSystemMorphism.morphism
    (power L D.exponent) D.sections f D.covers)
  infer_instance

/-- Semiampleness constructs a projective morphism and an actual pullback
isomorphism for a positive tensor power on the original quasi-compact scheme. -/
theorem exists_projective_realization
    (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsSemiample L) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : ℕ, ∃ g : X ⟶ projectiveSpace k n,
      g ≫ projectiveSpaceToSpec k n = f ∧
      Nonempty ((pullbackInvertibleSheaf g (degreeOne k n)).obj ≅ (power L m).obj) := by
  let D := powerSystem L hX hL
  exact ⟨D.exponent, D.positive, D.dimension, PowerSystem.toProjective L f D,
    PowerSystem.toProjective_structure L f D,
    ⟨PowerSystem.toProjective_pullbackDegreeOneIso L f D⟩⟩

/-- When the original structure morphism is proper, the constructed
projective realization is proper as well. -/
theorem exists_proper_projective_realization [IsProper f]
    (hX : IsCompact (Set.univ : Set X)) (hL : Positivity.IsSemiample L) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : ℕ, ∃ g : X ⟶ projectiveSpace k n,
      g ≫ projectiveSpaceToSpec k n = f ∧ IsProper g ∧
      Nonempty ((pullbackInvertibleSheaf g (degreeOne k n)).obj ≅ (power L m).obj) := by
  let D := powerSystem L hX hL
  exact ⟨D.exponent, D.positive, D.dimension, PowerSystem.toProjective L f D,
    PowerSystem.toProjective_structure L f D, inferInstance,
    ⟨PowerSystem.toProjective_pullbackDegreeOneIso L f D⟩⟩

end KltDP.Geometry.SemiampleProjectiveMap

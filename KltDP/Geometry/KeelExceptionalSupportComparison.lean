import KltDP.Geometry.KeelExceptionalSupport
import KltDP.Geometry.SchematicImageOpenBaseChange

/-!
Pointwise comparison of the actual exceptional-subvariety predicates gives
equality of the supports, equality of their actual radical vanishing ideals,
and the canonical isomorphism of the original reduced induced schemes.
The isomorphism commutes with the original closed inclusions and transports
the actual restricted line. The growth/birational comparison stays explicit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.KeelCompleteSystem

attribute [local instance] subvariety_isIntegral

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : InvertibleSheaf X)

/-- Pointwise equivalence of the actual exceptional predicates identifies their closures. -/
theorem exceptionalSupport_eq_nullLocus_of_isExceptional_iff
    (h : ∀ Z : IrreducibleCloseds X,
      IsExceptionalSubvariety f L Z ↔ Positivity.IsExceptionalSubvariety f L Z) :
    exceptionalSupport f L = Positivity.nullLocus f L := by
  have hset : {Z : IrreducibleCloseds X | IsExceptionalSubvariety f L Z} =
      {Z : IrreducibleCloseds X | Positivity.IsExceptionalSubvariety f L Z} :=
    Set.ext h
  rw [exceptionalSupport, Positivity.nullLocus, hset]

/-- Only positive-dimensional original subvarieties need a comparison between
the two concrete bigness predicates in order to identify these supports. -/
theorem exceptionalSupport_eq_nullLocus_of_birational_iff_big
    (h : ∀ (Z : IrreducibleCloseds X), 0 < topologicalKrullDim (Z : Set X) →
      (EventuallyBirational (Positivity.inclusion Z ≫ f)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) ↔
      Positivity.IsBig (Positivity.inclusion Z ≫ f)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L))) :
    exceptionalSupport f L = Positivity.nullLocus f L := by
  apply exceptionalSupport_eq_nullLocus_of_isExceptional_iff f L
  intro Z
  constructor
  · rintro ⟨hdim, hnot⟩
    exact ⟨hdim, fun hbig => hnot ((h Z hdim).mpr hbig)⟩
  · rintro ⟨hdim, hnot⟩
    exact ⟨hdim, fun hbirational => hnot ((h Z hdim).mp hbirational)⟩

/-- Equality of supports identifies the actual closed subsets used in the constructions. -/
theorem exceptionalClosed_eq_nullLocusClosed
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    exceptionalClosed f L = Positivity.nullLocusClosed f L := Closeds.ext h

/-- The two schemes use equal original radical vanishing ideals. -/
theorem exceptionalIdeal_eq_nullLocusIdeal
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    Scheme.IdealSheafData.vanishingIdeal (exceptionalClosed f L) =
      Scheme.IdealSheafData.vanishingIdeal (Positivity.nullLocusClosed f L) :=
  congrArg Scheme.IdealSheafData.vanishingIdeal
    (exceptionalClosed_eq_nullLocusClosed f L h)

/-- The canonical original reduced-scheme comparison induced by equal supports. -/
def exceptionalSchemeIso
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    exceptionalScheme f L ≅ Positivity.nullLocusScheme f L :=
  eqToIso (congrArg (fun I : X.IdealSheafData => I.glueData.glued)
    (exceptionalIdeal_eq_nullLocusIdeal f L h))

@[reassoc] theorem exceptionalSchemeIso_hom_inclusion
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    (exceptionalSchemeIso f L h).hom ≫ Positivity.nullLocusInclusion f L =
      exceptionalInclusion f L :=
  SchematicImageOpenBaseChange.gluedTo_eqToHom (exceptionalIdeal_eq_nullLocusIdeal f L h)

/-- This isomorphism preserves the original field structures as well. -/
theorem exceptionalSchemeIso_hom_structure
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    (exceptionalSchemeIso f L h).hom ≫ (Positivity.nullLocusInclusion f L ≫ f) =
      exceptionalInclusion f L ≫ f := by
  rw [← Category.assoc, exceptionalSchemeIso_hom_inclusion]

/-- Pulling the original null-locus restriction through the canonical scheme
isomorphism gives the actual line restricted to the complete-system support. -/
def exceptionalRestrictIso
    (h : exceptionalSupport f L = Positivity.nullLocus f L) :
    (pullbackInvertibleSheaf (exceptionalSchemeIso f L h).hom
      (Positivity.nullLocusRestrict f L)).obj ≅ (exceptionalRestrict f L).obj :=
  (schemeModulePullbackCompIso (exceptionalSchemeIso f L h).hom
    (Positivity.nullLocusInclusion f L)).app L.obj ≪≫
      eqToIso (congrArg (fun g => (schemeModulePullback g).obj L.obj)
        (exceptionalSchemeIso_hom_inclusion f L h))

end KltDP.Geometry.KeelCompleteSystem

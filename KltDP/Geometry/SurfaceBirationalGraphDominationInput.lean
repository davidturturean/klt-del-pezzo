import KltDP.Geometry.BirationalRationalMapOverTarget
import KltDP.Geometry.RationalMapGraphBirational
import KltDP.Geometry.ProperBirationalSurfaceDominationInput

/-!
# Original birational graphs and the actual inputs for point-blowup domination

The two original birational morphisms to `X` determine the actual partial map
by the original function-field inverses. Its actual graph projection is proper,
birational, and unchanged over that partial map's original domain. The proved
finite-bad-set package supplies the remaining hypotheses for a regular or
smooth normal projective source surface over an algebraically closed field.

The maps to the original `X` and the original domain agreement are retained
as separate exact equations. This module constructs no blowup sequence and
uses no domination or factorization hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SurfaceBirationalGraphDominationInput

variable {k : Type u} [Field k] (T : NormalProjectiveSurface k)

private instance source_isNoetherian : IsNoetherian T.toScheme := by
  letI : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian
  exact ⟨⟩

variable {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
  (t : T.toScheme ⟶ X) (v : V ⟶ X) [IsProper v]
  (ht : IsBirationalScheme t) (hv : IsBirationalScheme v)

/-- The original inverse-over-`K(X)` partial map. -/
abbrev representative : T.toScheme.PartialMap V :=
  BirationalRationalMapOverTarget.partialMap t v ht hv

/-- The actual kernel-image graph of the original correspondence. -/
abbrev model : Scheme.{u} :=
  RationalMapGraphClosure.model t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

abbrev projection : model T t v ht hv ⟶ T.toScheme :=
  RationalMapGraphClosure.projection t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

abbrev extension : model T t v ht hv ⟶ V :=
  RationalMapGraphClosure.extension t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

abbrev domainLift : (representative T t v ht hv).domain.toScheme ⟶ model T t v ht hv :=
  RationalMapGraphClosure.domainLift t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

instance model_isIntegral : IsIntegral (model T t v ht hv) :=
  RationalMapGraphClosure.model_isIntegral t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

instance projection_isProper : IsProper (projection T t v ht hv) :=
  RationalMapGraphClosure.projection_isProper t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

theorem projection_isBirationalScheme : IsBirationalScheme (projection T t v ht hv) :=
  RationalMapGraphClosure.projection_isBirationalScheme t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

/-- The actual graph extension and projection commute over the original `X`. -/
theorem extension_comp : extension T t v ht hv ≫ v = projection T t v ht hv ≫ t :=
  RationalMapGraphClosure.extension_comp t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

theorem domainLift_projection :
    domainLift T t v ht hv ≫ projection T t v ht hv = (representative T t v ht hv).domain.ι :=
  RationalMapGraphClosure.domainLift_projection t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

theorem domainLift_extension :
    domainLift T t v ht hv ≫ extension T t v ht hv = (representative T t v ht hv).hom :=
  RationalMapGraphClosure.domainLift_extension t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

theorem projection_restrict_originalDomain_isIso :
    IsIso (projection T t v ht hv ∣_ (representative T t v ht hv).domain) :=
  RationalMapGraphClosure.projection_restrict_isIso t v (representative T t v ht hv)
    (BirationalRationalMapOverTarget.partialMap_comp t v ht hv)

/-- The original domain is contained in the full isomorphism open, so the
actual bad locus avoids it. -/
theorem originalDomain_le_targetIsomorphismOpen :
    (representative T t v ht hv).domain ≤ targetIsomorphismOpen (projection T t v ht hv) :=
  fun _ hx => ⟨(representative T t v ht hv).domain, hx,
    projection_restrict_originalDomain_isIso T t v ht hv⟩

variable [IsAlgClosed k]

/-- Every geometric input to 0AHI for this actual graph projection is proved
from the original birational maps and regular source surface. -/
theorem exists_domination_input_of_regular (hreg : ∀ x, RegularPoint T.toScheme x) :
    ∃ (B : Set T.toScheme) (hfinite : B.Finite)
      (hclosed : ∀ x ∈ B, IsClosed ({x} : Set T.toScheme)),
      B = targetNonisomorphismLocus (projection T t v ht hv) ∧
      IsNoetherian T.toScheme ∧ IsProper (projection T t v ht hv) ∧
      (∀ x ∈ B, RegularPoint T.toScheme x ∧
        ringKrullDim (T.toScheme.presheaf.stalk x) = 2) ∧
      IsIso (projection T t v ht hv ∣_ finiteClosedPointComplement T.toScheme B hfinite hclosed) ∧
      extension T t v ht hv ≫ v = projection T t v ht hv ≫ t ∧
      domainLift T t v ht hv ≫ projection T t v ht hv = (representative T t v ht hv).domain.ι ∧
      domainLift T t v ht hv ≫ extension T t v ht hv = (representative T t v ht hv).hom := by
  obtain ⟨B, hfinite, hclosed, hB, hNoetherian, hregular, hiso⟩ :=
    ProperBirationalSurface.exists_domination_input_of_regular T (projection T t v ht hv)
      (projection_isBirationalScheme T t v ht hv) hreg
  exact ⟨B, hfinite, hclosed, hB, hNoetherian, projection_isProper T t v ht hv,
    hregular, hiso, extension_comp T t v ht hv, domainLift_projection T t v ht hv,
    domainLift_extension T t v ht hv⟩

/-- Smoothness of the original surface supplies regularity through the
proved finite-bad-set package; no regularity witness is added. -/
theorem exists_domination_input_of_smooth [IsSmooth T.structureMorphism] :
    ∃ (B : Set T.toScheme) (hfinite : B.Finite)
      (hclosed : ∀ x ∈ B, IsClosed ({x} : Set T.toScheme)),
      B = targetNonisomorphismLocus (projection T t v ht hv) ∧
      IsNoetherian T.toScheme ∧ IsProper (projection T t v ht hv) ∧
      (∀ x ∈ B, RegularPoint T.toScheme x ∧
        ringKrullDim (T.toScheme.presheaf.stalk x) = 2) ∧
      IsIso (projection T t v ht hv ∣_ finiteClosedPointComplement T.toScheme B hfinite hclosed) ∧
      extension T t v ht hv ≫ v = projection T t v ht hv ≫ t ∧
      domainLift T t v ht hv ≫ projection T t v ht hv = (representative T t v ht hv).domain.ι ∧
      domainLift T t v ht hv ≫ extension T t v ht hv = (representative T t v ht hv).hom := by
  obtain ⟨B, hfinite, hclosed, hB, hNoetherian, hregular, hiso⟩ :=
    ProperBirationalSurface.exists_domination_input_of_smooth T (projection T t v ht hv)
      (projection_isBirationalScheme T t v ht hv)
  exact ⟨B, hfinite, hclosed, hB, hNoetherian, projection_isProper T t v ht hv,
    hregular, hiso, extension_comp T t v ht hv, domainLift_projection T t v ht hv,
    domainLift_extension T t v ht hv⟩

end KltDP.Geometry.SurfaceBirationalGraphDominationInput

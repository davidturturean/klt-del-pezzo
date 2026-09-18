import KltDP.Geometry.ProperSurjectionTargetIso
import KltDP.Geometry.ContractedCurvesFiberConstancy
import KltDP.Geometry.ProperBirationalStructureSheaf
import KltDP.Geometry.ProperGenericPointSurjective

/-!
# The original normal target is determined by its contracted prime curves

The original proper birational maps supply their quotient structure and
pushforward-O isomorphisms. Contracting the same actual prime curves
supplies point-fiber constancy by the separate geometric theorem. Actual
scheme descent then constructs the target isomorphism over the field.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.ProperBirationalTargetIso

theorem exists_iso_of_same_exceptional_curves
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X Y : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (f : S.toScheme ⟶ Y.toScheme)
    [IsProper π] [IsProper f]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hf : f ≫ Y.structureMorphism = S.structureMorphism)
    (hbirπ : IsBirationalScheme π) (hbirf : IsBirationalScheme f)
    (hsame : ∀ C : S.PrimeCurve, IsExceptionalCurve π C ↔ IsExceptionalCurve f C) :
    ∃ e : X.toScheme ≅ Y.toScheme,
      π ≫ e.hom = f ∧ f ≫ e.inv = π ∧
        e.hom ≫ Y.structureMorphism = X.structureMorphism := by
  letI : GenericPointPreserving π := ⟨hbirπ.map_genericPoint⟩
  letI : GenericPointPreserving f := ⟨hbirf.map_genericPoint⟩
  letI : Surjective π := surjective_of_proper_genericPointPreserving π
  letI : Surjective f := surjective_of_proper_genericPointPreserving f
  letI : IsIso π.c := ProperBirationalStructureSheaf.c_isIso π hbirπ X.normal
  letI : IsIso f.c := ProperBirationalStructureSheaf.c_isIso f hbirf Y.normal
  exact ProperSurjectionTargetIso.exists_iso_over_of_mutual_factors π f
    S.structureMorphism X.structureMorphism Y.structureMorphism hπ hf
    (ContractedCurvesFiberConstancy.factorsThrough_of_contracts π f hbirπ hf
      (fun C hC => (hsame C).mp hC))
    (ContractedCurvesFiberConstancy.factorsThrough_of_contracts f π hbirf hπ
      (fun C hC => (hsame C).mpr hC))

end KltDP.Geometry.ProperBirationalTargetIso
#check @KltDP.Geometry.ProperBirationalTargetIso.exists_iso_of_same_exceptional_curves
#print axioms KltDP.Geometry.ProperBirationalTargetIso.exists_iso_of_same_exceptional_curves

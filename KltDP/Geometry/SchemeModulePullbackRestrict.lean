import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Pullback commutes with restriction to open subschemes

For a scheme morphism `f : X ⟶ Y` and an open `U ⊆ Y`, pulling back along `f`
and then restricting to `f⁻¹U` agrees with restricting to `U` and then pulling
back along the restricted morphism `f ∣_ U : f⁻¹U ⟶ U`. Restriction to an open
subscheme is here the pullback along the open immersion `U.ι` (naturally
isomorphic to the accepted image-open restriction by `restrictionIsoPullback`).

The comparison is assembled from the accepted composite-pullback isomorphisms
and the pinned identity `(f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f`; it is compatible
with the accepted structure-module unit isomorphisms. Consequently a
trivialization of a module sheaf on `U` pulls back to a trivialization of the
pulled-back sheaf on `f⁻¹U`.

The identification of these pulled-back trivializations with the accepted
`over`-site trivializations of `O(D)` (`cartierEquationOverIso`) is not made
here; see `F03_RESTRICTION_ADAPTERS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- Pullback along `f` followed by restriction to `f⁻¹U` is restriction to `U`
followed by pullback along `f ∣_ U`. -/
def schemeModulePullbackRestrictIso :
    schemeModulePullback f ⋙ schemeModulePullback (f ⁻¹ᵁ U).ι ≅
      schemeModulePullback U.ι ⋙ schemeModulePullback (f ∣_ U) :=
  schemeModulePullbackCompIso (f ⁻¹ᵁ U).ι f ≪≫
    eqToIso (congrArg schemeModulePullback (morphismRestrict_ι f U).symm) ≪≫
    (schemeModulePullbackCompIso (f ∣_ U) U.ι).symm

/-- The object-level pullback–restriction comparison. -/
def schemeModulePullbackRestrictObjIso (M : Y.Modules) :
    (schemeModulePullback (f ⁻¹ᵁ U).ι).obj ((schemeModulePullback f).obj M) ≅
      (schemeModulePullback (f ∣_ U)).obj ((schemeModulePullback U.ι).obj M) :=
  (schemeModulePullbackRestrictIso f U).app M

/-- The comparison is compatible with the accepted structure-module unit isomorphisms. -/
theorem schemeModulePullbackRestrictIso_unit :
    (schemeModulePullbackRestrictIso f U).hom.app (_root_.SheafOfModules.unit Y.ringCatSheaf) ≫
      (schemeModulePullback (f ∣_ U)).map (schemeModulePullbackUnitIso U.ι).hom ≫
        (schemeModulePullbackUnitIso (f ∣_ U)).hom =
    (schemeModulePullback (f ⁻¹ᵁ U).ι).map (schemeModulePullbackUnitIso f).hom ≫
      (schemeModulePullbackUnitIso (f ⁻¹ᵁ U).ι).hom := by
  rw [← schemeModulePullbackCompIso_unit (f ∣_ U) U.ι,
    ← schemeModulePullbackCompIso_unit (f ⁻¹ᵁ U).ι f,
    ← schemeModulePullbackUnit_eqToIso (morphismRestrict_ι f U).symm]
  simp only [schemeModulePullbackRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]

/-- A trivialization of `M` on `U` pulls back to a trivialization of `f^*M` on `f⁻¹U`. -/
def schemeModulePullbackTrivialization (M : Y.Modules)
    (t : (schemeModulePullback U.ι).obj M ≅
      _root_.SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (schemeModulePullback (f ⁻¹ᵁ U).ι).obj ((schemeModulePullback f).obj M) ≅
      _root_.SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  schemeModulePullbackRestrictObjIso f U M ≪≫ (schemeModulePullback (f ∣_ U)).mapIso t ≪≫
    schemeModulePullbackUnitIso (f ∣_ U)

end KltDP.Geometry

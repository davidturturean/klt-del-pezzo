import KltDP.Geometry.PullbackSectionMap

/-!
# Coherence of the original compatible-family section pullback

The existing local adjunction-unit comparison proves the composition
identity on top sections, hence on the actual compatible families.
Equality of morphisms and a commuting square then transport these same
families through the original pullback comparison isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.PullbackSectionCoherence

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSheafSectionPowersPullback

variable {X Y Z Y' : Scheme.{u}}

/-- The original composition isomorphism preserves the actual compatible
family obtained by pulling the same section back twice. -/
theorem compIso_sectionsMap (h : Z ⟶ Y) (g : Y ⟶ X) (M : X.Modules) (s : M.sections) :
    _root_.SheafOfModules.sectionsMap ((schemeModulePullbackCompIso h g).hom.app M)
      (InvertibleSheafSectionPowersPullback.pullbackSection h ((schemeModulePullback g).obj M) (InvertibleSheafSectionPowersPullback.pullbackSection g M s)) =
        InvertibleSheafSectionPowersPullback.pullbackSection (h ≫ g) M s := by
  apply (schemeModuleSectionsEquivTop ((schemeModulePullback (h ≫ g)).obj M)).injective
  change ((schemeModulePullbackCompIso h g).hom.app M).val.app
    (op (h ⁻¹ᵁ (g ⁻¹ᵁ (⊤ : X.Opens))))
      ((InvertibleSheafSectionPowersPullback.pullbackSection h ((schemeModulePullback g).obj M) (InvertibleSheafSectionPowersPullback.pullbackSection g M s)).val
        (op (h ⁻¹ᵁ (g ⁻¹ᵁ (⊤ : X.Opens))))) =
          (InvertibleSheafSectionPowersPullback.pullbackSection (h ≫ g) M s).val (op ((h ≫ g) ⁻¹ᵁ (⊤ : X.Opens)))
  rw [InvertibleSheafSectionPowersPullback.pullbackSection_val, InvertibleSheafSectionPowersPullback.pullbackSection_val, InvertibleSheafSectionPowersPullback.pullbackSection_val]
  exact RationalTreePicard.compIso_hom_val_app_pulledSection g h M ⊤ (s.val (op ⊤))

/-- The inverse composition isomorphism returns the actual double
pullback of the original compatible section. -/
theorem compIso_inv_sectionsMap (h : Z ⟶ Y) (g : Y ⟶ X) (M : X.Modules) (s : M.sections) :
    _root_.SheafOfModules.sectionsMap ((schemeModulePullbackCompIso h g).inv.app M)
      (InvertibleSheafSectionPowersPullback.pullbackSection (h ≫ g) M s) =
        InvertibleSheafSectionPowersPullback.pullbackSection h ((schemeModulePullback g).obj M) (InvertibleSheafSectionPowersPullback.pullbackSection g M s) := by
  have hsection := congrArg
    (_root_.SheafOfModules.sectionsMap ((schemeModulePullbackCompIso h g).inv.app M))
    (compIso_sectionsMap h g M s)
  rw [← _root_.SheafOfModules.sectionsMap_comp,
    (schemeModulePullbackCompIso h g).hom_inv_id_app M,
    _root_.SheafOfModules.sectionsMap_id] at hsection
  exact hsection.symm

/-- The original equality-of-morphisms comparison preserves the actual
pullback of the original compatible family. -/
theorem eqToIso_sectionsMap {f g : Y ⟶ X} (e : f = g) (M : X.Modules) (s : M.sections) :
    _root_.SheafOfModules.sectionsMap
      (eqToIso (congrArg (fun m : Y ⟶ X => (schemeModulePullback m).obj M) e)).hom
      (InvertibleSheafSectionPowersPullback.pullbackSection f M s) = InvertibleSheafSectionPowersPullback.pullbackSection g M s := by
  subst g
  exact _root_.SheafOfModules.sectionsMap_id (InvertibleSheafSectionPowersPullback.pullbackSection f M s)

/-- The actual double-pullback isomorphism determined by an original
commuting square, oriented from its first composite to its second. -/
def commutingSquareIso (h : Z ⟶ Y) (g : Y ⟶ X) (h' : Z ⟶ Y') (g' : Y' ⟶ X)
    (e : h ≫ g = h' ≫ g') (M : X.Modules) :
    (schemeModulePullback h).obj ((schemeModulePullback g).obj M) ≅
      (schemeModulePullback h').obj ((schemeModulePullback g').obj M) :=
  (schemeModulePullbackCompIso h g).app M ≪≫
    eqToIso (congrArg (fun m : Z ⟶ X => (schemeModulePullback m).obj M) e) ≪≫
      ((schemeModulePullbackCompIso h' g').app M).symm

/-- The original commuting-square comparison sends the literal first
double pullback of a section to its literal second double pullback. -/
theorem commutingSquareIso_sectionsMap
    (h : Z ⟶ Y) (g : Y ⟶ X) (h' : Z ⟶ Y') (g' : Y' ⟶ X)
    (e : h ≫ g = h' ≫ g') (M : X.Modules) (s : M.sections) :
    _root_.SheafOfModules.sectionsMap (commutingSquareIso h g h' g' e M).hom
      (InvertibleSheafSectionPowersPullback.pullbackSection h ((schemeModulePullback g).obj M) (InvertibleSheafSectionPowersPullback.pullbackSection g M s)) =
        InvertibleSheafSectionPowersPullback.pullbackSection h' ((schemeModulePullback g').obj M) (InvertibleSheafSectionPowersPullback.pullbackSection g' M s) := by
  simp only [commutingSquareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    _root_.SheafOfModules.sectionsMap_comp]
  rw [compIso_sectionsMap h g M s, eqToIso_sectionsMap e M s,
    compIso_inv_sectionsMap h' g' M s]

end KltDP.Geometry.PullbackSectionCoherence

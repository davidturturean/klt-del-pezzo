import KltDP.Geometry.SchemeModulePullbackTensorUnit

/-!
# The original pullback/sheafification comparisons on unit sections

The accepted hom-equivalence normalizations give the actual section
formulas for both comparisons in the original scheme pullback tensor map.
These formulas use the original sheaf and presheaf adjunction units and
the actual inverse-image open of the scheme morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeModulePullbackSheafificationSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The original pullback/sheafification isomorphism carries an original
sheaf pullback-unit section to the two original presheaf/sheafification units. -/
theorem pullbackSheafification_unit (M : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) :
    (schemeModulePullbackSheafificationIso f M).hom.val.app (op (f ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)).app
        (op (f ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (schemeRingSheafHom f).val).unit.app M.val).app (op U) m) := by
  have h := schemeModulePullbackSheafificationIso_homEquiv f M
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)) (𝟙 _)
  simp only [Category.comp_id, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact congrArg (fun a => a.app (op U) m) h

/-- The other original comparison carries the original composite unit
to the original presheaf pullback unit followed by sheafification. -/
theorem sheafificationCompPullback_unit (P : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) :
    ((_root_.SheafOfModules.sheafificationCompPullback (schemeRingSheafHom f)).hom.app P).val.app
      (op (f ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction f).unit.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.val)).unit.app P).app (op U) p)) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P)).app
        (op (f ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (schemeRingSheafHom f).val).unit.app P).app (op U) p) := by
  have h := schemeModuleSheafificationCompPullback_homEquiv f P
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).obj
      ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P)) (𝟙 _)
  simp only [Category.comp_id, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact congrArg (fun a => a.app (op U) p) h

end KltDP.Geometry.SchemeModulePullbackSheafificationSections

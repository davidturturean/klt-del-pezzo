import KltDP.Geometry.LinearSystemCartierCoordinateRatios
import KltDP.Geometry.SchemeModuleOpenPullbackSections
import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.OpenImmersionFunctionField

/-!
# Original Cartier section values through the actual open pullback

The existing inverse restriction/pullback isomorphism sends the original
compatible pulled section to its original section on the image open.
The resulting Cartier rational value lies in the original ambient function
field. Scalars use the inverse of the original open function-field iso.
This comparison requires no extension of a section from the open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.OpenPullbackCartierSectionValues

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction SchemeModuleOpenPullbackSections OpenImmersionRational

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The actual inverse pullback comparison recovers a compatible
original section on every actual image open. -/
theorem inverse_restriction_compatibleSection (M : X.Modules) (s : M.sections)
    (V : Y.Opens) :
    ((restrictionIsoPullback f).inv.app M).val.app (op V)
        ((InvertibleSheafSectionPowersPullback.pullbackSection f M s).val (op V)) =
      s.val (op (f ''ᵁ V)) := by
  let ψ := (restrictionIsoPullback f).inv.app M
  let t := InvertibleSheafSectionPowersPullback.pullbackSection f M s
  have htop : ψ.val.app (op ⊤) (t.val (op ⊤)) = s.val (op (f ''ᵁ ⊤)) := by
    change ψ.val.app (op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (t.val (op (f ⁻¹ᵁ (⊤ : X.Opens)))) = _
    rw [InvertibleSheafSectionPowersPullback.pullbackSection_val]
    exact (restrictionIsoPullback_inv_app_pullbackSection f M ⊤
      (homOfLE le_top) (s.val (op ⊤))).trans (s.property (homOfLE le_top).op)
  have h := PresheafOfModules.naturality_apply ψ.val
    (homOfLE (le_top : V ≤ ⊤)).op (t.val (op ⊤))
  have ht : ((schemeModulePullback f).obj M).val.map
      (homOfLE (le_top : V ≤ ⊤)).op (t.val (op ⊤)) = t.val (op V) :=
    t.property (homOfLE (le_top : V ≤ ⊤)).op
  rw [ht, htop] at h
  exact h.trans (s.property ((f.opensFunctor.map (homOfLE (le_top : V ≤ ⊤))).op))

/-- The original additive section comparison retains its exact scalar
transport through the original inverse map on image-open sections. -/
theorem sectionsEquiv_smul_image (M : X.Modules) (V : Y.Opens) (a : Γ(Y, V))
    (s : ((schemeModulePullback f).obj M).val.obj (op V)) :
    sectionsEquiv f M V (f ''ᵁ V) rfl (a • s) =
      (f.appIso V).inv a • sectionsEquiv f M V (f ''ᵁ V) rfl s := by
  change (restrictionSectionsIso f M V).hom
      (((restrictionIsoPullback f).inv.app M).val.app (op V) (a • s)) = _
  simp only [map_smul, restriction_smul]
  rfl

variable [IsIntegral X] [IsIntegral Y] (D : CartierDivisor X)
  (V : Y.Opens) [Nonempty V]

/-- The actual pulled Cartier section, evaluated in the original
ambient function field via the actual image-open section comparison. -/
def rationalValue
    (s : ((schemeModulePullback f).obj (cartierDivisorModule X D)).val.obj (op V)) :
    X.functionField := by
  letI := nonempty_image f V
  exact rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
    (sectionsEquiv f (cartierDivisorModule X D) V (f ''ᵁ V) rfl s).val

theorem rationalValue_zero : rationalValue f D V 0 = 0 := by
  letI := nonempty_image f V
  change rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
    (sectionsEquiv f (cartierDivisorModule X D) V (f ''ᵁ V) rfl 0).val = 0
  rw [map_zero]
  exact map_zero (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V))

theorem rationalValue_injective : Function.Injective (rationalValue f D V) := by
  letI := nonempty_image f V
  intro s t h
  apply (sectionsEquiv f (cartierDivisorModule X D) V (f ''ᵁ V) rfl).injective
  apply Subtype.ext
  exact (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)).injective h

/-- A literal pulled compatible section has its original global
Cartier rational value, with no new extension or chosen representative. -/
theorem rationalValue_pullbackSection
    (s : (cartierDivisorInvertibleSheaf X D).obj.sections) :
    rationalValue f D V
        ((InvertibleSheafSectionPowersPullback.pullbackSection f
          (cartierDivisorModule X D) s).val (op V)) =
      cartierGlobalSectionRationalValue X D (s.val (op ⊤)) := by
  letI := nonempty_image f V
  change rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
      (((restrictionIsoPullback f).inv.app (cartierDivisorModule X D)).val.app (op V)
        ((InvertibleSheafSectionPowersPullback.pullbackSection f
          (cartierDivisorModule X D) s).val (op V))).val = _
  rw [inverse_restriction_compatibleSection]
  exact LinearSystemMorphism.cartier_section_value_on_open X D s (f ''ᵁ V)

/-- Its scalar action is exactly the inverse original open function-field
map applied to the original generic-point germ of the local scalar. -/
theorem rationalValue_smul (a : Γ(Y, V))
    (s : ((schemeModulePullback f).obj (cartierDivisorModule X D)).val.obj (op V)) :
    rationalValue f D V (a • s) =
      (functionFieldIso f).inv (Y.germToFunctionField V a) * rationalValue f D V s := by
  letI := nonempty_image f V
  have ha : X.germToFunctionField (f ''ᵁ V) ((f.appIso V).inv a) =
      (functionFieldIso f).inv (Y.germToFunctionField V a) := by
    apply (ConcreteCategory.bijective_of_isIso (functionFieldIso f).hom).1
    rw [functionFieldIso_image_germ, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  unfold rationalValue
  rw [sectionsEquiv_smul_image]
  change rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
      ((f.appIso V).inv a •
        (sectionsEquiv f (cartierDivisorModule X D) V (f ''ᵁ V) rfl s).val) = _
  rw [map_smul, Algebra.smul_def]
  exact congrArg (fun z => z *
    rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
      (sectionsEquiv f (cartierDivisorModule X D) V (f ''ᵁ V) rfl s).val) ha

end KltDP.Geometry.OpenPullbackCartierSectionValues

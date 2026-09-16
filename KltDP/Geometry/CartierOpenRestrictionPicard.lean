import KltDP.Geometry.CartierModuleOpenRestriction
import KltDP.Geometry.PicardOpenRestriction
import KltDP.Geometry.CartierPrincipalPicard

/-!
# Actual O(D) and Picard compatibility for open restriction

The constructed restriction map O_X(D)|Y→O_Y(D|Y) is bijective on every
nonempty subopen of an actual equation chart. Its coordinates are the
actual section-ring isomorphism followed by a/g on each side. Empty
subopens use their zero modules. The existing local-bijectivity theorem
and actual sheafification counits yield an isomorphism of actual sheaves.

Consequently the actual Picard restriction homomorphism sends the class
of O_X(D) to the class of O_Y(D|Y), for the Cartier restriction already
constructed from the quotient sheaf. No representative or comparison
isomorphism is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

local instance (Z : Scheme.{u}) (U : Z.Opens) : CommRing Γ(Z, U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj (op U)))

/-- On an actual image equation chart the constructed map is bijective,
by the existing rank-one coordinates and the actual section-ring iso. -/
theorem cartierModuleRestrictionHom_app_bijective_of_image_equation
    (D : CartierDivisor X) (V : Y.Opens) [Nonempty V] (g : X.functionFieldˣ)
    (hg : letI := nonempty_image f V
      cartierEquationClassHom X (f ''ᵁ V) (Additive.ofMul g) =
        (cartierDivisorSheaf X).val.map
          (homOfLE (show f ''ᵁ V ≤ ⊤ from le_top)).op D) :
    Function.Bijective ((cartierModuleRestrictionHom f D).val.app (op V)) := by
  letI := nonempty_image f V
  constructor
  · intro s t hst
    apply Subtype.ext
    apply (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)).injective
    apply (functionFieldIso f).commRingCatIsoToRingEquiv.injective
    have hvalue := congrArg
      (fun q : (cartierDivisorModule Y (cartierRestrictionHom f D)).val.obj (op V) =>
        rationalFunctionModuleSectionsEquiv Y V q.val) hst
    simpa only [cartierModuleRestrictionHom_field] using hvalue
  · intro t
    let gY := Units.map (functionFieldIso f).hom.hom.toMonoidHom g
    let hgY := cartierRestriction_globalEquation_image f D V g hg
    let eY := cartierEquationSectionEquiv Y (cartierRestrictionHom f D) V gY hgY
    obtain ⟨a, rfl⟩ := eY.surjective t
    let s := cartierEquationSectionEquiv X D (f ''ᵁ V) g hg ((f.appIso V).inv a)
    refine ⟨s, ?_⟩
    apply Subtype.ext
    apply (rationalFunctionModuleSectionsEquiv Y V).injective
    change rationalFunctionModuleSectionsEquiv Y V
        ((cartierModuleRestrictionHom f D).val.app (op V) s).val =
      rationalFunctionModuleSectionsEquiv Y V
        (cartierEquationSectionEquiv Y (cartierRestrictionHom f D) V gY hgY a).val
    rw [cartierModuleRestrictionHom_field]
    dsimp only [s]
    rw [cartierEquationSectionEquiv_apply_field, cartierEquationSectionEquiv_apply_field,
      map_mul, functionFieldIso_image_germ, Iso.inv_hom_id_apply]
    rfl

/-- The actual map is locally bijective on the actual inverse-image
equation-chart cover, including every empty subopen. -/
theorem cartierModuleRestrictionHom_mem_sheafificationW (D : CartierDivisor X) :
    PresheafOfModules.sheafificationW (𝟙 Y.ringCatSheaf.val)
      (cartierModuleRestrictionHom f D).val := by
  apply PresheafOfModules.sheafificationW_of_bijective_on_coversTop
    (R := Y.ringCatSheaf) (cartierModuleRestrictionHom f D).val
    (fun c : CartierEquationChart X D => f ⁻¹ᵁ c.openSet)
    (cartierPreimageEquationCharts_coversTop f D)
  intro c V i
  classical
  by_cases hV : Nonempty V
  · letI := hV
    letI := nonempty_image f V
    have himage : f ''ᵁ V ≤ c.openSet := by
      rintro x ⟨y, hy, rfl⟩
      exact i.le hy
    exact cartierModuleRestrictionHom_app_bijective_of_image_equation f D V c.equation
      (cartierGlobalEquation_restrict X D (U := c.openSet) (V := f ''ᵁ V)
        (homOfLE himage) c.equation c.represents)
  · letI := sectionRing_subsingleton_of_empty V hV
    letI : Subsingleton
        (((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D)).val.obj
          (op V)) := Module.subsingleton Γ(Y, V) _
    letI : Subsingleton
        ((cartierDivisorModule Y (cartierRestrictionHom f D)).val.obj (op V)) :=
      Module.subsingleton Γ(Y, V) _
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun t => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The actual restriction of O_X(D) is isomorphic to O_Y(D restricted),
by the proved local bijectivity and actual sheafification counits. -/
def cartierModuleRestrictionIso (D : CartierDivisor X) :
    (SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D) ≅
      cartierDivisorModule Y (cartierRestrictionHom f D) := by
  letI : IsIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
      (cartierModuleRestrictionHom f D).val) :=
    (PresheafOfModules.sheafificationW_iff (𝟙 Y.ringCatSheaf.val) _).mp
      (cartierModuleRestrictionHom_mem_sheafificationW f D)
  exact (PresheafOfModules.sheafificationForgetIso Y.ringCatSheaf
      ((SchemeModuleRestriction.restriction f).obj (cartierDivisorModule X D))).symm ≪≫
    asIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map
      (cartierModuleRestrictionHom f D).val) ≪≫
    PresheafOfModules.sheafificationForgetIso Y.ringCatSheaf
      (cartierDivisorModule Y (cartierRestrictionHom f D))

/-- Restriction of the existing actual Picard class agrees with the
class of the actual Cartier restriction constructed from the unit quotient. -/
theorem picardRestrictionHom_cartierPicardClass (D : CartierDivisor X) :
    SchemeModuleRestriction.picardRestrictionHom f (cartierPicardClass X D) =
      cartierPicardClass Y (cartierRestrictionHom f D) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  apply Units.ext
  change (SchemeModuleRestriction.picardRestrictionHom f (cartierPicardClass X D) :
      Skeleton Y.Modules) = (cartierPicardClass Y (cartierRestrictionHom f D) :
      Skeleton Y.Modules)
  rw [SchemeModuleRestriction.picardRestrictionHom_val, cartierPicardClass_val,
    cartierPicardClass_val, SchemeModuleRestriction.restrictionClassHom_toSkeleton]
  exact Quotient.sound ⟨cartierModuleRestrictionIso f D⟩

end KltDP.Geometry.OpenImmersionRational

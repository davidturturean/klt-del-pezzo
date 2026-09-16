import KltDP.Geometry.ModuleOpenRestriction
import KltDP.Geometry.OpenImmersionFunctionField
import KltDP.Geometry.RationalFunctionModule

/-!
# Actual open restriction of the rational-function module

The actual restriction of the rational-function module is isomorphic to
the rational-function module on the source. The section map is the actual
generic-stalk field isomorphism, with scalar linearity supplied by the
proved section/germ square. Empty opens use their actual zero modules.

This comparison concerns the existing sheaves and their existing scalar
actions. It is the ambient comparison for the subsequent O(D) submodules;
it assumes no Cartier or Picard compatibility.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

local instance (Z : Scheme.{u}) (U : Z.Opens) : CommRing Γ(Z, U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj (op U)))

/-- The actual section ring on an empty open is a subsingleton. -/
theorem sectionRing_subsingleton_of_empty (V : Y.Opens) (hV : ¬ Nonempty V) :
    Subsingleton Γ(Y, V) := by
  have hbot : V = ⊥ := by
    apply SetLike.ext
    intro y
    exact ⟨fun hy => (hV ⟨⟨y, hy⟩⟩).elim, fun hy => hy.elim⟩
  subst V
  exact CommRingCat.subsingleton_of_isTerminal Y.sheaf.isTerminalOfEmpty

/-- The actual rational-field transport, linear for the scalar action
of the source section ring on the restricted module. -/
def rationalRestrictionSectionEquivNonempty (V : Y.Opens) [Nonempty V] :
    ((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj (op V)
      ≃ₗ[Γ(Y, V)] (rationalFunctionModule Y).val.obj (op V) := by
  letI := nonempty_image f V
  refine {
    (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)).toAddEquiv.trans
      ((functionFieldIso f).commRingCatIsoToRingEquiv.toAddEquiv.trans
        (rationalFunctionModuleSectionsEquiv Y V).symm.toAddEquiv) with
    map_smul' := ?_ }
  intro a s
  let s' : (rationalFunctionModule X).val.obj (op (f ''ᵁ V)) := s
  apply (rationalFunctionModuleSectionsEquiv Y V).injective
  change rationalFunctionModuleSectionsEquiv Y V
      ((rationalFunctionModuleSectionsEquiv Y V).symm
        ((functionFieldIso f).hom
          (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V)
            ((f.appIso V).inv a • s')))) =
    rationalFunctionModuleSectionsEquiv Y V
      (a • (rationalFunctionModuleSectionsEquiv Y V).symm
        ((functionFieldIso f).hom
          (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s')))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul,
    LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  change (functionFieldIso f).hom
      (X.germToFunctionField (f ''ᵁ V) ((f.appIso V).inv a) *
        rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s') =
    Y.germToFunctionField V a *
      (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s')
  rw [map_mul, functionFieldIso_image_germ, Iso.inv_hom_id_apply]

/-- The same actual linear isomorphism on all source opens. -/
def rationalRestrictionSectionEquiv (V : Y.Opens) :
    ((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj (op V)
      ≃ₗ[Γ(Y, V)] (rationalFunctionModule Y).val.obj (op V) := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    exact rationalRestrictionSectionEquivNonempty f V
  · letI := sectionRing_subsingleton_of_empty V hV
    letI : Subsingleton
        (((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj
          (op V)) := Module.subsingleton Γ(Y, V) _
    letI : Subsingleton ((rationalFunctionModule Y).val.obj (op V)) :=
      Module.subsingleton Γ(Y, V) _
    exact LinearEquiv.ofSubsingleton _ _

/-- Under the actual nonempty-open identifications, the module map is
exactly the actual generic-stalk field map. -/
theorem rationalRestrictionSectionEquiv_field (V : Y.Opens) [Nonempty V]
    (s : ((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj
      (op V)) :
    letI := nonempty_image f V
    rationalFunctionModuleSectionsEquiv Y V (rationalRestrictionSectionEquiv f V s) =
      (functionFieldIso f).hom (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s) := by
  classical
  letI := nonempty_image f V
  simp only [rationalRestrictionSectionEquiv, dif_pos (inferInstance : Nonempty V)]
  change rationalFunctionModuleSectionsEquiv Y V
      ((rationalFunctionModuleSectionsEquiv Y V).symm
        ((functionFieldIso f).hom
          (rationalFunctionModuleSectionsEquiv X (f ''ᵁ V) s))) = _
  exact LinearEquiv.apply_symm_apply _ _

set_option maxHeartbeats 800000 in
/-- The actual section comparisons commute with all actual restriction
maps. Empty target opens are handled by their zero modules. -/
theorem rationalRestrictionSectionEquiv_naturality {V W : Y.Opens} (i : W ⟶ V)
    (s : ((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.obj
      (op V)) :
    rationalRestrictionSectionEquiv f W
        (((SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X)).val.map
          i.op s) =
      (rationalFunctionModule Y).val.map i.op (rationalRestrictionSectionEquiv f V s) := by
  classical
  by_cases hW : Nonempty W
  · letI := hW
    letI : Nonempty V := by
      obtain ⟨⟨y, hy⟩⟩ := hW
      exact ⟨⟨y, i.le hy⟩⟩
    letI := nonempty_image f W
    letI := nonempty_image f V
    apply (rationalFunctionModuleSectionsEquiv Y W).injective
    rw [rationalRestrictionSectionEquiv_field, rationalFunctionModuleSectionsEquiv_naturality,
      rationalRestrictionSectionEquiv_field]
    let s' : (rationalFunctionModule X).val.obj (op (f ''ᵁ V)) := s
    exact congrArg (fun z : X.functionField => (functionFieldIso f).hom z)
      (rationalFunctionModuleSectionsEquiv_naturality X (f.opensFunctor.map i) s')
  · letI := sectionRing_subsingleton_of_empty W hW
    letI : Subsingleton ((rationalFunctionModule Y).val.obj (op W)) :=
      Module.subsingleton Γ(Y, W) _
    exact Subsingleton.elim _ _

/-- The actual module-sheaf comparison with its proved section
linearity and naturality. -/
def rationalRestrictionIso :
    (SchemeModuleRestriction.restriction f).obj (rationalFunctionModule X) ≅
      rationalFunctionModule Y :=
  (_root_.SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).preimageIso
    (_root_.PresheafOfModules.isoMk
      (fun V => (rationalRestrictionSectionEquiv f V.unop).toModuleIso)
      (fun {_ _} i => by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        exact rationalRestrictionSectionEquiv_naturality f i.unop s))

end KltDP.Geometry.OpenImmersionRational

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Topology.Sheaves.Functors
import KltDP.Compatibility.UnitsSheaf

/-!
# The actual sheaf of rational functions on an integral scheme

The sheaf is the direct image of the structure sheaf of the spectrum of the
original scheme's function field, under its canonical generic-point
morphism. Thus it is already a sheaf on every open, including the empty
open. On each nonempty open its sections are canonically the function field.
The structural map from the original structure sheaf agrees with the
existing germ-to-function-field map under this isomorphism.

Regular and rational units are obtained by applying the existing units
functor to the actual sheaves. Their quotient sheaf, its global Cartier
sections, associated invertible sheaves, and Picard comparison remain later
constructions. No gluing or comparison statement is supplied as a field.

All sheaf and scheme operations here are reused from the pinned Mathlib
sources (Apache-2.0), especially `Sheaf.pushforward`, `fromSpecStalk_app`,
`preimage_eq_top_of_closedPoint_mem`, and `Scheme.ΓSpecIso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

variable (X : Scheme.{u}) [IsIntegral X]

/-- The whole open of an integral scheme contains its actual generic point. -/
instance integralScheme_top_open_nonempty : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The actual morphism from the spectrum of the original function field
to the original integral scheme, obtained from its generic-point stalk. -/
abbrev genericPointMorphism : Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

@[simp]
theorem genericPointMorphism_base (p : Spec X.functionField) :
    (genericPointMorphism X).base p = genericPoint X := by
  have hp : p = IsLocalRing.closedPoint X.functionField :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  rw [hp]
  exact Scheme.fromSpecStalk_closedPoint

/-- Every nonempty open contains the generic point of the integral scheme. -/
theorem genericPoint_mem_nonempty_open (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

/-- The preimage of a nonempty open under the actual generic-point
morphism is the whole spectrum of the function field. -/
theorem genericPointMorphism_preimage_nonempty (U : X.Opens) [Nonempty U] :
    genericPointMorphism X ⁻¹ᵁ U = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  simpa only [genericPointMorphism_base] using genericPoint_mem_nonempty_open X U

/-- The actual sheaf of rational functions, constructed by sheaf
pushforward from the spectrum of the actual function field. -/
def rationalFunctionSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat (genericPointMorphism X).base).obj
    (Spec X.functionField).sheaf

@[simp]
theorem rationalFunctionSheaf_obj (U : X.Opens) :
    (rationalFunctionSheaf X).val.obj (op U) =
      Γ(Spec X.functionField, genericPointMorphism X ⁻¹ᵁ U) := rfl

/-- The empty-open section ring is the actual terminal ring supplied by
the sheaf condition. In particular it is not the nontrivial function field. -/
theorem rationalFunctionSheaf_empty_subsingleton :
    Subsingleton ((rationalFunctionSheaf X).val.obj (op ⊥)) :=
  CommRingCat.subsingleton_of_isTerminal (rationalFunctionSheaf X).isTerminalOfEmpty

/-- The actual structural map into rational functions, induced by the
generic-point morphism of schemes. -/
def structureToRationalFunctions : X.sheaf ⟶ rationalFunctionSheaf X :=
  CategoryTheory.Sheaf.Hom.mk (genericPointMorphism X).c

@[simp]
theorem structureToRationalFunctions_app (U : X.Opens) :
    (structureToRationalFunctions X).val.app (op U) =
      (genericPointMorphism X).app U := rfl

/-- Sections on a nonempty open are the actual function field, with
the canonical affine global-section isomorphism and proved preimage. -/
def rationalFunctionSectionsIso (U : X.Opens) [Nonempty U] :
    (rationalFunctionSheaf X).val.obj (op U) ≅ X.functionField :=
  (Spec X.functionField).presheaf.mapIso
      (eqToIso (genericPointMorphism_preimage_nonempty X U).symm).op ≪≫
    Scheme.ΓSpecIso X.functionField

/-- Under the canonical field identifications, restriction between
nonempty opens is the identity on the original function field. -/
theorem rationalFunctionSectionsIso_naturality
    {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) :
    (rationalFunctionSheaf X).val.map (homOfLE h).op ≫
        (rationalFunctionSectionsIso X V).hom =
      (rationalFunctionSectionsIso X U).hom := by
  change (Spec X.functionField).presheaf.map
      ((Opens.map (genericPointMorphism X).base).map (homOfLE h)).op ≫
        ((Spec X.functionField).presheaf.map
          (eqToHom (genericPointMorphism_preimage_nonempty X V).symm).op ≫
            (Scheme.ΓSpecIso X.functionField).hom) =
      (Spec X.functionField).presheaf.map
        (eqToHom (genericPointMorphism_preimage_nonempty X U).symm).op ≫
          (Scheme.ΓSpecIso X.functionField).hom
  rw [← Functor.map_comp_assoc]
  have hcomp :
      ((Opens.map (genericPointMorphism X).base).map (homOfLE h)).op ≫
        (eqToHom (genericPointMorphism_preimage_nonempty X V).symm).op =
      (eqToHom (genericPointMorphism_preimage_nonempty X U).symm).op :=
    Subsingleton.elim _ _
  rw [hcomp]

/-- The canonical structure-sheaf map is exactly the existing germ into
the function field under the nonempty-open section isomorphism. -/
theorem structureToRationalFunctions_app_comp_sectionsIso
    (U : X.Opens) [Nonempty U] :
    (structureToRationalFunctions X).val.app (op U) ≫
        (rationalFunctionSectionsIso X U).hom = X.germToFunctionField U := by
  change (X.fromSpecStalk (genericPoint X)).app U ≫
      ((Spec X.functionField).presheaf.map
        (eqToHom (genericPointMorphism_preimage_nonempty X U).symm).op ≫
          (Scheme.ΓSpecIso X.functionField).hom) = X.germToFunctionField U
  rw [Scheme.fromSpecStalk_app (genericPoint_mem_nonempty_open X U)]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  have hcomp :
      (homOfLE le_top : genericPointMorphism X ⁻¹ᵁ U ⟶ ⊤).op ≫
        (eqToHom (genericPointMorphism_preimage_nonempty X U).symm).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [hcomp, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id,
    Category.comp_id]

/-- The structure sheaf embeds sectionwise in rational functions. The
empty-open case uses its actual zero ring; it is not assigned the field. -/
theorem structureToRationalFunctions_app_injective (U : X.Opens) :
    Function.Injective ((structureToRationalFunctions X).val.app (op U)) := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    intro a b hab
    apply X.germToFunctionField_injective U
    have hmap := structureToRationalFunctions_app_comp_sectionsIso X U
    calc
      X.germToFunctionField U a =
          (rationalFunctionSectionsIso X U).hom
            ((structureToRationalFunctions X).val.app (op U) a) :=
        (congrArg (fun q : Γ(X, U) ⟶ X.functionField => q a) hmap).symm
      _ = (rationalFunctionSectionsIso X U).hom
          ((structureToRationalFunctions X).val.app (op U) b) := congrArg _ hab
      _ = X.germToFunctionField U b :=
        congrArg (fun q : Γ(X, U) ⟶ X.functionField => q b) hmap
  · have hbot : U = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    subst U
    letI : Subsingleton (X.sheaf.val.obj (op ⊥)) :=
      CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
    intro a b _
    exact Subsingleton.elim a b

/-- The sheaf of actual units of the original structure sheaf. -/
def regularUnitsSheaf : TopCat.Sheaf CommGrp.{u} X :=
  KltDP.Sheaf.unitsSheaf X.sheaf

/-- The sheaf of units of the actual rational-function sheaf. -/
def rationalUnitsSheaf : TopCat.Sheaf CommGrp.{u} X :=
  KltDP.Sheaf.unitsSheaf (rationalFunctionSheaf X)

/-- The actual homomorphism of unit sheaves induced by the structural
map into rational functions. -/
def regularToRationalUnits : regularUnitsSheaf X ⟶ rationalUnitsSheaf X :=
  KltDP.Sheaf.unitsSheafMap (structureToRationalFunctions X)

/-- Nonempty-open rational unit sections are the actual units of the
original function field, via the constructed ring-section isomorphism. -/
def rationalUnitSectionsIso (U : X.Opens) [Nonempty U] :
    (rationalUnitsSheaf X).val.obj (op U) ≅ CommGrp.of X.functionFieldˣ :=
  KltDP.Sheaf.commRingUnitsFunctor.mapIso (rationalFunctionSectionsIso X U)

/-- On every nonempty open, the regular-to-rational unit map is exactly
the map on units of the original germ-to-function-field homomorphism. -/
theorem regularToRationalUnits_app_comp_sectionsIso (U : X.Opens) [Nonempty U] :
    (regularToRationalUnits X).val.app (op U) ≫ (rationalUnitSectionsIso X U).hom =
      CommGrp.ofHom (Units.map (X.germToFunctionField U).hom.toMonoidHom) := by
  change KltDP.Sheaf.commRingUnitsFunctor.map
      ((structureToRationalFunctions X).val.app (op U)) ≫
        KltDP.Sheaf.commRingUnitsFunctor.map (rationalFunctionSectionsIso X U).hom = _
  rw [← Functor.map_comp, structureToRationalFunctions_app_comp_sectionsIso]
  rfl

/-- The actual regular units embed sectionwise into rational units. -/
theorem regularToRationalUnits_app_injective (U : X.Opens) :
    Function.Injective ((regularToRationalUnits X).val.app (op U)) := by
  change Function.Injective
    (Units.map ((structureToRationalFunctions X).val.app (op U)).hom.toMonoidHom)
  exact Units.map_injective (structureToRationalFunctions_app_injective X U)

end KltDP.Geometry

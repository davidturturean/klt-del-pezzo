/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel,
  Jujian Zhang, Weihong Xu, Andrew Yang, Brian Nugent

Adapted from official Mathlib Tilde.lean:127–140 at
79d0395a1825a6264ad5d269e35e60537518955e. The actual project restriction
and original base-ring section actions replace the later module API.
-/
import KltDP.Geometry.AffineModuleGlobalSections
import KltDP.Geometry.ModuleOpenRestriction

/-!
# Original base-ring scalars under affine open restriction

For an actual affine open immersion Spec S → Spec R, its original
ΓSpec/appIso square identifies the restricted S-action with the original
R-action. The section comparison uses the existing restriction's actual
additive section map; both scalar actions and all restriction maps remain
the original ones.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineModuleTilde

open SchemeModuleRestriction

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))]

/-- The original ΓSpec maps and actual open-immersion section isomorphism commute. -/
theorem restrictionScalar_square (V : (Spec (.of S)).Opens) :
    CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
      (Spec (.of S)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op ≫
      ((Spec.map (CommRingCat.ofHom φ)).appIso V).inv =
    (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).presheaf.map
      (homOfLE (show Spec.map (CommRingCat.ofHom φ) ''ᵁ V ≤ ⊤ from le_top)).op := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom φ)).appTop
    ((Spec (.of S)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op)
    ((Spec.map (CommRingCat.ofHom φ)).appIso V).inv]
  change (Scheme.ΓSpecIso (.of R)).inv ≫
    (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ V le_top ≫
      ((Spec.map (CommRingCat.ofHom φ)).appIso V).inv = _
  rw [Scheme.Hom.appLE_appIso_inv]

variable (M : (Spec (.of R)).Modules)

local instance restrictionOriginalSectionModule (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R), U) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule

/-- The original additive restriction comparison preserves the canonical
R-action, when the restricted module is acted on through φ. -/
theorem restrictionSections_smul (V : (Spec (.of S)).Opens) (r : R)
    (s : sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :
    (restrictionSectionsIso (Spec.map (CommRingCat.ofHom φ)) M V).hom (φ r • s) =
      r • (show sectionModule M (Spec.map (CommRingCat.ofHom φ) ''ᵁ V) from
        (restrictionSectionsIso (Spec.map (CommRingCat.ofHom φ)) M V).hom s) := by
  letI : Module Γ(Spec (.of R), Spec.map (CommRingCat.ofHom φ) ''ᵁ V)
      (sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :=
    (M.val.obj (op (Spec.map (CommRingCat.ofHom φ) ''ᵁ V))).isModule
  have hr := CategoryTheory.congr_fun (restrictionScalar_square φ V) r
  simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at hr
  change ((Spec.map (CommRingCat.ofHom φ)).appIso V).inv
      ((Spec (.of S)).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        ((Scheme.ΓSpecIso (.of S)).inv (φ r))) •
        (s : M.val.obj (op (Spec.map (CommRingCat.ofHom φ) ''ᵁ V))) =
    (Spec (.of R)).presheaf.map
      (homOfLE (show Spec.map (CommRingCat.ofHom φ) ''ᵁ V ≤ ⊤ from le_top)).op
      ((Scheme.ΓSpecIso (.of R)).inv r) •
        (s : M.val.obj (op (Spec.map (CommRingCat.ofHom φ) ''ᵁ V)))
  exact congrArg (fun a : Γ(Spec (.of R), Spec.map (CommRingCat.ofHom φ) ''ᵁ V) =>
    a • (s : M.val.obj (op (Spec.map (CommRingCat.ofHom φ) ''ᵁ V)))) hr

/-- The original section comparison, as an additive equivalence. -/
def restrictionSectionsAddEquiv (V : (Spec (.of S)).Opens) :
    sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V ≃+
      sectionModule M (Spec.map (CommRingCat.ofHom φ) ''ᵁ V) :=
  (restrictionSectionsIso (Spec.map (CommRingCat.ofHom φ)) M V).addCommGroupIsoToAddEquiv

/-- Naturality uses exactly the original maps on the actual image opens. -/
theorem restrictionSectionsAddEquiv_naturality {V W : (Spec (.of S)).Opens} (h : W ≤ V)
    (s : sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :
    restrictionSectionsAddEquiv φ M W
        (sectionRestrict ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) h s) =
      sectionRestrict M ((Spec.map (CommRingCat.ofHom φ)).image_le_image_of_le h)
        (restrictionSectionsAddEquiv φ M V s) := rfl

/-- Scalar compatibility in the additive-equivalence form used by denominator descent. -/
theorem restrictionSectionsAddEquiv_smul (V : (Spec (.of S)).Opens) (r : R)
    (s : sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :
    restrictionSectionsAddEquiv φ M V (φ r • s) =
      r • restrictionSectionsAddEquiv φ M V s :=
  restrictionSections_smul φ M V r s

/-- Identify the actual image open with a specified equal open. -/
def restrictionSectionsAddEquivOfEq (V : (Spec (.of S)).Opens)
    (U : (Spec (.of R)).Opens)
    (h : Spec.map (CommRingCat.ofHom φ) ''ᵁ V = U) :
    sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V ≃+
      sectionModule M U := by
  subst U
  exact restrictionSectionsAddEquiv φ M V

/-- Equality of the image open does not change the original scalar comparison. -/
theorem restrictionSectionsAddEquivOfEq_smul (V : (Spec (.of S)).Opens)
    (U : (Spec (.of R)).Opens)
    (h : Spec.map (CommRingCat.ofHom φ) ''ᵁ V = U) (r : R)
    (s : sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :
    restrictionSectionsAddEquivOfEq φ M V U h (φ r • s) =
      r • restrictionSectionsAddEquivOfEq φ M V U h s := by
  subst U
  exact restrictionSectionsAddEquiv_smul φ M V r s

/-- The equal-image presentation still commutes with the original restriction maps. -/
theorem restrictionSectionsAddEquivOfEq_naturality
    {V W : (Spec (.of S)).Opens} {U T : (Spec (.of R)).Opens}
    (hV : Spec.map (CommRingCat.ofHom φ) ''ᵁ V = U)
    (hW : Spec.map (CommRingCat.ofHom φ) ''ᵁ W = T) (h : W ≤ V) (h' : T ≤ U)
    (s : sectionModule ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) V) :
    restrictionSectionsAddEquivOfEq φ M W T hW
        (sectionRestrict ((restriction (Spec.map (CommRingCat.ofHom φ))).obj M) h s) =
      sectionRestrict M h' (restrictionSectionsAddEquivOfEq φ M V U hV s) := by
  subst U
  subst T
  exact restrictionSectionsAddEquiv_naturality φ M h s

end KltDP.Geometry.AffineModuleTilde

import KltDP.Geometry.OpenImmersionRationalSheaf
import KltDP.Geometry.CartierDivisorSheaf

/-!
# Actual Cartier restriction along an open immersion

The actual regular- and rational-unit sheaf maps form a commutative
square. The cokernel universal property therefore gives a map from the
actual Cartier divisor sheaf into the actual pushforward of the Cartier
divisor sheaf on the source. Global sections give Cartier restriction.

The local-equation formula below proves that this construction transports
an equation through the actual function-field isomorphism. No global
representative is assumed, and Cartier divisors are not replaced by a
pointwise quotient or by their Picard classes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- Transport of actual regular unit sheaves. -/
def regularUnitsPullback : regularUnitsSheaf X ⟶
    (TopCat.Sheaf.pushforward CommGrp f.base).obj (regularUnitsSheaf Y) :=
  KltDP.Sheaf.unitsSheafMap (structurePullback f)

/-- Transport of actual rational unit sheaves. -/
def rationalUnitsPullback : rationalUnitsSheaf X ⟶
    (TopCat.Sheaf.pushforward CommGrp f.base).obj (rationalUnitsSheaf Y) :=
  KltDP.Sheaf.unitsSheafMap (rationalPullback f)

/-- The same actual regular-unit map in additive notation. -/
def regularUnitsPullbackAdd : regularUnitsAddSheaf X ⟶
    (TopCat.Sheaf.pushforward AddCommGrp f.base).obj (regularUnitsAddSheaf Y) :=
  (additiveGroupSheafFunctor X).map (regularUnitsPullback f)

/-- The same actual rational-unit map in additive notation. -/
def rationalUnitsPullbackAdd : rationalUnitsAddSheaf X ⟶
    (TopCat.Sheaf.pushforward AddCommGrp f.base).obj (rationalUnitsAddSheaf Y) :=
  (additiveGroupSheafFunctor X).map (rationalUnitsPullback f)

/-- The actual regular-to-rational unit square commutes. -/
theorem regularToRationalUnitsAdd_pullback :
    regularToRationalUnitsAdd X ≫ rationalUnitsPullbackAdd f =
      regularUnitsPullbackAdd f ≫
        (TopCat.Sheaf.pushforward AddCommGrp f.base).map (regularToRationalUnitsAdd Y) := by
  let F := KltDP.Sheaf.unitsSheafFunctor (Opens.grothendieckTopology X) ⋙
    additiveGroupSheafFunctor X
  change F.map (structureToRationalFunctions X) ≫ F.map (rationalPullback f) =
    F.map (structurePullback f) ≫ F.map
      ((TopCat.Sheaf.pushforward CommRingCat f.base).map (structureToRationalFunctions Y))
  rw [← F.map_comp, ← F.map_comp, structureToRationalFunctions_pullback]

/-- The rational equation map into the target Cartier sheaf kills the
actual regular-unit sheaf. -/
theorem cartierPullback_condition :
    regularToRationalUnitsAdd X ≫
      (rationalUnitsPullbackAdd f ≫
        (TopCat.Sheaf.pushforward AddCommGrp f.base).map (rationalUnitsToCartier Y)) = 0 := by
  rw [← Category.assoc, regularToRationalUnitsAdd_pullback, Category.assoc,
    ← (TopCat.Sheaf.pushforward AddCommGrp f.base).map_comp,
    regularToRationalUnitsAdd_comp_quotient]
  have hz : (TopCat.Sheaf.pushforward AddCommGrp f.base).map
      (0 : regularUnitsAddSheaf Y ⟶ cartierDivisorSheaf Y) = 0 := by
    apply CategoryTheory.Sheaf.Hom.ext
    apply NatTrans.ext
    funext U
    rfl
  rw [hz, comp_zero]

/-- The actual Cartier sheaf map, obtained by the actual cokernel
universal property from the proved square of unit sheaves. -/
def cartierPullback : cartierDivisorSheaf X ⟶
    (TopCat.Sheaf.pushforward AddCommGrp f.base).obj (cartierDivisorSheaf Y) :=
  cokernel.desc (regularToRationalUnitsAdd X)
    (rationalUnitsPullbackAdd f ≫
      (TopCat.Sheaf.pushforward AddCommGrp f.base).map (rationalUnitsToCartier Y))
    (cartierPullback_condition f)

/-- The constructed Cartier map agrees with the actual rational
equation map before passing to the quotient. -/
theorem rationalUnitsToCartier_pullback :
    rationalUnitsToCartier X ≫ cartierPullback f =
      rationalUnitsPullbackAdd f ≫
        (TopCat.Sheaf.pushforward AddCommGrp f.base).map (rationalUnitsToCartier Y) :=
  cokernel.π_desc _ _ _

/-- Rational-unit sections transform by the actual generic-stalk field
map under their canonical nonempty-open identifications. -/
theorem rationalUnitsPullbackAdd_app_comp_sectionsIso (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    (rationalUnitsPullbackAdd f).val.app (op U) ≫
        (rationalUnitsAddSectionsIso Y (f ⁻¹ᵁ U)).hom =
      (rationalUnitsAddSectionsIso X U).hom ≫
        AddCommGrp.ofHom (Units.map (functionFieldIso f).hom.hom.toMonoidHom).toAdditive := by
  let F := KltDP.Sheaf.commRingUnitsFunctor ⋙ commGroupAddCommGroupEquivalence.functor
  change F.map (rationalPullbackApp f U) ≫
      F.map (rationalFunctionSectionsIso Y (f ⁻¹ᵁ U)).hom =
    F.map (rationalFunctionSectionsIso X U).hom ≫ F.map (functionFieldIso f).hom
  rw [← F.map_comp, rationalPullbackApp_comp_sectionsIso, F.map_comp]

/-- The actual Cartier map sends a local rational equation to its
actual transported equation. -/
theorem cartierPullback_equation (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (g : X.functionFieldˣ) :
    (cartierPullback f).val.app (op U) (cartierEquationClassHom X U (Additive.ofMul g)) =
      cartierEquationClassHom Y (f ⁻¹ᵁ U)
        (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) := by
  have hinv : (rationalUnitsAddSectionsIso X U).inv ≫
      (rationalUnitsPullbackAdd f).val.app (op U) =
    AddCommGrp.ofHom (Units.map (functionFieldIso f).hom.hom.toMonoidHom).toAdditive ≫
      (rationalUnitsAddSectionsIso Y (f ⁻¹ᵁ U)).inv := by
    apply (cancel_mono (rationalUnitsAddSectionsIso Y (f ⁻¹ᵁ U)).hom).1
    rw [Category.assoc, rationalUnitsPullbackAdd_app_comp_sectionsIso,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hfac := congrArg (fun q : rationalUnitsAddSheaf X ⟶
      (TopCat.Sheaf.pushforward AddCommGrp f.base).obj (cartierDivisorSheaf Y) =>
        q.val.app (op U)) (rationalUnitsToCartier_pullback f)
  change (cartierPullback f).val.app (op U)
      ((rationalUnitsToCartier X).val.app (op U)
        ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul g))) = _
  have heq := ConcreteCategory.congr_hom hfac
    ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul g))
  calc
    _ = (rationalUnitsToCartier Y).val.app (op (f ⁻¹ᵁ U))
        ((rationalUnitsPullbackAdd f).val.app (op U)
          ((rationalUnitsAddSectionsIso X U).inv (Additive.ofMul g))) := heq
    _ = _ := congrArg ((rationalUnitsToCartier Y).val.app (op (f ⁻¹ᵁ U)))
      (ConcreteCategory.congr_hom hinv (Additive.ofMul g))

/-- Restriction of actual global Cartier sections. The inverse image
of the whole open is definitionally the whole source open. -/
def cartierRestrictionHom : CartierDivisor X →+ CartierDivisor Y :=
  ((cartierPullback f).val.app (op ⊤)).hom

/-- Actual principal Cartier divisors restrict to the principal divisor
of the actual transported rational function. -/
theorem cartierRestrictionHom_principal (g : X.functionFieldˣ) :
    cartierRestrictionHom f (principalCartierDivisorHom X (Additive.ofMul g)) =
      principalCartierDivisorHom Y
        (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) := by
  letI : Nonempty (f ⁻¹ᵁ (⊤ : X.Opens)) := ⟨⟨genericPoint Y, trivial⟩⟩
  exact cartierPullback_equation f ⊤ g

end KltDP.Geometry.OpenImmersionRational

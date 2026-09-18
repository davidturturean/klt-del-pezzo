import KltDP.Geometry.DominantRationalFunctionSheaf
import KltDP.Geometry.CartierDivisorSheaf

/-!
The original dominant scheme map and function-field homomorphism give a
commutative square of the actual regular and rational unit sheaves. The
existing sheaf cokernel supplies pullback of arbitrary signed Cartier
divisors. The local-equation and principal formulas use the same original
functionFieldMap on actual rational units. No effective-equation or
function-field-isomorphism hypothesis is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.DominantCartierPullback

variable {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
variable (π : X ⟶ Y) [GenericPointPreserving π]

/-- Transport of actual regular unit sheaves. -/
def regularUnitsPullback : regularUnitsSheaf Y ⟶
    (TopCat.Sheaf.pushforward CommGrp π.base).obj (regularUnitsSheaf X) :=
  KltDP.Sheaf.unitsSheafMap (structurePullback π)

/-- Transport of actual rational unit sheaves. -/
def rationalUnitsPullback : rationalUnitsSheaf Y ⟶
    (TopCat.Sheaf.pushforward CommGrp π.base).obj (rationalUnitsSheaf X) :=
  KltDP.Sheaf.unitsSheafMap (rationalPullback π)

/-- The same actual regular-unit map in additive notation. -/
def regularUnitsPullbackAdd : regularUnitsAddSheaf Y ⟶
    (TopCat.Sheaf.pushforward AddCommGrp π.base).obj (regularUnitsAddSheaf X) :=
  (additiveGroupSheafFunctor Y).map (regularUnitsPullback π)

/-- The same actual rational-unit map in additive notation. -/
def rationalUnitsPullbackAdd : rationalUnitsAddSheaf Y ⟶
    (TopCat.Sheaf.pushforward AddCommGrp π.base).obj (rationalUnitsAddSheaf X) :=
  (additiveGroupSheafFunctor Y).map (rationalUnitsPullback π)

/-- The actual regular-to-rational unit square commutes. -/
theorem regularToRationalUnitsAdd_pullback :
    regularToRationalUnitsAdd Y ≫ rationalUnitsPullbackAdd π =
      regularUnitsPullbackAdd π ≫
        (TopCat.Sheaf.pushforward AddCommGrp π.base).map (regularToRationalUnitsAdd X) := by
  let F := KltDP.Sheaf.unitsSheafFunctor (Opens.grothendieckTopology Y) ⋙
    additiveGroupSheafFunctor Y
  change F.map (structureToRationalFunctions Y) ≫ F.map (rationalPullback π) =
    F.map (structurePullback π) ≫ F.map
      ((TopCat.Sheaf.pushforward CommRingCat π.base).map (structureToRationalFunctions X))
  rw [← F.map_comp, ← F.map_comp, structureToRationalFunctions_pullback]

/-- The rational equation map into the target Cartier sheaf kills the
actual regular-unit sheaf. -/
theorem cartierPullback_condition :
    regularToRationalUnitsAdd Y ≫
      (rationalUnitsPullbackAdd π ≫
        (TopCat.Sheaf.pushforward AddCommGrp π.base).map (rationalUnitsToCartier X)) = 0 := by
  rw [← Category.assoc, regularToRationalUnitsAdd_pullback, Category.assoc,
    ← (TopCat.Sheaf.pushforward AddCommGrp π.base).map_comp,
    regularToRationalUnitsAdd_comp_quotient]
  have hz : (TopCat.Sheaf.pushforward AddCommGrp π.base).map
      (0 : regularUnitsAddSheaf X ⟶ cartierDivisorSheaf X) = 0 := by
    apply CategoryTheory.Sheaf.Hom.ext
    apply NatTrans.ext
    funext U
    rfl
  rw [hz, comp_zero]

/-- The actual Cartier sheaf map, obtained by the actual cokernel
universal property from the proved square of unit sheaves. -/
def cartierPullback : cartierDivisorSheaf Y ⟶
    (TopCat.Sheaf.pushforward AddCommGrp π.base).obj (cartierDivisorSheaf X) :=
  cokernel.desc (regularToRationalUnitsAdd Y)
    (rationalUnitsPullbackAdd π ≫
      (TopCat.Sheaf.pushforward AddCommGrp π.base).map (rationalUnitsToCartier X))
    (cartierPullback_condition π)

/-- The constructed Cartier map agrees with the actual rational
equation map before passing to the quotient. -/
theorem rationalUnitsToCartier_pullback :
    rationalUnitsToCartier Y ≫ cartierPullback π =
      rationalUnitsPullbackAdd π ≫
        (TopCat.Sheaf.pushforward AddCommGrp π.base).map (rationalUnitsToCartier X) :=
  cokernel.π_desc _ _ _

/-- Rational-unit sections transform by the actual generic-stalk field
map under their canonical nonempty-open identifications. -/
theorem rationalUnitsPullbackAdd_app_comp_sectionsIso (U : Y.Opens)
    [Nonempty U] :
    (rationalUnitsPullbackAdd π).val.app (op U) ≫
        (rationalUnitsAddSectionsIso X (π ⁻¹ᵁ U)).hom =
      (rationalUnitsAddSectionsIso Y U).hom ≫
        AddCommGrp.ofHom (Units.map (functionFieldMap π).hom.toMonoidHom).toAdditive := by
  let F := KltDP.Sheaf.commRingUnitsFunctor ⋙ commGroupAddCommGroupEquivalence.functor
  change F.map (rationalPullbackApp π U) ≫
      F.map (rationalFunctionSectionsIso X (π ⁻¹ᵁ U)).hom =
    F.map (rationalFunctionSectionsIso Y U).hom ≫ F.map (functionFieldMap π)
  rw [← F.map_comp, rationalPullbackApp_comp_sectionsIso, F.map_comp]

/-- The actual Cartier map sends a local rational equation to its
actual transported equation. -/
theorem cartierPullback_equation (U : Y.Opens)
    [Nonempty U] (g : Y.functionFieldˣ) :
    (cartierPullback π).val.app (op U) (cartierEquationClassHom Y U (Additive.ofMul g)) =
      cartierEquationClassHom X (π ⁻¹ᵁ U)
        (Additive.ofMul (Units.map (functionFieldMap π).hom.toMonoidHom g)) := by
  have hinv : (rationalUnitsAddSectionsIso Y U).inv ≫
      (rationalUnitsPullbackAdd π).val.app (op U) =
    AddCommGrp.ofHom (Units.map (functionFieldMap π).hom.toMonoidHom).toAdditive ≫
      (rationalUnitsAddSectionsIso X (π ⁻¹ᵁ U)).inv := by
    apply (cancel_mono (rationalUnitsAddSectionsIso X (π ⁻¹ᵁ U)).hom).1
    rw [Category.assoc, rationalUnitsPullbackAdd_app_comp_sectionsIso,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hfac := congrArg (fun q : rationalUnitsAddSheaf Y ⟶
      (TopCat.Sheaf.pushforward AddCommGrp π.base).obj (cartierDivisorSheaf X) =>
        q.val.app (op U)) (rationalUnitsToCartier_pullback π)
  change (cartierPullback π).val.app (op U)
      ((rationalUnitsToCartier Y).val.app (op U)
        ((rationalUnitsAddSectionsIso Y U).inv (Additive.ofMul g))) = _
  have heq := ConcreteCategory.congr_hom hfac
    ((rationalUnitsAddSectionsIso Y U).inv (Additive.ofMul g))
  calc
    _ = (rationalUnitsToCartier X).val.app (op (π ⁻¹ᵁ U))
        ((rationalUnitsPullbackAdd π).val.app (op U)
          ((rationalUnitsAddSectionsIso Y U).inv (Additive.ofMul g))) := heq
    _ = _ := congrArg ((rationalUnitsToCartier X).val.app (op (π ⁻¹ᵁ U)))
      (ConcreteCategory.congr_hom hinv (Additive.ofMul g))

/-- Pullback of arbitrary signed actual global Cartier sections. The inverse image
of the whole open is definitionally the whole source open. -/
def pullbackHom : CartierDivisor Y →+ CartierDivisor X :=
  ((cartierPullback π).val.app (op ⊤)).hom

/-- Actual principal Cartier divisors pull back to the principal divisor
of the actual transported rational function. -/
theorem pullbackHom_principal (g : Y.functionFieldˣ) :
    pullbackHom π (principalCartierDivisorHom Y (Additive.ofMul g)) =
      principalCartierDivisorHom X
        (Additive.ofMul (Units.map (functionFieldMap π).hom.toMonoidHom g)) := by
  letI : Nonempty (π ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨genericPoint X, trivial⟩⟩
  exact cartierPullback_equation π ⊤ g

end KltDP.Geometry.DominantCartierPullback

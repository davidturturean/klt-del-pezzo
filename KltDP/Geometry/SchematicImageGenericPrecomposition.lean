import KltDP.Geometry.CartierDivisorPullback
import KltDP.Geometry.SchematicImageOpenBaseChange

/-!
# Original schematic images after generic-point-preserving precomposition

The original field-map/germ square makes every section map injective.
Consequently such precomposition preserves the actual kernel ideal
sheaf and its original quotient-glued image, without a quasi-compactness
or an assumed scheme-theoretic density premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.SchematicImageGenericPrecomposition

attribute [local instance] Types.instFunLike Types.instConcreteCategory
open SchematicImageGlued SchematicImageOpenBaseChange

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (h : X ⟶ Y) [GenericPointPreserving h]

/-- The original section map is injective on every original target open. -/
theorem app_injective (V : Y.Opens) : Function.Injective (h.app V) := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    intro a b hab
    apply Y.germToFunctionField_injective V
    apply (functionFieldMap h).hom.injective
    rw [functionFieldMap_germ, functionFieldMap_germ, hab]
  · have hbot : V = ⊥ := by
      apply SetLike.ext
      intro x
      exact ⟨fun hx => (hV ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    subst V
    letI : Subsingleton (Y.sheaf.val.obj (op ⊥)) :=
      CommRingCat.subsingleton_of_isTerminal Y.sheaf.isTerminalOfEmpty
    intro a b _
    exact Subsingleton.elim a b

/-- The original ideal-sheaf kernel is unchanged by this actual precomposition. -/
theorem ker_precompose (g : Y ⟶ Z) : (h ≫ g).ker = g.ker := by
  unfold Scheme.Hom.ker
  apply congrArg Scheme.IdealSheafData.ofIdeals
  funext V
  rw [Scheme.comp_app, CommRingCat.hom_comp]
  exact RingHom.ker_comp_of_injective (g.app V).hom (app_injective h (g ⁻¹ᵁ V))

/-- The canonical equality of the original kernels gives the actual image isomorphism. -/
def imageIso (g : Y ⟶ Z) : image (h ≫ g) ≅ image g :=
  imageIsoOfKerEq (h ≫ g) g (ker_precompose h g)

@[reassoc]
theorem imageIso_hom_inclusion (g : Y ⟶ Z) :
    (imageIso h g).hom ≫ inclusion g = inclusion (h ≫ g) :=
  imageIsoOfKerEq_hom_inclusion (h ≫ g) g (ker_precompose h g)

/-- The isomorphism identifies the two original factorizations, over the original target. -/
theorem toImage_comp_imageIso (g : Y ⟶ Z) :
    toImage (h ≫ g) ≫ (imageIso h g).hom = h ≫ toImage g := by
  apply (cancel_mono (inclusion g)).mp
  rw [Category.assoc, imageIso_hom_inclusion, toImage_inclusion,
    Category.assoc, toImage_inclusion]

end KltDP.Geometry.SchematicImageGenericPrecomposition

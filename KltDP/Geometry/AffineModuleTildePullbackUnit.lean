import KltDP.Geometry.AffineModuleTildePullbackComp
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.SchemeModulePullbackTensorUnit
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Unit and linear-coordinate normalization for the original affine pullback

The actual tilde/pullback comparison commutes with the original tilde-unit
and scheme-pullback-unit isomorphisms. Naturality then identifies the two
actual pullbacks of every linear coordinate. The proof uses the existing
adjunction normalizations on original constant sections, with no chosen
comparison or compatibility witness as an input.

The tensor evaluation square and global conormal gluing are separate results.
All constructions used here are proved in the accepted pinned sources;
the source bindings and remaining square are recorded in the reuse dossier.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineModuleTildePullbackUnit

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The original scalar-extension unit, with the ring-map action retained. -/
def scalarUnitIso (φ : A →+* B) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of A A) ≅ ModuleCat.of B B := by
  letI : Algebra A B := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso

/-- Its value on the original pure tensors. -/
theorem scalarUnitIso_tmul (φ : A →+* B) (b : B) (a : A) :
    (scalarUnitIso φ).hom (b ⊗ₜ[A,φ] a) = φ a * b := rfl

/-- The original tilde-unit map sends every constant section to the
same original structure-sheaf section. -/
theorem unitIso_hom_toOpen (R : Type u) [CommRing R]
    (U : (Spec (CommRingCat.of R)).Opens) (r : R) :
    (AffineModuleTilde.unitIso R).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (ModuleCat.of R R) U r) =
      StructureSheaf.toOpen R U r := by
  apply Subtype.ext
  funext p
  change AffineModuleTilde.unitFiberEquiv R p.val
      (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl R r) =
    algebraMap R (Localization.AtPrime p.val.asIdeal) r
  exact AffineModuleTilde.unitFiberEquiv_mkLinearMap R p.val r

private theorem affineHomEquiv_apply (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of A)).Modules) (a : M.tilde ⟶ N) (m : M) :
    (AffineModuleTilde.adjunction A).homEquiv M N a m =
      a.val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m) := by
  change (AffineModuleTilde.globalSectionsFunctor A).map a
    ((AffineModuleTilde.unitNatIso A).hom.app M m) = _
  simpa only [AffineModuleTilde.unitNatIso_hom_app] using
    AffineModuleTilde.globalSectionsFunctor_map_apply a (ModuleCat.Tilde.toOpen M ⊤ m)

/-- The original affine pullback and the original scheme unit comparison
give exactly the same morphism of actual module sheaves. -/
theorem pullback_unit (φ : A →+* B) :
    (AffineModuleTilde.pullbackIso φ (ModuleCat.of A A)).hom ≫
        AffineModuleTilde.map (scalarUnitIso φ).hom ≫ (AffineModuleTilde.unitIso B).hom =
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map
        (AffineModuleTilde.unitIso A).hom ≫
          (schemeModulePullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom := by
  apply ((schemeModulePullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom φ))).homEquiv _ _).injective
  apply ((AffineModuleTilde.adjunction A).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rw [AffineModuleTilde.pullbackIso_homEquiv_apply]
  change _ = (AffineModuleTilde.adjunction A).homEquiv _ _
    ((schemeModulePullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom φ))).homEquiv _ _
        ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map
          (AffineModuleTilde.unitIso A).hom ≫
            schemeModulePullbackUnitHom (Spec.map (CommRingCat.ofHom φ)))) a
  rw [Adjunction.homEquiv_naturality_left,
    schemeModulePullbackUnitHom_adjunction', affineHomEquiv_apply]
  change (AffineModuleTilde.unitIso B).hom.val.app (op ⊤)
      ((AffineModuleTilde.map (scalarUnitIso φ).hom).val.app (op ⊤)
        (ModuleCat.Tilde.toOpen ((ModuleCat.extendScalars φ).obj (ModuleCat.of A A)) ⊤
          ((1 : B) ⊗ₜ[A,φ] a))) =
    (structureToPushforwardUnit (Spec.map (CommRingCat.ofHom φ))).val.app (op ⊤)
      ((AffineModuleTilde.unitIso A).hom.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (ModuleCat.of A A) ⊤ a))
  rw [AffineModuleTilde.map_app_toOpen, scalarUnitIso_tmul, mul_one,
    unitIso_hom_toOpen, unitIso_hom_toOpen, structureToPushforwardUnit_app]
  exact (AffineModuleTilde.specMap_globalScalar φ a).symm

/-- Naturality retains the original module homomorphism and scalar extension. -/
theorem pullback_natural (φ : A →+* B) {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map (AffineModuleTilde.map g) ≫
        (AffineModuleTilde.pullbackIso φ N).hom =
      (AffineModuleTilde.pullbackIso φ M).hom ≫
        AffineModuleTilde.map ((ModuleCat.extendScalars φ).map g) :=
  (AffineModuleTilde.pullbackTildeIso φ).hom.naturality g

/-- The original scalar extension of a linear coordinate, followed by
the actual scalar-extension unit. -/
def extendedCoordinate (φ : A →+* B) {M : ModuleCat.{u} A}
    (g : M ⟶ ModuleCat.of A A) :
    (ModuleCat.extendScalars φ).obj M ⟶ ModuleCat.of B B :=
  (ModuleCat.extendScalars φ).map g ≫ (scalarUnitIso φ).hom

/-- Pulling back an actual tilde linear coordinate agrees with extending
that coordinate and using the original unit comparisons. -/
theorem pullback_coordinate (φ : A →+* B) {M : ModuleCat.{u} A}
    (g : M ⟶ ModuleCat.of A A) :
    (AffineModuleTilde.pullbackIso φ M).hom ≫
        AffineModuleTilde.map (extendedCoordinate φ g) ≫ (AffineModuleTilde.unitIso B).hom =
      (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).map
          (AffineModuleTilde.map g ≫ (AffineModuleTilde.unitIso A).hom) ≫
        (schemeModulePullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom := by
  rw [extendedCoordinate, AffineModuleTilde.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (AffineModuleTilde.pullbackIso φ M).hom
    (AffineModuleTilde.map ((ModuleCat.extendScalars φ).map g)), ← pullback_natural φ g]
  rw [Category.assoc, pullback_unit, ← Category.assoc, ← Functor.map_comp]

end KltDP.Geometry.AffineModuleTildePullbackUnit

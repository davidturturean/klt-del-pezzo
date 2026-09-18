import KltDP.Geometry.AffineProductKaehlerProjectionMaps
import KltDP.Geometry.AffineModuleTildeTransposeNormalization
import KltDP.Geometry.SchemeKaehlerPullbackMap

/-!
# The affine product inclusions are the original scheme differential maps

The original affine adjunction and the spanning universal differentials
identify the maps without any open-immersion assumption. The only target
transport is the proved equality of the original Spec structure morphisms.
This is the map normalization needed before gluing the product comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineProductKaehler

open AffineKaehlerTildeDerivation SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private def transportedDifferential {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g) :
    (schemeModulePullback j).obj (baseRingSheaf f) ⟶ baseRingSheaf g :=
  SchemeKaehlerPullbackMap.map f j ≫ eqToHom (congrArg baseRingSheaf hg)

private theorem transportedDifferential_unit_d {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g)
    (U : X.Opens) (s : Γ(X, U)) :
    (transportedDifferential f j g hg).val.app (op (j ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction j).unit.app
          (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      (baseRingDerivation g).d (j.app U s) := by
  subst g
  exact SchemeKaehlerPullbackMap.map_unit_d f j U s

/-- Reassociate only the original scheme map and its equality transport. -/
private theorem transportedDifferential_comp {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g)
    (N : Y.Modules) (e : baseRingSheaf g ⟶ N) :
    transportedDifferential f j g hg ≫ e =
      SchemeKaehlerPullbackMap.map f j ≫ eqToHom (congrArg baseRingSheaf hg) ≫ e := by
  subst g
  simp only [transportedDifferential, eqToHom_refl, Category.comp_id, Category.id_comp]

section AffineNormalization

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

private theorem differentialIso_inv_toOpen (a : A) :
    (AffineKaehlerTildeLocalization.iso R A).inv.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen (differentialModule R A) ⊤
          (KaehlerDifferential.D R A a)) =
      (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
        (StructureSheaf.toOpen A ⊤ a) := by
  let e := AffineKaehlerTildeLocalization.iso R A
  let s := (baseRingDerivation
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d (StructureSheaf.toOpen A ⊤ a)
  have h := congrArg (fun z => e.inv.val.app (op ⊤) z)
    ((AffineKaehlerTildeLocalization.iso_d R A ⊤ (StructureSheaf.toOpen A ⊤ a)).trans
      (sectionD_toOpen R A ⊤ a))
  exact h.symm.trans (congrArg (fun z :
    baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))) =>
    z.val.app (op ⊤) s) e.hom_inv_id)

variable (hbase :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)))

private def affineOriginalForwardMap
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ⟶ N :=
  transportedDifferential
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) hbase ≫ e

private def affineOriginalMap
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (differentialModule R A).tilde ⟶ N :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
    (AffineKaehlerTildeLocalization.iso R A).inv ≫
      affineOriginalForwardMap R A B hbase N e

/-- Evaluate the already proved original unit formula at the actual top open. -/
private theorem affineOriginalForwardMap_unit_d
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N) (a : A) :
    (affineOriginalForwardMap R A B hbase N e).val.app (op ⊤)
        (((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app
            (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))).val.app
          (op ⊤) ((baseRingDerivation
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
              (StructureSheaf.toOpen A ⊤ a))) =
      e.val.app (op ⊤)
        ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
          (StructureSheaf.toOpen B ⊤ (algebraMap A B a))) := by
  have h := congrArg (e.val.app (op ⊤))
    (transportedDifferential_unit_d
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) hbase ⊤
      (StructureSheaf.toOpen A ⊤ a))
  exact h.trans (congrArg (fun s => e.val.app (op ⊤)
    ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d s))
      (AffineModuleTilde.specMap_globalScalar (algebraMap A B) a))

/-- Apply the compiled transpose normalization to the two separately proved images. -/
private def affineOriginalMap_transpose_d
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N) (a : A) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq
    (algebraMap A B) (differentialModule R A)
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))) N
    (AffineKaehlerTildeLocalization.iso R A).inv
    (affineOriginalForwardMap R A B hbase N e) (KaehlerDifferential.D R A a)
    ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
      (StructureSheaf.toOpen A ⊤ a)) _ (differentialIso_inv_toOpen R A a)
    (affineOriginalForwardMap_unit_d R A B hbase N e a)

private theorem affineOriginalMap_eq
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (differentialModule R A).tilde ⟶ N)
    (hd : ∀ a : A,
      (AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
          (differentialModule R A) N t (KaehlerDifferential.D R A a) =
        e.val.app (op ⊤)
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
            (StructureSheaf.toOpen B ⊤ (algebraMap A B a)))) :
    t = affineOriginalMap R A B hbase N e := by
  apply ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
    (differentialModule R A) N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
  intro a
  exact (hd a).trans (affineOriginalMap_transpose_d R A B hbase N e a).symm

private theorem sourceIso_cancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q : C} {T : D} (e : P ≅ Q)
    (a : F.obj Q ⟶ T) (b : F.obj P ⟶ T)
    (h : a = F.map e.inv ≫ b) : F.map e.hom ≫ a = b := by
  rw [h, Iso.map_hom_inv_id_assoc]

/-- Cancel the original affine source comparison before exposing target transport. -/
private def comparison_cancel_source
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (differentialModule R A).tilde ⟶ N)
    (hd : ∀ a : A,
      (AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
          (differentialModule R A) N t (KaehlerDifferential.D R A a) =
        e.val.app (op ⊤)
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
            (StructureSheaf.toOpen B ⊤ (algebraMap A B a)))) :=
  sourceIso_cancel
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (AffineKaehlerTildeLocalization.iso R A) t (affineOriginalForwardMap R A B hbase N e)
    (affineOriginalMap_eq R A B hbase N e t hd)

/-- Normalize the original target composition independently of source cancellation. -/
private theorem affineOriginalForwardMap_comp
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N) :
    affineOriginalForwardMap R A B hbase N e =
      SchemeKaehlerPullbackMap.map
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫
        eqToHom (congrArg baseRingSheaf hbase) ≫ e :=
  transportedDifferential_comp
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) hbase N e

/-- Compose the two separately checked original-map equalities. -/
private def comparison_eq_original_proof
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (differentialModule R A).tilde ⟶ N)
    (hd : ∀ a : A,
      (AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
          (differentialModule R A) N t (KaehlerDifferential.D R A a) =
        e.val.app (op ⊤)
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
            (StructureSheaf.toOpen B ⊤ (algebraMap A B a)))) :=
  (comparison_cancel_source R A B hbase N e t hd).trans
    (affineOriginalForwardMap_comp R A B hbase N e)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

/-- Original differential generators determine the actual pulled affine map.
The transparent statement is the full original equality inferred above;
this avoids checking an expanded copy of the same categorical objects. -/
theorem comparison_eq_original
    (N : (Spec (CommRingCat.of B)).Modules)
    (e : baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶ N)
    (t : (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      (differentialModule R A).tilde ⟶ N)
    (hd : ∀ a : A,
      (AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
          (differentialModule R A) N t (KaehlerDifferential.D R A a) =
        e.val.app (op ⊤)
          ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
            (StructureSheaf.toOpen B ⊤ (algebraMap A B a)))) :
    statementOf (comparison_eq_original_proof R A B hbase N e t hd) :=
  comparison_eq_original_proof R A B hbase N e t hd

end AffineNormalization

section Product

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The first comparison is the original projection differential followed by the
normalized original product splitting. -/
theorem leftComparison_eq_original :
    leftComparison R S T =
      SchemeKaehlerPullbackMap.map
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) (firstProjection R S T) ≫
        eqToHom (congrArg baseRingSheaf (firstProjection_comp R S T)) ≫
          (iso R S T).hom :=
  comparison_eq_original R S (S ⊗[R] T) (firstProjection_comp R S T)
    (splitModule R S T).tilde (iso R S T).hom (leftTildeInclusion R S T)
    (leftTildeInclusion_transpose_D R S T)

/-- The second comparison retains the exact second-projection structure-map transport. -/
theorem rightComparison_eq_original :
    rightComparison R S T =
      SchemeKaehlerPullbackMap.map
          (Spec.map (CommRingCat.ofHom (algebraMap R T))) (secondProjection R S T) ≫
        eqToHom (congrArg baseRingSheaf (secondProjection_comp R S T)) ≫
          (iso R S T).hom :=
  comparison_eq_original R T (S ⊗[R] T) (secondProjection_comp R S T)
    (splitModule R S T).tilde (iso R S T).hom (rightTildeInclusion R S T)
    (rightTildeInclusion_transpose_D R S T)

/-- The first affine differential map is the pre-existing original scheme map. -/
theorem leftDifferentialMap_eq_original :
    leftDifferentialMap R S T =
      SchemeKaehlerPullbackMap.map
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) (firstProjection R S T) ≫
        eqToHom (congrArg baseRingSheaf (firstProjection_comp R S T)) := by
  rw [leftDifferentialMap, leftComparison_eq_original]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The second affine differential map is the pre-existing original scheme map. -/
theorem rightDifferentialMap_eq_original :
    rightDifferentialMap R S T =
      SchemeKaehlerPullbackMap.map
          (Spec.map (CommRingCat.ofHom (algebraMap R T))) (secondProjection R S T) ≫
        eqToHom (congrArg baseRingSheaf (secondProjection_comp R S T)) := by
  rw [rightDifferentialMap, rightComparison_eq_original]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Product

end KltDP.Geometry.AffineProductKaehler

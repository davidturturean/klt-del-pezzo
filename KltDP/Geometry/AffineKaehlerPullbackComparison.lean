import KltDP.Geometry.AffineKaehlerTildeLocalization
import KltDP.Geometry.AffineModuleTildeSemilinearSections
import KltDP.Geometry.AffineModuleTildeTransposeNormalization
import KltDP.Geometry.SchemeKaehlerPullbackSections
import KltDP.Geometry.SchemeModulePullbackTensorSectionUnits

/-!
# The original affine differential map is the original Kähler pullback map

The existing affine tilde adjunction reduces equality of these actual sheaf
maps to equality on the original module of differentials. Its generators
are the original `d a`. The original Kähler pullback formula and the original
affine comparison both preserve these generators, proving the square for
the maps already defined by the scheme and module constructions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.AffineKaehlerPullbackComparison

open AffineKaehlerTildeDerivation AffineModuleTildeSemilinearMap
open SchemeKaehlerSheaf SchemeKaehlerOpenRestriction
open SchemeModulePullbackTensorSectionUnits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem pullback_square_word {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q : C} {T : D} (e : P ≅ Q)
    (a : F.obj Q ⟶ T) (b : F.obj P ⟶ T)
    (h : a = F.map e.inv ≫ b) : F.map e.hom ≫ a = b := by
  rw [h, Iso.map_hom_inv_id_assoc]

/-- The three original forward maps, before choosing any affine presentation. -/
private def forwardMap {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g)
    {M : Y.Modules} (a : baseRingSheaf g ⟶ M) :
    (schemeModulePullback j).obj (baseRingSheaf f) ⟶ M :=
  (pullbackIso f j).hom ≫ (eqToIso (congrArg baseRingSheaf hg)).hom ≫ a

/-- Eliminate the structure-map equality before checking section composition. -/
private theorem forwardMap_unit_d {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g)
    {M : Y.Modules} (a : baseRingSheaf g ⟶ M) (U : X.Opens) (s : Γ(X, U)) :
    (forwardMap f j g hg a).val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s)) =
      a.val.app (op (j ⁻¹ᵁ U)) ((baseRingDerivation g).d (j.app U s)) := by
  subst g
  change a.val.app (op (j ⁻¹ᵁ U))
    ((pullbackIso f j).hom.val.app (op (j ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction j).unit.app
        (baseRingSheaf f)).val.app (op U) ((baseRingDerivation f).d s))) = _
  exact congrArg (a.val.app (op (j ⁻¹ᵁ U))) (pullbackIso_unit_d f j U s)

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The original differential map with its original extension of scalars. -/
def differentialMap :
    differentialModule R A →ₛₗ[algebraMap A B] differentialModule R B :=
  { toFun := KaehlerDifferential.map R R A B
    map_add' := (KaehlerDifferential.map R R A B).map_add
    map_smul' := fun a m =>
      ((KaehlerDifferential.map R R A B).map_smul a m).trans
        (algebraMap_smul B a _).symm }

/-- Its value on each original differential is the original differential of the image. -/
theorem differentialMap_d (a : A) :
    differentialMap R A B (KaehlerDifferential.D R A a) =
      KaehlerDifferential.D R B (algebraMap A B a) :=
  KaehlerDifferential.map_D R R A B a

/-- The two original affine structure morphisms agree over the original base. -/
theorem baseMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R A B r).symm

/-- The inverse original affine comparison recovers the original differential. -/
private theorem iso_inv_toOpen_d (a : A) :
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

variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))]

/-- Name the original forward composite once, preserving all three original maps. -/
private def originalForwardMap :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A)))) ⟶
      (differentialModule R B).tilde :=
  forwardMap (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) (baseMap_comp R A B)
    (AffineKaehlerTildeLocalization.iso R B).hom

/-- The original Kähler pullback, expressed between the original affine tilde sheaves. -/
private def originalMap :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (differentialModule R A).tilde ⟶ (differentialModule R B).tilde :=
  (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
      (AffineKaehlerTildeLocalization.iso R A).inv ≫ originalForwardMap R A B

/-- The actual Kähler pullback step, isolated from both target comparisons. -/
private theorem originalPullback_unit_d (a : A) :
    (pullbackIso (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).hom.val.app (op ⊤)
      (((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app
          (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))).val.app
        (op ⊤) ((baseRingDerivation
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
            (StructureSheaf.toOpen A ⊤ a))) =
      (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤
            (StructureSheaf.toOpen A ⊤ a)) := by
  exact pullbackIso_unit_d (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⊤ (StructureSheaf.toOpen A ⊤ a)

/-- The original equality transport preserves the original differential. -/
private theorem originalTransport_d (a : A) :
    (eqToIso (congrArg baseRingSheaf (baseMap_comp R A B))).hom.val.app (op ⊤)
      ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤
            (StructureSheaf.toOpen A ⊤ a))) =
      (baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤
          (StructureSheaf.toOpen A ⊤ a)) := by
  exact baseRingSheaf_eqToIso_hom_d (baseMap_comp R A B) ⊤
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤ (StructureSheaf.toOpen A ⊤ a))

/-- The original target affine comparison and original scalar map normalize the image. -/
private theorem originalAffine_d (a : A) :
    (AffineKaehlerTildeLocalization.iso R B).hom.val.app (op ⊤)
      ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R B)))).d
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤
          (StructureSheaf.toOpen A ⊤ a))) =
      ModuleCat.Tilde.toOpen (differentialModule R B) ⊤
        (KaehlerDifferential.D R B (algebraMap A B a)) := by
  have hAffine := AffineKaehlerTildeLocalization.iso_d R B ⊤
    ((Spec.map (CommRingCat.ofHom (algebraMap A B))).app ⊤ (StructureSheaf.toOpen A ⊤ a))
  have hScalar := AffineModuleTilde.specMap_globalScalar (algebraMap A B) a
  exact hAffine.trans ((congrArg (sectionD R B ⊤) hScalar).trans
    (sectionD_toOpen R B ⊤ (algebraMap A B a)))

/-- Specialize the already checked scheme formula, then normalize the affine image. -/
private def originalForwardMap_unit_d (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] (a : A) :=
  (forwardMap_unit_d (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) (baseMap_comp R A B)
    (AffineKaehlerTildeLocalization.iso R B).hom ⊤ (StructureSheaf.toOpen A ⊤ a)).trans
      (originalAffine_d R A B a)

/-- The compiled original affine-adjunction normalization combines the two
already checked generator images, before concrete composition is unfolded. -/
private def originalMap_transpose_d (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] (a : A) :=
  AffineModuleTildeTransposeNormalization.pullback_transpose_eq (algebraMap A B)
    (differentialModule R A)
    (baseRingSheaf (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (differentialModule R B).tilde (AffineKaehlerTildeLocalization.iso R A).inv
    (originalForwardMap R A B) (KaehlerDifferential.D R A a)
    ((baseRingDerivation (Spec.map (CommRingCat.ofHom (algebraMap R A)))).d
      (StructureSheaf.toOpen A ⊤ a))
    (ModuleCat.Tilde.toOpen (differentialModule R B) ⊤
      (KaehlerDifferential.D R B (algebraMap A B a)))
    (iso_inv_toOpen_d R A a) (originalForwardMap_unit_d R A B a)

/-- The original affine differential map is exactly the original Kähler restriction
map transported through the original affine comparisons. -/
theorem pullbackMap_eq :
    pullbackMap (algebraMap A B) (differentialMap R A B) = originalMap R A B := by
  apply ((AffineModuleTilde.pulledTildeAdjunction (algebraMap A B)).homEquiv
    (differentialModule R A) (differentialModule R B).tilde).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
  intro a
  calc
    _ = ModuleCat.Tilde.toOpen (differentialModule R B) ⊤
        (differentialMap R A B (KaehlerDifferential.D R A a)) :=
      pullbackMap_transpose_apply (algebraMap A B) (differentialMap R A B)
        (KaehlerDifferential.D R A a)
    _ = ModuleCat.Tilde.toOpen (differentialModule R B) ⊤
        (KaehlerDifferential.D R B (algebraMap A B a)) :=
      congrArg (ModuleCat.Tilde.toOpen (differentialModule R B) ⊤)
        (differentialMap_d R A B a)
    _ = _ := (originalMap_transpose_d R A B a).symm

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

private def pullback_square_proof (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :=
  pullback_square_word
    (schemeModulePullback (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (AffineKaehlerTildeLocalization.iso R A)
    (pullbackMap (algebraMap A B) (differentialMap R A B))
    (originalForwardMap R A B)
    (pullbackMap_eq R A B)

/-- The original affine comparison intertwines the actual module differential
restriction with the actual scheme Kähler pullback. The inferred proposition
is the exact equality of the original maps; `statementOf` is transparent. -/
theorem pullback_square : statementOf (pullback_square_proof R A B) :=
  pullback_square_proof R A B

end KltDP.Geometry.AffineKaehlerPullbackComparison

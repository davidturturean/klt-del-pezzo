import KltDP.Geometry.AffineModuleTildeTensorIso
import KltDP.Geometry.AffineModuleTildeFunctor
import KltDP.Geometry.AffineModuleTildeUnit
import KltDP.Geometry.SchemeModulePullbackTensorNaturality
import KltDP.Geometry.SchemeStructureTensor

/-!
# Actual tilde tensor pairings in linear coordinates

The original tilde tensor comparison sends the tensor product of two
linear coordinates to their product in the actual structure module.
The proof checks the original localized fractions and then uses the
accepted naturality and multiplication of monoidal sheafification.

No tensor or evaluation compatibility is an input. Pullback compatibility
and global conormal gluing remain separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.AffineModuleTildeTensorPairing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

variable {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}

/-- The literal tensor product of two original linear coordinates. -/
def moduleProduct (g : M ⟶ ModuleCat.of R R) (h : N ⟶ ModuleCat.of R R) :
    AffineModuleTildeTensor.tensorModule M N ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom ((TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map g.hom h.hom))

/-- The original product pairing on pure tensors. -/
theorem moduleProduct_tmul (g : M ⟶ ModuleCat.of R R) (h : N ⟶ ModuleCat.of R R)
    (m : M) (n : N) : moduleProduct g h (m ⊗ₜ[R] n) = g m * h n := by
  change TensorProduct.lid R R (TensorProduct.map g.hom h.hom (m ⊗ₜ[R] n)) = _
  rw [TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]

/-- An original linear coordinate, regarded as an actual structure-module map. -/
def coordinate {P : ModuleCat.{u} R} (g : P ⟶ ModuleCat.of R R) :
    P.tilde ⟶ _root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  AffineModuleTilde.map g ≫ (AffineModuleTilde.unitIso R).hom

private theorem fiber_product (g : M ⟶ ModuleCat.of R R) (h : N ⟶ ModuleCat.of R R)
    (p : PrimeSpectrum R)
    (a : LocalizedModule p.asIdeal.primeCompl M)
    (b : LocalizedModule p.asIdeal.primeCompl N) :
    AffineModuleTilde.unitFiberEquiv R p
        (AffineModuleTilde.fiberMap (moduleProduct g h) p
          (KltDP.RingTheory.LocalizedTensorProduct.equiv p.asIdeal.primeCompl M N
            (Localization.AtPrime p.asIdeal) (a ⊗ₜ[Localization.AtPrime p.asIdeal] b))) =
      AffineModuleTilde.unitFiberEquiv R p (AffineModuleTilde.fiberMap g p a) *
        AffineModuleTilde.unitFiberEquiv R p (AffineModuleTilde.fiberMap h p b) := by
  have hbase (m : M) (n : N) :
      AffineModuleTilde.unitFiberEquiv R p
          (AffineModuleTilde.fiberMap (moduleProduct g h) p
            (KltDP.RingTheory.LocalizedTensorProduct.equiv p.asIdeal.primeCompl M N
              (Localization.AtPrime p.asIdeal)
              (LocalizedModule.mk m 1 ⊗ₜ[Localization.AtPrime p.asIdeal]
                LocalizedModule.mk n 1))) =
        AffineModuleTilde.unitFiberEquiv R p
            (AffineModuleTilde.fiberMap g p (LocalizedModule.mk m 1)) *
          AffineModuleTilde.unitFiberEquiv R p
            (AffineModuleTilde.fiberMap h p (LocalizedModule.mk n 1)) := by
    rw [KltDP.RingTheory.LocalizedTensorProduct.equiv_mk_one]
    change AffineModuleTilde.unitFiberEquiv R p
        (AffineModuleTilde.fiberMap (moduleProduct g h) p
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl
            (AffineModuleTildeTensor.tensorModule M N) (m ⊗ₜ[R] n))) =
      AffineModuleTilde.unitFiberEquiv R p
          (AffineModuleTilde.fiberMap g p (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m)) *
        AffineModuleTilde.unitFiberEquiv R p
          (AffineModuleTilde.fiberMap h p (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N n))
    rw [AffineModuleTilde.fiberMap_mkLinearMap (moduleProduct g h) p (m ⊗ₜ[R] n),
      AffineModuleTilde.fiberMap_mkLinearMap g p m,
      AffineModuleTilde.fiberMap_mkLinearMap h p n,
      AffineModuleTilde.unitFiberEquiv_mkLinearMap R p (moduleProduct g h (m ⊗ₜ[R] n)),
      AffineModuleTilde.unitFiberEquiv_mkLinearMap R p (g m),
      AffineModuleTilde.unitFiberEquiv_mkLinearMap R p (h n), moduleProduct_tmul]
    exact (algebraMap R (Localization.AtPrime p.asIdeal)).map_mul (g m) (h n)
  refine LocalizedModule.induction_on (fun m s => ?_) a
  refine LocalizedModule.induction_on (fun n t => ?_) b
  have hm : LocalizedModule.mk m s =
      IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 s • LocalizedModule.mk m 1 := by
    simpa using (LocalizedModule.mk'_smul_mk
      (T := Localization.AtPrime p.asIdeal) 1 m s 1).symm
  have hn : LocalizedModule.mk n t =
      IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 t • LocalizedModule.mk n 1 := by
    simpa using (LocalizedModule.mk'_smul_mk
      (T := Localization.AtPrime p.asIdeal) 1 n t 1).symm
  rw [hm, hn, TensorProduct.smul_tmul_smul]
  rw [(KltDP.RingTheory.LocalizedTensorProduct.equiv p.asIdeal.primeCompl M N
      (Localization.AtPrime p.asIdeal)).map_smul,
    AffineModuleTilde.fiberMap_local_smul (moduleProduct g h) p,
    AffineModuleTilde.fiberMap_local_smul g p,
    AffineModuleTilde.fiberMap_local_smul h p,
    (AffineModuleTilde.unitFiberEquiv R p).map_smul,
    (AffineModuleTilde.unitFiberEquiv R p).map_smul,
    (AffineModuleTilde.unitFiberEquiv R p).map_smul]
  change (IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 s *
      IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 t) * _ =
    (IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 s * _) *
      (IsLocalization.mk' (Localization.AtPrime p.asIdeal) 1 t * _)
  rw [hbase]
  exact mul_mul_mul_comm _ _ _ _

/-- On the original tensor presheaf, tilde of the literal product is the
actual multiplication of the two coordinate sections. -/
theorem presheaf_product (g : M ⟶ ModuleCat.of R R) (h : N ⟶ ModuleCat.of R R) :
    AffineModuleTildeTensor.presheafMap M N ≫ (coordinate (moduleProduct g h)).val =
      ((coordinate g).val ⊗ (coordinate h).val) ≫
        (ρ_ (_root_.PresheafOfModules.unit
          (Spec (CommRingCat.of R)).ringCatSheaf.val)).hom := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  change (coordinate (moduleProduct g h)).val.app U
      (AffineModuleTildeTensor.sectionsPure M N U.unop a b) =
    (coordinate h).val.app U b • (coordinate g).val.app U a
  apply Subtype.ext
  funext p
  change AffineModuleTilde.unitFiberEquiv R p.val
      (AffineModuleTilde.fiberMap (moduleProduct g h) p.val
        (KltDP.RingTheory.LocalizedTensorProduct.equiv p.val.asIdeal.primeCompl M N
          (Localization.AtPrime p.val.asIdeal)
          (a.val p ⊗ₜ[Localization.AtPrime p.val.asIdeal] b.val p))) =
    AffineModuleTilde.unitFiberEquiv R p.val (AffineModuleTilde.fiberMap h p.val (b.val p)) *
      AffineModuleTilde.unitFiberEquiv R p.val (AffineModuleTilde.fiberMap g p.val (a.val p))
  exact (fiber_product g h p.val (a.val p) (b.val p)).trans (mul_comm _ _)

/-- The original tilde tensor and unit comparisons preserve literal
products of coordinates as maps of the actual module sheaves. -/
theorem iso_inv_product (g : M ⟶ ModuleCat.of R R) (h : N ⟶ ModuleCat.of R R) :
    (AffineModuleTildeTensor.iso M N).inv ≫ coordinate (moduleProduct g h) =
      (coordinate g ⊗ coordinate h) ≫
        (schemeStructureTensorRightIso
          (_root_.SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)).hom := by
  let X := Spec (CommRingCat.of R)
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let O := _root_.SheafOfModules.unit X.ringCatSheaf
  let t := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M.tilde N.tilde
  let e := PresheafOfModules.sheafificationForgetIso
    X.ringCatSheaf (AffineModuleTildeTensor.tensorModule M N).tilde
  change t.hom ≫ S.map (AffineModuleTildeTensor.presheafMap M N) ≫ e.hom ≫
    coordinate (moduleProduct g h) = _
  calc
    _ = t.hom ≫
        S.map (AffineModuleTildeTensor.presheafMap M N ≫ (coordinate (moduleProduct g h)).val) ≫
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf O).hom := by
      rw [Functor.map_comp, Category.assoc, schemeSheafificationForgetIso_hom_natural]
    _ = t.hom ≫ S.map ((coordinate g).val ⊗ (coordinate h).val) ≫
        S.map (ρ_ (_root_.PresheafOfModules.unit X.ringCatSheaf.val)).hom ≫
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf O).hom := by
      rw [presheaf_product, Functor.map_comp, Category.assoc]
    _ = (coordinate g ⊗ coordinate h) ≫
        (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond O O).hom ≫
        S.map (ρ_ (_root_.PresheafOfModules.unit X.ringCatSheaf.val)).hom ≫
        (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf O).hom := by
      rw [← schemeSheafTensorIsoSheafification_natural_assoc]
    _ = _ := by
      change (coordinate g ⊗ coordinate h) ≫
        (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond O O).hom ≫
        S.map (ρ_ (_root_.PresheafOfModules.unit X.ringCatSheaf.val)).hom ≫
        (PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond).hom = _
      exact congrArg (fun k => (coordinate g ⊗ coordinate h) ≫ k)
        (schemeSheafTensorIso_structure_mul X)

end KltDP.Geometry.AffineModuleTildeTensorPairing

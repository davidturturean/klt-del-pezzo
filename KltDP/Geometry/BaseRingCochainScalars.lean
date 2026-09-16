import KltDP.Geometry.BaseRingCohomology
import KltDP.Compatibility.MapCochainExtension

/-!
# Canonical base-ring multiplication on complexes of scheme modules

The base ring acts through the original map to the global functions.
Its multiplication morphisms define a natural endomorphism of the identity,
which the pinned complex functor applies to the original complexes.
Extension by zero and the existing map-extension comparison commute with
these same morphisms, including after applying the actual homology functor.

The component formula uses the existing Ext-based cohomology action.
No comparison with right-derived cohomology or choice of an injective
resolution is assumed or constructed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.ModuleCohomology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of A))

/-- Multiplication by the image of a base-ring element on every original module. -/
def baseRingSmulNatTrans (a : A) : 𝟭 X.Modules ⟶ 𝟭 X.Modules where
  app M := globalSmulHom M
    (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
  naturality M N g := (globalSmulHom_naturality g _).symm

/-- The same multiplication as an endomorphism of the original complex. -/
def baseRingComplexSmul {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (a : A) : K ⟶ K :=
  (Functor.mapHomologicalComplexIdIso X.Modules c).inv.app K ≫
    (NatTrans.mapHomologicalComplex (baseRingSmulNatTrans f a) c).app K ≫
    (Functor.mapHomologicalComplexIdIso X.Modules c).hom.app K

/-- Every component is the original multiplication morphism. -/
theorem baseRingComplexSmul_f {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (a : A) (i : ι) :
    (baseRingComplexSmul f K a).f i = globalSmulHom (K.X i)
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
  change (𝟙 _) ≫ globalSmulHom (K.X i) _ ≫ (𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

/-- Multiplication commutes with every actual morphism of complexes. -/
theorem baseRingComplexSmul_naturality {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex X.Modules c} (g : K ⟶ L) (a : A) :
    baseRingComplexSmul f K a ≫ g = g ≫ baseRingComplexSmul f L a := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, baseRingComplexSmul_f]
  exact globalSmulHom_naturality (g.f i) _

/-- Componentwise Ext cohomology sees the existing canonical base-ring action. -/
theorem baseRingComplexSmul_cohomology {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex X.Modules c) (a : A) (i : ι) (n : ℕ)
    (x : H (K.X i) n) :
    letI := baseRingModule f (K.X i) n
    (zariskiFunctor X n).map ((baseRingComplexSmul f K a).f i) x = a • x := by
  letI := baseRingModule f (K.X i) n
  rw [baseRingComplexSmul_f]
  exact (baseRingModule_smul f (K.X i) n a x).symm

/-- Extension by zero retains the original multiplication on every term. -/
theorem extendMap_baseRingComplexSmul (K : CochainComplex X.Modules ℕ) (a : A) :
    HomologicalComplex.extendMap (baseRingComplexSmul f K a)
        ComplexShape.embeddingUpNat =
      baseRingComplexSmul f (K.extend ComplexShape.embeddingUpNat) a := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : ∃ k, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := hn
    rw [HomologicalComplex.extendMap_f _ _ hk, baseRingComplexSmul_f,
      baseRingComplexSmul_f]
    let e := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat hk
    change e.hom ≫ globalSmulHom (K.X k) _ ≫ e.inv = _
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (globalSmulHom_naturality e.hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))).symm
  · exact (K.isZero_extend_X ComplexShape.embeddingUpNat n
      (fun k hk => hn ⟨k, hk⟩)).eq_of_src _ _

/-- The existing map-extension isomorphism commutes with these scalar maps. -/
theorem mapExtendIso_baseRingComplexSmul
    (G : X.Modules ⥤ AddCommGrp.{u}) [G.Additive]
    (K : CochainComplex X.Modules ℕ) (a : A) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (baseRingComplexSmul f (K.extend ComplexShape.embeddingUpNat) a) ≫
      (KltDP.CochainComparison.mapExtendIso (G := G) K).hom =
    (KltDP.CochainComparison.mapExtendIso (G := G) K).hom ≫
      HomologicalComplex.extendMap
        ((G.mapHomologicalComplex (.up ℕ)).map (baseRingComplexSmul f K a))
        ComplexShape.embeddingUpNat := by
  rw [← extendMap_baseRingComplexSmul]
  exact KltDP.CochainComparison.mapExtendIso_naturality (G := G)
    (baseRingComplexSmul f K a)

/-- The same equality after applying the original homology functor. -/
theorem homology_mapExtendIso_baseRingComplexSmul
    (G : X.Modules ⥤ AddCommGrp.{u}) [G.Additive]
    (K : CochainComplex X.Modules ℕ) (a : A) (n : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        ((G.mapHomologicalComplex (.up ℤ)).map
          (baseRingComplexSmul f (K.extend ComplexShape.embeddingUpNat) a)) ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        (KltDP.CochainComparison.mapExtendIso (G := G) K).hom =
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        (KltDP.CochainComparison.mapExtendIso (G := G) K).hom ≫
      (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
        (HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (.up ℕ)).map (baseRingComplexSmul f K a))
          ComplexShape.embeddingUpNat) := by
  simpa only [Functor.map_comp] using congrArg
    (HomologicalComplex.homologyFunctor AddCommGrp.{u} (.up ℤ) n).map
    (mapExtendIso_baseRingComplexSmul f G K a)

end KltDP.Geometry.ModuleCohomology

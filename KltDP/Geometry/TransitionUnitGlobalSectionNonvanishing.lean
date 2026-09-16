import KltDP.Geometry.TransitionUnitGlobalSections
import KltDP.Geometry.InvertibleSectionNonvanishingOpen

/-! # Intrinsic nonvanishing of original glued-coordinate sections -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance coordinateOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance coordinateOverLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

open InvertibleSectionNonvanishingOpen TransitionUnitExtraction

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ) (hc : IsCocycle X U g)
  (hU : (⨆ i, U i) = ⊤)

/-- The existing glued atlas cancels just its singleton-free comparison. -/
theorem localTrivializations_unitIso_hom (i : ι) :
    ((localTrivializations X U g hc hU).unitIso i).hom =
      (chartIsoOn X U g hc i (le_refl (U i))).hom := by
  simp only [localTrivializations, KltDP.SheafOfModules.LocalTrivializations.unitIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

variable (r : ∀ i, Γ(X, U i))
  (hr : ∀ i j,
    res X (inf_le_left : U i ⊓ U j ≤ U i) (r i) =
      (g i j : Γ(X, U i ⊓ U j)) *
        res X (inf_le_right : U i ⊓ U j ≤ U j) (r j))

/-- The actual rank-one atlas reads exactly the prescribed original coordinates. -/
theorem chartCoefficient_globalSectionOfCoordinates (i : ι) :
    chartCoefficient X (moduleSheaf X U g) (localTrivializations X U g hc hU)
      (globalSectionOfCoordinates X U g r hr) i = r i := by
  have h := congrArg
    (fun f : (moduleSheaf X U g).over (U i) ⟶
        _root_.SheafOfModules.unit (X.ringCatSheaf.over (U i)) =>
      f.val.app (op (Over.mk (homOfLE (show U i ≤ U i from le_rfl))))
        ((globalSectionOfCoordinates X U g r hr).val (op (U i))))
    (localTrivializations_unitIso_hom X U g hc hU i)
  have he := (chartEquiv_apply X (moduleSheaf X U g)
    (localTrivializations X U g hc hU) i le_rfl
      ((globalSectionOfCoordinates X U g r hr).val (op (U i)))).trans h
  have ht := chartIsoOn_hom_app_apply X U g hc i (le_refl (U i))
    (op (Over.mk (homOfLE (le_refl (U i)))))
    ((globalSectionOfCoordinates X U g r hr).val (op (U i)))
  exact he.trans (ht.trans
    ((trivialization_globalSectionOfCoordinates X U g r hr hc i le_rfl).trans
      (res_self X (U i) (r i))))

/-- The intrinsic nonvanishing open is the union of the basic opens of
the original specified chart functions. No atlas choice is an input. -/
theorem nonvanishingOpen_globalSectionOfCoordinates :
    nonvanishingOpen X (invertibleSheaf X U g hc hU)
        (globalSectionOfCoordinates X U g r hr) = ⨆ i, X.basicOpen (r i) := by
  change nonvanishingOpenOfAtlas X (moduleSheaf X U g)
    (invertibleSheaf X U g hc hU).localTrivializations
    (globalSectionOfCoordinates X U g r hr) = _
  rw [nonvanishingOpenOfAtlas_eq X (moduleSheaf X U g)
    (invertibleSheaf X U g hc hU).localTrivializations
    (localTrivializations X U g hc hU)]
  unfold nonvanishingOpenOfAtlas
  apply iSup_congr
  intro i
  rw [chartCoefficient_globalSectionOfCoordinates]

end KltDP.Geometry.TransitionUnitGluing

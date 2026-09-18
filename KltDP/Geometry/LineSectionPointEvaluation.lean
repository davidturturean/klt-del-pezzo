import KltDP.Geometry.InvertibleSheafOnField
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Geometry.RationalPointPushforwardCohomology
import KltDP.Geometry.SheafSectionPullbackCoefficient
import KltDP.Geometry.InvertibleSectionNonvanishingOpen
import KltDP.Geometry.SchemeModulePullbackUnit
import KltDP.Geometry.RationalPoints

/-! Evaluation of an original line section at an actual rational point.
The original adjunction unit and a proved frame on Spec k supply a native
k-linear functional. Its kernel vanishes at the original image point. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry.LineSectionPointEvaluation
open ModuleCohomology InvertibleSectionNonvanishingOpen TransitionUnitExtraction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The original map on top sections is linear for the original base action. -/
def sectionsLinearMap (f : X ⟶ Spec (CommRingCat.of k))
    {M N : X.Modules} (g : M ⟶ N) :
    letI := baseSectionsModule f M
    letI := baseSectionsModule f N
    sections M →ₗ[k] sections N := by
  letI := baseSectionsModule f M
  letI := baseSectionsModule f N
  exact {
    toFun := g.val.app (op (⊤ : X.Opens))
    map_add' := (g.val.app (op (⊤ : X.Opens))).hom.map_add
    map_smul' := fun a s =>
      (g.val.app (op (⊤ : X.Opens))).hom.map_smul (baseFieldToGlobalSections f a) s }

/-- The actual pulled-back line on the actual field spectrum has a frame. -/
def pointFrame (i : Spec (CommRingCat.of k) ⟶ X) (L : InvertibleSheaf X) :
    (schemeModulePullback i).obj L.obj ≅
      _root_.SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf :=
  Classical.choice (InvertibleSheafOnField.exists_unitIso k (pullbackInvertibleSheaf i L))

/-- Original restriction to the point, expressed in its proved frame. -/
def restriction (i : Spec (CommRingCat.of k) ⟶ X) (L : InvertibleSheaf X) :
    L.obj ⟶ RationalPointPushforward.unitPushforward i :=
  (schemeModulePullbackPushforwardAdjunction i).unit.app L.obj ≫
    (schemeModulePushforward i).map (pointFrame i L).hom

/-- A k-linear evaluation functional on the original global sections. -/
def evaluation (f : X ⟶ Spec (CommRingCat.of k))
    (i : Spec (CommRingCat.of k) ⟶ X) (hi : i ≫ f = 𝟙 _) (L : InvertibleSheaf X) :
    letI := baseSectionsModule f L.obj
    sections L.obj →ₗ[k] k := by
  letI := baseSectionsModule f L.obj
  letI := baseSectionsModule f (RationalPointPushforward.unitPushforward i)
  exact (RationalPointPushforward.sectionsLinearEquiv i f hi).toLinearMap.comp
    (sectionsLinearMap f (restriction i L))

/-- A zero point value is a zero literal adjunction-unit pullback. -/
theorem pulledSection_eq_zero_of_evaluation_eq_zero
    (f : X ⟶ Spec (CommRingCat.of k))
    (i : Spec (CommRingCat.of k) ⟶ X) (hi : i ≫ f = 𝟙 _) (L : InvertibleSheaf X)
    (s : sections L.obj) (hs : evaluation f i hi L s = 0) :
    RationalTreePicard.pulledSection i L.obj ⊤ s = 0 := by
  letI := baseSectionsModule f (RationalPointPushforward.unitPushforward i)
  have hv : (restriction i L).val.app (op (⊤ : X.Opens)) s = 0 := by
    apply (RationalPointPushforward.sectionsLinearEquiv i f hi).injective
    exact hs.trans (map_zero (RationalPointPushforward.sectionsLinearEquiv i f hi)).symm
  let P : (Spec (CommRingCat.of k)).Modules := (schemeModulePullback i).obj L.obj
  let U : (Spec (CommRingCat.of k)).Opens := i ⁻¹ᵁ (⊤ : X.Opens)
  let t : P.val.obj (op U) := RationalTreePicard.pulledSection i L.obj ⊤ s
  let e : P ≅ _root_.SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf := pointFrame i L
  change e.hom.val.app (op U) t = 0 at hv
  have hc : e.inv.val.app (op U) (e.hom.val.app (op U) t) = t :=
    congrArg (fun g : P ⟶ P => g.val.app (op U) t) e.hom_inv_id
  change t = 0
  rw [← hc, hv, map_zero]

/-- A section in the evaluation kernel does not belong to its intrinsic
nonvanishing open at the same original point. -/
theorem not_mem_nonvanishing_of_evaluation_eq_zero
    (f : X ⟶ Spec (CommRingCat.of k))
    (i : Spec (CommRingCat.of k) ⟶ X) (hi : i ≫ f = 𝟙 _) (L : InvertibleSheaf X)
    (s : sections L.obj) (hs : evaluation f i hi L s = 0) :
    fieldMorphismPoint i ∉ nonvanishingOpen X L (schemeModuleSectionOfTop L.obj s) := by
  let t := L.localTrivializations
  have hx : fieldMorphismPoint i ∈ (⨆ j, t.X j) := by
    rw [chartOpens_cover X L.obj t]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  have hz := pulledSection_eq_zero_of_evaluation_eq_zero f i hi L s hs
  have hn := SheafSectionPullbackCoefficient.not_isUnit_germ_of_global_pulledSection_eq_zero
    i L.obj s hz (t.X j) (t.unitIso j) (IsLocalRing.closedPoint k) hj
  change ¬ IsUnit (X.presheaf.germ (t.X j) (fieldMorphismPoint i) hj
    (chartCoefficient X L.obj t (schemeModuleSectionOfTop L.obj s) j)) at hn
  intro hmem
  exact hn ((mem_nonvanishingOpen_iff_isUnit_germ X L
    (schemeModuleSectionOfTop L.obj s) t j (fieldMorphismPoint i) hj).mp hmem)

end KltDP.Geometry.LineSectionPointEvaluation

#check @KltDP.Geometry.LineSectionPointEvaluation.evaluation
#print axioms KltDP.Geometry.LineSectionPointEvaluation.not_mem_nonvanishing_of_evaluation_eq_zero

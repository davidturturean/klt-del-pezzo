import KltDP.Geometry.LinearSystemTrivialConstant
import KltDP.Geometry.ProjectiveSpaceDegreeOneSheaf
import KltDP.Geometry.InvertibleSectionNonvanishingPullback
import KltDP.Geometry.ProperConnectedReducedConstants

/-!
# A projective map with trivial original pullback of the degree-one sheaf

Pull back the actual homogeneous sections. Their original nonvanishing opens
cover, and an actual frame on the pulled line makes one of these sections
everywhere nonvanishing by proper connected reduced global constants. Thus the given
map lands in an original affine projective chart. Its actual affine lift
factors through the original field, preserving the original structure map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.ProjectiveMapTrivialPullback

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowersPullback
open InvertibleSectionNonvanishingPullback ProjectiveSpaceDegreeOneSheaf
open ProjectiveCoordinateSectionBasicOpen LinearSystemTrivialConstant

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsReduced Y] [ConnectedSpace Y] [IsProper f]

include f in
private theorem base_endomorphism_eq_id
    (a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k))
    (ha : f ≫ a = f) : a = 𝟙 _ := by
  letI : IsIso (specHomRingHom f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ProperConnectedReducedConstants.baseFieldToGlobalSections_bijective f)
  let φ := Spec.preimage a
  have ha' : f ≫ Spec.map φ = f := by
    simpa only [φ, Spec.map_preimage] using ha
  have hφ : φ ≫ specHomRingHom f = specHomRingHom f :=
    (specHomRingHom_comp_specMap f φ).symm.trans (congrArg specHomRingHom ha')
  have hid : φ = 𝟙 _ :=
    (cancel_mono (specHomRingHom f)).mp (hφ.trans (Category.id_comp _).symm)
  calc
    a = Spec.map φ := (Spec.map_preimage a).symm
    _ = 𝟙 _ := by rw [hid, Spec.map_id]

variable {n : ℕ} (g : Y ⟶ projectiveSpace k n)
  (e : (pullbackInvertibleSheaf g (degreeOne k n)).obj ≅
    _root_.SheafOfModules.unit Y.ringCatSheaf)

include f e in
/-- The given projective map lands in one original coordinate chart. -/
theorem exists_coordinateChart_range :
    ∃ i : Fin (n + 1), Set.range g.base ⊆
      Set.range (ProjectiveChart.coordinateChartMorphism k n i).base := by
  let L := pullbackInvertibleSheaf g (degreeOne k n)
  let s : Fin (n + 1) → L.obj.sections :=
    fun i => InvertibleSheafSectionPowersPullback.pullbackSection g
      (degreeOne k n).obj (homogeneousSection k n i)
  have hs (i : Fin (n + 1)) :
      nonvanishingOpen Y L (s i) = g ⁻¹ᵁ standardOpen k n i :=
    (nonvanishingOpen_pullback g (degreeOne k n) (homogeneousSection k n i)).trans
      (congrArg (fun U => g ⁻¹ᵁ U) (nonvanishingOpen_homogeneousSection k n i))
  have hcover : (⨆ i, nonvanishingOpen Y L (s i)) = ⊤ :=
    (iSup_congr hs).trans
      (g.preimage_iSup_eq_top (ProjectiveChart.iSup_coordinateStandardOpen k n))
  obtain ⟨i, hi⟩ := LinearSystemTrivialConstant.exists_nonvanishingOpen_eq_top f L e s hcover
  have hpre : g ⁻¹ᵁ standardOpen k n i = ⊤ := (hs i).symm.trans hi
  refine ⟨i, ?_⟩
  rintro _ ⟨y, rfl⟩
  change g.base y ∈ (ProjectiveChart.coordinateChartMorphism k n i).opensRange
  rw [ProjectiveChart.coordinateChartMorphism_opensRange]
  change y ∈ g ⁻¹ᵁ standardOpen k n i
  rw [hpre]
  trivial

include e in
/-- The original map factors through a point over the original base field. -/
theorem factors_through_structure
    (hgf : g ≫ projectiveSpaceToSpec k n = f) :
    ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k n,
      g = f ≫ p ∧ p ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
  obtain ⟨i, hi⟩ := exists_coordinateChart_range f g e
  let ι := ProjectiveChart.coordinateChartMorphism k n i
  let a := IsOpenImmersion.lift ι g hi
  have ha : a ≫ ι = g := IsOpenImmersion.lift_fac _ _ _
  let p := affineConstantPoint f a ≫ ι
  have hp : f ≫ p = g :=
    (Category.assoc f (affineConstantPoint f a) ι).symm.trans
      ((congrArg (fun q => q ≫ ι) (structure_affineConstantPoint f a)).trans ha)
  refine ⟨p, hp.symm, base_endomorphism_eq_id f (p ≫ projectiveSpaceToSpec k n) ?_⟩
  exact (Category.assoc f p (projectiveSpaceToSpec k n)).symm.trans
    ((congrArg (fun q => q ≫ projectiveSpaceToSpec k n) hp).trans hgf)

end KltDP.Geometry.ProjectiveMapTrivialPullback

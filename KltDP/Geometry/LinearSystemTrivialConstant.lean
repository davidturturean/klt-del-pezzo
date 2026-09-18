import KltDP.Geometry.LinearSystemNonvanishingPreimage
import KltDP.Geometry.InvertibleSectionNonvanishingFrame
import KltDP.Geometry.ProperConnectedReducedConstants
import KltDP.Geometry.SpecHomRingHom

/-!
# The actual linear-system morphism of a trivial line bundle is constant

On a reduced connected proper scheme over an algebraically closed field, the original
scalar map identifies all global functions with constants. In an actual frame,
a nonzero section coefficient is therefore a unit. A covering tuple has such
a coefficient, so the original linear-system morphism lands in one original
affine projective chart. Its actual ring map then factors through the original
base-field scalar map, giving a point over that field and the exact factorization.

This uses the compiled nonvanishing-preimage theorem; no coordinate appLE
calculation, finite-map hypothesis, or contraction hypothesis is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.LinearSystemTrivialConstant

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSectionNonvanishingFrame
open InvertibleSheafSectionPowers LinearSystemMorphism

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsReduced X] [ConnectedSpace X] [IsProper f]

include f

private theorem scalarMap_isIso : IsIso (specHomRingHom f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ProperConnectedReducedConstants.baseFieldToGlobalSections_bijective f

/-- The actual affine map determines a point by the inverse of the original
base-field map on global functions. -/
def affineConstantPoint {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    Spec (CommRingCat.of k) ⟶ Spec R := by
  letI := scalarMap_isIso f
  exact Spec.map (specHomRingHom g ≫ inv (specHomRingHom f))

/-- Every original morphism into an affine scheme factors through the given
structure morphism, using its own original global ring map. -/
theorem structure_affineConstantPoint {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    f ≫ affineConstantPoint f g = g := by
  letI := scalarMap_isIso f
  let a : R ⟶ CommRingCat.of k := specHomRingHom g ≫ inv (specHomRingHom f)
  have ha : a ≫ specHomRingHom f = specHomRingHom g := by
    dsimp only [a]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  change f ≫ Spec.map a = g
  calc
    f ≫ Spec.map a =
        (X.toSpecΓ ≫ Spec.map (specHomRingHom f)) ≫ Spec.map a :=
      congrArg (fun h : X ⟶ Spec (CommRingCat.of k) => h ≫ Spec.map a)
        (specHom_eq_toSpecΓ f)
    _ = X.toSpecΓ ≫ Spec.map (a ≫ specHomRingHom f) := by
      rw [Category.assoc, ← Spec.map_comp]
    _ = X.toSpecΓ ≫ Spec.map (specHomRingHom g) := by rw [ha]
    _ = g := (specHom_eq_toSpecΓ g).symm

private theorem structure_postcomp_eq_id
    (h : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k))
    (hh : f ≫ h = f) : h = 𝟙 _ := by
  letI := scalarMap_isIso f
  let a := Spec.preimage h
  have hh' : f ≫ Spec.map a = f := by
    simpa only [a, Spec.map_preimage] using hh
  have ha : a ≫ specHomRingHom f = specHomRingHom f :=
    (specHomRingHom_comp_specMap f a).symm.trans (congrArg specHomRingHom hh')
  have hid : a = 𝟙 _ :=
    (cancel_mono (specHomRingHom f)).mp (ha.trans (Category.id_comp _).symm)
  calc
    h = Spec.map a := (Spec.map_preimage h).symm
    _ = 𝟙 _ := by rw [hid, Spec.map_id]

variable (L : InvertibleSheaf X)
  (e : L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf)

include e

/-- A nonzero coefficient in the original global frame makes the section
nonvanishing everywhere. -/
theorem nonvanishingOpen_eq_top_of_coefficient_ne_zero (s : L.obj.sections)
    (hs : frameCoefficient L e s ≠ 0) : nonvanishingOpen X L s = ⊤ := by
  obtain ⟨a, ha⟩ := (ProperConnectedReducedConstants.baseFieldToGlobalSections_bijective f).surjective (frameCoefficient L e s)
  have hane : a ≠ 0 := by
    intro h
    apply hs
    rw [← ha, h, map_zero]
  have hu : IsUnit (frameCoefficient L e s) := by
    rw [← ha]
    exact (isUnit_iff_ne_zero.mpr hane).map (baseFieldToGlobalSections f)
  rw [nonvanishingOpen_eq_basicOpen L e s]
  exact X.basicOpen_of_isUnit hu

variable {n : ℕ} (s : Fin (n + 1) → L.obj.sections)
  (hcover : (⨆ j, nonvanishingOpen X L (s j)) = ⊤)

include hcover

/-- One of the specified sections is everywhere nonvanishing, proved from
the original covering condition and the original frame. -/
theorem exists_nonvanishingOpen_eq_top :
    ∃ j : Fin (n + 1), nonvanishingOpen X L (s j) = ⊤ := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hx : x ∈ ⨆ j, nonvanishingOpen X L (s j) := by
    rw [hcover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  refine ⟨j, nonvanishingOpen_eq_top_of_coefficient_ne_zero f L e (s j) ?_⟩
  intro hz
  rw [nonvanishingOpen_eq_basicOpen L e (s j), hz, Scheme.basicOpen_zero] at hj
  exact hj

/-- The actual projective morphism lands in one original standard affine chart. -/
theorem exists_coordinateChart_range :
    ∃ j : Fin (n + 1), Set.range (morphism L s f hcover).base ⊆
      Set.range (ProjectiveChart.coordinateChartMorphism k n j).base := by
  obtain ⟨j, hj⟩ := exists_nonvanishingOpen_eq_top f L e s hcover
  refine ⟨j, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ morphism L s f hcover ⁻¹ᵁ
      (ProjectiveChart.coordinateChartMorphism k n j).opensRange := by
    rw [morphism_preimage_coordinateChart, hj]
    trivial
  exact hx

/-- The original linear-system morphism factors through the original
structure morphism and a point over the original field. -/
theorem morphism_factors_through_structure :
    ∃ p : Spec (CommRingCat.of k) ⟶ projectiveSpace k n,
      morphism L s f hcover = f ≫ p ∧ p ≫ projectiveSpaceToSpec k n = 𝟙 _ := by
  obtain ⟨j, hj⟩ := exists_coordinateChart_range f L e s hcover
  let ι := ProjectiveChart.coordinateChartMorphism k n j
  let g := IsOpenImmersion.lift ι (morphism L s f hcover) hj
  have hg : g ≫ ι = morphism L s f hcover := IsOpenImmersion.lift_fac _ _ _
  let p := affineConstantPoint f g ≫ ι
  have hp : f ≫ p = morphism L s f hcover := by
    dsimp only [p]
    rw [← Category.assoc, structure_affineConstantPoint, hg]
  refine ⟨p, hp.symm, structure_postcomp_eq_id f (p ≫ projectiveSpaceToSpec k n) ?_⟩
  rw [← Category.assoc, hp, morphism_structure]

end KltDP.Geometry.LinearSystemTrivialConstant

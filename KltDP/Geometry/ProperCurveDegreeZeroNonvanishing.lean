import KltDP.Geometry.CurveDegreeZeroNotBig
import KltDP.Geometry.InvertibleSectionNonvanishingFrame

/-!
# Nonvanishing of original degree-zero sections on proper integral curves

The accepted degree-zero Cartier argument gives an actual global frame.
The original coefficient is a nonzero global function, hence a unit by
the pinned proper global-functions theorem. Its actual nonvanishing open
is therefore the whole curve. No chosen frame or constancy is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.ProperCurveDegreeZeroNonvanishing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open InvertibleSectionNonvanishingOpen InvertibleSectionNonvanishingFrame
open InvertibleSheafSectionPowers

variable {Y : Scheme.{u}}

/-- A compatible section with zero value on the whole scheme has empty
original nonvanishing open. -/
theorem nonvanishingOpen_eq_bot_of_top_eq_zero (L : InvertibleSheaf Y)
    (s : L.obj.sections) (hs : s.val (op (⊤ : Y.Opens)) = 0) :
    nonvanishingOpen Y L s = ⊥ := by
  unfold nonvanishingOpen nonvanishingOpenOfAtlas
  apply iSup_eq_bot.mpr
  intro i
  have hi : s.val (op (L.localTrivializations.X i)) = 0 := by
    have h := s.property
      (homOfLE (le_top : L.localTrivializations.X i ≤ (⊤ : Y.Opens))).op
    change L.obj.val.map
      (homOfLE (le_top : L.localTrivializations.X i ≤ (⊤ : Y.Opens))).op
        (s.val (op (⊤ : Y.Opens))) = s.val (op (L.localTrivializations.X i)) at h
    rw [hs, map_zero] at h
    exact h.symm
  have hc : chartCoefficient Y L.obj L.localTrivializations s i = 0 := by
    dsimp only [chartCoefficient]
    rw [hi, map_zero]
  rw [hc, Scheme.basicOpen_zero]

variable {k : Type u} [Field k] [IsIntegral Y]
  (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (hdim : topologicalKrullDim Y ≤ 1)

include f hdim

/-- A nonzero original section of a degree-zero invertible sheaf is
nowhere zero on the original proper integral curve. -/
theorem nonvanishingOpen_eq_top_of_nonzero_top (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)
    (s : L.obj.sections) (hs : s.val (op (⊤ : Y.Opens)) ≠ 0) :
    nonvanishingOpen Y L s = ⊤ := by
  obtain ⟨e⟩ := (RationalTreePicard.toPic_eq_one_iff_iso_unit L).mp
    (CurveDegreeZeroNotBig.toPic_eq_one_of_nonzero_section_of_degree_zero
      f hdim L hdeg (s.val (op (⊤ : Y.Opens))) hs)
  have hc : frameCoefficient L e s ≠ 0 := by
    intro hc
    apply hs
    have hback : e.inv.val.app (op (⊤ : Y.Opens))
        (e.hom.val.app (op (⊤ : Y.Opens)) (s.val (op (⊤ : Y.Opens)))) =
          s.val (op (⊤ : Y.Opens)) :=
      congrArg (fun a : L.obj ⟶ L.obj =>
        a.val.app (op (⊤ : Y.Opens)) (s.val (op (⊤ : Y.Opens)))) e.hom_inv_id
    change e.hom.val.app (op (⊤ : Y.Opens)) (s.val (op (⊤ : Y.Opens))) = 0 at hc
    rw [hc, map_zero] at hback
    exact hback.symm
  letI := (isField_of_universallyClosed k f).toField
  rw [nonvanishingOpen_eq_basicOpen L e s]
  exact Y.basicOpen_of_isUnit (isUnit_iff_ne_zero.mpr hc)

/-- If a degree-zero section is nonvanishing anywhere, it is
nonvanishing everywhere on the same actual proper integral curve. -/
theorem nonvanishingOpen_eq_top_of_nonempty (L : InvertibleSheaf Y)
    (hdeg : eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf) = 0)
    (s : L.obj.sections) (hn : (nonvanishingOpen Y L s : Set Y).Nonempty) :
    nonvanishingOpen Y L s = ⊤ := by
  apply nonvanishingOpen_eq_top_of_nonzero_top f hdim L hdeg s
  intro hz
  obtain ⟨y, hy⟩ := hn
  rw [nonvanishingOpen_eq_bot_of_top_eq_zero L s hz] at hy
  exact hy

end KltDP.Geometry.ProperCurveDegreeZeroNonvanishing

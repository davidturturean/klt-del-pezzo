import KltDP.Geometry.KeelExceptionalSupport
import KltDP.Geometry.CompleteLinearSystemBirational
import KltDP.Geometry.SubsystemPositiveDimension
import KltDP.Geometry.ProjectiveEmbeddingLinearSystem

/-!
Zero-dimensional integral projective schemes contribute no exceptional
subvariety for the actual complete-system predicate. Original line bundles
are trivial by the accepted zero-dimensional local-frame theorem. Thus an
original embedding line is isomorphic to every target line, and the proved
embedding-subsystem theorem applies to every original tensor power.
No growth-to-birational implication is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.KeelCompleteSystem

attribute [local instance] Types.instFunLike Types.instConcreteCategory
attribute [local instance] subvariety_isIntegral

open InvertibleSheafSectionPowers

private theorem iso_hom_ne_zero_of_top_section {X : Scheme.{u}}
    (H L : InvertibleSheaf X) (e : H.obj ≅ L.obj)
    (s : H.obj.sections) (hs : s.val (op ⊤) ≠ 0) : e.hom ≠ 0 := by
  intro hz
  have hi : Function.Injective (e.hom.val.app (op ⊤)) :=
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv.injective
  have h := congrArg (fun g : H.obj ⟶ L.obj => g.val.app (op ⊤) (s.val (op ⊤))) hz
  change e.hom.val.app (op ⊤) (s.val (op ⊤)) = 0 at h
  apply hs
  apply hi
  exact h.trans (map_zero ((e.hom.val.app (op ⊤)).hom)).symm

/-- Every original complete system on an integral zero-dimensional projective
scheme is birational onto its actual image, over any field. -/
theorem birational_of_dimension_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (hproj : IsProjectiveOverField f)
    (hdim : topologicalKrullDim X = 0) (L : InvertibleSheaf X) :
    letI : IsProper f := hproj.isProper
    Birational f L := by
  letI : IsProper f := hproj.isProper
  obtain ⟨H, m, s, hcover, hclosed⟩ := hproj.exists_closedImmersion_linearSystem
  obtain ⟨eH⟩ := ZeroDimensionalBigness.nonempty_iso_unit hdim H
  obtain ⟨eL⟩ := ZeroDimensionalBigness.nonempty_iso_unit hdim L
  let e : H.obj ≅ L.obj := eH ≪≫ eL.symm
  obtain ⟨j, hj⟩ := SubsystemPositiveDimension.exists_top_ne_zero_of_cover H s hcover
  have he : e.hom ≠ 0 := iso_hom_ne_zero_of_top_section H L e (s j) hj
  have hpos := SubsystemPositiveDimension.dimension_pos_of_nonzero_map
    f H L s hcover e.hom he
  refine ⟨hpos, ?_⟩
  exact CompleteLinearSystemMap.toImage_isBirationalScheme_of_subsystem
    f H L s hcover e.hom he hclosed hpos

/-- Every power works, hence in particular every sufficiently large power works. -/
theorem eventuallyBirational_of_dimension_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (hproj : IsProjectiveOverField f)
    (hdim : topologicalKrullDim X = 0) (L : InvertibleSheaf X) :
    letI : IsProper f := hproj.isProper
    EventuallyBirational f L := by
  letI : IsProper f := hproj.isProper
  exact ⟨1, Nat.zero_lt_one, fun n _ =>
    birational_of_dimension_zero f hproj hdim (power L n)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- Non-eventual-birationality forces positive dimension on an original
irreducible subvariety of any original projective ambient scheme. -/
theorem dimension_pos_of_not_eventuallyBirational
    (hproj : IsProjectiveOverField f) (L : InvertibleSheaf X)
    (Z : IrreducibleCloseds X)
    (h : ¬ EventuallyBirational (Positivity.inclusion Z ≫ f)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L)) :
    0 < topologicalKrullDim (Z : Set X) := by
  apply lt_of_le_of_ne' (ZeroDimensionalSubvarietyBigness.dimension_nonneg Z)
  intro hzero
  exact h (eventuallyBirational_of_dimension_zero (Positivity.inclusion Z ≫ f)
    (subvariety_isProjective f hproj Z)
    ((ZeroDimensionalSubvarietyBigness.toScheme_dimension Z).trans hzero) _)

/-- The positive-dimensional support encoding omits no subvariety from
Keel's full original exceptional-subvariety condition. -/
theorem isExceptionalSubvariety_iff_not_eventuallyBirational
    (hproj : IsProjectiveOverField f) (L : InvertibleSheaf X)
    (Z : IrreducibleCloseds X) :
    IsExceptionalSubvariety f L Z ↔
      ¬ EventuallyBirational (Positivity.inclusion Z ≫ f)
        (pullbackInvertibleSheaf (Positivity.inclusion Z) L) :=
  ⟨fun h => h.2,
    fun h => ⟨dimension_pos_of_not_eventuallyBirational f hproj L Z h, h⟩⟩

end KltDP.Geometry.KeelCompleteSystem

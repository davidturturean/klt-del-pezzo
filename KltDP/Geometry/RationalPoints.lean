import KltDP.Geometry.ClosedPoints

/-!
# Actual rational points and closed scheme points

A section of a scheme's structure map to the spectrum of a field is a
closed immersion. Its underlying point is therefore closed. Conversely,
over an algebraically closed field, a closed point of a scheme locally of
finite type gives a section through its actual residue-field isomorphism.

The residue-field factorization of a morphism from a field spectrum proves
uniqueness of this section at its underlying point. Thus the rational points
of the project's actual projective surface are equivalent to its closed
scheme points. No assertion about closedness of singular points is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The underlying point of an actual morphism from the spectrum of a field. -/
def fieldMorphismPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (g : Spec (CommRingCat.of k) ⟶ X) : X :=
  g.base (IsLocalRing.closedPoint k)

/-- A field spectrum has one point, so the actual morphism has singleton range. -/
theorem range_fieldMorphism {k : Type u} [Field k] {X : Scheme.{u}}
    (g : Spec (CommRingCat.of k) ⟶ X) :
    Set.range g.base = {fieldMorphismPoint g} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact congrArg g.base (Subsingleton.elim t (IsLocalRing.closedPoint k))
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨IsLocalRing.closedPoint k, rfl⟩

/-- An actual section over a field is a closed immersion. This direction
requires neither finite type nor algebraic closedness of the field. -/
theorem section_isClosedImmersion {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Spec (CommRingCat.of k) ⟶ X)
    (hg : g ≫ f = 𝟙 (Spec (CommRingCat.of k))) : IsClosedImmersion g :=
  isClosedImmersion_of_comp_eq_id f g hg

/-- The underlying singleton of a section over a field is actually closed. -/
theorem isClosed_point_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Spec (CommRingCat.of k) ⟶ X)
    (hg : g ≫ f = 𝟙 (Spec (CommRingCat.of k))) :
    IsClosed ({fieldMorphismPoint g} : Set X) := by
  letI : IsClosedImmersion g := section_isClosedImmersion f g hg
  rw [← range_fieldMorphism g]
  exact g.isClosedEmbedding.isClosed_range

/-- The residue-field construction returns the prescribed underlying point. -/
@[simp]
theorem fieldMorphismPoint_closedPointSection {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    fieldMorphismPoint (closedPointSection f x hclosed) = x :=
  closedPointSection_base f x hclosed (IsLocalRing.closedPoint k)

/-- A section whose underlying point is `x` equals the section constructed
from the canonical base-to-residue-field isomorphism at `x`. The proof uses
the actual residue-field factorization of the given scheme morphism. -/
theorem section_eq_closedPointSection {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Spec (CommRingCat.of k) ⟶ X)
    (hg : g ≫ f = 𝟙 (Spec (CommRingCat.of k)))
    (x : X) (hclosed : IsClosed ({x} : Set X)) (hx : fieldMorphismPoint g = x) :
    g = closedPointSection f x hclosed := by
  subst x
  let e := closedPointResidueFieldIso f (fieldMorphismPoint g) hclosed
  let a := Spec.map (X.descResidueField (Scheme.stalkClosedPointTo g))
  have hfactor : a ≫ X.fromSpecResidueField (fieldMorphismPoint g) = g :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X g
  have he : Spec.map e.hom = X.fromSpecResidueField (fieldMorphismPoint g) ≫ f := by
    simpa only [e, closedPointResidueFieldIso_hom] using
      Spec_map_baseToResidueFieldMap f (fieldMorphismPoint g)
  have ha : a ≫ Spec.map e.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [he, ← Category.assoc, hfactor, hg]
  have hainv : a = Spec.map e.inv := by
    calc
      a = a ≫ (Spec.map e.hom ≫ Spec.map e.inv) := by
        rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
        exact (Category.comp_id a).symm
      _ = Spec.map e.inv := by
        rw [← Category.assoc, ha, Category.id_comp]
  calc
    g = a ≫ X.fromSpecResidueField (fieldMorphismPoint g) := hfactor.symm
    _ = closedPointSection f (fieldMorphismPoint g) hclosed := by
      rw [hainv]
      rfl

/-- Sections over an algebraically closed field are determined by their
underlying scheme point when the structure map is locally of finite type. -/
theorem section_eq_of_point_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g h : Spec (CommRingCat.of k) ⟶ X)
    (hg : g ≫ f = 𝟙 (Spec (CommRingCat.of k)))
    (hh : h ≫ f = 𝟙 (Spec (CommRingCat.of k)))
    (hpoint : fieldMorphismPoint g = fieldMorphismPoint h) : g = h := by
  let hc := isClosed_point_of_section f h hh
  exact (section_eq_closedPointSection f g hg (fieldMorphismPoint h) hc hpoint).trans
    (section_eq_closedPointSection f h hh (fieldMorphismPoint h) hc rfl).symm

/-- On a scheme locally of finite type over an algebraically closed field,
being closed is equivalent to being the underlying point of an actual
section of the structure morphism. -/
theorem isClosed_singleton_iff_exists_section {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) :
    IsClosed ({x} : Set X) ↔
      ∃ g : Spec (CommRingCat.of k) ⟶ X,
        g ≫ f = 𝟙 (Spec (CommRingCat.of k)) ∧ fieldMorphismPoint g = x := by
  constructor
  · intro hx
    exact ⟨closedPointSection f x hx, closedPointSection_over_base f x hx,
      fieldMorphismPoint_closedPointSection f x hx⟩
  · rintro ⟨g, hg, rfl⟩
    exact isClosed_point_of_section f g hg

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- The actual underlying scheme point of a rational point. -/
def RationalPoint.point (P : X.RationalPoint) : X.Point :=
  fieldMorphismPoint P.morphism

theorem RationalPoint.isClosedImmersion (P : X.RationalPoint) :
    IsClosedImmersion P.morphism :=
  section_isClosedImmersion X.structureMorphism P.morphism P.over_base

theorem RationalPoint.isClosed_point (P : X.RationalPoint) :
    IsClosed ({P.point} : Set X.Point) :=
  isClosed_point_of_section X.structureMorphism P.morphism P.over_base

@[ext]
theorem RationalPoint.ext {P Q : X.RationalPoint} (h : P.morphism = Q.morphism) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

variable [IsAlgClosed k]

@[simp]
theorem point_rationalPointOfIsClosed (X : NormalProjectiveSurface k) (x : X.Point)
    (hclosed : IsClosed ({x} : Set X.Point)) :
    (X.rationalPointOfIsClosed x hclosed).point = x :=
  fieldMorphismPoint_closedPointSection X.structureMorphism x hclosed

theorem RationalPoint.point_injective (X : NormalProjectiveSurface k) :
    Function.Injective (RationalPoint.point (X := X)) := by
  intro P Q h
  exact RationalPoint.ext
    (section_eq_of_point_eq X.structureMorphism P.morphism Q.morphism
      P.over_base Q.over_base h)

/-- The equivalence uses actual sections and actual closed points, with the
canonical residue-field construction as its inverse. -/
def rationalPointEquivClosedPoint (X : NormalProjectiveSurface k) :
    X.RationalPoint ≃ {x : X.Point // IsClosed ({x} : Set X.Point)} where
  toFun P := ⟨P.point, P.isClosed_point⟩
  invFun x := X.rationalPointOfIsClosed x.1 x.2
  left_inv P := by
    apply RationalPoint.point_injective X
    exact point_rationalPointOfIsClosed X P.point P.isClosed_point
  right_inv x := by
    apply Subtype.ext
    exact point_rationalPointOfIsClosed X x.1 x.2

end NormalProjectiveSurface

end KltDP.Geometry

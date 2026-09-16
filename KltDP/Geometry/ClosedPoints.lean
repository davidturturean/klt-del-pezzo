import KltDP.Geometry.ProjectiveFiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Residue fields and sections at actual closed points

For a scheme locally of finite type over an algebraically closed field, the
canonical base-to-residue-field map at a closed point is an isomorphism.
The map is defined by the actual composite `Spec κ(x) → X → Spec k`.
The proof turns the first morphism into a closed immersion using the
explicit closedness of `{x}`, applies Zariski's lemma, and then uses algebraic
closedness of the base field.

No point is assumed singular here, and closedness is an explicit hypothesis.
The later normal-surface proof must independently establish closedness of its
singular points before using these results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- The actual homomorphism `k → κ(x)` induced by the structure morphism.
Full faithfulness of `Spec` identifies it with the given composite of schemes. -/
def baseToResidueFieldMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    CommRingCat.of k ⟶ X.residueField x :=
  Spec.preimage (X.fromSpecResidueField x ≫ f)

@[simp]
theorem Spec_map_baseToResidueFieldMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Spec.map (baseToResidueFieldMap f x) = X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- At a closed point, the canonical residue-field morphism is an actual
closed immersion, not merely a set-theoretic inclusion of points. -/
theorem fromSpecResidueField_isClosedImmersion (X : Scheme.{u}) (x : X)
    (hclosed : IsClosed ({x} : Set X)) : IsClosedImmersion (X.fromSpecResidueField x) := by
  apply IsClosedImmersion.of_isPreimmersion (X.fromSpecResidueField x)
  simpa only [Scheme.range_fromSpecResidueField] using hclosed

/-- Closed-point residue extensions inherit finite type from the actual
structure morphism and the canonical residue-field closed immersion. -/
theorem baseToResidueFieldMap_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    (baseToResidueFieldMap f x).hom.FiniteType := by
  letI : IsClosedImmersion (X.fromSpecResidueField x) :=
    fromSpecResidueField_isClosedImmersion X x hclosed
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec_map_baseToResidueFieldMap f x] at hcomp
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hcomp

/-- Zariski's lemma makes the actual residue extension at a closed point a
finite extension of the base field. -/
theorem baseToResidueFieldMap_finite {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    (baseToResidueFieldMap f x).hom.Finite :=
  RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr
    (baseToResidueFieldMap_finiteType f x hclosed)

/-- Over an algebraically closed field, the same canonical map `k → κ(x)`
is bijective. No independent choice of a field isomorphism is used. -/
theorem baseToResidueFieldMap_bijective {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    Function.Bijective (baseToResidueFieldMap f x).hom :=
  IsAlgClosed.ringHom_bijective_of_isIntegral (baseToResidueFieldMap f x).hom
    (baseToResidueFieldMap_finite f x hclosed).to_isIntegral

/-- The base-to-residue-field ring isomorphism at an actual closed point. -/
def closedPointResidueFieldEquiv {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) : k ≃+* X.residueField x :=
  RingEquiv.ofBijective (baseToResidueFieldMap f x).hom
    (baseToResidueFieldMap_bijective f x hclosed)

/-- The same isomorphism in the category of commutative rings. -/
def closedPointResidueFieldIso {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    CommRingCat.of k ≅ X.residueField x :=
  (closedPointResidueFieldEquiv f x hclosed).toCommRingCatIso

@[simp]
theorem closedPointResidueFieldIso_hom {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    (closedPointResidueFieldIso f x hclosed).hom = baseToResidueFieldMap f x := rfl

/-- The closed point as a `k`-valued point of the actual scheme. -/
def closedPointSection {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) : Spec (CommRingCat.of k) ⟶ X :=
  Spec.map (closedPointResidueFieldIso f x hclosed).inv ≫ X.fromSpecResidueField x

/-- The constructed point is a section of the given structure map. -/
theorem closedPointSection_over_base {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) :
    closedPointSection f x hclosed ≫ f = 𝟙 (Spec (CommRingCat.of k)) := by
  rw [closedPointSection, Category.assoc, ← Spec_map_baseToResidueFieldMap f x,
    ← closedPointResidueFieldIso_hom f x hclosed, ← Spec.map_comp,
    Iso.hom_inv_id, Spec.map_id]

/-- Its underlying point is the prescribed point `x`. -/
theorem closedPointSection_base {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (x : X) (hclosed : IsClosed ({x} : Set X)) (t : Spec (CommRingCat.of k)) :
    (closedPointSection f x hclosed).base t = x := by
  change (X.fromSpecResidueField x).base _ = x
  exact X.fromSpecResidueField_apply x _

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- A closed point gives the existing actual rational-point structure. -/
def rationalPointOfIsClosed (x : X.Point) (hclosed : IsClosed ({x} : Set X.Point)) :
    X.RationalPoint where
  morphism := closedPointSection X.structureMorphism x hclosed
  over_base := closedPointSection_over_base X.structureMorphism x hclosed

end NormalProjectiveSurface

end KltDP.Geometry

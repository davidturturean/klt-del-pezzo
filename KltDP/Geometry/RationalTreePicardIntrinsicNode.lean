import KltDP.Geometry.AffineFiniteType
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Intrinsic geometric nodes on the original scheme

The scalar action on an original stalk comes from its canonical scheme
map to the given affine base. Its compatibility with every original
affine neighborhood is proved below. Completion uses this same action.

The ordinary-double-point normal form is used only over an algebraically
closed field, as in Stacks 0C1W and the discussion before 0C47. A node over
an arbitrary field is witnessed on the actual algebraic-closure base
change. The defining isomorphism is an algebra isomorphism over that
algebraic closure, not an isomorphism with unrelated coefficients.

These are local predicates. Dimension one and local finite type remain
separate hypotheses of any curve theorem using them. No component ideal,
ambient embedding, branch position, or cut-intersection conclusion is
part of a predicate. No nodal-cut theorem is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.IntrinsicNodal

section StalkScalars

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The scalar map determined by the original canonical stalk morphism
and the given structure morphism to the actual affine base. -/
def baseToStalkMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    CommRingCat.of R ⟶ X.presheaf.stalk x :=
  Spec.preimage (X.fromSpecStalk x ≫ f)

@[simp]
theorem Spec_map_baseToStalkMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    Spec.map (baseToStalkMap f x) = X.fromSpecStalk x ≫ f :=
  Spec.map_preimage _

/-- The original affine scalar map followed by the original section germ
is independent of the affine neighborhood and equals the stalk scalar map. -/
@[reassoc]
theorem baseToAffineSectionsMap_germ (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    baseToAffineSectionsMap f hU ≫ X.presheaf.germ U x hx =
      baseToStalkMap f x := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_baseToAffineSectionsMap, Spec_map_baseToStalkMap,
    ← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hx]
  rfl

/-- This map is also the literal map from the base's global sections to
its stalk, followed by the original structure morphism's stalk map. -/
theorem baseToStalkMap_eq_germ_stalkMap
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    baseToStalkMap f x =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base x) trivial ≫
          f.stalkMap x := by
  apply Spec.map_injective
  rw [Spec_map_baseToStalkMap, ← Category.assoc, Spec.map_comp,
    ← Scheme.Spec_fromSpecStalk, Scheme.Spec_map_stalkMap_fromSpecStalk]

/-- The actual stalk maps respect the same original base map. -/
@[reassoc]
theorem baseToStalkMap_comp (g : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    baseToStalkMap (g ≫ f) x = baseToStalkMap f (g.base x) ≫ g.stalkMap x := by
  apply Spec.map_injective
  simp only [Spec.map_comp, Spec_map_baseToStalkMap,
    Scheme.Spec_map_stalkMap_fromSpecStalk_assoc]

/-- A named algebra structure for the actual stalk, with no global
instance that could silently choose a different scheme structure map. -/
abbrev stalkAlgebra (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    Algebra R (X.presheaf.stalk x) :=
  (baseToStalkMap f x).hom.toAlgebra

@[simp]
theorem stalkAlgebra_algebraMap (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    letI := stalkAlgebra f x
    algebraMap R (X.presheaf.stalk x) = (baseToStalkMap f x).hom := rfl

/-- The section germ is an algebra homomorphism for the two structures
induced by the same original map to the base. -/
def affineGermAlgHom (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI := affineSectionsAlgebra f hU
    letI := stalkAlgebra f x
    Γ(X, U) →ₐ[R] X.presheaf.stalk x := by
  letI := affineSectionsAlgebra f hU
  letI := stalkAlgebra f x
  refine { (X.presheaf.germ U x hx).hom with commutes' := ?_ }
  intro r
  exact congrArg (fun φ : CommRingCat.of R ⟶ X.presheaf.stalk x => φ.hom r)
    (baseToAffineSectionsMap_germ f hU x hx)

@[simp]
theorem affineGermAlgHom_toRingHom (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI := affineSectionsAlgebra f hU
    letI := stalkAlgebra f x
    (affineGermAlgHom f hU x hx).toRingHom = (X.presheaf.germ U x hx).hom := rfl

end StalkScalars

/-- Completion at the maximal ideal of the original scheme stalk. -/
abbrev completedStalk (X : Scheme.{u}) (x : X) :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)

/-- The complete local model appearing immediately before Stacks 0C47,
with its canonical coefficient-algebra structure. -/
abbrev ordinaryDoublePointModel (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k ⧸ Ideal.span
    ({MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)} :
      Set (MvPowerSeries (Fin 2) k))

/-- The algebraically closed ordinary-double-point predicate. The scalar
action on completion is induced by the actual structure morphism. -/
def IsOrdinaryDoublePoint {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X) : Prop :=
  letI := stalkAlgebra f x
  IsClosed ({x} : Set X) ∧
    Nonempty (completedStalk X x ≃ₐ[k] ordinaryDoublePointModel k)

section GeometricBaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The original field's canonical algebraic-closure morphism. -/
abbrev algebraicClosureToSpec : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶
    Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- Actual base change of the original scheme along `Spec(k̄) → Spec(k)`. -/
abbrev geometricBaseChange : Scheme.{u} :=
  pullback f (algebraicClosureToSpec (k := k))

/-- Its original projection to the given scheme. -/
abbrev geometricProjection : geometricBaseChange f ⟶ X :=
  pullback.fst f (algebraicClosureToSpec (k := k))

/-- Its actual structure morphism over the algebraic closure. -/
abbrev geometricStructure : geometricBaseChange f ⟶
    Spec (CommRingCat.of (AlgebraicClosure k)) :=
  pullback.snd f (algebraicClosureToSpec (k := k))

/-- The base-change square retains both original structure morphisms. -/
@[reassoc]
theorem geometricProjection_over :
    geometricProjection f ≫ f =
      geometricStructure f ≫ algebraicClosureToSpec (k := k) :=
  pullback.condition

/-- Local algebraicity survives the actual algebraic-closure base change. -/
instance geometricStructure_locallyOfFiniteType [LocallyOfFiniteType f] :
    LocallyOfFiniteType (geometricStructure f) := by
  dsimp only [geometricStructure]
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- Stacks 0C47's geometric definition: an original closed point has an
ordinary double point above it on the actual algebraic-closure base change. -/
def IsNode (x : X) : Prop :=
  IsClosed ({x} : Set X) ∧
    ∃ y : geometricBaseChange f,
      (geometricProjection f).base y = x ∧ IsOrdinaryDoublePoint (geometricStructure f) y

theorem IsNode.isClosed {x : X} (hx : IsNode f x) : IsClosed ({x} : Set X) := hx.1

/-- Unfolding the geometric definition retains the actual completed stalk
and the coefficient field of its actual base-change structure morphism. -/
theorem isNode_iff (x : X) :
    IsNode f x ↔ IsClosed ({x} : Set X) ∧
      ∃ y : geometricBaseChange f,
        (geometricProjection f).base y = x ∧
          (letI := stalkAlgebra (geometricStructure f) y
           IsClosed ({y} : Set (geometricBaseChange f)) ∧
             Nonempty (completedStalk (geometricBaseChange f) y ≃ₐ[AlgebraicClosure k]
               ordinaryDoublePointModel (AlgebraicClosure k))) := Iff.rfl

end GeometricBaseChange

/-- Smoothness at an original point means smoothness on an actual open
neighborhood, using pinned scheme smoothness. -/
def IsSmoothAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ IsSmooth (U.ι ≫ f)

theorem isSmoothAt_of_isSmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSmooth f] (x : X) :
    IsSmoothAt f x :=
  ⟨⊤, trivial, inferInstance⟩

/-- The closed-point quantifier and alternatives are those of Stacks
0C47. This predicate permits reducible schemes and has no ambient scheme. -/
def HasAtWorstNodalSingularities {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → IsSmoothAt f x ∨ IsNode f x

theorem hasAtWorstNodalSingularities_of_isSmooth {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSmooth f] :
    HasAtWorstNodalSingularities f :=
  fun x _ => Or.inl (isSmoothAt_of_isSmooth f x)

end KltDP.Geometry.IntrinsicNodal

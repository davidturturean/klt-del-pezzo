import KltDP.Geometry.SchemeModulePullbackTensor

/-!
# Pullback on the actual Picard group

The original scheme-module pullback sends actual isomorphisms to
isomorphisms. Its proved tensor and unit comparisons therefore induce
a homomorphism on the tensor monoid of sheaf isomorphism classes. Taking
units gives the pullback on the existing Picard group.

Identity and composition use the actual functor isomorphisms. No
Cartier representative, integrality hypothesis, or rational pullback is
needed for this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X)

/-- The action of the actual pullback functor on actual sheaf isomorphism classes. -/
def schemeModulePullbackClassMap : Skeleton X.Modules → Skeleton Y.Modules :=
  Quotient.map (schemeModulePullback f).obj
    (fun _ _ h => h.map (fun e => (schemeModulePullback f).mapIso e))

@[simp]
theorem schemeModulePullbackClassMap_toSkeleton (M : X.Modules) :
    schemeModulePullbackClassMap f (toSkeleton M) =
      toSkeleton ((schemeModulePullback f).obj M) := rfl

/-- Tensor and unit preservation on the existing tensor monoids of classes. -/
def schemeModulePullbackClassHom :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    Skeleton X.Modules →* Skeleton Y.Modules := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact {
    toFun := schemeModulePullbackClassMap f
    map_one' := by
      rw [Skeleton.one_eq, schemeModulePullbackClassMap_toSkeleton, Skeleton.one_eq]
      exact Quotient.sound ⟨schemeModulePullbackTensorUnitIso f⟩
    map_mul' := by
      intro a b
      refine Quotient.inductionOn₂ a b (fun M N => ?_)
      change schemeModulePullbackClassMap f (toSkeleton M * toSkeleton N) =
        schemeModulePullbackClassMap f (toSkeleton M) *
          schemeModulePullbackClassMap f (toSkeleton N)
      rw [← Skeleton.toSkeleton_tensorObj, schemeModulePullbackClassMap_toSkeleton,
        schemeModulePullbackClassMap_toSkeleton, schemeModulePullbackClassMap_toSkeleton,
        ← Skeleton.toSkeleton_tensorObj]
      exact Quotient.sound ⟨schemeModulePullbackTensorIso f M N⟩ }

/-- Pullback on the original actual Picard group of any scheme. -/
def schemePicardPullbackHom : X.Pic →* Y.Pic := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  exact Units.map (schemeModulePullbackClassHom f)

/-- Identity on classes follows from the actual pullback identity isomorphism. -/
theorem schemeModulePullbackClassMap_id (a : Skeleton X.Modules) :
    schemeModulePullbackClassMap (𝟙 X) a = a := by
  refine Quotient.inductionOn a (fun M => ?_)
  exact Quotient.sound ⟨(schemeModulePullbackIdIso X).app M⟩

/-- Composition on classes follows from the actual pullback composition isomorphism. -/
theorem schemeModulePullbackClassMap_comp (g : Z ⟶ Y) (a : Skeleton X.Modules) :
    schemeModulePullbackClassMap (g ≫ f) a =
      schemeModulePullbackClassMap g (schemeModulePullbackClassMap f a) := by
  refine Quotient.inductionOn a (fun M => ?_)
  exact Quotient.sound ⟨((schemeModulePullbackCompIso g f).app M).symm⟩

/-- Actual Picard pullback along the identity is the identity homomorphism. -/
theorem schemePicardPullbackHom_id (X : Scheme.{u}) :
    schemePicardPullbackHom (𝟙 X) = MonoidHom.id X.Pic := by
  letI := Scheme.Modules.monoidalCategory X
  apply MonoidHom.ext
  intro p
  apply Units.ext
  change schemeModulePullbackClassMap (𝟙 X)
    (show (Skeleton X.Modules)ˣ from p).val = (show (Skeleton X.Modules)ˣ from p).val
  exact schemeModulePullbackClassMap_id _

/-- Actual Picard pullback is contravariantly compatible with composition. -/
theorem schemePicardPullbackHom_comp (g : Z ⟶ Y) :
    schemePicardPullbackHom (g ≫ f) =
      (schemePicardPullbackHom g).comp (schemePicardPullbackHom f) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  letI := Scheme.Modules.monoidalCategory Z
  apply MonoidHom.ext
  intro p
  apply Units.ext
  change schemeModulePullbackClassMap (g ≫ f)
    (show (Skeleton X.Modules)ˣ from p).val =
      schemeModulePullbackClassMap g (schemeModulePullbackClassMap f
        (show (Skeleton X.Modules)ˣ from p).val)
  exact schemeModulePullbackClassMap_comp f g _

end KltDP.Geometry

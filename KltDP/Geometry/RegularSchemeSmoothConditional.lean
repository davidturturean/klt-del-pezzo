import KltDP.Geometry.AffineSmoothLocalizationTransport
import KltDP.Geometry.RegularLocalDimensionTwo

/-!
# Conditional regular-to-smooth specialization on the original scheme

The two source hypotheses are explicit and generic. The first retains the
native algebraic smooth-locus equality, openness and density of Stacks
0B8X. The second is the separately stated standard-smooth cover assertion
of Stacks 00TA, over arbitrary commutative rings.

This ordinary consumer adds no source axiom or opaque source predicate.
Its conclusion concerns the given scheme morphism and its actual stalks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RegularSchemeSmoothConditional

/-- A regular reduced scheme locally of finite type over a perfect field
is smooth, conditional on the two full explicit generic source assertions.
No surface, properness, dimension or geometric-regularity premise is used. -/
theorem isSmooth_of_regularPoints
    (h0B8X : ∀ (k₀ : Type u) [Field k₀] [PerfectField k₀]
      (X₀ : Scheme.{u}) [AlgebraicGeometry.IsReduced X₀]
      (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f₀],
      let L : Set X₀ := {x | AffineSmoothLocalizationTransport.algebraSmoothAt f₀ x}
      let G : Set X₀ := {x | RegularLocalByGenerators (X₀.presheaf.stalk x)}
      L = G ∧ IsOpen L ∧ Dense L)
    (h00TA : ∀ (R A : Type u) [CommRing R] [CommRing A] (φ : R →+* A),
      (letI : Algebra R A := φ.toAlgebra
       Algebra.Smooth R A) →
      ∃ T : Set A, Ideal.span T = ⊤ ∧ ∀ g ∈ T,
        RingHom.IsStandardSmooth ((algebraMap A (Localization.Away g)).comp φ))
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hreg : ∀ x, RegularPoint X x) : IsSmooth f := by
  have hloc : {x : X | AffineSmoothLocalizationTransport.algebraSmoothAt f x} =
      {x : X | RegularLocalByGenerators (X.presheaf.stalk x)} :=
    (h0B8X k X f).1
  have hnative : ∀ x : X, AffineSmoothLocalizationTransport.algebraSmoothAt f x := by
    intro x
    change x ∈ {x : X | AffineSmoothLocalizationTransport.algebraSmoothAt f x}
    rw [hloc]
    exact regularLocalByGenerators_of_regularLocal (hreg x)
  apply AffineSmoothLocalizationTransport.isSmooth_of_algebraSmoothAt_of_localization_covers
    f hnative
  intro U V e hsm
  exact h00TA Γ(Spec (CommRingCat.of k), U.1) Γ(X, V.1)
    (f.appLE U V e).hom hsm

end KltDP.Geometry.RegularSchemeSmoothConditional

#check @KltDP.Geometry.RegularSchemeSmoothConditional.isSmooth_of_regularPoints
#print axioms KltDP.Geometry.RegularSchemeSmoothConditional.isSmooth_of_regularPoints


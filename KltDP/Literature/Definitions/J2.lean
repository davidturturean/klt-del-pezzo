import KltDP.Geometry.RegularLocalDimensionTwo
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The J-1 and J-2 definitions in the Stacks Project

This file contains definitions only, with no literature axioms. The Stacks
Project, tag 07P7, defines J-1 for a Noetherian ring by openness of its regular
prime locus, and J-2 by requiring every finite-type algebra to be J-1.
Regularity uses the maximal-ideal generator definition of tag 00KU.

The algebra universe is independent of the base-ring universe. These
predicates impose no domain, dimension, characteristic, or geometric
assumptions beyond the published definitions.
-/

universe u v

namespace KltDP.Literature

/-- The regular primes using the source's actual maximal-ideal generator
condition on the original ring's prime localizations. -/
def generatorRegularLocus (R : Type u) [CommRing R] : Set (PrimeSpectrum R) :=
  {p | Geometry.RegularLocalByGenerators (Localization.AtPrime p.asIdeal)}

/-- Stacks 07P7, J-1, retaining its Noetherian-ring hypothesis. -/
def J1Ring (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ IsOpen (generatorRegularLocus R)

/-- Stacks 07P7, J-2: every finite-type algebra is J-1. Both the base and
algebra are actual commutative rings with their given algebra map. -/
def J2Ring (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], J1Ring A

/-- Applying the definition retains the exact algebra structure supplied
by the caller; this is the entire J-2 to affine-openness specialization. -/
theorem J2Ring.isOpen_generatorRegularLocus
    {R : Type u} [CommRing R] (hR : J2Ring.{u, v} R)
    (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsOpen (generatorRegularLocus A) :=
  (hR.2 A).2

end KltDP.Literature

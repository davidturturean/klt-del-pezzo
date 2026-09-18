import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Geometry.NefTwistedMaps
import KltDP.Geometry.InvertibleNonzeroIsoOpen

/-!
# Actual maps into powers of the original Frobenius contracting line

The original line M has the proved class B + (n-2)b, is nef, and has square
(q+1)(n-2). The existing eventual twisted-map theorem therefore supplies
nonzero maps from any original line H into every sufficiently high power
of M. Every such nonzero map is an isomorphism on an actual nonempty dense
open of the original multicentre surface.

The Riemann--Roch dependency remains in the existing private, unaccepted
branch. No bigness, semiampleness, generation, or contraction premise is added.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreEmbeddingSubsystem

open NormalProjectiveSurface InvertibleSheafSectionPowers
open KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreIntegral
open KltDP.Examples.FrobeniusMultiCentreContractingNef

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Any original line maps nontrivially into every sufficiently high power
of the original contracting line when there are more than two centres. -/
theorem contractingLine_eventually_nonzero_map (hn : 2 < n)
    (H : InvertibleSheaf (multiSurface (q + 1) n a)) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      ∃ g : H.obj ⟶ (power (contractingLine q n a ha hproj) m).obj, g ≠ 0 := by
  letI : IsSmoothOfRelativeDimension 2
      (multiSurfaceSurface (q + 1) n a ha hproj).structureMorphism :=
    multiStructure_smoothTwo (q + 1) n a ha
  letI : IsSmooth (multiSurfaceSurface (q + 1) n a ha hproj).structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 _
  apply NefTwistedMaps.eventually_nonzero_map
    (multiSurfaceSurface (q + 1) n a ha hproj) (contractingLine q n a ha hproj) H
    (contractingLine_isNef q n a ha hproj hn.le)
  change 0 < (multiSurfaceSurface (q + 1) n a ha hproj).picardPairing
    (multiSurfaceSurface (q + 1) n a ha hproj).regularPoints_of_isSmooth
    (cartierPicardClass (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj))
    (cartierPicardClass (multiSurfaceSurface (q + 1) n a ha hproj).toScheme
      (contractingDivisor q n a ha hproj))
  rw [(multiSurfaceSurface (q + 1) n a ha hproj).picardPairing_class,
    contractingDivisor_square]
  have hn' : (2 : ℤ) < n := by exact_mod_cast hn
  exact mul_pos (by positivity) (sub_pos.mpr hn')

/-- Every nonzero original map into a power of M is an isomorphism on an
actual nonempty dense open of the original surface. -/
theorem nonzero_map_isIso_dense_open
    (H : InvertibleSheaf (multiSurface (q + 1) n a)) (m : ℕ)
    (g : H.obj ⟶ (power (contractingLine q n a ha hproj) m).obj) (hg : g ≠ 0) :
    ∃ U : (multiSurface (q + 1) n a).Opens, Nonempty U ∧
      Dense (U : Set (multiSurface (q + 1) n a)) ∧
      IsIso ((schemeModulePullback U.ι).map g) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨U, hU, hIso⟩ := InvertibleNonzeroIsoOpen.exists_isIso_open
    (multiSurface (q + 1) n a) H (power (contractingLine q n a ha hproj) m) g hg
  refine ⟨U, hU, U.2.dense ?_, hIso⟩
  obtain ⟨x⟩ := hU
  exact ⟨x.1, x.2⟩

/-- The eventual original maps come with actual dense-open isomorphism
witnesses; no generic-isomorphism condition is supplied. -/
theorem contractingLine_eventually_isIso_dense_open (hn : 2 < n)
    (H : InvertibleSheaf (multiSurface (q + 1) n a)) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      ∃ g : H.obj ⟶ (power (contractingLine q n a ha hproj) m).obj, g ≠ 0 ∧
        ∃ U : (multiSurface (q + 1) n a).Opens, Nonempty U ∧
          Dense (U : Set (multiSurface (q + 1) n a)) ∧
          IsIso ((schemeModulePullback U.ι).map g) := by
  obtain ⟨N, hN, hmaps⟩ := contractingLine_eventually_nonzero_map q n a ha hproj hn H
  refine ⟨N, hN, ?_⟩
  intro m hm
  obtain ⟨g, hg⟩ := hmaps m hm
  exact ⟨g, hg, nonzero_map_isIso_dense_open q n a ha hproj H m g hg⟩

end KltDP.Geometry.FrobeniusMultiCentreEmbeddingSubsystem

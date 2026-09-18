import KltDP.Geometry.FrobeniusMultiCentreNormalFactor
import KltDP.Geometry.ProperSteinConnected

/-!
The same original Frobenius normal proper ample factor has geometrically
connected fibers and connected nonempty point fibers. This strengthens
the existing witness using its proper source map and original canonical
structure-sheaf isomorphism; the target, field triangle, ample line and
positive-power pullback iso are unchanged.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  InvertibleSheafSectionPowers

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- Connected fibers of the same actual normal proper ample factor of
the original Frobenius contracting line, without new geometric premises. -/
theorem normal_proper_ample_factor_connected (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y),
              ConnectedSpace (pullback π y : Scheme.{u})) ∧
            (∀ y : Y, IsConnected (π.base ⁻¹' {y})) ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅
                (power (originalLine q n a ha) m).obj) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, Y, σ, hσ, hnormalY, hY, hfactor⟩ :=
    normal_proper_ample_factor q n a ha hn
  letI : IsIntegral Y := hY
  obtain ⟨π, hπσ, hπ, hsurj, hbir, hc, A, hA, hpull⟩ := hfactor
  letI : IsProper σ := hσ
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_spec σ
  letI : IsProper π := hπ
  letI : IsIso π.c := hc
  exact ⟨m, hm, Y, σ, hσ, hnormalY, hY, π, hπσ, hπ, hsurj, hbir, hc,
    ProperSteinConnected.geometrically_connected π,
    ProperSteinConnected.pointFibers_connected π, A, hA, hpull⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

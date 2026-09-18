import KltDP.Geometry.SemiampleNormalFactor
import KltDP.Geometry.ProperSteinConnected

/-!
Connectedness of the same normal proper ample factor already constructed.
The original proper target is locally Noetherian over its field. The
original source map's properness and canonical structure-sheaf isomorphism
then give every field-valued fiber and every point fiber connectedness.
All existing witnesses, including the ample line and its pullback iso,
are retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.SemiampleNormalFactor

open InvertibleSheafSectionPowers

/-- The existing normal proper ample factor has geometrically connected
and connected nonempty point fibers, for the same original source map. -/
theorem normal_proper_ample_factor_connected
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (L : InvertibleSheaf X)
    (hnormal : IsNormalScheme X) (hsemi : Positivity.IsSemiample L)
    (hevent : KeelCompleteSystem.EventuallyBirational f L) :
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : X ⟶ Y, π ≫ σ = f ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            (∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
              ConnectedSpace (pullback π q : Scheme.{u})) ∧
            (∀ y : Y, IsConnected (π.base ⁻¹' {y})) ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power L m).obj) := by
  obtain ⟨m, hm, Y, σ, hσ, hnormalY, hY, hfactor⟩ :=
    normal_proper_ample_factor f L hnormal hsemi hevent
  letI : IsIntegral Y := hY
  obtain ⟨π, hπσ, hπ, hsurj, hbir, hc, A, hA, hpull⟩ := hfactor
  letI : IsProper σ := hσ
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_spec σ
  letI : IsProper π := hπ
  letI : IsIso π.c := hc
  exact ⟨m, hm, Y, σ, hσ, hnormalY, hY, π, hπσ, hπ, hsurj, hbir, hc,
    ProperSteinConnected.geometrically_connected π,
    ProperSteinConnected.pointFibers_connected π, A, hA, hpull⟩

end KltDP.Geometry.SemiampleNormalFactor

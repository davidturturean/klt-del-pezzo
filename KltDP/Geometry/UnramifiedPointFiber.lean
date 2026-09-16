import KltDP.Compatibility.IdealGermEquality
import KltDP.Geometry.EtaleCoordinateTranslation
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# A reduced selected fiber on an actual principal neighborhood

The pinned local criterion for an unramified morphism identifies the
extended base prime with the maximal ideal of the actual source stalk.
Finite generation then spreads that equality to a principal open.
For a closed source point the resulting actual quotient ideal is maximal,
so this isolates the reduced selected point, including its scheme structure.
-/

noncomputable section

open AlgebraicGeometry

namespace KltDP.Geometry

universe u

/-- The actual extended base prime and source prime have equal ideals
in the source's prime localization, by the pinned unramified criterion. -/
theorem unramified_fiber_ideal_eq_atPrime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime q)) =
      q.map (algebraMap S (Localization.AtPrime q)) := by
  have hq : Algebra.IsUnramifiedAt R q := inferInstance
  have heq := ((Algebra.isUnramifiedAt_iff_map_eq R p q).mp hq).2
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    heq, Localization.AtPrime.map_eq_maximalIdeal]

/-- A finitely generated source prime in an unramified fiber is the
actual fiber ideal on some principal neighborhood of that point. -/
theorem exists_away_unramified_fiber_ideal_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (hq : q.FG) :
    ∃ r : S, r ∉ q ∧
      (p.map (algebraMap R S)).map (algebraMap S (Localization.Away r)) =
        q.map (algebraMap S (Localization.Away r)) := by
  apply KltDP.Compatibility.exists_away_ideal_eq_of_atPrime_eq
    q (p.map (algebraMap R S)) q
  · exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (q.over_def p))
  · exact hq
  · exact unramified_fiber_ideal_eq_atPrime p q

/-- For a closed source point the actual isolated fiber ideal is maximal.
In particular, the quotient has no nilpotent thickening of the point. -/
theorem exists_away_unramified_closed_fiber
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsMaximal] [q.LiesOver p]
    (hq : q.FG) :
    ∃ r : S, r ∉ q ∧
      (p.map (algebraMap R S)).map (algebraMap S (Localization.Away r)) =
        q.map (algebraMap S (Localization.Away r)) ∧
      ((p.map (algebraMap R S)).map
        (algebraMap S (Localization.Away r))).IsMaximal := by
  obtain ⟨r, hr, heq⟩ := exists_away_unramified_fiber_ideal_eq p q hq
  refine ⟨r, hr, heq, ?_⟩
  rw [heq]
  exact KltDP.Compatibility.isMaximal_map_away q r hr

namespace EtaleCoordinates

/-- The source point defined by an actual algebra character lies over
the origin after the proved coordinate translation. -/
theorem centeredCharacter_liesOver_origin
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] {n : ℕ}
    (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k) :
    letI := (centeredCoordinateMap g χ).toRingHom.toAlgebra
    (RingHom.ker χ.toRingHom).LiesOver
      (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom) := by
  letI := (centeredCoordinateMap g χ).toRingHom.toAlgebra
  constructor
  change RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom =
    (RingHom.ker χ.toRingHom).comap (centeredCoordinateMap g χ).toRingHom
  rw [RingHom.comap_ker]
  exact congrArg (fun h : MvPolynomial (Fin n) k →ₐ[k] k ↦ RingHom.ker h.toRingHom)
    (character_comp_centeredCoordinateMap g χ).symm

/-- The inverse-image origin ideal of the actual centered étale map
equals the chosen character's actual maximal ideal on a constructed
principal open. The maximal-ideal conclusion retains the reduced scheme
structure of the isolated point, not only its underlying support. -/
theorem exists_away_centered_coordinate_fiber
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] [IsNoetherianRing S]
    {n : ℕ} (g : MvPolynomial (Fin n) k →ₐ[k] S) (χ : S →ₐ[k] k)
    (hg : g.toRingHom.IsStandardSmoothOfRelativeDimension 0) :
    ∃ r : S, χ r ≠ 0 ∧
      ((RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom).map
        (centeredCoordinateMap g χ).toRingHom).map
          (algebraMap S (Localization.Away r)) =
        (RingHom.ker χ.toRingHom).map (algebraMap S (Localization.Away r)) ∧
      (((RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom).map
        (centeredCoordinateMap g χ).toRingHom).map
          (algebraMap S (Localization.Away r))).IsMaximal := by
  letI := (centeredCoordinateMap g χ).toRingHom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) k) S :=
    centeredCoordinateMap_standardSmoothZero g χ hg
  letI : (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  letI : (RingHom.ker χ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χ.toRingHom (fun a ↦
      ⟨algebraMap k S a, by simpa using χ.commutes a⟩)
  letI : (RingHom.ker χ.toRingHom).LiesOver
      (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom) :=
    centeredCharacter_liesOver_origin g χ
  obtain ⟨r, hr, heq, hmax⟩ := exists_away_unramified_closed_fiber
    (RingHom.ker (MvPolynomial.aeval (R := k) (fun _ : Fin n ↦ (0 : k))).toRingHom)
    (RingHom.ker χ.toRingHom) (IsNoetherian.noetherian _)
  exact ⟨r, hr, heq, hmax⟩

end EtaleCoordinates

end KltDP.Geometry

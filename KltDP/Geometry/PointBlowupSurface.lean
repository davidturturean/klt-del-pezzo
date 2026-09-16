import KltDP.Geometry.PointBlowupIntegral
import KltDP.Geometry.PrimeCurveCodimension
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# Nonempty point blowups of actual surfaces

A closed point of an integral surface cannot be its generic point: otherwise
every point would coincide with it, contradicting dimension two. The actual
prime ideal of that point in any affine open chart is therefore nonzero.
This discharges the essential nonzero-center hypothesis of the actual glued
blowup without storing it as part of the surface or blowup data.

The topology and dimension argument reuses the pinned generic-point API and
the existing `topologicalKrullDim_nonpos_of_subsingleton` theorem. Local
Noetherianity and finite generation come from the actual projective embedding.
No new dimension formula or connected-fiber result is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- On an actual integral surface, no closed point is the generic point. -/
theorem NormalProjectiveSurface.closedPoint_ne_genericPoint
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (x : X.toScheme) (hx : IsClosed ({x} : Set X.toScheme)) :
    x ≠ genericPoint X.toScheme := by
  intro h
  have hall : (Set.univ : Set X.toScheme) ⊆ {x} :=
    ((genericPoint_spec X.toScheme).mem_closed_set_iff hx).mp
      (Set.mem_singleton_iff.mpr h.symm)
  letI : Subsingleton X.toScheme := ⟨fun a b =>
    (Set.mem_singleton_iff.mp (hall (Set.mem_univ a))).trans
      (Set.mem_singleton_iff.mp (hall (Set.mem_univ b))).symm⟩
  have hd := topologicalKrullDim_nonpos_of_subsingleton X.toScheme
  rw [X.dimension_two] at hd
  have hpos : (0 : WithBot ℕ∞) < 2 :=
    WithBot.coe_lt_coe.mpr (by simp : (0 : ℕ∞) < 2)
  exact hpos.not_le hd

/-- The actual prime ideal of a globally closed point in an affine open
chart of the surface is nonzero. The chart ring is proved to be a domain. -/
theorem NormalProjectiveSurface.affine_closed_point_ideal_ne_bot
    {k R : Type u} [Field k] [CommRing R] (X : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) (hclosed : IsClosed ({j.base q} : Set X.toScheme)) :
    q.asIdeal ≠ ⊥ := by
  letI : Nonempty (Spec (CommRingCat.of R)) := ⟨q⟩
  letI : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion j
  letI : IsDomain R := PointBlowupGluing.affine_open_chart_isDomain_of_integral j q
  intro hq
  have hqbot : q = (⊥ : PrimeSpectrum R) := PrimeSpectrum.ext hq
  apply X.closedPoint_ne_genericPoint (j.base q) hclosed
  rw [hqbot, ← genericPoint_eq_bot_of_affine (CommRingCat.of R)]
  exact genericPoint_eq_of_isOpenImmersion j

/-- The original projective surface supplies finite generation of the
actual affine center ideal. No finite-generation field is added. -/
theorem NormalProjectiveSurface.affine_point_ideal_fg
    {k R : Type u} [Field k] [CommRing R] (X : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) : q.asIdeal.FG := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  letI : IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    isLocallyNoetherian_of_isOpenImmersion j
  letI : IsNoetherianRing Γ(Spec (CommRingCat.of R), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩
  letI : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv Γ(Spec (CommRingCat.of R), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  exact IsNoetherian.noetherian q.asIdeal

namespace PointBlowupGluing

variable {k R : Type u} [Field k] [CommRing R] (X : NormalProjectiveSurface k)
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- The actual glued blowup of a closed point on the surface is integral. -/
theorem surface_scheme_isIntegral : IsIntegral (scheme j q hclosed) :=
  scheme_isIntegral j q hclosed (X.affine_closed_point_ideal_ne_bot j q hclosed)

/-- The surface generic point belongs to the actual unchanged puncture. -/
theorem surface_genericPoint_mem_puncture :
    genericPoint X.toScheme ∈ puncture j q hclosed :=
  genericPoint_mem_puncture j q hclosed
    (X.affine_closed_point_ideal_ne_bot j q hclosed)

/-- The actual surface blowup projection maps the actual generic point to
the original surface generic point; nonzero center is a proved consequence. -/
theorem surface_projection_genericPoint :
    letI : IsIntegral (scheme j q hclosed) := surface_scheme_isIntegral X j q hclosed
    (projection j q hclosed).base (genericPoint (scheme j q hclosed)) =
      genericPoint X.toScheme := by
  exact projection_genericPoint j q hclosed
    (X.affine_closed_point_ideal_ne_bot j q hclosed)

end PointBlowupGluing

end KltDP.Geometry

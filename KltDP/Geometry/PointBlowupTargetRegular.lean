import KltDP.Geometry.Resolution
import KltDP.Geometry.RegularLocalEquiv

/-!
# Target regularity from the original blowup complement and center

The unchanged complement is an actual open subscheme of both schemes.
Regularity therefore transports on that complement through the original
stalk isomorphisms. The only remaining target point is the given regular
center. This removes global target regularity from a first-kind contraction
translation; it does not assert existence of the contraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Outside the original center, the actual glued blowup has the same
local rings as the target. Regularity at the center completes the target. -/
theorem PointBlowupGluing.target_regular
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (hregular : ∀ s : PointBlowupGluing.scheme j q hclosed,
      RegularPoint (PointBlowupGluing.scheme j q hclosed) s)
    (hcenter : RegularPoint X (j.base q)) : ∀ x : X, RegularPoint X x := by
  intro x
  by_cases hx : x = j.base q
  · simpa only [hx] using hcenter
  · let x' : (PointBlowupGluing.puncture j q hclosed).toScheme := ⟨x, hx⟩
    have hp := (regularPoint_iff_of_isOpenImmersion
      (PointBlowupGluing.complementι j q hclosed) x').mpr
        (hregular ((PointBlowupGluing.complementι j q hclosed).base x'))
    exact (regularPoint_iff_of_isOpenImmersion
      (PointBlowupGluing.puncture j q hclosed).ι x').mp hp

/-- The conclusion retains the original arbitrary scheme target and the
original source isomorphism with the accepted point blowup. -/
theorem PointBlowupChart.target_regular {S T : Scheme.{u}} {z : T}
    (c : PointBlowupChart T z) (e : S ≅ c.scheme)
    (hregular : ∀ s : S, RegularPoint S s) (hcenter : RegularPoint T z) :
    ∀ t : T, RegularPoint T t := by
  letI : CommRing c.R := c.instCommRing
  letI : IsOpenImmersion c.j := c.instOpenImmersion
  letI : c.q.asIdeal.IsMaximal := c.instMaximal
  apply PointBlowupGluing.target_regular c.j c.q c.isClosed
  · intro s
    exact (regularPoint_iff_of_isOpenImmersion e.inv s).mpr (hregular (e.inv.base s))
  · simpa only [c.base_eq] using hcenter

/-- Specialization to the original map in the public point-blowup predicate. -/
theorem IsPointBlowupAt.target_regular
    {k : Type u} [Field k] {S T : NormalProjectiveSurface k}
    {b : S.toScheme ⟶ T.toScheme} {z : T.Point}
    (hb : IsPointBlowupAt S T b z)
    (hregular : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hcenter : RegularPoint T.toScheme z) :
    ∀ t : T.Point, RegularPoint T.toScheme t := by
  obtain ⟨c, e, -⟩ := hb.blowup
  exact c.target_regular e hregular hcenter

end KltDP.Geometry

#print axioms KltDP.Geometry.PointBlowupChart.target_regular
#print axioms KltDP.Geometry.IsPointBlowupAt.target_regular

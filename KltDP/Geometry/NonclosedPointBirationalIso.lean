import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.BirationalIsomorphismOpen
import KltDP.Geometry.PointClosureCurve

/-!
Every nonclosed point on a normal projective surface is its generic point
or the generic point of its independently constructed closure curve.
The actual birational morphism is an isomorphism near either kind of point.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NonclosedPointBirationalIso

theorem exists_isomorphism_open {k : Type u} [Field k]
    {S : Scheme.{u}} [IsIntegral S] (X : NormalProjectiveSurface k)
    (π : S ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
    (x : X.toScheme) (hx : ¬ IsClosed ({x} : Set X.toScheme)) :
    ∃ U : X.toScheme.Opens, x ∈ U ∧ IsIso (π ∣_ U) := by
  by_cases hgeneric : x = genericPoint X.toScheme
  · obtain ⟨U, hUne, hU⟩ := exists_isomorphism_open_of_isBirationalScheme π hbir
    refine ⟨U, ?_, hU⟩
    rw [hgeneric]
    exact ((genericPoint_spec X.toScheme).mem_open_set_iff U.isOpen).mpr
      (by simpa using hUne)
  · obtain ⟨U, hxU, hU⟩ :=
      ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X π hbir
        (X.primeCurveOfNonclosedPoint x hgeneric hx)
    exact ⟨U, by simpa only [X.primeCurveOfNonclosedPoint_genericPoint] using hxU, hU⟩

/-- An isomorphism over an original target open makes every point fiber
over that open a subsingleton, on the original source carrier. -/
theorem pointFiber_subsingleton_of_isIso_restrict {S X : Scheme.{u}}
    (π : S ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] (x : X) (hx : x ∈ U) :
    (π.base ⁻¹' {x}).Subsingleton := by
  intro a ha b hb
  let aU : (π ⁻¹ᵁ U).toScheme := ⟨a, by change π.base a ∈ U; rwa [ha]⟩
  let bU : (π ⁻¹ᵁ U).toScheme := ⟨b, by change π.base b ∈ U; rwa [hb]⟩
  have hab : (π ∣_ U).base aU = (π ∣_ U).base bU := by
    apply Subtype.ext
    exact (morphismRestrict_base_coe π U aU).trans
      (ha.trans (hb.symm.trans (morphismRestrict_base_coe π U bU).symm))
  have hinj : Function.Injective (π ∣_ U).base :=
    (TopCat.homeoOfIso (asIso (π ∣_ U).base)).injective
  exact congrArg Subtype.val (hinj hab)

end KltDP.Geometry.NonclosedPointBirationalIso

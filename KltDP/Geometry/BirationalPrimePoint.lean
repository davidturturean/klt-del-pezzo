import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.CodimensionOneOpen

/-!
# The original point above a target prime

The proved isomorphism near the target generic point gives its inverse
through the existing codimension-one correspondence. The same restricted
isomorphism proves uniqueness among all original source points and proves
that the original stalk map is an isomorphism.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.BirationalPrimeCorrespondence

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

include hbir in
/-- The actual target prime point lifts through the existing original
codimension-one equivalence on its proved isomorphism neighborhood. -/
theorem exists_point_above_primeCurve (C : X.PrimeCurve) :
    ∃ x : CodimensionOnePoint S.toScheme, π.base x.val = C.genericPoint := by
  obtain ⟨U, hCU, hπU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X π hbir C
  letI : IsIso (π ∣_ U) := hπU
  let E := codimensionOneOverOpenEquiv π U
  let y : CodimensionOnePointInOpen U :=
    ⟨⟨C.genericPoint, C.ringKrullDim_stalk_genericPoint⟩, hCU⟩
  let x := E.symm y
  have hxy : E x = y := E.apply_symm_apply y
  refine ⟨x.val, ?_⟩
  calc
    π.base x.val.val = (E x).val.val :=
      (codimensionOneOverOpenEquiv_apply_val π U x).symm
    _ = y.val.val := congrArg (fun z : CodimensionOnePointInOpen U => z.val.val) hxy
    _ = C.genericPoint := rfl

/-- The source point is selected from the original point correspondence. -/
def point (C : X.PrimeCurve) : CodimensionOnePoint S.toScheme :=
  (exists_point_above_primeCurve π hbir C).choose

/-- Its image under the original morphism is the original target generic point. -/
theorem point_map (C : X.PrimeCurve) :
    π.base (point π hbir C).val = C.genericPoint :=
  (exists_point_above_primeCurve π hbir C).choose_spec

/-- Every original source point above this target generic point is the
same point, independently of the chosen isomorphism neighborhood. -/
theorem point_unique (C : X.PrimeCurve) (x : S.toScheme)
    (hx : π.base x = C.genericPoint) : x = (point π hbir C).val := by
  obtain ⟨U, hCU, hπU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X π hbir C
  letI : IsIso (π ∣_ U) := hπU
  let x' : (π ⁻¹ᵁ U).toScheme := ⟨x, by
    change π.base x ∈ U
    rw [hx]
    exact hCU⟩
  let p' : (π ⁻¹ᵁ U).toScheme :=
    ⟨(point π hbir C).val, by
      change π.base (point π hbir C).val ∈ U
      rw [point_map]
      exact hCU⟩
  have he : (π ∣_ U).base x' = (π ∣_ U).base p' := by
    apply Subtype.ext
    calc
      ((π ∣_ U).base x').val = π.base x := morphismRestrict_base_coe π U x'
      _ = C.genericPoint := hx
      _ = π.base (point π hbir C).val := (point_map π hbir C).symm
      _ = ((π ∣_ U).base p').val := (morphismRestrict_base_coe π U p').symm
  have hxp : x' = p' := (π ∣_ U).isOpenEmbedding.injective he
  exact congrArg (fun z : (π ⁻¹ᵁ U).toScheme => z.val) hxp

/-- The actual stalk map at the lifted source point is an isomorphism. -/
theorem point_stalkMap_isIso (C : X.PrimeCurve) :
    IsIso (π.stalkMap (point π hbir C).val) := by
  obtain ⟨U, hCU, hπU⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_primeCurve X π hbir C
  letI : IsIso (π ∣_ U) := hπU
  exact isIso_stalkMap_of_isIso_restrict π U (point π hbir C).val
    (by rw [point_map]; exact hCU)

end KltDP.Geometry.BirationalPrimeCorrespondence

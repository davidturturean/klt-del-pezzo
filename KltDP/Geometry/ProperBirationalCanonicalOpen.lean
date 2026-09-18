import KltDP.Geometry.TargetIsomorphismOpen
import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.NormalFiniteTypeValuationPoint
import KltDP.Geometry.SmoothStructureOnIsomorphismOpen

/-!
# The original big open of a proper birational normal model

The inverse of the original restricted morphism gives an actual open
immersion into its source. On a normal finite-type target this single
open contains every codimension-one point. No chosen common-open map
or compatibility equality is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.ProperBirationalCanonicalOpen

attribute [local instance] integralSchemeStalk_isDomain

variable {S V : Scheme.{u}}

local instance restrictionIsIso (q : S ⟶ V) :
    IsIso (q ∣_ targetIsomorphismOpen q) := isIso_targetIsomorphismOpen q

/-- The original inverse restriction, followed by its original source inclusion. -/
def lift (q : S ⟶ V) : (targetIsomorphismOpen q).toScheme ⟶ S :=
  inv (q ∣_ targetIsomorphismOpen q) ≫ (q ⁻¹ᵁ targetIsomorphismOpen q).ι

theorem lift_isOpenImmersion (q : S ⟶ V) : IsOpenImmersion (lift q) := by
  unfold lift
  infer_instance

/-- The lift has the original target inclusion as its composite with q. -/
theorem lift_comp (q : S ⟶ V) : lift q ≫ q = (targetIsomorphismOpen q).ι := by
  unfold lift
  rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

theorem restrict_comp_lift (q : S ⟶ V) :
    (q ∣_ targetIsomorphismOpen q) ≫ lift q =
      (q ⁻¹ᵁ targetIsomorphismOpen q).ι := by
  unfold lift
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

/-- The inverse restriction returns the very same original source point. -/
theorem lift_base (q : S ⟶ V) (s : S)
    (hs : q.base s ∈ targetIsomorphismOpen q) :
    (lift q).base ⟨q.base s, hs⟩ = s := by
  have h := congrArg
    (fun a : (q ⁻¹ᵁ targetIsomorphismOpen q).toScheme ⟶ S => a.base ⟨s, hs⟩)
    (restrict_comp_lift q)
  simpa only [Scheme.comp_base_apply, morphismRestrict_base] using h

/-- The original over-base triangle restricts along the constructed inverse. -/
theorem structure_eq {B : Scheme.{u}} (q : S ⟶ V)
    (fS : S ⟶ B) (fV : V ⟶ B) (hq : q ≫ fV = fS) :
    lift q ≫ fS = (targetIsomorphismOpen q).ι ≫ fV := by
  rw [← hq, ← Category.assoc, lift_comp]

/-- Proper birationality puts the original target generic point in this open. -/
theorem genericPoint_mem [IsIntegral S] [IsIntegral V]
    (q : S ⟶ V) [IsProper q] (hbir : IsBirationalScheme q) :
    genericPoint V ∈ targetIsomorphismOpen q := by
  letI : ValuationRing (V.presheaf.stalk (genericPoint V)) := by
    change ValuationRing V.functionField
    infer_instance
  exact ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk
    q hbir (genericPoint V)

theorem isIntegral [IsIntegral S] [IsIntegral V]
    (q : S ⟶ V) [IsProper q] (hbir : IsBirationalScheme q) :
    IsIntegral (targetIsomorphismOpen q).toScheme := by
  letI : Nonempty (targetIsomorphismOpen q).toScheme :=
    ⟨⟨genericPoint V, genericPoint_mem q hbir⟩⟩
  exact isIntegral_of_isOpenImmersion (targetIsomorphismOpen q).ι

/-- Every original codimension-one point of a normal finite-type target
belongs to the same isomorphism open. -/
theorem codimensionOne_mem {k : Type u} [Field k]
    [IsIntegral S] [IsIntegral V] (q : S ⟶ V) [IsProper q]
    (hbir : IsBirationalScheme q) (fV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fV] (hnormal : IsNormalScheme V)
    (x : CodimensionOnePoint V) : x.val ∈ targetIsomorphismOpen q := by
  letI := normalFiniteTypePoint_isDiscreteValuationRing fV hnormal x
  exact ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk
    q hbir x.val

/-- Relative smoothness of the original source descends to this target open. -/
theorem smooth {B : Scheme.{u}} (q : S ⟶ V) (n : ℕ)
    (fS : S ⟶ B) (fV : V ⟶ B) (hq : q ≫ fV = fS)
    [IsSmoothOfRelativeDimension n fS] :
    IsSmoothOfRelativeDimension n ((targetIsomorphismOpen q).ι ≫ fV) :=
  SmoothStructureOnIsomorphismOpen.isSmoothOfRelativeDimension
    n fS fV q hq (targetIsomorphismOpen q)

end KltDP.Geometry.ProperBirationalCanonicalOpen

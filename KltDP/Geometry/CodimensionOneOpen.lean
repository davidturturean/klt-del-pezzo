import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Actual codimension-one points on an isomorphism open

The indexing points are actual scheme points with one-dimensional actual
local rings. Open immersions preserve their local rings by the canonical
stalk map. Hence an actual isomorphism over an open gives an equivalence
of these points and of their finite integer sums on that open.

This does not assert that the closure of every such point is a curve on
an arbitrary scheme. The separate surface adapter proves that comparison
with the existing manuscript `PrimeCurve` type. No intersection or Picard
class is used or assumed here.

Reuse: the pinned open-immersion stalk isomorphism, ring Krull dimension
invariance, `Equiv.subtypeEquiv`, and `Finsupp.domCongr`. The newer official
and relevant-library snapshots in the connected-fiber reuse packet do not
provide an import-compatible general Weil-divisor carrier for this pin.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

/-- Actual scheme points of codimension one, measured by their actual
structure-sheaf local rings. -/
def CodimensionOnePoint (X : Scheme.{u}) :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

/-- The same actual codimension-one points whose points lie in an open. -/
abbrev CodimensionOnePointInOpen {X : Scheme.{u}} (U : X.Opens) :=
  {x : CodimensionOnePoint X // x.val ∈ U}

/-- The canonical stalk map of an actual open immersion preserves
the dimension of the actual local ring. -/
theorem ringKrullDim_stalk_openImmersion {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    ringKrullDim (X.presheaf.stalk (j.base y)) =
      ringKrullDim (Y.presheaf.stalk y) :=
  ringKrullDim_eq_of_ringEquiv
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv

/-- Restricting to the actual open transports precisely the same local
rings and points, with no assumed correspondence. -/
def codimensionOnePointOpenEquiv {X : Scheme.{u}} (U : X.Opens) :
    CodimensionOnePoint U.toScheme ≃ CodimensionOnePointInOpen U where
  toFun x := ⟨⟨x.val.val,
    (ringKrullDim_stalk_openImmersion U.ι x.val).trans x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩,
    (ringKrullDim_stalk_openImmersion U.ι ⟨x.val.val, x.property⟩).symm.trans x.val.property⟩
  left_inv x := rfl
  right_inv x := rfl

/-- An actual scheme isomorphism transports actual codimension-one points
by its own point map; the dimension equivalence follows from its stalks. -/
def codimensionOnePointIsoEquiv {X Y : Scheme.{u}} (e : X ≅ Y) :
    CodimensionOnePoint X ≃ CodimensionOnePoint Y :=
  e.hom.homeomorph.toEquiv.subtypeEquiv (fun x => by
    change ringKrullDim (X.presheaf.stalk x) = 1 ↔
      ringKrullDim (Y.presheaf.stalk (e.hom.base x)) = 1
    rw [ringKrullDim_stalk_openImmersion e.hom x])

@[simp] theorem codimensionOnePointIsoEquiv_apply_val {X Y : Scheme.{u}}
    (e : X ≅ Y) (x : CodimensionOnePoint X) :
    (codimensionOnePointIsoEquiv e x).val = e.hom.base x.val := rfl

/-- The correspondence over an actual isomorphism open, obtained by
restricting the source and target and using the actual restricted map. -/
def codimensionOneOverOpenEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    CodimensionOnePointInOpen (f ⁻¹ᵁ U) ≃ CodimensionOnePointInOpen U :=
  (codimensionOnePointOpenEquiv (f ⁻¹ᵁ U)).symm.trans
    ((codimensionOnePointIsoEquiv (asIso (f ∣_ U))).trans
      (codimensionOnePointOpenEquiv U))

/-- The correspondence's point map is the original morphism, not a
separately chosen set bijection. -/
@[simp] theorem codimensionOneOverOpenEquiv_apply_val {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : CodimensionOnePointInOpen (f ⁻¹ᵁ U)) :
    (codimensionOneOverOpenEquiv f U x).val.val = f.base x.val.val := by
  change ((f ∣_ U).base ⟨x.val.val, x.property⟩).val = f.base x.val.val
  exact morphismRestrict_base_coe f U ⟨x.val.val, x.property⟩

/-- Finite integer sums are transported along the actual point
correspondence using the existing finitely supported free abelian group. -/
def codimensionOneDivisorOverOpenEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    (CodimensionOnePointInOpen (f ⁻¹ᵁ U) →₀ ℤ) ≃+
      (CodimensionOnePointInOpen U →₀ ℤ) :=
  Finsupp.domCongr (codimensionOneOverOpenEquiv f U)

end KltDP.Geometry

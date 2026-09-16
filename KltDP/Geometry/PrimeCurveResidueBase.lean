import KltDP.Geometry.PrimeCurveLocalLengthFinrank
import KltDP.Geometry.ClosedPoints

/-!
# The induced base-field map to the residue field is the accepted one

`stalkBaseMap` sends `k` to the stalk `O_{C,y}` through global sections; composed
with the residue map it gives `k → κ(y)`. This module proves that this composite
is exactly the accepted `baseToResidueFieldMap C.toSpec y` (defined through
`Spec κ(y) → C → Spec k`), by computing `Spec.map` of the composite with the
pinned `fromSpecStalk_toSpecΓ` and `toSpecΓ_naturality` identities.

Consequently the accepted finiteness (`baseToResidueFieldMap_finite`) and, over an
algebraically closed field, bijectivity (`baseToResidueFieldMap_bijective`) at closed
points apply verbatim to `stalkBaseResidueMap`. Transporting `RingHom.Finite` of this
map to the quotient-algebra `k`-structure used in `finrank_quotient_span_eq_localLength_mul`
is carried out in `KltDP.Geometry.PrimeCurveResidueFinrank`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve) (y : C.toScheme)

/-- The induced map `k → κ(y)`: base field → global sections → stalk → residue field. -/
def stalkBaseResidueMap : CommRingCat.of k ⟶ C.toScheme.residueField y :=
  CommRingCat.ofHom ((C.toScheme.residue y).hom.comp (C.stalkBaseMap y))

/-- `Spec` of the induced map is the composite `Spec κ(y) → C → Spec k`. -/
theorem Spec_map_stalkBaseResidueMap :
    Spec.map (C.stalkBaseResidueMap y) = C.toScheme.fromSpecResidueField y ≫ C.toSpec := by
  have hunit : (Spec (CommRingCat.of k)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv = 𝟙 _ := by
    rw [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  have hstalk : C.toScheme.fromSpecStalk y ≫ C.toSpec =
      Spec.map (C.toScheme.presheaf.germ ⊤ y trivial) ≫ Spec.map C.toSpec.appTop ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    symm
    rw [← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, ← Scheme.toSpecΓ_naturality_assoc,
      hunit, Category.comp_id]
  have h1 : C.stalkBaseResidueMap y =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.toSpec.appTop ≫
        C.toScheme.presheaf.germ ⊤ y trivial ≫ C.toScheme.residue y := rfl
  rw [h1, Spec.map_comp, Spec.map_comp, Spec.map_comp]
  show ((Spec.map (C.toScheme.residue y) ≫ Spec.map (C.toScheme.presheaf.germ ⊤ y trivial)) ≫
      Spec.map C.toSpec.appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv =
    (Spec.map (C.toScheme.residue y) ≫ C.toScheme.fromSpecStalk y) ≫ C.toSpec
  simp only [Category.assoc]
  rw [hstalk]

/-- The induced map is the accepted base-to-residue-field map. -/
theorem baseToResidueFieldMap_eq_stalkBaseResidueMap :
    baseToResidueFieldMap C.toSpec y = C.stalkBaseResidueMap y := by
  unfold baseToResidueFieldMap
  rw [← C.Spec_map_stalkBaseResidueMap y, Spec.preimage_map]

/-- At a closed point the induced `k → κ(y)` is a finite ring homomorphism. -/
theorem stalkBaseResidueMap_finite (hclosed : IsClosed ({y} : Set C.toScheme)) :
    (C.stalkBaseResidueMap y).hom.Finite := by
  rw [← C.baseToResidueFieldMap_eq_stalkBaseResidueMap y]
  exact baseToResidueFieldMap_finite C.toSpec y hclosed

/-- Over an algebraically closed field the induced `k → κ(y)` is bijective at a closed point. -/
theorem stalkBaseResidueMap_bijective [IsAlgClosed k] (hclosed : IsClosed ({y} : Set C.toScheme)) :
    Function.Bijective (C.stalkBaseResidueMap y).hom := by
  rw [← C.baseToResidueFieldMap_eq_stalkBaseResidueMap y]
  exact baseToResidueFieldMap_bijective C.toSpec y hclosed

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

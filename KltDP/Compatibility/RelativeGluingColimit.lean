/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/RelativeGluing.lean:94-193. The original diagram's
colimit is constructed by LocallyDirectedColimit, not supplied as a
hypothesis. The original chart maps define toBase, and its actual
cartesian chart squares are proved using their pointwise ranges.
-/
import KltDP.Compatibility.RelativeGluingData
import KltDP.Compatibility.LocallyDirectedColimit

noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable {S : Scheme.{u}} {𝒰 : OpenCover.{u} S}
  [SmallCategory 𝒰.J] [LocallyDirected 𝒰] [Quiver.IsThin 𝒰.J]
  (d : RelativeGluingData 𝒰)

/-- The actual colimit of the original relative diagram. Its existence
follows from the constructed locally directed gluing, not an extra input. -/
abbrev glued : Scheme.{u} := colimit d.functor

/-- The original diagram objects and colimit inclusions cover the glued scheme. -/
def cover : OpenCover.{u} d.glued := Scheme.IsLocallyDirected.openCover d.functor

instance : SmallCategory d.cover.J := inferInstanceAs (SmallCategory 𝒰.J)
instance : Quiver.IsThin d.cover.J := inferInstanceAs (Quiver.IsThin 𝒰.J)

@[simp]
theorem cover_obj (i : 𝒰.J) : d.cover.obj i = d.functor.obj i := rfl

@[simp]
theorem cover_map (i : 𝒰.J) : d.cover.map i = colimit.ι d.functor i := rfl

/-- The original chart maps to the base determine the structure morphism. -/
def toBase : d.glued ⟶ S :=
  colimit.desc d.functor
    { pt := S
      ι := d.natTrans ≫ functorOfLocallyDirectedHomBase 𝒰 }

@[simp, reassoc]
theorem ι_toBase (i : 𝒰.J) :
    colimit.ι d.functor i ≫ d.toBase = d.natTrans.app i ≫ 𝒰.map i := by
  simp [toBase, functorOfLocallyDirectedHomBase]

/-- Pointwise form of the original chart structure-map equality. -/
theorem ι_toBase_apply (i : 𝒰.J) (x : d.functor.obj i) :
    d.toBase.base ((colimit.ι d.functor i).base x) =
      (𝒰.map i).base ((d.natTrans.app i).base x) := by
  exact congrArg (fun a : d.functor.obj i ⟶ S => a.base x) (ι_toBase d i)

/-- The inverse image of the original base chart is precisely the range
of the corresponding original colimit inclusion. -/
theorem preimage_toBase_eq_range_ι (i : 𝒰.J) :
    d.toBase.base ⁻¹' Set.range (𝒰.map i).base =
      Set.range (colimit.ι d.functor i).base := by
  ext x
  constructor
  · rintro ⟨ui, hui⟩
    obtain ⟨j, xj, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective d.functor x
    have heq : (𝒰.map i).base ui =
        (𝒰.map j).base ((d.natTrans.app j).base xj) :=
      hui.trans (ι_toBase_apply d j xj)
    obtain ⟨k, fi, fj, uk, hki, hkj⟩ :=
      exists_of_map_eq_map 𝒰 ui ((d.natTrans.app j).base xj) heq
    have hpb : (d.natTrans.app j).base xj =
        ((functorOfLocallyDirected 𝒰).map fj).base uk := hkj.symm
    obtain ⟨xk, hxk, hαk⟩ :=
      Scheme.exists_preimage_of_isPullback (d.equifibered fj) xj uk hpb
    refine ⟨(d.functor.map fi).base xk, ?_⟩
    calc
      (colimit.ι d.functor i).base ((d.functor.map fi).base xk) =
          (colimit.ι d.functor k).base xk := by
        rw [← Scheme.comp_base_apply, colimit.w]
      _ = (colimit.ι d.functor j).base ((d.functor.map fj).base xk) := by
        rw [← Scheme.comp_base_apply, colimit.w]
      _ = (colimit.ι d.functor j).base xj :=
        congrArg (colimit.ι d.functor j).base hxk
  · rintro ⟨y, rfl⟩
    exact ⟨(d.natTrans.app i).base y, (ι_toBase_apply d i y).symm⟩

/-- Equality of the actual chart opens, not just a homeomorphism of replacements. -/
theorem toBase_preimage_eq_opensRange_ι (i : 𝒰.J) :
    d.toBase ⁻¹ᵁ (𝒰.map i).opensRange = (colimit.ι d.functor i).opensRange :=
  Opens.coe_inj.mp (preimage_toBase_eq_range_ι d i)

/-- Each original relative chart square is cartesian after gluing. -/
theorem isPullback_natTrans_ι_toBase (i : 𝒰.J) :
    IsPullback (d.natTrans.app i) (colimit.ι d.functor i) (𝒰.map i) d.toBase := by
  refine ⟨⟨(ι_toBase d i).symm⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    apply IsOpenImmersion.lift (colimit.ι d.functor i) s.snd
    rw [← preimage_toBase_eq_range_ι]
    rintro x ⟨t, rfl⟩
    refine ⟨s.fst.base t, ?_⟩
    exact congrArg (fun a : s.pt ⟶ S => a.base t) s.condition
  · intro s
    rw [← cancel_mono (𝒰.map i), Category.assoc, ← ι_toBase,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s m h1 h2
    rw [← cancel_mono (colimit.ι d.functor i), IsOpenImmersion.lift_fac]
    exact h2

end AlgebraicGeometry.Scheme.Cover.RelativeGluingData

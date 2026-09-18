/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Bounded adaptation of Mathlib 80cbd0498ab39e21d24d6730b3f932cec672a702,
AlgebraicGeometry/RelativeGluing.lean:128-151. Directedness of the actual
colimit cover follows from the original base-cover overlap condition and
the original cartesian transition squares. No new gluing inputs are added.
-/
import KltDP.Compatibility.RelativeGluingColimit

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable {S : Scheme.{u}} {𝒰 : OpenCover.{u} S}
  [SmallCategory 𝒰.J] [LocallyDirected 𝒰] [Quiver.IsThin 𝒰.J]
  (d : RelativeGluingData 𝒰)

/-- The original diagram transitions make the actual colimit cover directed. -/
instance cover_locallyDirected : LocallyDirected d.cover where
  trans {i j} hij := d.functor.map hij
  trans_id i := d.functor.map_id i
  trans_comp hij hjk := d.functor.map_comp hij hjk
  w hij := colimit.w d.functor hij
  directed {i j} x := by
    let xi : d.functor.obj i := (pullback.fst (d.cover.map i) (d.cover.map j)).base x
    let xj : d.functor.obj j := (pullback.snd (d.cover.map i) (d.cover.map j)).base x
    have hpair : (colimit.ι d.functor i).base xi =
        (colimit.ι d.functor j).base xj := by
      exact congrArg
        (fun a : pullback (d.cover.map i) (d.cover.map j) ⟶ d.glued => a.base x)
        (pullback.condition (f := d.cover.map i) (g := d.cover.map j))
    have heq : (𝒰.map i).base ((d.natTrans.app i).base xi) =
        (𝒰.map j).base ((d.natTrans.app j).base xj) := by
      calc
        (𝒰.map i).base ((d.natTrans.app i).base xi) =
            d.toBase.base ((colimit.ι d.functor i).base xi) :=
          (ι_toBase_apply d i xi).symm
        _ = d.toBase.base ((colimit.ι d.functor j).base xj) :=
          congrArg d.toBase.base hpair
        _ = (𝒰.map j).base ((d.natTrans.app j).base xj) := ι_toBase_apply d j xj
    obtain ⟨k, fi, fj, uk, hki, hkj⟩ :=
      exists_of_map_eq_map 𝒰 ((d.natTrans.app i).base xi)
        ((d.natTrans.app j).base xj) heq
    have hpb : (d.natTrans.app j).base xj =
        ((functorOfLocallyDirected 𝒰).map fj).base uk := hkj.symm
    obtain ⟨xk, hxk, hαk⟩ :=
      Scheme.exists_preimage_of_isPullback (d.equifibered fj) xj uk hpb
    refine ⟨k, fi, fj, xk, ?_⟩
    apply (show IsOpenImmersion (pullback.snd (d.cover.map i) (d.cover.map j)) from
      inferInstance).base_open.injective
    rw [← Scheme.comp_base_apply, pullback.lift_snd]
    exact hxk

end AlgebraicGeometry.Scheme.Cover.RelativeGluingData

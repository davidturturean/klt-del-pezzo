/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# A scheme pullback square from its original open-cover squares

The original local source objects must be actual pullbacks of the target
cover. Their squares over the original lower cospan must also be cartesian.
These two conditions imply that the original whole square is cartesian.
The proof uses the pinned target-locality of isomorphisms and ordinary
pullback pasting; no geometric conclusion is included in auxiliary data.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.SchemeLocalPullback

/-- Cartesian squares can be checked on an open cover of the upper-right
scheme, using any original representatives of the restricted source charts. -/
theorem isPullback_of_openCover
    {A B C D : Scheme.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (w : f ≫ h = g ≫ k)
    (U : B.OpenCover) (Aᵢ : U.J → Scheme.{u})
    (u : ∀ i, Aᵢ i ⟶ A) (v : ∀ i, Aᵢ i ⟶ U.obj i)
    (hpre : ∀ i, IsPullback (u i) (v i) f (U.map i))
    (hchart : ∀ i, IsPullback (v i) (u i ≫ g) (U.map i ≫ h) k) :
    IsPullback f g h k := by
  let c : A ⟶ pullback h k := pullback.lift f g w
  have hc₁ : c ≫ pullback.fst h k = f := pullback.lift_fst f g w
  have hc₂ : c ≫ pullback.snd h k = g := pullback.lift_snd f g w
  let V : (pullback h k).OpenCover := U.pullbackCover (pullback.fst h k)
  letI : IsIso c := by
    apply IsLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) V
    intro i
    let Q := pullback (pullback.fst h k) (U.map i)
    let q₁ : Q ⟶ pullback h k := pullback.fst _ _
    let q₂ : Q ⟶ U.obj i := pullback.snd _ _
    have ht : IsPullback q₂ q₁ (U.map i) (pullback.fst h k) :=
      (IsPullback.of_hasPullback (pullback.fst h k) (U.map i)).flip
    have ht' : IsPullback q₂ (q₁ ≫ pullback.snd h k) (U.map i ≫ h) k :=
      ht.paste_vert (IsPullback.of_hasPullback h k)
    let e : Aᵢ i ≅ Q := (hchart i).isoIsPullback _ _ ht'
    have he₁ : e.hom ≫ q₂ = v i :=
      (hchart i).isoIsPullback_hom_fst _ _ ht'
    have he₂ : e.hom ≫ q₁ ≫ pullback.snd h k = u i ≫ g :=
      (hchart i).isoIsPullback_hom_snd _ _ ht'
    have he : e.hom ≫ q₁ = u i ≫ c := by
      apply pullback.hom_ext
      · calc
          (e.hom ≫ q₁) ≫ pullback.fst h k = (e.hom ≫ q₂) ≫ U.map i := by
            rw [Category.assoc, ← ht.w, ← Category.assoc]
          _ = v i ≫ U.map i := by rw [he₁]
          _ = u i ≫ f := (hpre i).w.symm
          _ = (u i ≫ c) ≫ pullback.fst h k := by rw [Category.assoc, hc₁]
      · simpa only [Category.assoc, hc₂] using he₂
    have hs : IsPullback (e.hom ≫ q₂) (u i) (U.map i) (c ≫ pullback.fst h k) := by
      rw [he₁, hc₁]
      exact (hpre i).flip
    have hl : IsPullback (u i) e.hom c q₁ := (hs.of_right he ht).flip
    change IsIso (pullback.snd c q₁)
    rw [← hl.isoPullback_inv_snd]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) hc₁ hc₂

end KltDP.Geometry.SchemeLocalPullback

#print axioms KltDP.Geometry.SchemeLocalPullback.isPullback_of_openCover

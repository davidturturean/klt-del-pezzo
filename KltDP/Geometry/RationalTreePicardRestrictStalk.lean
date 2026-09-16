import KltDP.Geometry.RationalTreePicardTransverseTransfer

/-!
# Stalk maps of a morphism that is an isomorphism over an open

BRIEF12, task (b), first part. Stalk maps of isomorphisms of schemes are isomorphisms
(`isIso_stalkMap_of_isIso`, from `Scheme.stalkMap_inv_hom` and `Scheme.stalkMap_hom_inv`), and a
morphism `f` whose restriction `f ∣_ V` over an open `V` of the target is an isomorphism has
isomorphic stalk maps at the points over `V` (`isIso_stalkMap_of_isIso_restrict`, through
`morphismRestrict_ι`, `Scheme.stalkMap_comp` and the open-immersion stalk isomorphisms). Applied to
`ι_{Cᶜ}` over `componentUnionComplementOpen Y {C}` (`componentUnionInclusion_restrict_isIso`):
`isIso_stalkMap_componentUnionInclusion_compl`. The transport of the four germ conditions along
this isomorphism (`TransversePointTransfer`) remains; see `LEMMA22_PROGRESS.md`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

/-- Stalk maps of an isomorphism of schemes are isomorphisms. -/
theorem isIso_stalkMap_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    IsIso (f.stalkMap x) := by
  let e : X ≅ Y := asIso f
  have h1 := Scheme.stalkMap_inv_hom e x
  have h2 := Scheme.stalkMap_hom_inv e (e.hom.base x)
  haveI hmono : Mono (e.inv.stalkMap (e.hom.base x)) := mono_of_mono_fac h1
  haveI hsplit : IsSplitEpi (e.inv.stalkMap (e.hom.base x)) :=
    ⟨⟨⟨inv (Y.presheaf.stalkCongr (.of_eq (by simp))).hom ≫
        e.hom.stalkMap (e.inv.base (e.hom.base x)), by
      rw [Category.assoc, h2, IsIso.inv_hom_id]⟩⟩⟩
  haveI hA : IsIso (e.inv.stalkMap (e.hom.base x)) := isIso_of_mono_of_isSplitEpi _
  haveI : IsIso (e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x) := by
    rw [h1]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.inv.stalkMap (e.hom.base x)) (e.hom.stalkMap x)

/-- Stalk maps of open immersions are isomorphisms (scheme form). -/
theorem isIso_stalkMap_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) : IsIso (f.stalkMap x) :=
  inferInstanceAs (IsIso (f.toLRSHom.stalkMap x))

/-- A morphism whose restriction over an open `V` is an isomorphism has isomorphic stalk maps at
the points over `V`. -/
theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] (x : X) (hx : f.base x ∈ V) : IsIso (f.stalkMap x) := by
  let x' : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  have h := Scheme.stalkMap_congr_hom _ _ (morphismRestrict_ι f V) x'
  rw [Scheme.stalkMap_comp, Scheme.stalkMap_comp] at h
  haveI : IsIso ((f ∣_ V).stalkMap x') := isIso_stalkMap_of_isIso _ _
  haveI : IsIso (V.ι.stalkMap ((f ∣_ V).base x')) := isIso_stalkMap_of_isOpenImmersion _ _
  haveI : IsIso ((f ⁻¹ᵁ V).ι.stalkMap x') := isIso_stalkMap_of_isOpenImmersion _ _
  haveI hbc : IsIso (f.stalkMap ((f ⁻¹ᵁ V).ι.base x') ≫ (f ⁻¹ᵁ V).ι.stalkMap x') :=
    IsIso.of_isIso_fac_left h.symm
  exact IsIso.of_isIso_comp_right (f.stalkMap ((f ⁻¹ᵁ V).ι.base x')) ((f ⁻¹ᵁ V).ι.stalkMap x')

/-- The stalk maps of the closed immersion of the complement of a component are isomorphisms
at the points mapping off that component. -/
theorem isIso_stalkMap_componentUnionInclusion_compl (Y : Scheme.{u}) [NoetherianSpace Y]
    [AlgebraicGeometry.IsReduced Y] (C : ↥(irreducibleComponents Y))
    (z : componentUnionScheme Y ({C}ᶜ)) (hz : (componentUnionInclusion Y ({C}ᶜ)).base z ∉ C.1) :
    IsIso ((componentUnionInclusion Y ({C}ᶜ)).stalkMap z) := by
  have hV : (componentUnionComplementOpen Y {C} : Set Y) ⊆ componentClosedUnion Y ({C}ᶜ) := by
    intro y hy
    rcases (Set.mem_union y _ _).mp
      ((componentClosedUnion_union_compl Y {C}).symm ▸ Set.mem_univ y) with h | h
    · exact absurd h hy
    · exact h
  haveI := componentUnionInclusion_restrict_isIso Y ({C}ᶜ) (componentUnionComplementOpen Y {C}) hV
  refine isIso_stalkMap_of_isIso_restrict _ (componentUnionComplementOpen Y {C}) z ?_
  show (componentUnionInclusion Y ({C}ᶜ)).base z ∈ (componentClosedUnion Y {C}).compl
  intro h
  exact hz (by rwa [coe_componentClosedUnion_singleton] at h)

end KltDP.Geometry.RationalTreePicard

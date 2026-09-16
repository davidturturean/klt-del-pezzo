import KltDP.Geometry.RationalTreePicardLeafOverlap

/-!
# The gluing step, reduced to the scalar identity

With the two overlap comparisons (`complementOverlap_coordinate` for `hcomplT`,
`leafOverlap_coordinate_raw` and `leafOpen_coordinate_value` for the leaf side), the
leaf coordinate equation `hleafT` of `leafNodeUnitIsoOfTransposes` follows from the
single scalar identity `LeafScalarIdentity β`: the leaf gauge unit `β`, restricted
and read on the chart piece of the leaf component, is the inverse of the transported
lifted node scalar (`leafOverlap_coordinate`). Consequently
`leafNodeUnitIsoOfScalar β hβ : L.obj ≅ unit` trivializes the original line bundle
on the whole curve, for the leaf/complement decomposition, conditional on that one
identity about constants. Its proof for the inverse node-scalar gauge unit is
`leafScalarIdentity_nodeScalarGauge_inv` in `RationalTreePicardLeafScalarIdentity`, which
yields the unconditional `leafNodeUnitIso`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.RationalTreePicard

attribute [local instance] Types.instFunLike Types.instConcreteCategory

open SchemeModuleRestriction TransitionUnitGluing

section Injectivity

variable (X : Scheme.{u}) [NoetherianSpace X]
  (S : Set ↥(irreducibleComponents X))

/-- The section map of the closed immersion of a component union is injective on opens
inside an open contained in that union (where the restricted closed immersion is an
isomorphism). -/
theorem componentInclusion_app_injective [AlgebraicGeometry.IsReduced X] (V : X.Opens)
    (hV : (V : Set X) ⊆ componentClosedUnion X S) {W : X.Opens} (hWV : W ≤ V) :
    Function.Injective ((componentUnionInclusion X S).app W) := by
  intro y₁ y₂ hy
  have hg := componentUnionInclusion_restrict_isIso X S V hV
  have h1 := congrArg ((componentUnionInclusion X S ⁻¹ᵁ V).ι.app
    (componentUnionInclusion X S ⁻¹ᵁ W)) hy
  change ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S).app W y₁ =
    ((componentUnionInclusion X S ⁻¹ᵁ V).ι ≫ componentUnionInclusion X S).app W y₂ at h1
  rw [Scheme.congr_app (morphismRestrict_ι (componentUnionInclusion X S) V).symm W] at h1
  change (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.presheaf.map (eqToHom _).op
      ((componentUnionInclusion X S ∣_ V).app (V.ι ⁻¹ᵁ W) (V.ι.app W y₁)) =
    (componentUnionInclusion X S ⁻¹ᵁ V).toScheme.presheaf.map (eqToHom _).op
      ((componentUnionInclusion X S ∣_ V).app (V.ι ⁻¹ᵁ W) (V.ι.app W y₂)) at h1
  have h2 := presheaf_map_eqToHom_injective _ h1
  have h3 := isIso_app_injective (componentUnionInclusion X S ∣_ V) _ h2
  exact openImmersion_app_injective V.ι W (by simpa using hWV) h3

/-- The section map of the chart identification of a component piece followed by its
open inclusion is injective on opens inside the chart. -/
theorem chartPiece_app_injective (U : X.affineOpens) {W : X.Opens} (hWU : W ≤ U.1) :
    Function.Injective
      (((componentUnionChartIso X S U).hom ≫ (componentUnionInclusion X S ⁻¹ᵁ U.1).ι).app
        (componentUnionInclusion X S ⁻¹ᵁ W)) := by
  change Function.Injective (fun z => (componentUnionChartIso X S U).hom.app _
    ((componentUnionInclusion X S ⁻¹ᵁ U.1).ι.app (componentUnionInclusion X S ⁻¹ᵁ W) z))
  exact (isIso_app_injective (componentUnionChartIso X S U).hom _).comp
    (openImmersion_app_injective (componentUnionInclusion X S ⁻¹ᵁ U.1).ι
      (componentUnionInclusion X S ⁻¹ᵁ W)
      (by
        rw [Scheme.Opens.opensRange_ι]
        exact fun x hx => hWU hx))

end Injectivity

section Gluing

variable {X : Scheme.{u}} [NoetherianSpace X] [AlgebraicGeometry.IsReduced X]
  (L : InvertibleSheaf X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
  {C : ↥(irreducibleComponents X)} {q : X} {U : X.affineOpens} {hq : q ∈ U.1}
  (h : LeafNodeChart X C q U hq)
  (frameC : (schemeModulePullback (componentUnionInclusion X {C})).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X {C}).ringCatSheaf)
  (frameC' : (schemeModulePullback (componentUnionInclusion X ({C}ᶜ))).obj L.obj ≅
    _root_.SheafOfModules.unit (componentUnionScheme X ({C}ᶜ)).ringCatSheaf)

/-- The leaf coordinate equation follows from the scalar identity. -/
theorem leafOverlap_coordinate (β : Γ(X, leafOpen X C)ˣ)
    (hβ : LeafScalarIdentity L f h frameC frameC' β)
    (W : X.Opens) (hWU : W ≤ U.1) (hWl : W ≤ leafOpen X C) (s : L.obj.val.obj (op W)) :
    res X hWl (β : Γ(X, leafOpen X C)) *
        openSectionsInv (leafOpen X C) hWl ((leafOpenTranspose L frameC).val.app (op W) s) =
      openSectionsInv U.1 hWU ((leafChartTranspose L f h frameC frameC').val.app (op W) s) := by
  apply componentInclusion_app_injective X {C} (leafOpen X C) (leafOpen_subset X C) hWl
  apply chartPiece_app_injective X {C} U hWU
  rw [map_mul, map_mul, leafOpen_coordinate_value L frameC hWl s,
    ← leafOverlap_coordinate_raw L f h frameC frameC' hWU s, ← mul_assoc, mul_comm _
      (transportedNodeScalar L f h frameC frameC'), ← mul_assoc,
    mul_comm (transportedNodeScalar L f h frameC frameC'), hβ W hWU hWl, one_mul]

/-- The gluing step: the original line bundle is trivial on the curve, for the
leaf/complement decomposition, given the scalar identity for the leaf gauge unit. -/
def leafNodeUnitIsoOfScalar (hcut : C.1 ∩ (componentClosedUnion X ({C}ᶜ) : Set X) = {q})
    (β : Γ(X, leafOpen X C)ˣ) (hβ : LeafScalarIdentity L f h frameC frameC' β) :
    L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
  leafNodeUnitIsoOfTransposes L f h frameC frameC' hcut β
    (leafOverlap_coordinate L f h frameC frameC' β hβ)
    (fun _ hWU hWc s => complementOverlap_coordinate L f h frameC frameC' hWU hWc s)

end Gluing

end KltDP.Geometry.RationalTreePicard

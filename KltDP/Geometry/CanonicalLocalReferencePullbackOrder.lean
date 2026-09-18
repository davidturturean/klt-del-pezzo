import KltDP.Geometry.NormalModelCanonicalFrameOrder
import KltDP.Geometry.DominantCartierPullbackFunctorial
import KltDP.Geometry.DominantCartierPullbackOpenRestriction

/-!
# Original Cartier numerator orders on a local canonical reference

The original factor through the reference preserves generic points because
its composite is the original dominant model map. The actual local Cartier
multiple then pulls back through this same triangle. Its order is transported
through the original frame-neighborhood stalk isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CanonicalLocalReferencePullbackOrder

open NormalModelCanonical DominantCartierPullback OpenImmersionRational

attribute [local instance] integralSchemeStalk_isDomain

local instance referenceIntegralOpen {k : Type u} [Field k]
    (X : NormalProjectiveSurface k) (W : X.toScheme.Opens) [Nonempty W.toScheme] :
    IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι

local instance referenceOpenGeneric {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] : GenericPointPreserving i :=
  ⟨genericPoint_eq_of_isOpenImmersion i⟩

private theorem pullback_eq_of_hom_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (f g : Y ⟶ Z) [GenericPointPreserving f] [GenericPointPreserving g]
    (h : f = g) (A : CartierDivisor Z) : pullbackHom f A = pullbackHom g A := by
  subst g
  rfl

/-- Generic-point compatibility of the actual reference map follows from
its original over-target triangle. -/
theorem referenceMap_genericPointPreserving
    {k : Type u} [Field k] (S X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (C : S.PrimeCurve) (G : LocalFrame (π ≫ X.structureMorphism) C.genericPoint)
    (W : X.toScheme.Opens) [Nonempty W.toScheme]
    (p : G.neighborhood ⟶ W.toScheme) (hp : p ≫ W.ι = G.toModel ≫ π) :
    GenericPointPreserving p := by
  letI : IsIntegral G.neighborhood := G.neighborhood_isIntegral
  refine ⟨?_⟩
  apply W.ι.isOpenEmbedding.injective
  calc
    W.ι.base (p.base (genericPoint G.neighborhood)) =
        (p ≫ W.ι).base (genericPoint G.neighborhood) :=
      (Scheme.comp_base_apply p W.ι (genericPoint G.neighborhood)).symm
    _ = (G.toModel ≫ π).base (genericPoint G.neighborhood) :=
      congrArg (fun f => f.base (genericPoint G.neighborhood)) hp
    _ = genericPoint X.toScheme :=
      @GenericPointPreserving.base_genericPoint G.neighborhood X.toScheme
        G.neighborhood_isIntegral (inferInstance) (G.toModel ≫ π) (inferInstance)
    _ = W.ι.base (genericPoint W.toScheme) :=
      (genericPoint_eq_of_isOpenImmersion W.ι).symm

/-- The actual local Cartier multiple determines its original source-prime
order through the same original map, without a valuation-comparison premise. -/
theorem multiple_pullback_order
    {k : Type u} [Field k] (S X : NormalProjectiveSurface k)
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (C : S.PrimeCurve) (G : LocalFrame (π ≫ X.structureMorphism) C.genericPoint)
    (W : X.toScheme.Opens) [Nonempty W.toScheme]
    (p : G.neighborhood ⟶ W.toScheme) (hp : p ≫ W.ι = G.toModel ≫ π)
    (KW : CartierDivisor W.toScheme) (n : ℕ) (A : CartierDivisor X.toScheme)
    (hmultiple : n • KW = cartierRestrictionHom W.ι A) :
    letI := C.genericPoint_isDiscreteValuationRing
    letI := referenceMap_genericPointPreserving S X π C G W p hp
    n • cartierOrderAt G.neighborhood (pullbackHom p KW) G.point =
      S.cartierToWeilHom (pullbackHom π A) C := by
  letI := C.genericPoint_isDiscreteValuationRing
  letI := referenceMap_genericPointPreserving S X π C G W p hp
  have hlocal : n • KW = pullbackHom W.ι A :=
    hmultiple.trans (congrArg (fun f => f A) (pullbackHom_eq_cartierRestrictionHom W.ι)).symm
  have hdiv : n • pullbackHom p KW = pullbackHom G.toModel (pullbackHom π A) := by
    calc
      _ = pullbackHom p (n • KW) := ((pullbackHom p).map_nsmul KW n).symm
      _ = pullbackHom p (pullbackHom W.ι A) := congrArg (pullbackHom p) hlocal
      _ = pullbackHom (p ≫ W.ι) A :=
        (congrArg (fun f => f A) (pullbackHom_comp p W.ι)).symm
      _ = pullbackHom (G.toModel ≫ π) A := pullback_eq_of_hom_eq _ _ hp A
      _ = _ := congrArg (fun f => f A) (pullbackHom_comp G.toModel π)
  have hord := congrArg (cartierOrderAtHom G.neighborhood G.point) hdiv
  have hlin := (cartierOrderAtHom G.neighborhood G.point).map_nsmul (pullbackHom p KW) n
  have hopen : cartierOrderAt G.neighborhood (pullbackHom G.toModel (pullbackHom π A))
      G.point = S.cartierToWeilHom (pullbackHom π A) C := by
    rw [pullbackHom_eq_cartierRestrictionHom]
    exact cartierOrderAt_cartierRestrictionHom G.toModel (pullbackHom π A)
      G.point C.genericPoint G.point_eq
  exact hlin.symm.trans (hord.trans hopen)

end KltDP.Geometry.CanonicalLocalReferencePullbackOrder

#check @KltDP.Geometry.CanonicalLocalReferencePullbackOrder.referenceMap_genericPointPreserving
#check @KltDP.Geometry.CanonicalLocalReferencePullbackOrder.multiple_pullback_order
#print axioms KltDP.Geometry.CanonicalLocalReferencePullbackOrder.referenceMap_genericPointPreserving
#print axioms KltDP.Geometry.CanonicalLocalReferencePullbackOrder.multiple_pullback_order

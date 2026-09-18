import KltDP.Geometry.MinimalResolutionDiscrepancy
import KltDP.Geometry.NonpositiveResolutionSingularCount
import KltDP.Geometry.ProperBirationalConnectedFibers

/-!
# Actual singular points and the original minimal-resolution graph

Minimality and actual projective-line isomorphisms give nonpositive original
canonical discrepancies. Proper birationality gives connected original fibers.
The existing original-map count theorem and graph-component correspondence
therefore give exact counts, with finiteness established before cardinality.

This derives the sign and connectedness inputs; it does not construct a
minimal resolution or prove general rationality of its exceptional curves.
The selected Hodge and Stein literature dependencies remain isolated.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open NormalProjectiveSurface NormalModelCanonical

/-- The connected components of the original exceptional locus count exactly
the actual singular points. The sign and connected-fiber facts are derived. -/
theorem IsMinimalResolution.singularPoints_card_eq_exceptional_components
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hpush : letI : IsProper π := hmin.toIsResolution.isProper
      BirationalWeilPushforward.pushforward π
        ((isBirational_iff_isBirationalScheme π).mp hmin.birational)
        (S.cartierToWeilHom KS) = KX) :
    Finite (ConnectedComponents (exceptionalLocus π)) ∧
      X.singularPoints.card = Nat.card (ConnectedComponents (exceptionalLocus π)) := by
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  exact hmin.toIsResolution.singularPoints_card_eq_exceptional_components_of_nonpositive
    (ProperBirationalConnectedFibers.resolution_pointFibers_connected π hmin.toIsResolution)
    KS eKS KX hcanonical hK hpush
    (fun C _ => MinimalResolutionDiscrepancy.coefficient_nonpos S X π hmin
      KS eKS KX hK hrational hpush C)

/-- The graph whose vertices are all actual contracted primes has exactly one
connected component for each actual singular point. No graph count is supplied. -/
theorem IsMinimalResolution.singularPoints_card_eq_graph_components
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme} (hmin : IsMinimalResolution S X π)
    (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (KX : X.WeilDivisor) (hcanonical : IsCanonicalWeilDivisor X KX)
    (hK : X.QCartier (rationalizeWeilDivisor X KX))
    (hrational : ∀ C : S.PrimeCurve, IsExceptionalCurve π C →
      ∃ e : C.toScheme ≅ projectiveSpace k 1,
        e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hpush : letI : IsProper π := hmin.toIsResolution.isProper
      BirationalWeilPushforward.pushforward π
        ((isBirational_iff_isBirationalScheme π).mp hmin.birational)
        (S.cartierToWeilHom KS) = KX) :
    Finite (ActualExceptionalIncidence.graph π).ConnectedComponent ∧
      X.singularPoints.card =
        Nat.card (ActualExceptionalIncidence.graph π).ConnectedComponent := by
  obtain ⟨hfinite, hcount⟩ :=
    hmin.singularPoints_card_eq_exceptional_components KS eKS KX hcanonical hK hrational hpush
  letI : Finite (ConnectedComponents (exceptionalLocus π)) := hfinite
  let e := ActualExceptionalIncidence.resolutionComponentEquiv π hmin.toIsResolution
    (ProperBirationalConnectedFibers.resolution_pointFibers_connected π hmin.toIsResolution)
  exact ⟨Finite.of_equiv _ e, hcount.trans (Nat.card_congr e)⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsMinimalResolution.singularPoints_card_eq_exceptional_components
#print axioms KltDP.Geometry.IsMinimalResolution.singularPoints_card_eq_graph_components

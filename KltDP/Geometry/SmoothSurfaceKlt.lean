import KltDP.Geometry.NormalModelKltOfSNC
import KltDP.Geometry.CanonicalWeilOfCartier
import KltDP.Geometry.SmoothCanonicalCartierExterior
import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.QCartierPullbackFunctorial
import KltDP.Geometry.StrictNormalCrossingsCartierLocality
import KltDP.Geometry.EffectiveCartierZero

/-!
# Smooth surfaces satisfy the original all-normal-model klt definition

Apply the proved SNC criterion to the original identity morphism and its
zero discrepancy. The canonical divisor is represented by the original
second differential exterior; no model-wise inequality is an input.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

open SmoothCanonicalExteriorComparison NormalProjectiveSurface

theorem isStrictNormalCrossingsCartier_zero (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] : IsStrictNormalCrossingsCartier X 0 := by
  apply isStrictNormalCrossingsCartier_of_local_equations
  intro x
  refine ⟨zeroCartierChart X, Set.mem_univ _, Or.inl ?_⟩
  change IsUnit (X.presheaf.germ ⊤ x (Set.mem_univ _) (1 : Γ(X, ⊤)))
  rw [map_one]
  exact isUnit_one

theorem isKltWithCanonicalDivisor_of_smooth_cartier
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 X.structureMorphism]
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅ relativeDifferentialExterior X.structureMorphism 2) :
    IsKltWithCanonicalDivisor X (X.cartierToWeilHom K) := by
  letI : IsSmooth X.structureMorphism :=
    IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism
  let hid : IsBirationalScheme (𝟙 X.toScheme) :=
    ⟨rfl, by rw [Scheme.stalkMap_id]; exact CategoryTheory.IsIso.id _⟩
  letI : GenericPointPreserving (𝟙 X.toScheme) := ⟨hid.map_genericPoint⟩
  have hK : X.QCartier (rationalizeWeilDivisor X (X.cartierToWeilHom K)) :=
    (X.rationalCartierMap K).property
  have hpush : BirationalWeilPushforward.pushforward (𝟙 X.toScheme) hid
      (X.cartierToWeilHom K) = X.cartierToWeilHom K := by
    have h := BirationalWeilPushforward.pushforward_cartier_pullback (𝟙 X.toScheme) hid K
    rw [DominantCartierPullback.pullbackHom_id] at h
    exact h
  have hzero : X.rationalCartierToWeilHom K - QCartierPullback.pullback (𝟙 X.toScheme)
      (rationalizeWeilDivisor X (X.cartierToWeilHom K)) hK = 0 := by
    rw [QCartierPullback.pullback_id]
    exact sub_self _
  apply isKltWithCanonicalDivisor_of_snc_discrepancy X X (𝟙 X.toScheme) hid
    (Category.id_comp _) K eK (X.cartierToWeilHom K)
    (IsCanonicalWeilDivisor.of_cartier X K eK) hK hpush 0
    (isStrictNormalCrossingsCartier_zero X.toScheme)
    (fun C => Or.inl (by rw [map_zero]; rfl))
  · rw [hzero]
    simp only [Finsupp.support_zero, Finset.empty_subset]
  · intro C
    rw [hzero]
    norm_num

/-- The canonical choice is constructed internally on the original smooth surface. -/
theorem NormalProjectiveSurface.isKlt_of_isSmooth
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    [IsSmoothOfRelativeDimension 2 X.structureMorphism] : IsKlt X := by
  let K := SmoothCanonicalCartierRepresentative.cartierRepresentative X.structureMorphism
  exact ⟨X.cartierToWeilHom K,
    isKltWithCanonicalDivisor_of_smooth_cartier X K
      (SmoothCanonicalCartierExterior.representativeIsoExterior X.structureMorphism)⟩

end KltDP.Geometry

#check @KltDP.Geometry.NormalProjectiveSurface.isKlt_of_isSmooth
#print axioms KltDP.Geometry.NormalProjectiveSurface.isKlt_of_isSmooth

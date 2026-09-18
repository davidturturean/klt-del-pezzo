import KltDP.Geometry.GloballyGeneratedPullback
import KltDP.Geometry.AmpleNefUnconditional
import KltDP.Geometry.DominantCartierPullbackModule

/-!
# An original ample line sheaf has nef pullback

Actual scheme pullback preserves the original generating family and the
positive Picard power witnessing semiampleness. The existing unconditional
surface theorem then gives nefness of the original pullback. This holds
for every morphism; neither birationality nor an intersection formula is
assumed. Positive self-intersection is a further, separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AmplePullbackNef

/-- The positive-power witness for semiampleness pulls back along the
original morphism, with its original Picard power preserved. -/
theorem isSemiample_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : InvertibleSheaf X) (hL : Positivity.IsSemiample L) :
    Positivity.IsSemiample (pullbackInvertibleSheaf f L) := by
  obtain ⟨n, hn, M, hM, hgen⟩ := hL
  refine ⟨n, hn, pullbackInvertibleSheaf f M, ?_,
    GloballyGeneratedPullback.isGloballyGenerated f M.obj hgen⟩
  calc
    (pullbackInvertibleSheaf f M).toPic = schemePicardPullbackHom f M.toPic :=
      (schemePicardPullbackHom_toPic f M).symm
    _ = (schemePicardPullbackHom f L.toPic) ^ n := by rw [hM, map_pow]
    _ = (pullbackInvertibleSheaf f L).toPic ^ n := by
      rw [schemePicardPullbackHom_toPic]

/-- An ample original target sheaf gives a semiample original pullback. -/
theorem isSemiample_pullback_of_isAmple {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : Y ⟶ X) (L : InvertibleSheaf X)
    (hL : AmpleSerre.IsAmple L) : Positivity.IsSemiample (pullbackInvertibleSheaf f L) :=
  isSemiample_pullback f L (AmpleSerre.isSemiample_of_isAmple L hL)

/-- Every original morphism from a normal projective surface pulls an
ample target line sheaf back to an actual nef line sheaf. -/
theorem isNef_pullback_of_isAmple {k : Type u} [Field k]
    (S : NormalProjectiveSurface k) {X : Scheme.{u}} [IsLocallyNoetherian X]
    (π : S.toScheme ⟶ X) (L : InvertibleSheaf X) (hL : AmpleSerre.IsAmple L) :
    Positivity.IsNef S.structureMorphism (pullbackInvertibleSheaf π L) :=
  AmpleNefUnconditional.isNef_of_isSemiample S _
    (isSemiample_pullback_of_isAmple π L hL)

/-- The signed Cartier pullback has the same actual nefness, through the
proved isomorphism of its original module with the original pulled module. -/
theorem isNef_signedCartier_pullback {k : Type u} [Field k]
    {S X : NormalProjectiveSurface k} (π : S.toScheme ⟶ X.toScheme)
    [GenericPointPreserving π] (D : CartierDivisor X.toScheme)
    (hD : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme D)) :
    Positivity.IsNef S.structureMorphism
      (cartierDivisorInvertibleSheaf S.toScheme (DominantCartierPullback.pullbackHom π D)) := by
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  have h := isNef_pullback_of_isAmple S π (cartierDivisorInvertibleSheaf X.toScheme D) hD
  rw [Positivity.isNef_iff_forall_primeCurve] at h ⊢
  intro C
  exact (h C).trans_eq
    (C.restrictionDegree_eq_of_iso (DominantCartierPullback.modulePullbackIso π D))

end KltDP.Geometry.AmplePullbackNef

#print axioms KltDP.Geometry.AmplePullbackNef.isNef_signedCartier_pullback

import KltDP.Geometry.NormalSchemeAffineNormalization

/-!
# Restriction in the original function-field integral closures

The restriction map keeps the literal rational function unchanged.  Its
integrality over the smaller open follows from the original sheaf
restriction and the generic-germ scalar tower.  Normality then identifies
these maps with the restrictions of the original structure sheaf.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalSchemeAffineNormalization

variable (X : Scheme.{u}) [IsIntegral X]

/-- Original section restriction does not change the original rational function. -/
theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE hVU).op a) =
      X.germToFunctionField U a :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) (genericPoint X) _ a

/-- An integral rational function stays integral after restricting coefficients. -/
theorem integral_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) {q : X.functionField} (hq : IsIntegral Γ(X, U) q) :
    IsIntegral Γ(X, V) q := by
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a =>
      (germ_restrict X hVU a).symm)
  exact hq.tower_top

/-- The actual restriction is the identity on elements of the original function field. -/
def restriction {U V : X.Opens} [Nonempty U] [Nonempty V] (hVU : V ≤ U) :
    integralClosure Γ(X, U) X.functionField →+*
      integralClosure Γ(X, V) X.functionField where
  toFun q := ⟨q, integral_restrict X hVU q.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[simp] theorem restriction_coe {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (q : integralClosure Γ(X, U) X.functionField) :
    (restriction X hVU q : X.functionField) = q := rfl

/-- Original normal-section identifications commute with every original restriction. -/
theorem sectionsEquiv_naturality (hnormal : IsNormalScheme X)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (hVU : V ≤ U) :
    (restriction X hVU).comp (sectionsEquiv X hnormal U).toRingEquiv.toRingHom =
      (sectionsEquiv X hnormal V).toRingEquiv.toRingHom.comp
        (X.presheaf.map (homOfLE hVU).op).hom := by
  ext a
  change X.germToFunctionField U a = _
  exact (germ_restrict X hVU a).symm

/-- The actual integral-closure spectrum transitions retain the original projections. -/
@[reassoc] theorem restriction_projection {U V : X.Opens}
    [Nonempty U] [Nonempty V] (hVU : V ≤ U) :
    Spec.map (CommRingCat.ofHom (restriction X hVU)) ≫ projection X U =
      projection X V ≫ Spec.map (X.presheaf.map (homOfLE hVU).op) := by
  unfold projection
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  change X.germToFunctionField U a = _
  exact (germ_restrict X hVU a).symm

end KltDP.Geometry.NormalSchemeAffineNormalization

#print axioms KltDP.Geometry.NormalSchemeAffineNormalization.sectionsEquiv_naturality
#print axioms KltDP.Geometry.NormalSchemeAffineNormalization.restriction_projection

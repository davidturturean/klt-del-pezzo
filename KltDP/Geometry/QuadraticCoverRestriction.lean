import KltDP.Geometry.AffineQuadraticCover
import KltDP.Geometry.TransitionUnitSections

/-!
# Restricting actual quadratic charts to affine open subsets

The coefficient map on quadratic quotients is the first projection of the
proved affine base-change square. Consequently restriction along an actual
open immersion is an open immersion of the cover charts. The final adapters
apply this to actual affine opens of one scheme and their original section
restriction maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.QuadraticCover

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual coefficient-induced map of affine quadratic schemes. -/
def baseChangeProjection (s : R) :
    affineScheme (algebraMap R S s) ⟶ affineScheme s :=
  Spec.map (CommRingCat.ofHom (baseChangeCoeffHom (S := S) s).toRingHom)

/-- The coefficient map is the first projection of the actual base-change square. -/
@[reassoc]
theorem baseChangeSpecIso_inv_fst (s : R) :
    (baseChangeSpecIso S s).inv ≫ pullback.fst _ _ = baseChangeProjection (S := S) s := by
  change (Spec.map (CommRingCat.ofHom (baseChangeTensorEquiv S s).toRingHom) ≫
    (pullbackSpecIso R (CoverAlgebra s) S).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  change Spec.map _ = Spec.map _
  congr 1
  ext x
  change baseChangeEquiv (S := S) s
    ((Algebra.TensorProduct.comm R (CoverAlgebra s) S)
      (x ⊗ₜ[R] (1 : S))) = baseChangeCoeffHom (S := S) s x
  rw [Algebra.TensorProduct.comm_tmul, baseChangeEquiv_tmul, map_one, one_mul]

/-- Restriction of the cover commutes with the actual original base map. -/
@[reassoc]
theorem baseChangeProjection_toBase (s : R) :
    baseChangeProjection (S := S) s ≫ toBase s =
      toBase (algebraMap R S s) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact baseChangeCoeffHom_algebraMap s r

/-- Open immersion of a base chart induces an open immersion of actual cover charts. -/
theorem baseChangeProjection_isOpenImmersion (s : R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    IsOpenImmersion (baseChangeProjection (S := S) s) := by
  rw [← baseChangeSpecIso_inv_fst (S := S) s]
  infer_instance

end KltDP.Geometry.QuadraticCover

namespace KltDP.Geometry.QuadraticCoverOpen

open TransitionUnitGluing QuadraticCover

variable (X : Scheme.{u}) {U W : X.Opens} (hWU : W ≤ U)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W)

include hU hW in
/-- An actual section-ring restriction between affine opens induces an open immersion. -/
theorem restrictionSpec_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (res X hWU))) := by
  have heq : Spec.map (CommRingCat.ofHom (res X hWU)) ≫ hU.fromSpec = hW.fromSpec :=
    hU.map_fromSpec hW (homOfLE hWU).op
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (res X hWU)) ≫ hU.fromSpec) := by
    rw [heq]
    infer_instance
  exact IsOpenImmersion.of_comp _ hU.fromSpec

/-- The actual quadratic chart restricted along the original section-ring map. -/
def restrictionMap (a : Γ(X, U)) :
    affineScheme (res X hWU a) ⟶ affineScheme a := by
  letI : Algebra Γ(X, U) Γ(X, W) := (res X hWU).toAlgebra
  exact baseChangeProjection (S := Γ(X, W)) a

include hU hW in
/-- The restricted quadratic chart is an actual open subscheme of the original chart. -/
theorem restrictionMap_isOpenImmersion (a : Γ(X, U)) :
    IsOpenImmersion (restrictionMap X hWU a) := by
  letI : Algebra Γ(X, U) Γ(X, W) := (res X hWU).toAlgebra
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(X, W)))) :=
    restrictionSpec_isOpenImmersion X hWU hU hW
  exact baseChangeProjection_isOpenImmersion (S := Γ(X, W)) a

/-- The restriction square preserves the original scheme, not merely the chart coordinate rings. -/
@[reassoc]
theorem restrictionMap_toBase (a : Γ(X, U)) :
    restrictionMap X hWU a ≫ toBase a ≫ hU.fromSpec =
      toBase (res X hWU a) ≫ hW.fromSpec := by
  letI : Algebra Γ(X, U) Γ(X, W) := (res X hWU).toAlgebra
  change baseChangeProjection (S := Γ(X, W)) a ≫ toBase a ≫ hU.fromSpec = _
  rw [← Category.assoc, baseChangeProjection_toBase, Category.assoc]
  change toBase (res X hWU a) ≫
    Spec.map (CommRingCat.ofHom (res X hWU)) ≫ hU.fromSpec = _
  have heq : Spec.map (CommRingCat.ofHom (res X hWU)) ≫ hU.fromSpec = hW.fromSpec :=
    hU.map_fromSpec hW (homOfLE hWU).op
  rw [heq]

end KltDP.Geometry.QuadraticCoverOpen

import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra

/-!
# The original quotient restriction in its two algebra presentations

Prove the two identities with abstract rings and their actual ring homomorphism,
then retain the inferred equations at the original section restriction.
No scheme-module carrier is constructed in this producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionSourceRingMap

private theorem quotient_map_of_toAlgebra {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ) :
    letI : Algebra A B := φ.toAlgebra
    KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMap A B J J' hφ =
      Ideal.quotientMap J' φ hφ := rfl

private theorem quotient_algebraMap_of_toAlgebra {A B : Type u}
    [CommRing A] [CommRing B]
    {φ : A →+* B} {J : Ideal A} {J' : Ideal B} (hφ : J ≤ J'.comap φ) :
    letI : Algebra A B := φ.toAlgebra
    letI : Algebra (A ⧸ J) (B ⧸ J') :=
      (KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMap A B J J' hφ).toAlgebra
    algebraMap (A ⧸ J) (B ⧸ J') = Ideal.quotientMap J' φ hφ := by
  letI : Algebra A B := φ.toAlgebra
  exact (RingHom.algebraMap_toAlgebra
    (KltDP.RingTheory.SmoothPrincipalDeterminantRestriction.quotientMap A B J J' hφ)).trans
      (quotient_map_of_toAlgebra hφ)

private theorem spec_map_congr {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (h : φ = ψ) :
    Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) :=
  congrArg (fun θ : A →+* B => Spec.map (CommRingCat.ofHom θ)) h

/-- The native quotient map is the original ideal quotient of the section restriction. -/
def quotient_map {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  quotient_map_of_toAlgebra (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))

/-- Its induced algebra retains precisely that same original quotient ring map. -/
def quotient_algebraMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  quotient_algebraMap_of_toAlgebra (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))

/-- Applying Spec to the first equation gives the literal original quotient chart map. -/
def quotient_specMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  spec_map_congr (quotient_map I U r)

/-- Applying Spec to the second equation gives the same literal original chart map. -/
def quotient_algebraSpecMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  spec_map_congr (quotient_algebraMap I U r)

end KltDP.Geometry.GluedAdjunctionSourceRingMap

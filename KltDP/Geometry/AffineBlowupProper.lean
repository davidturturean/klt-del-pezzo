import KltDP.Geometry.AffineBlowup
import KltDP.Compatibility.ProjProper

/-!
# Properness of the actual affine Rees blowup

The degree-zero ring of the polynomial Rees algebra is identified with
the original coefficient ring by the actual algebra map. Pinned
`reesAlgebra.fg` supplies finite type from finite generation of the ideal.
The already ported, proved `ProjProper.proj_isProper` then applies to the
actual Rees Proj and its original projection.

Reuse: Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
`RingTheory/ReesAlgebra.lean` (Andrew Yang, Apache 2.0), and the existing
attributed proper-Proj port in `Compatibility/ProjProper.lean` from
Mathlib 568f63d367aed3eca2b5efc21f2ac6c9daf18819. No properness assumption
or new valuative-criterion proof is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace KltDP.Geometry.AffineBlowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Every degree-zero Rees element is the image of its constant coefficient. -/
theorem constants_surjective :
    Function.Surjective (algebraMap R (ReesGrading.component I 0)) := by
  intro x
  refine ⟨((x : reesAlgebra I) : R[X]).coeff 0, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change C (((x : reesAlgebra I) : R[X]).coeff 0) =
    ((x : reesAlgebra I) : R[X])
  simpa only [monomial_zero_left] using
    (ReesGrading.homogeneous_eq_monomial I x).symm

/-- The existing degree-zero algebra map is bijective over any commutative ring. -/
theorem constants_bijective :
    Function.Bijective (algebraMap R (ReesGrading.component I 0)) := by
  refine ⟨?_, constants_surjective I⟩
  intro r s h
  apply Polynomial.C_injective
  exact congrArg (fun x : ReesGrading.component I 0 =>
    ((x : reesAlgebra I) : R[X])) h

/-- The original coefficient ring is the actual degree-zero Rees ring. -/
def zeroRingEquiv : R ≃+* ReesGrading.component I 0 :=
  RingEquiv.ofBijective (algebraMap R (ReesGrading.component I 0))
    (constants_bijective I)

/-- The precise constants morphism used by `toSpec` is an isomorphism. -/
instance constants_isIso :
    IsIso (CommRingCat.ofHom (R := R) (S := ReesGrading.component I 0)
      (algebraMap R (ReesGrading.component I 0))) := by
  let e : CommRingCat.of R ≅ CommRingCat.of (ReesGrading.component I 0) :=
    (zeroRingEquiv I).toCommRingCatIso
  have he : e.hom =
      CommRingCat.ofHom (R := R) (S := ReesGrading.component I 0)
        (algebraMap R (ReesGrading.component I 0)) := by
    ext r
    rfl
  rw [← he]
  infer_instance

/-- Finite generation of the center ideal implies properness of the actual
affine blowup projection. -/
theorem toSpec_isProper_of_fg (hI : I.FG) : IsProper (toSpec I) := by
  let 𝒜 := ReesGrading.component I
  letI : Algebra.FiniteType R (reesAlgebra I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  letI : IsScalarTower R (𝒜 0) (reesAlgebra I) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := 𝒜 0)
      (A := reesAlgebra I) (fun _ => rfl)
  letI : Algebra.FiniteType (𝒜 0) (reesAlgebra I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) _
  letI : IsIso (CommRingCat.ofHom (R := R) (S := 𝒜 0) (algebraMap R (𝒜 0))) :=
    constants_isIso I
  letI : IsProper (Proj.toSpecZero 𝒜) :=
    KltDP.Compatibility.ProjProper.proj_isProper 𝒜
  change IsProper (Proj.toSpecZero 𝒜 ≫
    Spec.map (CommRingCat.ofHom (R := R) (S := 𝒜 0) (algebraMap R (𝒜 0))))
  infer_instance

/-- Every actual ideal over a Noetherian base gives a proper Rees blowup. -/
instance toSpec_isProper [IsNoetherianRing R] : IsProper (toSpec I) :=
  toSpec_isProper_of_fg I (IsNoetherian.noetherian I)

end KltDP.Geometry.AffineBlowup

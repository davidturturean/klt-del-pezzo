import KltDP.Compatibility.ReesGrading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The affine Rees Proj construction

For an ideal `I` of `R`, this is the actual scheme
`Proj (R ⊕ I ⊕ I² ⊕ ⋯)` and its canonical morphism to `Spec R`.
The ring is Mathlib's polynomial Rees subalgebra with the grading proved
in `ReesGrading`; no properties of a blowup are included as fields.

The degree-one charts are the spectra of the actual homogeneous
localizations at `aT`, for `a ∈ I`. The general blowup universal property,
gluing over a non-affine base, and exceptional-divisor and surface
formulas are not asserted here.

The construction follows Stacks 01OF (Definition 31.33.1 and
Lemma 31.33.2), with affine chart rings as in Stacks 052Q.
No literature statement is used as an axiom.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.AffineBlowup

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The actual Proj of the ordinary Rees algebra of `I`. -/
def scheme : Scheme := AlgebraicGeometry.Proj (ReesGrading.component I)

/-- The canonical morphism from the Rees Proj to the original affine scheme. -/
def toSpec : scheme I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (ReesGrading.component I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ReesGrading.component I 0)))

/-- The degree-one homogeneous element associated to an actual element of `I`. -/
def degreeOne (a : I) : reesAlgebra I :=
  ReesGrading.single I 1 ⟨(a : R), by simpa using a.property⟩

theorem degreeOne_mem (a : I) : degreeOne I a ∈ ReesGrading.component I 1 :=
  ReesGrading.single_mem_component I 1 _

/-- The actual homogeneous localization defining the chart at `aT`. -/
abbrev chartRing (a : I) :=
  HomogeneousLocalization.Away (ReesGrading.component I) (degreeOne I a)

/-- The actual degree-one basic open of the Rees Proj. -/
def chartOpen (a : I) : (scheme I).Opens :=
  Proj.basicOpen (ReesGrading.component I) (degreeOne I a)

/-- The existing Proj chart theorem identifies this open with the spectrum
of its actual homogeneous localization. -/
def chartIso (a : I) :
    (chartOpen I a).toScheme ≅ Spec (CommRingCat.of (chartRing I a)) :=
  Proj.basicOpenIsoSpec (ReesGrading.component I) (degreeOne I a)
    (degreeOne_mem I a) (by decide)

/-- The actual affine chart open immersion. -/
def chartι (a : I) : Spec (CommRingCat.of (chartRing I a)) ⟶ scheme I :=
  Proj.awayι (ReesGrading.component I) (degreeOne I a)
    (degreeOne_mem I a) (by decide)

instance (a : I) : IsOpenImmersion (chartι I a) := by
  unfold chartι
  infer_instance

/-- On each chart the structure map is the actual algebra map through
the degree-zero part of the Rees algebra. -/
theorem chartι_toSpec (a : I) :
    chartι I a ≫ toSpec I =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (ReesGrading.component I)
          (Submonoid.powers (degreeOne I a))).comp
            (algebraMap R (ReesGrading.component I 0)))) := by
  unfold chartι toSpec
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end KltDP.Geometry.AffineBlowup

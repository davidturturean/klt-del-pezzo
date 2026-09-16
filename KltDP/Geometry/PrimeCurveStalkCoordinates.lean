import KltDP.Geometry.HeightOneLocalization
import KltDP.Geometry.PrincipalDivisor

/-!
# Actual prime-curve coordinates at a surface stalk

Every curve through a point determines a height-one prime in that point's
actual structure-sheaf stalk. The construction uses any affine neighborhood
of the point and extends the curve prime through the actual germ map.
Contraction recovers the affine prime, so distinct curves remain distinct.
The original curve order agrees with the localized stalk-prime order in
the original function field.

No affine ring is assumed factorial. No reverse correspondence between
all height-one stalk primes and dimension-one closed curves is asserted.
The pinned localization correspondence and height preservation are used
through `HeightOneLocalization`; the scheme identifications use Mathlib's
actual affine-chart and structure-sheaf germ maps.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}

/-- The generic point of an actual curve specializes to each of its points. -/
theorem genericPoint_specializes_of_mem (C : X.PrimeCurve) {x : X.toScheme}
    (hx : x ∈ C) : C.genericPoint ⤳ x := by
  apply specializes_iff_mem_closure.mpr
  rwa [C.closure_genericPoint]

/-- Every open neighborhood of a point on a curve contains its generic point. -/
theorem genericPoint_mem_of_mem (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (x : U) (hx : (x : X.toScheme) ∈ C) : C.genericPoint ∈ U :=
  (C.genericPoint_specializes_of_mem hx).mem_open U.isOpen x.2

/-- In an actual affine chart, the curve prime lies below the prime of
each point on that curve. This is the specialization order, not an input. -/
theorem affineHeightOnePrime_le (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (x : X.toScheme) ∈ C) :
    (C.affineHeightOnePrime hU (C.genericPoint_mem_of_mem x hx)).1.asIdeal ≤
      (hU.primeIdealOf x).asIdeal := by
  have hspecial : (⟨C.genericPoint, C.genericPoint_mem_of_mem x hx⟩ : U) ⤳ x :=
    (subtype_specializes_iff _ _).mpr (C.genericPoint_specializes_of_mem hx)
  exact (PrimeSpectrum.le_iff_specializes _ _).mpr
    (hspecial.map hU.isoSpec.hom.continuous)

/-- The actual height-one stalk prime of a curve through a point. The
ideal is extended along the structure-sheaf germ of the affine chart. -/
def stalkHeightOnePrime (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (x : X.toScheme) ∈ C) :
    RingTheory.AffineHeightOnePrime (X.stalk x) := by
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  exact RingTheory.affineHeightOnePrimeAtPrime Γ(X.toScheme, U)
    (hU.primeIdealOf x).asIdeal (X.stalk x)
    (C.affineHeightOnePrime hU (C.genericPoint_mem_of_mem x hx))
    (C.affineHeightOnePrime_le hU x hx)

/-- Contracting the stalk prime along the actual germ recovers the
curve's affine prime. -/
theorem stalkHeightOnePrime_comap (C : X.PrimeCurve) {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (x : X.toScheme) ∈ C) :
    (C.stalkHeightOnePrime hU x hx).1.asIdeal.comap
        (X.toScheme.presheaf.germ U x x.2).hom =
      (C.affineHeightOnePrime hU (C.genericPoint_mem_of_mem x hx)).1.asIdeal := by
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  exact RingTheory.affineHeightOnePrimeAtPrime_comap Γ(X.toScheme, U)
    (hU.primeIdealOf x).asIdeal (X.stalk x)
    (C.affineHeightOnePrime hU (C.genericPoint_mem_of_mem x hx))
    (C.affineHeightOnePrime_le hU x hx)

/-- Different actual curves through a point give different height-one
primes of the point's actual stalk. -/
theorem stalkHeightOnePrime_injective {U : X.toScheme.Opens}
    (hU : IsAffineOpen U) (x : U) :
    Function.Injective (fun C : {C : X.PrimeCurve // (x : X.toScheme) ∈ C} =>
      C.1.stalkHeightOnePrime hU x C.2) := by
  intro C D h
  apply Subtype.ext
  apply genericPoint_injective
  have hc := congrArg (fun p : RingTheory.AffineHeightOnePrime (X.stalk x) =>
    p.1.asIdeal.comap (X.toScheme.presheaf.germ U x x.2).hom) h
  simp only [stalkHeightOnePrime_comap] at hc
  have hp := PrimeSpectrum.ext hc
  have hpoints := congrArg (fun p => hU.fromSpec.base p) hp
  simpa only [affineHeightOnePrime, hU.fromSpec_primeIdealOf] using hpoints

/-- The actual curve order equals its normalized height-one-prime order
in the stalk of any point on the curve. The maps into the function field
are the original structure-sheaf maps. -/
theorem order_eq_stalkHeightOnePrime_order (C : X.PrimeCurve)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (x : U)
    (hx : (x : X.toScheme) ∈ C) (f : X.toScheme.functionFieldˣ) :
    C.order f = RingTheory.affinePrincipalOrder (X.stalk x) X.toScheme.functionField
      (C.stalkHeightOnePrime hU x hx) f := by
  letI : Nonempty U := ⟨x⟩
  letI : IsNoetherianRing Γ(X.toScheme, U) := X.affineSections_isNoetherianRing hU
  letI : IsIntegrallyClosed Γ(X.toScheme, U) := X.affineSections_isIntegrallyClosed hU
  letI : IsFractionRing Γ(X.toScheme, U) X.toScheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.toScheme U hU
  letI : Algebra Γ(X.toScheme, U) (X.stalk x) :=
    X.toScheme.presheaf.algebra_section_stalk x
  letI : IsLocalization.AtPrime (X.stalk x) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  rw [C.order_eq_affinePrincipalOrder hU (C.genericPoint_mem_of_mem x hx) f]
  exact (RingTheory.affinePrincipalOrder_atPrime Γ(X.toScheme, U)
    (hU.primeIdealOf x).asIdeal (X.stalk x) X.toScheme.functionField
    (C.affineHeightOnePrime hU (C.genericPoint_mem_of_mem x hx))
    (C.affineHeightOnePrime_le hU x hx) f).symm

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

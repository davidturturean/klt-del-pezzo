import KltDP.Geometry.FinitePrimeCartierSumSupport
import KltDP.Geometry.ProperBirationalConnectedFibers

/-!
# The actual exceptional locus is the support of the reduced Cartier sum

For an original resolution, all contracted primes form a finite family.
The actual reduced sum of their prime Cartier divisors is supported on
their original union, which the proved connected-fiber and structure-sheaf
results identify with the whole original exceptional locus. This uses the
selected isolated Stein dependency; no klt, rationality, or support premise
is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- The finite reduced prime Cartier sum represents the entire original
exceptional locus of an actual resolution, without additional isolated points. -/
theorem IsResolution.reduced_exceptional_cartier_support
    {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    {π : S.toScheme ⟶ X.toScheme} (hres : IsResolution S X π) :
    letI : IsProper π := hres.isProper
    let hbir : IsBirationalScheme π :=
      (isBirational_iff_isBirationalScheme π).mp hres.birational
    letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
      (exceptionalCurves_finite_of_proper_birational π hbir).fintype
    ((effectiveCartierIdealDataOfRegularEquations S.toScheme
      (∑ C : ActualExceptionalIncidence.Vertices π, S.primeCurveCartier hres.regular C.val)
      (S.finite_primeCartier_sum_hasRegularEquations hres.regular
        (fun C : ActualExceptionalIncidence.Vertices π => C.val) Subtype.val_injective)).support :
      Set S.toScheme) = exceptionalLocus π := by
  classical
  letI : IsProper π := hres.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  letI : Fintype (ActualExceptionalIncidence.Vertices π) :=
    (exceptionalCurves_finite_of_proper_birational π hbir).fintype
  letI : IsIso π.c := ProperBirationalStructureSheaf.resolution_c_isIso π hres
  dsimp only
  rw [S.finite_primeCartier_sum_support hres.regular
    (fun C : ActualExceptionalIncidence.Vertices π => C.val) Subtype.val_injective]
  rw [ActualExceptionalLocus.exceptionalLocus_eq_primeSupport π hbir hres.over_base
    (ProperBirationalConnectedFibers.resolution_pointFibers_connected π hres)]
  ext x
  simp only [Set.mem_iUnion, ActualExceptionalLocus.mem_primeSupport]
  constructor
  · rintro ⟨C, hx⟩
    exact ⟨C.val, C.property, hx⟩
  · rintro ⟨C, hC, hx⟩
    exact ⟨⟨C, hC⟩, hx⟩

end KltDP.Geometry

#print axioms KltDP.Geometry.IsResolution.reduced_exceptional_cartier_support

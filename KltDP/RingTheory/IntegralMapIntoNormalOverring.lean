import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral maps inside the original normal overring

An integral algebra embedded into an overring in which the original base
is integrally closed cannot contain any new elements. The commuting square
uses the original scalar homomorphism, not an independently chosen algebra.
-/

noncomputable section

universe u v w

namespace KltDP.RingTheory.IntegralMapIntoNormalOverring

/-- The actual integral scalar map is bijective when an injective map to
the original normal overring commutes with its original base inclusion. -/
theorem bijective
    {A : Type u} {B : Type v} {F : Type w}
    [CommRing A] [CommRing B] [CommRing F] [Algebra A F]
    [IsIntegrallyClosedIn A F]
    (f : A →+* B) (hf : f.IsIntegral)
    (j : B →+* F) (hj : Function.Injective j)
    (hcomm : j.comp f = algebraMap A F) : Function.Bijective f := by
  letI : Algebra A B := f.toAlgebra
  let jA : B →ₐ[A] F :=
    { toRingHom := j
      commutes' := fun a => DFunLike.congr_fun hcomm a }
  constructor
  · intro a b hab
    apply IsIntegralClosure.algebraMap_injective' (A := A) (R := A) (B := F)
    calc
      algebraMap A F a = j (f a) := (DFunLike.congr_fun hcomm a).symm
      _ = j (f b) := congrArg j hab
      _ = algebraMap A F b := DFunLike.congr_fun hcomm b
  · intro b
    have hb : _root_.IsIntegral A b := hf b
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (hb.map jA)
    exact ⟨a, hj ((DFunLike.congr_fun hcomm a).trans ha)⟩

end KltDP.RingTheory.IntegralMapIntoNormalOverring

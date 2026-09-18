import KltDP.Geometry.ClosedPointDimension
import KltDP.Geometry.CotangentGenerators
import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# Actual cotangent parameters at a regular closed surface point

Regularity and the original closed-stalk dimension supply two actual
maximal-ideal elements whose cotangent classes form a basis. Nakayama gives
generation of that same maximal ideal, and their residue-cotangent wedge
has coordinate one in its actual determinant frame.

This is a statement about the actual cotangent space m/m². It does not
assert formal smoothness or a basis of the stalk's Kähler module over k.
-/

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (x : X.toScheme) (hclosed : IsClosed ({x} : Set X.toScheme))
    (hregular : RegularPoint X.toScheme x)

include hclosed hregular

/-- The original residue cotangent space at a regular closed surface point has dimension two. -/
theorem regular_closed_stalk_cotangent_finrank :
    Module.finrank (ResidueField (X.stalk x)) (CotangentSpace (X.stalk x)) = 2 := by
  have hreg : RegularLocal (X.stalk x) := hregular
  have h :
      (Module.finrank (ResidueField (X.stalk x)) (CotangentSpace (X.stalk x)) :
        WithBot ℕ∞) = 2 :=
    hreg.2.symm.trans (X.closed_stalk_dimension_two x hclosed)
  exact ENat.coe_inj.mp (WithBot.coe_inj.mp h)

/-- Actual vanishing parameters form a residue-cotangent basis and generate the original maximal ideal.
Their actual residue-cotangent top wedge is primitive, with frame coordinate one. -/
theorem exists_regular_closed_stalk_cotangent_parameters :
    ∃ (v : Fin 2 → maximalIdeal (X.stalk x))
      (b : Basis (Fin 2) (ResidueField (X.stalk x)) (CotangentSpace (X.stalk x))),
      (∀ i, (maximalIdeal (X.stalk x)).toCotangent (v i) = b i) ∧
      Ideal.span (Set.range (fun i => (v i : X.stalk x))) = maximalIdeal (X.stalk x) ∧
      AffineTopDifferentialFrame.determinantEquiv b
        (exteriorPower.ιMulti (ResidueField (X.stalk x)) 2
          (fun i => (maximalIdeal (X.stalk x)).toCotangent (v i))) = 1 := by
  letI : IsNoetherianRing (X.stalk x) := hregular.1
  let b := Module.finBasisOfFinrankEq (ResidueField (X.stalk x)) (CotangentSpace (X.stalk x))
    (X.regular_closed_stalk_cotangent_finrank x hclosed hregular)
  choose v hv using fun i => (maximalIdeal (X.stalk x)).toCotangent_surjective (b i)
  have heq : (fun i => (maximalIdeal (X.stalk x)).toCotangent (v i)) = b := funext hv
  refine ⟨v, b, hv, ?_, ?_⟩
  · apply (maximal_generators_iff_cotangent_spans v).mpr
    rw [heq]
    exact b.span_eq
  · rw [heq]
    exact AffineTopDifferentialFrame.determinantEquiv_basis_wedge b

end KltDP.Geometry.NormalProjectiveSurface

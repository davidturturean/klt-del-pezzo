import KltDP.Geometry.FiniteClosedPointComplement
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Stacks 0AHI: the complete published point-blowup domination statement

Isolated literature candidate, admitted by the root successor source review.
Source: Stacks 0AHI, resolve.tex 928–941, commit
a04446e57ec1fbc252a871afcec7752fb2807b14; GFDL-1.2-or-later.

The original arbitrary Noetherian scheme, finite closed set, regular
dimension-two stalks on that set, and proper morphism are retained. The
existing actual Rees point blowups form a finite sequence above the original
set. This literal supplies no independent over-base equation, smoothness,
projectivity, discrepancy, or klt conclusion. Production activation is separate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open KltDP.Geometry

universe u

namespace KltDP.Literature.Stacks

axiom closed_point_blowups_dominate_proper_literal :
  ∀ (X Y : Scheme.{u}) (f : Y ⟶ X),
    IsNoetherian X →
    ∀ (T : Set X) (hfinite : T.Finite)
      (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)),
      (∀ x ∈ T, RegularPoint X x) →
      (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) →
      IsProper f →
      IsIso (f ∣_ finiteClosedPointComplement X T hfinite hclosed) →
      ∃ (Z : Scheme.{u}) (b : Z ⟶ X),
        SchemePointBlowup.SequenceAway X Tᶜ Z b ∧
        ∃ (g : Z ⟶ Y), g ≫ f = b

end KltDP.Literature.Stacks

#check @KltDP.Literature.Stacks.closed_point_blowups_dominate_proper_literal

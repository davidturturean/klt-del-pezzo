import KltDP.Geometry.ProjectiveProductCanonicalDifferentials

/-!
# The original second differential and its original base transport

The native equation is obtained from the original map itself, with its
original Hom carrier and dictionaries, by unfolding only one side of its
reflexive equality. A generic categorical lemma changes only the proof
argument of the base transport. No scheme or original morphism is replaced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalSecondMapEquality

open SchemeKaehlerSheaf
open KltDP.Examples.FrobeniusProjectivePoints
open ProjectiveProductCanonicalDifferentials

private theorem replace_transport_proof
    {C : Type*} [Category C] {A B T : C}
    {f : A ⟶ B} {g : A ⟶ T} {h : B = T}
    (hg : f ≫ eqToHom h = g) (h' : B = T) :
    f ≫ eqToHom h' = g := by
  have hh : h' = h := Subsingleton.elim _ _
  cases hh
  exact hg

variable (k : Type u) [Field k]

/-- Keep the original equality carrier and original defining expression;
no independently reconstructed morphism type occurs in this producer. -/
private def original_stored_map_eq := by
  have h := Eq.refl (secondDifferential k)
  conv at h =>
    lhs
    unfold secondDifferential
  exact h

private def original_second_map_eq_proof :=
  replace_transport_proof (original_stored_map_eq k)
    (congrArg (fun f => baseRingSheaf f) (secondProjection_structure k))

private abbrev statementOf {P : Prop} (_proof : P) : Prop := P

/-- The unchanged original second map equals `secondDifferential`.
The transparent proposition is precisely the original map followed by the
`congrArg baseRingSheaf secondProjection_structure` transport, with original
source `secondFactor k` and original product cotangent target. -/
theorem original_second_map_eq : statementOf (original_second_map_eq_proof k) :=
  original_second_map_eq_proof k

private def original_second_map_eq_for_transport_proof :=
  replace_transport_proof (original_stored_map_eq k)

/-- The same original map equation for every proof of its original base-sheaf
identification. Its argument type is inherited directly from the stored producer;
this lets a consumer retain its exact already checked transport proof. -/
theorem original_second_map_eq_for_transport :
    statementOf (original_second_map_eq_for_transport_proof k) :=
  original_second_map_eq_for_transport_proof k

end KltDP.Geometry.ProjectiveProductCanonicalSecondMapEquality

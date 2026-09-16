import KltDP.Geometry.CartierPicardComparison
import KltDP.Geometry.InvertibleSheaf
import KltDP.Geometry.CartierDivisorTrivialization

/-!
# An actual line-bundle frame inside a prescribed neighborhood

On an integral scheme, the accepted Cartier/Picard comparison represents
an actual invertible sheaf by an actual Cartier divisor. Apply the local
equation theorem to that divisor restricted to the prescribed open. Its
actual equation frame therefore lies inside that open. No frame or local
trivialization witness is supplied as an additional hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFrameWithin

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X]

/-- An actual invertible sheaf admits an actual unit frame near a point
inside any prescribed open neighborhood of that point. -/
theorem exists_unit_frame_within (L : InvertibleSheaf X)
    (V : X.Opens) (y : X) (hy : y ∈ V) :
    ∃ U : X.Opens, U ≤ V ∧ y ∈ U ∧
      Nonempty (L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_cartierDivisor_module_iso X L.obj
  obtain ⟨U, i, hyU, f, hf⟩ := exists_local_cartier_equation X V
    ((cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op D) y hy
  letI : Nonempty U := ⟨⟨y, hyU⟩⟩
  have hres : (cartierDivisorSheaf X).val.map i.op
      ((cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op D) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D := by
    calc
      _ = (cartierDivisorSheaf X).val.map
          ((homOfLE (le_top : V ≤ ⊤)).op ≫ i.op) D :=
        (ConcreteCategory.congr_hom ((cartierDivisorSheaf X).val.map_comp
          (homOfLE (le_top : V ≤ ⊤)).op i.op) D).symm
      _ = _ := congrArg (fun j => (cartierDivisorSheaf X).val.map j D)
        (Subsingleton.elim _ _)
  have hf' : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D :=
    hf.trans hres
  exact ⟨U, i.le, hyU, ⟨(_root_.SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e ≪≫
    (cartierEquationOverIso X D U f hf').symm⟩⟩

end KltDP.Geometry.InvertibleSheafFrameWithin

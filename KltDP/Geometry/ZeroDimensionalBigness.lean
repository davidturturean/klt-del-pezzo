import KltDP.Compatibility.SheafOverTerminal
import KltDP.Compatibility.InvertibleTensorUnit
import KltDP.Geometry.RationalTreePicardMultidegree
import KltDP.Geometry.PrimeCurveIntersectionDegreeSum
import KltDP.Geometry.ProperGlobalSectionsFinite
import KltDP.Geometry.Positivity

/-!
# Every invertible sheaf on an integral proper zero-dimensional scheme is big

Dimension zero makes every irreducible closed subset maximal. The closures
of points therefore equal the whole integral scheme, and the scheme's T0
property identifies its points. Any actual local invertible frame then
covers the whole scheme, so the original Picard class is trivial.

Properness gives finite-dimensional global functions for the original base
field action. Their nonzero unit makes this dimension positive. Every
original Picard power consequently has h0 at least one, giving the
coefficient one in the unchanged zero-dimensional `Positivity.IsBig`.
No algebraic closedness, triviality, or section bound is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.ZeroDimensionalBigness

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} [IsIntegral X]

/-- An integral zero-dimensional scheme has just one point. -/
theorem subsingleton_of_dimension_zero (hdim : topologicalKrullDim X = 0) :
    Subsingleton X := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmax : ∀ Z : IrreducibleCloseds X, IsMax Z :=
    Order.krullDim_nonpos_iff_forall_isMax.mp hdim.le
  have hclosure (x : X) : closure ({x} : Set X) = Set.univ := by
    let Z : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hZT : Z ≤ T := Set.subset_univ _
    exact congrArg (fun W : IrreducibleCloseds X => (W : Set X))
      (le_antisymm hZT (hmax Z hZT))
  exact ⟨fun x y =>
    (inseparable_iff_closure_eq.mpr ((hclosure x).trans (hclosure y).symm)).eq⟩

/-- An actual local frame is global on the one-point scheme. -/
theorem nonempty_iso_unit (hdim : topologicalKrullDim X = 0)
    (L : InvertibleSheaf X) :
    Nonempty (L.obj ≅ _root_.SheafOfModules.unit X.ringCatSheaf) := by
  letI : Subsingleton X := subsingleton_of_dimension_zero hdim
  let x : X := genericPoint X
  let t := L.localTrivializations
  obtain ⟨V, φ, ⟨i, ⟨g⟩⟩, hxV⟩ := t.coversTop ⊤ x trivial
  have hx : x ∈ t.X i := g.le hxV
  have hU : t.X i = ⊤ := by
    apply le_antisymm le_top
    intro y _
    simpa only [Subsingleton.elim y x] using hx
  let e : L.obj.over ⊤ ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over ⊤) := by
    exact Eq.mp (congrArg (fun U : X.Opens =>
      L.obj.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) hU) (t.unitIso i)
  exact ⟨KltDP.SheafOfModules.isoFromOverTerminal X.ringCatSheaf
    (⊤ : X.Opens) isTerminalTop
    (e ≪≫ (_root_.SheafOfModules.unitOverIso (R := X.ringCatSheaf) ⊤).symm)⟩

/-- The original Picard class of every invertible sheaf is the unit. -/
theorem toPic_eq_one (hdim : topologicalKrullDim X = 0) (L : InvertibleSheaf X) :
    L.toPic = 1 :=
  (RationalTreePicard.toPic_eq_one_iff_iso_unit L).mpr (nonempty_iso_unit hdim L)

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- Proper global functions have positive dimension over the original base field. -/
theorem hZero_unit_pos :
    0 < cohomologyDimension f (_root_.SheafOfModules.unit X.ringCatSheaf) 0 := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  letI := (baseFieldToGlobalSections f).toAlgebra
  letI : Module.Finite k Γ(X, ⊤) := globalSections_moduleFinite f
  rw [cohomologyDimension_zero_unit_eq_finrank]
  exact Module.finrank_pos

/-- The same positivity for the original unit Picard class. -/
theorem picardHZero_one_pos : 0 < Positivity.picardHZero f (1 : X.Pic) := by
  have htriv : (InvertibleSheaf.trivial X).toPic = 1 :=
    (RationalTreePicard.toPic_eq_one_iff_iso_unit _).mpr ⟨Iso.refl _⟩
  rw [← htriv, Positivity.picardHZero_toPic]
  exact hZero_unit_pos f

/-- Every actual Picard power has a positive section dimension. -/
theorem picardHZero_pow_pos (hdim : topologicalKrullDim X = 0)
    (L : InvertibleSheaf X) (n : ℕ) :
    0 < Positivity.picardHZero f (L.toPic ^ n) := by
  rw [toPic_eq_one hdim L, one_pow]
  exact picardHZero_one_pos f

/-- Every invertible sheaf on an actual integral proper zero-dimensional
scheme is big in the original section-growth definition. -/
theorem isBig (hdim : topologicalKrullDim X = 0) (L : InvertibleSheaf X) :
    Positivity.IsBig f L := by
  refine ⟨1, by norm_num, ?_⟩
  intro N
  refine ⟨N, le_rfl, ?_⟩
  have hzero : Positivity.natDim X = 0 := by simp [Positivity.natDim, hdim]
  rw [hzero, pow_zero, one_mul]
  exact_mod_cast (Nat.succ_le_iff.mpr (picardHZero_pow_pos f hdim L N))

end KltDP.Geometry.ZeroDimensionalBigness

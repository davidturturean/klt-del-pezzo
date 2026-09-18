import KltDP.Geometry.AffineProjectiveGraphClosure
import KltDP.Geometry.BirationalComposition

/-!
# Proper birational completion retaining the original affine model

The original affine graph closure embeds the original W openly in its
actual integral image Z. This open immersion preserves generic points.
The original triangle to X and birationality of the original w therefore
give generic-point preservation and birationality of the actual projection
Z → X, using the existing original function-field composition theorem.

No normality of Z away from the original W is needed or asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.AffineBirationalProjectiveCompletion

/-- The original affine birational model embeds openly in an actual proper
integral birational model over the original X, closed in the original finite
projective bundle and retaining both the original triangle and closure support. -/
theorem exists_completion {k : Type u} [Field k]
    {W X : Scheme.{u}} [IsAffine W] [IsIntegral W] [IsIntegral X]
    (σ : X ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (w : W ⟶ X) [LocallyOfFiniteType (w ≫ σ)] (hw : IsBirationalScheme w) :
    ∃ (n : ℕ) (Z : Scheme.{u}) (j : W ⟶ Z)
        (i : Z ⟶ pullback (projectiveSpaceToSpec k n) σ) (hZ : IsIntegral Z),
      letI := hZ
      IsOpenImmersion j ∧ IsClosedImmersion i ∧
      IsProper (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ) ∧
      IsBirationalScheme (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ) ∧
      j ≫ i ≫ pullback.snd (projectiveSpaceToSpec k n) σ = w ∧
      Set.range i.base = closure (Set.range (j ≫ i).base) := by
  obtain ⟨n, Z, j, i, hZ, hj, hi, hp, hfac, hclosure⟩ :=
    AffineProjectiveGraphClosure.exists_projective_closure σ w
  letI := hZ
  letI : IsOpenImmersion j := hj
  let p := i ≫ pullback.snd (projectiveSpaceToSpec k n) σ
  have hcomp : IsBirationalScheme (j ≫ p) := by
    change IsBirationalScheme (j ≫ i ≫ pullback.snd (projectiveSpaceToSpec k n) σ)
    rw [hfac]
    exact hw
  have hgeneric : p.base (genericPoint Z) = genericPoint X := by
    calc
      p.base (genericPoint Z) = p.base (j.base (genericPoint W)) :=
        congrArg p.base (genericPoint_eq_of_isOpenImmersion j).symm
      _ = (j ≫ p).base (genericPoint W) := rfl
      _ = genericPoint X := hcomp.map_genericPoint
  letI : GenericPointPreserving j := ⟨genericPoint_eq_of_isOpenImmersion j⟩
  letI : GenericPointPreserving p := ⟨hgeneric⟩
  have hbir : IsBirationalScheme p :=
    BirationalComposition.isBirationalScheme_right_of_comp j p hcomp
  exact ⟨n, Z, j, i, hZ, hj, hi, hp, hbir, hfac, hclosure⟩

end KltDP.Geometry.AffineBirationalProjectiveCompletion

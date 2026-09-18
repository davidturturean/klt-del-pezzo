import KltDP.Geometry.AffineBirationalProjectiveCompletion
import KltDP.Geometry.ImmersionBirational

/-!
# Proper birational completion of an original affine neighborhood

Choose an actual affine open of the original integral model containing the
specified original point. It also contains the original generic point.
Restriction of the original finite-type birational map to this open remains
finite type and birational. The proved affine graph completion then gives
an actual proper integral birational model retaining that same open, point,
and map to the original X. No properness or normality of the original model
is required, and no normality of the completion boundary is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.BirationalModelAffineNeighborhoodCompletion

/-- Every original point of an integral finite-type birational model has
an actual affine neighborhood in a proper integral birational completion,
with the original point and both original maps to X retained. -/
theorem exists_completion_near_point {k : Type u} [Field k]
    {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
    (σ : X ⟶ Spec (CommRingCat.of k)) [IsSeparated σ]
    (v : V ⟶ X) [LocallyOfFiniteType (v ≫ σ)]
    (hv : IsBirationalScheme v) (x : V) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (hx : x ∈ U)
        (n : ℕ) (Z : Scheme.{u}) (j : U.toScheme ⟶ Z)
        (i : Z ⟶ pullback (projectiveSpaceToSpec k n) σ) (hZ : IsIntegral Z),
      letI := hZ
      genericPoint V ∈ U ∧ IsOpenImmersion j ∧ IsClosedImmersion i ∧
      IsProper (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ) ∧
      IsBirationalScheme (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ) ∧
      j ≫ i ≫ pullback.snd (projectiveSpaceToSpec k n) σ = U.ι ≫ v ∧
      (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ).base (j.base ⟨x, hx⟩) = v.base x ∧
      Set.range i.base = closure (Set.range (j ≫ i).base) := by
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hx, -⟩ :=
    (isBasis_affine_open V).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : V.Opens := U₀
  letI : IsAffine U.toScheme := hU
  letI : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  letI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hgeneric : genericPoint V ∈ U := genericPoint_mem_nonempty_open V U
  let w := U.ι ≫ v
  letI : LocallyOfFiniteType (w ≫ σ) := by
    dsimp only [w]
    rw [Category.assoc]
    infer_instance
  letI : GenericPointPreserving U.ι := ⟨genericPoint_eq_of_isOpenImmersion U.ι⟩
  letI : GenericPointPreserving v := ⟨hv.map_genericPoint⟩
  have hw : IsBirationalScheme w :=
    (BirationalComposition.isBirationalScheme_comp_iff U.ι v).mpr
      ⟨ImmersionBirational.isBirationalScheme_of_isOpenImmersion U.ι, hv⟩
  obtain ⟨n, Z, j, i, hZ, h⟩ := AffineBirationalProjectiveCompletion.exists_completion σ w hw
  letI := hZ
  obtain ⟨hj, hi, hp, hbir, hfac, hclosure⟩ := h
  have hpoint :
      (i ≫ pullback.snd (projectiveSpaceToSpec k n) σ).base (j.base ⟨x, hx⟩) = v.base x :=
    congrArg (fun f : U.toScheme ⟶ X => f.base ⟨x, hx⟩) hfac
  exact ⟨U, hU, hx, n, Z, j, i, hZ, hgeneric, hj, hi, hp, hbir, hfac, hpoint, hclosure⟩

end KltDP.Geometry.BirationalModelAffineNeighborhoodCompletion

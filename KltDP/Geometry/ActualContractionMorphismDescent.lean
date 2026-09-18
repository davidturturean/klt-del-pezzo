import KltDP.Geometry.SchemeMorphismDescent
import KltDP.Geometry.PointBlowupCenterIrreducible
import KltDP.Geometry.PointBlowupOffCenterInjective
import KltDP.Geometry.ProperBirationalStructureSheaf
import KltDP.Geometry.MinimalResolutionCount
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The original contraction's universal property, proved from its actual maps

The original center fiber is irreducible and proper. The original contracted
prime curve therefore fills that fiber, by the proved dimension-one maximality
lemma. The actual puncture isomorphism gives all remaining fibers at most one
point. Ordinary quotient-topology and sheaf descent now construct the unique
factorization, removing the old ContractionUniversalLiteral premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

variable {k : Type u} [Field k]

/-- The chosen original contracted prime is the entire original center
fiber, derived from actual point-blowup geometry and prime-curve maximality. -/
theorem IsContraction.centerFiber_eq_curve
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S T b E) :
    ∃ z : T.Point, IsClosed ({z} : Set T.toScheme) ∧
      b.base ⁻¹' {z} = (E : Set S.toScheme) ∧ IsPointBlowupAt S T b z := by
  obtain ⟨z, hzclosed, hEimage, hdim, hbl⟩ := hb.center
  have hirr := hbl.pointFiber_isIrreducible (hb.regular z) hdim
  let W : IrreducibleCloseds S.toScheme :=
    ⟨b.base ⁻¹' {z}, hirr, hzclosed.preimage b.continuous⟩
  have hEW : (E : Set S.toScheme) ⊆ W := by
    intro x hx
    have h := Set.mem_image_of_mem b.base hx
    rw [hEimage] at h
    exact h
  have hzgen : z ≠ genericPoint T.toScheme := by
    intro hz
    have h : ringKrullDim T.toScheme.functionField = 2 :=
      (congrArg (fun p : T.Point => ringKrullDim (T.toScheme.presheaf.stalk p))
        hz).symm.trans hdim
    rw [ringKrullDim_eq_zero_of_field] at h
    norm_num at h
  have hW : (W : Set S.toScheme) ≠ Set.univ := by
    intro hW
    have hg : b.base (genericPoint S.toScheme) = z := by
      have hmem : genericPoint S.toScheme ∈ (W : Set S.toScheme) := by
        rw [hW]
        trivial
      exact hmem
    exact hzgen (hg.symm.trans hb.birational.map_genericPoint)
  exact ⟨z, hzclosed, (E.coe_eq_of_subset_irreducibleCloseds W hEW hW).symm, hbl⟩

private theorem properBirational_surjective
    {S T : NormalProjectiveSurface k} (b : S.toScheme ⟶ T.toScheme)
    [IsProper b] (hbir : IsBirational b) : Surjective b := by
  constructor
  intro y
  have hgen : genericPoint T.toScheme ∈ Set.range b.base :=
    ⟨genericPoint S.toScheme, hbir.map_genericPoint⟩
  have hcl : closure ({genericPoint T.toScheme} : Set T.toScheme) ⊆ Set.range b.base :=
    closure_minimal (Set.singleton_subset_iff.mpr hgen) b.isClosedMap.isClosed_range
  have hclosure : closure ({genericPoint T.toScheme} : Set T.toScheme) = Set.univ :=
    genericPoint_spec T.toScheme
  rw [hclosure] at hcl
  exact hcl (Set.mem_univ y)

/-- Every original morphism contracting the original exceptional curve
factors uniquely through the actual contraction. No universal-property,
fiber, sheaf-map, or topology premise is supplied. -/
theorem IsContraction.existsUnique_factor
    {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
    {E : S.PrimeCurve} (hb : IsContraction S T b E)
    {Y : Scheme.{u}} (φ : S.toScheme ⟶ Y)
    (hφ : ∃ y : Y, φ.base '' (E : Set S.toScheme) = {y}) :
    ∃! φ' : T.toScheme ⟶ Y, b ≫ φ' = φ := by
  letI : IsProper b := hb.isProper
  letI : Surjective b := properBirational_surjective b hb.birational
  letI : IsIso b.c := ProperBirationalStructureSheaf.c_isIso b
    ((isBirational_iff_isBirationalScheme b).mp hb.birational) T.normal
  obtain ⟨z, -, hEfiber, hbl⟩ := hb.centerFiber_eq_curve
  obtain ⟨y, hy⟩ := hφ
  have hφpoint : ∀ x : S.Point, x ∈ (E : Set S.toScheme) → φ.base x = y := by
    intro x hx
    have h := Set.mem_image_of_mem φ.base hx
    rw [hy] at h
    exact h
  apply SchemeMorphismDescent.existsUnique_lift_of_proper b φ
  intro x x' hxx'
  by_cases hx : b.base x = z
  · have hx' : b.base x' = z := hxx'.symm.trans hx
    have hxE : x ∈ (E : Set S.toScheme) := by rw [← hEfiber]; exact hx
    have hxE' : x' ∈ (E : Set S.toScheme) := by rw [← hEfiber]; exact hx'
    exact (hφpoint x hxE).trans (hφpoint x' hxE').symm
  · have hx' : b.base x' ≠ z := by rwa [← hxx']
    exact congrArg φ.base (hbl.base_injOn_off_center hx hx' hxx')

/-- The old universal-property input is now an ordinary theorem about the
same original contraction objects. This admits no new literature axiom. -/
theorem contractionUniversal (k : Type u) [Field k] :
    KltDP.Literature.Stacks.ContractionUniversalLiteral k := by
  constructor
  intro S T b E hb Y φ hφ
  exact hb.existsUnique_factor φ hφ

end KltDP.Geometry

#print axioms KltDP.Geometry.IsContraction.existsUnique_factor
#print axioms KltDP.Geometry.contractionUniversal

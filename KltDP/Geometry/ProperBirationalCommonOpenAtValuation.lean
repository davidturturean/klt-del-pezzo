import KltDP.Geometry.ProperBirationalCodimensionOne
import KltDP.Geometry.SchemePullbackOverOpenIso

/-!
# An actual common open through a detected divisorial point

The original proper birational map is an isomorphism near the original
valuation stalk. Restrict the other original open chart to this locus and
take the actual fiber product. Its two projections give open immersions
through the original points and retain the original commutative square.
No alternate local-ring map or supplied common neighborhood is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace KltDP.Geometry
attribute [local instance] integralSchemeStalk_isDomain

theorem exists_common_open_at_valuation_point
    {S Z U : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (q : S ⟶ Z) [IsProper q] (hq : IsBirationalScheme q)
    (j : U ⟶ Z) [IsOpenImmersion j] (s : S) (y : U)
    [ValuationRing (Z.presheaf.stalk (j.base y))]
    (hpoint : q.base s = j.base y) :
    ∃ (W : Scheme.{u}) (iS : W ⟶ S) (iU : W ⟶ U) (w : W),
      IsOpenImmersion iS ∧ IsOpenImmersion iU ∧
      iS.base w = s ∧ iU.base w = y ∧ iS ≫ q = iU ≫ j := by
  obtain ⟨O, hyO, hqO⟩ :=
    ProperBirationalCodimensionOne.exists_isomorphism_open_at_valuation_stalk q hq (j.base y)
  letI : IsIso (q ∣_ O) := hqO
  let V : U.Opens := j ⁻¹ᵁ O
  let j' : V.toScheme ⟶ Z := V.ι ≫ j
  have hr : Set.range j'.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨j.base z.val, z.property⟩, rfl⟩
  letI : IsIso (pullback.snd q j') :=
    isIso_pullback_snd_of_range_subset q j' O hr
  let W : Scheme.{u} := pullback q j'
  let iS : W ⟶ S := pullback.fst q j'
  let iU : W ⟶ U := pullback.snd q j' ≫ V.ι
  have hcomm : iS ≫ q = iU ≫ j := by
    exact (pullback.condition (f := q) (g := j')).trans (Category.assoc _ _ _).symm
  have hs : s ∈ Set.range iS.base := by
    change s ∈ Set.range (pullback.fst q j').base
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    exact ⟨⟨y, hyO⟩, hpoint.symm⟩
  obtain ⟨w, hw⟩ := hs
  have hy : iU.base w = y := by
    apply j.isOpenEmbedding.injective
    calc
      j.base (iU.base w) = q.base (iS.base w) :=
        congrArg (fun a : W ⟶ Z => a.base w) hcomm.symm
      _ = j.base y := (congrArg q.base hw).trans hpoint
  exact ⟨W, iS, iU, w, inferInstance, inferInstance, hw, hy, hcomm⟩

end KltDP.Geometry

#check @KltDP.Geometry.exists_common_open_at_valuation_point
#print axioms KltDP.Geometry.exists_common_open_at_valuation_point

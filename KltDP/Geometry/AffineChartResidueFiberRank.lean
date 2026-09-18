import KltDP.Geometry.AffineFiberScalarRank
import KltDP.Geometry.FieldFiberIsoTransport
import KltDP.Compatibility.ClosedAlgebraResidue

/-!
At every actual maximal ideal of an original affine target chart,
the native residue tensor has dimension one when the original morphism
has point fibers over all original base-field sections. The field
identification is the proved canonical closed-residue-field equivalence.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

namespace KltDP.Geometry.AffineChartResidueFiberRank

theorem finrank_eq_one
    (k R A : Type u) [Field k] [IsAlgClosed k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.FiniteType k R] [Algebra R A]
    {X Y : Scheme.{u}} (σ : Y ⟶ Spec (CommRingCat.of k)) (π : X ⟶ Y)
    (a : Spec (CommRingCat.of A) ⟶ X) (c : Spec (CommRingCat.of R) ⟶ Y)
    (H : IsPullback a (Spec.map (CommRingCat.ofHom (algebraMap R A))) π c)
    (hc : c ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (hfib : ∀ i : Spec (CommRingCat.of k) ⟶ Y, i ≫ σ = 𝟙 _ →
      IsIso (pullback.snd π i))
    (p : Ideal R) [p.IsMaximal] :
    Module.finrank p.ResidueField (p.ResidueField ⊗[R] A) = 1 := by
  let χ : R →ₐ[k] k := KltDP.Compatibility.closedPointCharacter k p
  let q : Spec (CommRingCat.of k) ⟶ Y := Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ c
  have hχ : CommRingCat.ofHom (algebraMap k R) ≫
      CommRingCat.ofHom χ.toRingHom = 𝟙 (CommRingCat.of k) := by
    apply CommRingCat.hom_ext
    exact χ.comp_algebraMap
  have hq : q ≫ σ = 𝟙 _ := by
    dsimp only [q]
    rw [Category.assoc, hc, ← Spec.map_comp, hχ, Spec.map_id]
  let e : CommRingCat.of k ≅ CommRingCat.of p.ResidueField :=
    (KltDP.Compatibility.closedResidueFieldAlgEquiv k p).toRingEquiv.toCommRingCatIso
  let t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of p.ResidueField) := Spec.map e.inv
  let j : Spec (CommRingCat.of p.ResidueField) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)) ≫ c
  letI : IsIso t := by dsimp only [t]; infer_instance
  have htj : t ≫ j = q := by
    dsimp only [t, j, q]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  letI : IsIso (pullback.snd π (t ≫ j)) := by rw [htj]; exact hfib q hq
  letI : IsIso (pullback.snd π j) :=
    FieldFiberIsoTransport.isIso_snd_of_precomp_iso π j t
  letI : IsIso (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))) :=
    AffineFiberScalarRank.isIso_snd_of_chart_square a _ π c H _
  exact AffineFiberScalarRank.finrank_eq_one_of_isIso_snd R A p.ResidueField

#check KltDP.Geometry.AffineChartResidueFiberRank.finrank_eq_one
#print axioms KltDP.Geometry.AffineChartResidueFiberRank.finrank_eq_one

end KltDP.Geometry.AffineChartResidueFiberRank

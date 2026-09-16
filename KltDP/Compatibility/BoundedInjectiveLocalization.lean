import KltDP.Compatibility.BoundedInjectiveNullHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Derived localization into bounded-below complexes of injectives

The original homotopy-category localization induces a bijection on maps into
a bounded-below complex of injectives. The proof uses the actual acyclic-cone
triangles, their Yoneda exactness, and the pinned calculus of right fractions.
The preceding module constructs the required null homotopies. No localization
bijection or K-injectivity property is assumed.
-/

universe w v u

open CategoryTheory Category Limits Preadditive

namespace KltDP.BoundedInjectiveComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  (L : CochainComplex C ℤ) (d : ℤ)
  [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)]

include d in
/-- Maps from actual acyclic objects of the homotopy category vanish at the
given target, by the constructed null homotopy of a representative. -/
lemma hom_eq_zero_of_acyclic
    {K : HomotopyCategory C (ComplexShape.up ℤ)}
    (hK : (HomotopyCategory.subcategoryAcyclic C).P K)
    (f : K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :
    f = 0 := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨f, rfl⟩ :=
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
  have hK' : K.Acyclic :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt K).1 hK
  obtain ⟨h⟩ :=
    CochainComplex.nonempty_homotopy_zero_of_boundedBelow_injective L d f hK'
  simpa only [Functor.map_zero] using HomotopyCategory.eq_of_homotopy f 0 h

include d in
/-- Precomposition by an actual quasi-isomorphism is bijective on maps into
the target in the homotopy category. -/
lemma precomp_bijective
    {Y Z : HomotopyCategory C (ComplexShape.up ℤ)} (s : Y ⟶ Z)
    (hs : HomotopyCategory.quasiIso C (ComplexShape.up ℤ) s) :
    Function.Bijective
      (fun f : Z ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L => s ≫ f) := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W] at hs
  constructor
  · intro f g h
    change s ≫ f = s ≫ g at h
    obtain ⟨A, b, c, hT, hA⟩ := hs
    have hz : s ≫ (f - g) = 0 := by rw [comp_sub, h, sub_self]
    obtain ⟨a, ha⟩ := (Pretriangulated.Triangle.mk s b c).yoneda_exact₂ hT (f - g) hz
    have ha0 := hom_eq_zero_of_acyclic L d hA a
    apply sub_eq_zero.mp
    rw [ha, ha0, comp_zero]
  · intro f
    obtain ⟨A, a, b, hT, hA⟩ :=
      ((HomotopyCategory.subcategoryAcyclic C).W_iff' s).1 hs
    have hz : a ≫ f = 0 := hom_eq_zero_of_acyclic L d hA (a ≫ f)
    obtain ⟨g, hg⟩ := (Pretriangulated.Triangle.mk a s b).yoneda_exact₂ hT f hz
    exact ⟨g, hg.symm⟩

variable [HasDerivedCategory.{w} C]

include d in
/-- The actual localization map on hom sets is bijective at this target. -/
lemma Qh_map_bijective (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) → _) := by
  constructor
  · intro f g h
    obtain ⟨Y, s, hs, hfg⟩ :=
      (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f g).1 h
    exact (precomp_bijective L d s hs).1 hfg
  · intro f
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f
    obtain ⟨g, hg⟩ := (precomp_bijective L d φ.s φ.hs).2 φ.f
    change φ.s ≫ g = φ.f at hg
    refine ⟨g, ?_⟩
    letI : IsIso (DerivedCategory.Qh.map φ.s) :=
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) φ.s φ.hs
    apply (cancel_epi (DerivedCategory.Qh.map φ.s)).1
    rw [← Functor.map_comp, hg, hφ, φ.map_s_comp_map]

/-- The additive comparison retains the original localization map. -/
noncomputable def homAddEquiv (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) ≃+
      (DerivedCategory.Qh.obj K ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)) where
  toEquiv := Equiv.ofBijective DerivedCategory.Qh.map (Qh_map_bijective L d K)
  map_add' _ _ := DerivedCategory.Qh.map_add

lemma homAddEquiv_apply (K : HomotopyCategory C (ComplexShape.up ℤ))
    (f : K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :
    homAddEquiv L d K f = DerivedCategory.Qh.map f := rfl

/-- Naturality in the source uses the original homotopy-category morphism. -/
lemma homAddEquiv_precomp
    {K K' : HomotopyCategory C (ComplexShape.up ℤ)} (f : K' ⟶ K)
    (g : K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :
    homAddEquiv L d K' (f ≫ g) =
      DerivedCategory.Qh.map f ≫ homAddEquiv L d K g :=
  DerivedCategory.Qh.map_comp f g

/-- Naturality in the target uses the original map of cochain complexes. -/
lemma homAddEquiv_postcomp
    (L' : CochainComplex C ℤ) (d' : ℤ)
    [L'.IsStrictlyGE d'] [∀ (n : ℤ), Injective (L'.X n)]
    (f : L ⟶ L') (K : HomotopyCategory C (ComplexShape.up ℤ))
    (g : K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :
    homAddEquiv L' d' K
        (g ≫ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      homAddEquiv L d K g ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) :=
  DerivedCategory.Qh.map_comp g ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)

end KltDP.BoundedInjectiveComparison

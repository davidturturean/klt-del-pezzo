import KltDP.Geometry.AmpleOfAffineNonvanishingCover
import KltDP.Geometry.FiniteGlobalGenerationOfLocalExtensions

/-!
# Finite global free epimorphisms for high original twists

Retain the finite family of extended local affine generators through the
actual global gluing theorem. The result is a finite global generating
family for every sufficiently high original twist, including the literal
coherent sheaves and left tensor order in the existing Serre definition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AffineNonvanishingCoverFiniteGeneration

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- Use the explicit pinned dictionaries already compiled for these same
-- original Over sites in CoherentQuasicoherent and FiniteLocallyFreeCoherent.
local instance schemeOverHasWeakSheafify (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrp.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology X).over U) AddCommGrp.{u}).isRightAdjoint

local instance schemeOverWEqualsLocallyBijective (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrp.{u} := by
  let J := (Opens.grothendieckTopology X).over U
  letI : J.PreservesSheafification (forget AddCommGrp.{u}) :=
    GrothendieckTopology.instPreservesSheafification J (forget AddCommGrp.{u})
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallyInjective_toSheafify' J P
  letI (P : (Over U)ᵒᵖ ⥤ AddCommGrp.{u}) :
      Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
    Presheaf.isLocallySurjective_toSheafify' J P
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrp.{u}

local instance finiteTwistMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance finiteTwistSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSectionNonvanishingOpen AmpleOfAffineNonvanishingCover

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

-- Keep the finite maximum and the resulting finite family abstract in
-- the original local generators, before the affine finite-type choice.
private theorem eventually_exists_finite_generatingSections_of_generators (M : X.Modules)
    [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i))
    (G : ∀ i, (M.over (nonvanishingOpen X L (s i))).GeneratingSections)
    (hG : ∀ i, Finite (G i).I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ H : (M ⊗ (power L n).obj).GeneratingSections, Finite H.I := by
  classical
  let D (i : I) := nonvanishingOpen X L (s i)
  letI (i : I) : Finite (G i).I := hG i
  let J := Σ i : I, (G i).I
  letI : Fintype J := Fintype.ofFinite J
  have hext (j : J) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ t : (M ⊗ (power L n).obj).val.obj (op (⊤ : X.Opens)),
        (M ⊗ (power L n).obj).val.map
            (homOfLE (show D j.1 ≤ ⊤ from le_top)).op t =
          (rightTwistMap M L (s j.1) n).val.app (op (D j.1))
            (((G j.1).s j.2).val (op (Over.mk (𝟙 (D j.1))))) :=
    InvertibleSheafSectionExtension.eventually_exists_twisted_extension L M (s j.1)
      hX hXqs (((G j.1).s j.2).val (op (Over.mk (𝟙 (D j.1)))))
  choose N hN using hext
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  let T := M ⊗ (power L n).obj
  letI (i : I) : Epi ((_root_.SheafOfModules.overFunctor X.ringCatSheaf (D i)).map
      (rightTwistMap M L (s i) n)) := rightTwistMap_over_epi L M (s i) n le_rfl
  let G' (i : I) : (T.over (D i)).GeneratingSections :=
    (G i).ofEpi ((_root_.SheafOfModules.overFunctor X.ringCatSheaf (D i)).map
      (rightTwistMap M L (s i) n))
  apply FiniteGlobalGenerationOfLocalExtensions.exists_finite_generatingSections
    T D hcover G' (fun i => inferInstanceAs (Finite (G i).I))
  intro i k
  exact hN ⟨i, k⟩ n ((Finset.le_sup (f := N) (Finset.mem_univ ⟨i, k⟩)).trans hn)

/-- An actual finite affine nonvanishing cover gives finite global
generators for every sufficiently high original right twist. -/
theorem eventually_exists_finite_generatingSections_right (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ G : (M ⊗ (power L n).obj).GeneratingSections, Finite G.I := by
  classical
  have hG : ∀ i, ∃ G : (M.over (nonvanishingOpen X L (s i))).GeneratingSections,
      Finite G.I := fun i => AffineFiniteTypeGenerators.exists_over M (ha i)
  choose G hG using hG
  exact eventually_exists_finite_generatingSections_of_generators L M hX hXqs s hcover G hG

/-- Literal coherent sheaves have finite global generating families in
the original left-twist order for every sufficiently high degree. -/
theorem eventually_exists_finite_generatingSections_coherent (M : X.Modules)
    [IsCoherentModule M]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ G : ((power L n).obj ⊗ M).GeneratingSections, Finite G.I := by
  letI : M.IsQuasicoherent :=
    CoherentQuasicoherent.isQuasicoherent_of_isCoherentModule M
  obtain ⟨N, hN⟩ := eventually_exists_finite_generatingSections_right
    L M hX hXqs s ha hcover
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  letI : Finite G.I := hG
  exact ⟨G.ofEpi (β_ M (power L n).obj).hom, inferInstanceAs (Finite G.I)⟩

end KltDP.Geometry.AffineNonvanishingCoverFiniteGeneration

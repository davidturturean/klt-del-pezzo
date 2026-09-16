import KltDP.Geometry.AffineFiniteTypeGenerators
import KltDP.Geometry.GlobalGenerationOfLocalExtensions
import KltDP.Geometry.InvertibleSheafOriginalTwistNonvanishing
import KltDP.Geometry.InvertibleSheafCoherentSectionExtension

/-!
# Serre ampleness from an actual affine nonvanishing-section cover

Original sections of an invertible sheaf whose intrinsic nonvanishing
opens are affine and cover a QCQS scheme make that same sheaf ample in
the existing Serre sense. Finite affine generators, extension thresholds,
the common exponent, and the final global free epimorphism are derived.

This criterion takes sections of the original sheaf itself. It neither
assumes a globally generating twisted sheaf nor produces the initial
affine nonvanishing cover from a projective embedding.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.AmpleOfAffineNonvanishingCover

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

local instance affineCoverMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance affineCoverSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

open InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSectionNonvanishingOpen

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- The actual twist map is an epimorphism on the original Over site of
each subopen of the original nonvanishing open. -/
theorem rightTwistMap_over_epi (M : X.Modules) (s : L.obj.sections) (n : ℕ)
    {U : X.Opens} (hUD : U ≤ nonvanishingOpen X L s) :
    Epi ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map
      (rightTwistMap M L s n)) where
  left_cancellation {N} a b hab := by
    ext V t
    obtain ⟨v, hv⟩ :=
      (InvertibleSheafOriginalTwistNonvanishing.rightTwistMap_app_bijective
        L M s n (V.unop.hom.le.trans hUD)).surjective t
    have h := congrArg (fun q => q.val.app V v) hab
    change a.val.app V ((rightTwistMap M L s n).val.app (op V.unop.left) v) =
      b.val.app V ((rightTwistMap M L s n).val.app (op V.unop.left) v) at h
    rw [← hv]
    exact h

-- Check the finite maximum and gluing with the original local generating
-- families abstract, before selecting them from affine finite type.
private theorem eventually_isGloballyGenerated_of_generators (M : X.Modules)
    [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i))
    (G : ∀ i, (M.over (nonvanishingOpen X L (s i))).GeneratingSections)
    (hG : ∀ i, Finite (G i).I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Positivity.IsGloballyGenerated (M ⊗ (power L n).obj) := by
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
  apply GlobalGenerationOfLocalExtensions.isGloballyGenerated T D hcover G'
  intro i k
  exact hN ⟨i, k⟩ n ((Finset.le_sup (f := N) (Finset.mem_univ ⟨i, k⟩)).trans hn)

/-- A finite actual affine nonvanishing cover eventually generates every
original right twist of a finite-type quasicoherent module. -/
theorem eventually_isGloballyGenerated_right (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Positivity.IsGloballyGenerated (M ⊗ (power L n).obj) := by
  classical
  have hG : ∀ i, ∃ G : (M.over (nonvanishingOpen X L (s i))).GeneratingSections,
      Finite G.I := fun i => AffineFiniteTypeGenerators.exists_over M (ha i)
  choose G hG using hG
  exact eventually_isGloballyGenerated_of_generators L M hX hXqs s hcover G hG

/-- A finite affine cover by intrinsic nonvanishing opens of actual
sections proves the existing Serre ampleness of the original line sheaf. -/
theorem isAmple_of_finite_cover
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} [Finite I] (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    AmpleSerre.IsAmple L := by
  intro M hM
  letI : IsCoherentModule M := hM
  letI : M.IsQuasicoherent :=
    CoherentQuasicoherent.isQuasicoherent_of_isCoherentModule M
  obtain ⟨N, hN⟩ := eventually_isGloballyGenerated_right L M hX hXqs s ha hcover
  refine ⟨N, fun n hn => ⟨power L n, power_toPic L n, ?_⟩⟩
  exact AmpleSerre.isGloballyGenerated_of_iso (β_ M (power L n).obj) (hN n hn)

/-- Compactness selects the finite subcover, so no finite indexing family
is an input to the affine nonvanishing-section ampleness criterion. -/
theorem isAmple_of_cover
    (hX : IsCompact (Set.univ : Set X))
    (hXqs : IsQuasiSeparated (Set.univ : Set X))
    {I : Type u} (s : I → L.obj.sections)
    (ha : ∀ i, IsAffineOpen (nonvanishingOpen X L (s i)))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, nonvanishingOpen X L (s i)) :
    AmpleSerre.IsAmple L := by
  classical
  let D (i : I) := nonvanishingOpen X L (s i)
  have hc : (Set.univ : Set X) ⊆ ⋃ i, (D i : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp (hcover hx))
  obtain ⟨S, hS⟩ := hX.elim_finite_subcover (fun i => (D i : Set X))
    (fun i => (D i).isOpen) hc
  apply isAmple_of_finite_cover L hX hXqs (fun i : S => s i.1) (fun i => ha i.1)
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS hx)
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨⟨i, hiS⟩, hxi⟩

end KltDP.Geometry.AmpleOfAffineNonvanishingCover

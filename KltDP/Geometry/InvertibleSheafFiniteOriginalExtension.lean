import KltDP.Geometry.InvertibleSheafFiniteAffineExtension
import KltDP.Geometry.InvertibleSheafOpenTwistSections

/-!
# Finite affine twisted lifts in the original ambient sheaf

Return the constructed affine chart lifts to the original ambient tensor
sheaf using the actual open-pullback section equivalence. On the original
intersection with the nonvanishing open, their restrictions are the original
power-section map applied to the original restricted input section.

All finite covers, common exponents and original chart sections are derived.
The eventual agreement on chart overlaps and global gluing remain open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.InvertibleSheafFiniteOriginalExtension

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance finiteOriginalExtensionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

open InvertibleSectionNonvanishingOpen InvertibleSheafSectionPowers InvertibleSheafTwistFrame
open InvertibleSheafFiniteAffineExtension SchemeModuleOpenPullbackSections
open InvertibleSheafOpenTwistSections

variable {X : Scheme.{u}} (L : InvertibleSheaf X) (M : X.Modules) (s : L.obj.sections)

private theorem imagePreimageNonvanishing (a : Chart L) :
    (chartOpen L a).ι ''ᵁ ((chartOpen L a).ι ⁻¹ᵁ nonvanishingOpen X L s) =
      chartOpen L a ⊓ nonvanishingOpen X L s := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]

private theorem imageBasicNonvanishing (a : Chart L) :
    (chartOpen L a).ι ''ᵁ
        (chartOpen L a).toScheme.basicOpen
          (InvertibleSheafFiniteAffineExtension.chartCoefficient L s a) =
      chartOpen L a ⊓ nonvanishingOpen X L s :=
  (congrArg (fun V => (chartOpen L a).ι ''ᵁ V) (chartBasicOpen_eq L s a)).trans
    (imagePreimageNonvanishing L s a)

private theorem localSection_equiv
    (t : M.val.obj (op (nonvanishingOpen X L s))) (a : Chart L) :
    sectionsEquiv (chartOpen L a).ι M
        ((chartOpen L a).toScheme.basicOpen
          (InvertibleSheafFiniteAffineExtension.chartCoefficient L s a))
        (chartOpen L a ⊓ nonvanishingOpen X L s) (imageBasicNonvanishing L s a)
        (localSection L M s t a) =
      M.val.map (homOfLE (show chartOpen L a ⊓ nonvanishingOpen X L s ≤
        nonvanishingOpen X L s from inf_le_right)).op t := by
  let η := chartBasicOpen_eq L s a
  have hm : homOfLE η.le = eqToHom η := Subsingleton.elim _ _
  have hn := sectionsEquiv_naturality (chartOpen L a).ι M
    (imagePreimageNonvanishing L s a) (imageBasicNonvanishing L s a) η.le le_rfl
    (pullbackSection (chartOpen L a).ι M (nonvanishingOpen X L s) t)
  rw [hm] at hn
  have hs := sectionsEquiv_pulledSection (chartOpen L a).ι M
    (nonvanishingOpen X L s) (chartOpen L a ⊓ nonvanishingOpen X L s)
    (imagePreimageNonvanishing L s a) inf_le_right t
  rw [hs] at hn
  exact hn.trans (by
    change M.val.presheaf.map (𝟙 (op (chartOpen L a ⊓ nonvanishingOpen X L s)))
      (M.val.map (homOfLE (show chartOpen L a ⊓ nonvanishingOpen X L s ≤
        nonvanishingOpen X L s from inf_le_right)).op t) = _
    rw [CategoryTheory.Functor.map_id]
    rfl)

/-- A common threshold gives actual original twisted sections on a finite
affine cover, with their required original restrictions on the nonvanishing open. -/
theorem eventually_exists_original_lifts [M.IsQuasicoherent]
    (hX : IsCompact (Set.univ : Set X))
    (t : M.val.obj (op (nonvanishingOpen X L s))) :
    ∃ S : Finset (Chart L), (⨆ a : S, chartOpen L a.val) = ⊤ ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : S,
        ∃ v : (M ⊗ (power L n).obj).val.obj (op (chartOpen L a.val)),
          (M ⊗ (power L n).obj).val.map
              (homOfLE (show chartOpen L a.val ⊓ nonvanishingOpen X L s ≤
                chartOpen L a.val from inf_le_left)).op v =
            (rightTwistMap M L s n).val.app (op (chartOpen L a.val ⊓ nonvanishingOpen X L s))
              (M.val.map (homOfLE (show chartOpen L a.val ⊓ nonvanishingOpen X L s ≤
                nonvanishingOpen X L s from inf_le_right)).op t) := by
  obtain ⟨S, hS, N, hN⟩ := eventually_exists_on_finite_affine_cover L M hX s t
  refine ⟨S, hS, N, fun n hn a => ?_⟩
  obtain ⟨v, hv⟩ := hN n hn a
  let f := (chartOpen L a.val).ι
  let D := nonvanishingOpen X L s
  let V := (chartOpen L a.val).toScheme.basicOpen
    (InvertibleSheafFiniteAffineExtension.chartCoefficient L s a.val)
  let eTop := twistSectionsEquiv f M L n ⊤ (chartOpen L a.val) (chartOpen L a.val).ι_image_top
  let eD := twistSectionsEquiv f M L n V (chartOpen L a.val ⊓ D)
    (imageBasicNonvanishing L s a.val)
  refine ⟨eTop v, ?_⟩
  calc
    _ = eD (((schemeModulePullback f).obj M ⊗
        (power (pullbackInvertibleSheaf f L) n).obj).val.map
          (homOfLE (show V ≤ ⊤ from le_top)).op v) :=
      (twistSectionsEquiv_naturality f M L n (chartOpen L a.val).ι_image_top
        (imageBasicNonvanishing L s a.val) le_top inf_le_left v).symm
    _ = eD ((rightTwistMap (chartModule L M a.val) (chartLine L a.val)
        (chartSection L s a.val) n).val.app (op V) (localSection L M s t a.val)) :=
      congrArg eD hv
    _ = (rightTwistMap M L s n).val.app (op (chartOpen L a.val ⊓ D))
        (sectionsEquiv f M V (chartOpen L a.val ⊓ D)
          (imageBasicNonvanishing L s a.val) (localSection L M s t a.val)) :=
      twistSectionsEquiv_rightTwistMap f M L s n V (chartOpen L a.val ⊓ D)
        (imageBasicNonvanishing L s a.val) (localSection L M s t a.val)
    _ = _ := congrArg ((rightTwistMap M L s n).val.app (op (chartOpen L a.val ⊓ D)))
      (localSection_equiv L M s t a.val)

end KltDP.Geometry.InvertibleSheafFiniteOriginalExtension

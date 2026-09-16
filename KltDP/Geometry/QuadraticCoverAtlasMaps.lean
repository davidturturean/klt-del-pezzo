import KltDP.Geometry.QuadraticCoverMappedRescaling
import KltDP.Geometry.QuadraticTransitionCocycle

/-!
# Actual maps between quadratic charts on an open atlas

Every map below is induced by an original structure-sheaf restriction and
an original transition unit. The coefficient, root, composition, identity,
open-immersion and range laws are derived. The maps may use different chart
indices and different actual opens; this handles permutations of pair and
triple intersections without identifying their section rings by assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.QuadraticCoverAtlas

open TransitionUnitGluing QuadraticCover QuadraticTransitionCocycle QuadraticCoverOpen

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (g : ∀ i j, Γ(X, U i ⊓ U j)ˣ) (s : ∀ i, Γ(X, U i))
    (hs : ∀ i j,
      res X (inf_le_left : U i ⊓ U j ≤ U i) (s i) =
        (g i j : Γ(X, U i ⊓ U j)) ^ 2 *
          res X (inf_le_right : U i ⊓ U j ≤ U j) (s j))

/-- The actual quadratic chart belonging to frame `i` on an actual smaller open. -/
abbrev localChart (i : ι) {W : X.Opens} (hi : W ≤ U i) : Scheme.{u} :=
  affineScheme (res X hi (s i))

/-- A coefficient restriction and the original transition unit define this
actual scheme map, with contravariant chart orientation. -/
def localMap {i j : ι} {V W : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V) :
    localChart X U s j hj ⟶ localChart X U s i hi :=
  mappedRescaleMap (res X hWV) (res X hi (s i)) (res X hj (s j))
    (restrictedUnit X U g (hWV.trans hi) hj)
    (by simpa only [res_res] using
      branchCondition_of_le X U g s hs (hWV.trans hi) hj)

/-- Restricting the transition on the first leg and multiplying by the second
transition gives the original direct transition on the final actual open. -/
theorem localMap_transition_mul (hc : IsCocycle X U g)
    {i j k : ι} {V W Z : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hk : Z ≤ U k)
    (hWV : W ≤ V) (hZW : Z ≤ W) :
    Units.map (res X hZW).toMonoidHom (restrictedUnit X U g (hWV.trans hi) hj) *
        restrictedUnit X U g (hZW.trans hj) hk =
      restrictedUnit X U g ((hZW.trans hWV).trans hi) hk := by
  apply Units.ext
  change res X hZW (res X (le_inf (hWV.trans hi) hj) (g i j)) *
      res X (le_inf (hZW.trans hj) hk) (g j k) =
    res X (le_inf ((hZW.trans hWV).trans hi) hk) (g i k)
  rw [res_res]
  exact IsCocycle.mul_res_of_le X U g hc
    (le_inf (le_inf ((hZW.trans hWV).trans hi) (hZW.trans hj)) hk)

/-- The cocycle of original units proves composition of the actual scheme maps. -/
@[reassoc]
theorem localMap_comp (hc : IsCocycle X U g)
    {i j k : ι} {V W Z : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hk : Z ≤ U k)
    (hWV : W ≤ V) (hZW : Z ≤ W) :
    localMap X U g s hs hj hk hZW ≫ localMap X U g s hs hi hj hWV =
      localMap X U g s hs hi hk (hZW.trans hWV) := by
  have hres : (res X hZW).comp (res X hWV) = res X (hZW.trans hWV) := by
    ext a
    exact res_res X hZW hWV a
  simp only [localMap]
  rw [mappedRescaleMap_comp]
  simp only [hres, localMap_transition_mul X U g hc hi hj hk hWV hZW]

/-- The actual self-transition is the identity scheme map. -/
@[simp]
theorem localMap_self (hc : IsCocycle X U g) {i : ι} {W : X.Opens}
    (hi : W ≤ U i) (hWW : W ≤ W) :
    localMap X U g s hs hi hi hWW = 𝟙 (localChart X U s i hi) := by
  have hres : res X hWW = RingHom.id Γ(X, W) := by
    ext a
    exact res_self X W a
  simp only [localMap, restrictedUnit_self X U g hc, hres, mappedRescaleMap_id]

/-- Equal actual opens give an actual isomorphism between their two frame charts;
both directions are constructed from original restriction and unit data. -/
def localIso (hc : IsCocycle X U g) {i j : ι} {V W : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V) (hVW : V ≤ W) :
    localChart X U s j hj ≅ localChart X U s i hi where
  hom := localMap X U g s hs hi hj hWV
  inv := localMap X U g s hs hj hi hVW
  hom_inv_id := by rw [localMap_comp X U g s hs hc, localMap_self X U g s hs hc]
  inv_hom_id := by rw [localMap_comp X U g s hs hc, localMap_self X U g s hs hc]

/-- The original base structural maps are preserved by every actual atlas map. -/
@[reassoc]
theorem localMap_toBase {i j : ι} {V W : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    localMap X U g s hs hi hj hWV ≫ toBase (res X hi (s i)) ≫ hV.fromSpec =
      toBase (res X hj (s j)) ≫ hW.fromSpec := by
  rw [localMap, ← Category.assoc, mappedRescaleMap_toBase, Category.assoc]
  have hspec : Spec.map (CommRingCat.ofHom (res X hWV)) ≫ hV.fromSpec =
      hW.fromSpec := hV.map_fromSpec hW (homOfLE hWV).op
  rw [hspec]

/-- Actual affine-open restrictions and unit changes give actual chart open immersions. -/
theorem localMap_isOpenImmersion {i j : ι} {V W : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    IsOpenImmersion (localMap X U g s hs hi hj hWV) := by
  letI := restrictionSpec_isOpenImmersion X hWV hV hW
  exact mappedRescaleMap_isOpenImmersion _ _ _ _ _

/-- The actual range is the inverse image of the smaller base open; it is
independent of which frame is used on that smaller open. -/
theorem range_localMap {i j : ι} {V W : X.Opens}
    (hi : V ≤ U i) (hj : W ≤ U j) (hWV : W ≤ V)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    Set.range (localMap X U g s hs hi hj hWV).base =
      (toBase (res X hi (s i)) ≫ hV.fromSpec).base ⁻¹' (W : Set X) := by
  have hspec : Set.range (Spec.map (CommRingCat.ofHom (res X hWV))).base =
      hV.fromSpec.base ⁻¹' (W : Set X) := by
    have hcomp : Spec.map (CommRingCat.ofHom (res X hWV)) ≫ hV.fromSpec =
        hW.fromSpec := hV.map_fromSpec hW (homOfLE hWV).op
    rw [← IsAffineOpen.range_fromSpec hW, ← hcomp, Scheme.comp_base,
      TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ hV.fromSpec.isOpenEmbedding.injective]
  rw [localMap, range_mappedRescaleMap, hspec]
  rfl

end KltDP.Geometry.QuadraticCoverAtlas

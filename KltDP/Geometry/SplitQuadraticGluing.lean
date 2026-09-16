import KltDP.Geometry.SplitQuadraticNaturality
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing compatible affine quadratic splittings

The source is an actual scheme covered by open immersions from the quadratic
quotients used in `SplitQuadraticCover`. Given compatibility on the actual
chart intersections, the local splittings glue to an isomorphism with two
copies of the base scheme. Both global morphisms and their restrictions are
retained.

The restriction lemmas express the compatibility equations for coefficient
restriction maps preserving the chosen square roots. Existence of such roots,
the actual cover atlas, and identifications of chart intersections are not
asserted here. In particular this file does not assert that a cover of an
arbitrary curve or tree splits.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace KltDP.Geometry.SplitQuadraticGluing

/-- Pinned gluing extensionality uses a cover indexed in the scheme universe.
Selecting the already supplied chart at each point gives such a subcover,
without restricting the universe of the original actual open cover. -/
private theorem hom_ext_of_openCover {Z T : Scheme.{u}} (𝒲 : Scheme.OpenCover.{v} Z)
    (f g : Z ⟶ T) (h : ∀ i, 𝒲.map i ≫ f = 𝒲.map i ≫ g) : f = g := by
  let 𝒱 : Scheme.OpenCover.{u} Z :=
    { J := Z
      obj := fun z => 𝒲.obj (𝒲.f z)
      map := fun z => 𝒲.map (𝒲.f z)
      f := id
      covers := 𝒲.covers
      map_prop := fun z => 𝒲.map_prop (𝒲.f z) }
  exact 𝒱.hom_ext f g (fun z => h (𝒲.f z))

variable {X Y : Scheme.{u}} (𝒰 : X.AffineOpenCover)
    (a : ∀ i : 𝒰.J, (𝒰.obj i)ˣ)
    (h2 : ∀ i : 𝒰.J, IsUnit (2 : 𝒰.obj i))

/-- The actual affine quadratic chart over a member of the base cover. -/
abbrev chart (i : 𝒰.J) : Scheme.{u} :=
  Spec (.of (SplitQuadraticAlgebra (a i)))

variable (q : ∀ i : 𝒰.J, chart 𝒰 a i ⟶ Y)

/-- The positive evaluation, followed by the actual chart immersion. -/
def positive (i : 𝒰.J) : Spec (𝒰.obj i) ⟶ Y :=
  coprod.inl ≫ (splitQuadraticSpecIso (a i) (h2 i)).inv ≫ q i

/-- The negative evaluation, followed by the actual chart immersion. -/
def negative (i : 𝒰.J) : Spec (𝒰.obj i) ⟶ Y :=
  coprod.inr ≫ (splitQuadraticSpecIso (a i) (h2 i)).inv ≫ q i

/-- The local splitting followed by the two base-chart inclusions. -/
def toCoprod (i : 𝒰.J) : chart 𝒰 a i ⟶ X ⨿ X :=
  (splitQuadraticSpecIso (a i) (h2 i)).hom ≫ coprod.map (𝒰.map i) (𝒰.map i)

variable [∀ i, IsOpenImmersion (q i)]
    (covers : ∀ y : Y, ∃ i z, (q i).base z = y)

/-- The open cover of the actual source scheme furnished by its quadratic charts. -/
def chartCover : Y.OpenCover :=
  Scheme.Cover.mkOfCovers 𝒰.J (chart 𝒰 a) q covers

variable
    (hpositive : ∀ i j,
      pullback.fst (𝒰.map i) (𝒰.map j) ≫ positive 𝒰 a h2 q i =
      pullback.snd _ _ ≫ positive 𝒰 a h2 q j)
    (hnegative : ∀ i j,
      pullback.fst (𝒰.map i) (𝒰.map j) ≫ negative 𝒰 a h2 q i =
      pullback.snd _ _ ≫ negative 𝒰 a h2 q j)
    (hforward : ∀ i j,
      pullback.fst (q i) (q j) ≫ toCoprod 𝒰 a h2 i =
      pullback.snd _ _ ≫ toCoprod 𝒰 a h2 j)

/-- Compatible splittings of actual quadratic charts descend to an isomorphism.
The three compatibility hypotheses are equalities on the actual intersections,
not an assertion that the global cover is already split. -/
def glueIso : Y ≅ X ⨿ X := by
  let 𝒱 := chartCover 𝒰 a q covers
  let F : Y ⟶ X ⨿ X := 𝒱.glueMorphisms (toCoprod 𝒰 a h2) hforward
  let Gp : X ⟶ Y := 𝒰.openCover.glueMorphisms (positive 𝒰 a h2 q) hpositive
  let Gm : X ⟶ Y := 𝒰.openCover.glueMorphisms (negative 𝒰 a h2 q) hnegative
  have hF (i : 𝒰.J) : q i ≫ F = toCoprod 𝒰 a h2 i :=
    𝒱.ι_glueMorphisms _ _ i
  have hGp (i : 𝒰.J) : 𝒰.map i ≫ Gp = positive 𝒰 a h2 q i :=
    𝒰.openCover.ι_glueMorphisms _ _ i
  have hGm (i : 𝒰.J) : 𝒰.map i ≫ Gm = negative 𝒰 a h2 q i :=
    𝒰.openCover.ι_glueMorphisms _ _ i
  refine
    { hom := F
      inv := coprod.desc Gp Gm
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply 𝒱.hom_ext
    intro i
    change q i ≫ (F ≫ coprod.desc Gp Gm) = q i ≫ 𝟙 Y
    rw [← Category.assoc, hF]
    have hd : coprod.desc (positive 𝒰 a h2 q i) (negative 𝒰 a h2 q i) =
        (splitQuadraticSpecIso (a i) (h2 i)).inv ≫ q i := by
      apply coprod.hom_ext <;> simp [positive, negative]
    simp only [toCoprod, Category.assoc, coprod.map_desc, hGp, hGm, hd,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · apply coprod.hom_ext
    · apply 𝒰.openCover.hom_ext
      intro i
      change 𝒰.map i ≫ (coprod.inl ≫ (coprod.desc Gp Gm ≫ F)) =
        𝒰.map i ≫ (coprod.inl ≫ 𝟙 (X ⨿ X))
      simp only [coprod.inl_desc_assoc, Category.comp_id]
      rw [← Category.assoc, hGp]
      simp only [positive, Category.assoc, hF, toCoprod,
        Iso.inv_hom_id_assoc, coprod.inl_map]
    · apply 𝒰.openCover.hom_ext
      intro i
      change 𝒰.map i ≫ (coprod.inr ≫ (coprod.desc Gp Gm ≫ F)) =
        𝒰.map i ≫ (coprod.inr ≫ 𝟙 (X ⨿ X))
      simp only [coprod.inr_desc_assoc, Category.comp_id]
      rw [← Category.assoc, hGm]
      simp only [negative, Category.assoc, hF, toCoprod,
        Iso.inv_hom_id_assoc, coprod.inr_map]

@[simp, reassoc]
theorem chart_glueIso_hom (i : 𝒰.J) :
    q i ≫ (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).hom =
      toCoprod 𝒰 a h2 i :=
  (chartCover 𝒰 a q covers).ι_glueMorphisms (toCoprod 𝒰 a h2) hforward i

@[simp, reassoc]
theorem base_inl_glueIso_inv (i : 𝒰.J) :
    𝒰.map i ≫ coprod.inl ≫
        (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).inv =
      positive 𝒰 a h2 q i := by
  change 𝒰.map i ≫ coprod.inl ≫ coprod.desc
      (𝒰.openCover.glueMorphisms _ hpositive)
      (𝒰.openCover.glueMorphisms _ hnegative) = _
  rw [coprod.inl_desc]
  exact 𝒰.openCover.ι_glueMorphisms (positive 𝒰 a h2 q) hpositive i

@[simp, reassoc]
theorem base_inr_glueIso_inv (i : 𝒰.J) :
    𝒰.map i ≫ coprod.inr ≫
        (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).inv =
      negative 𝒰 a h2 q i := by
  change 𝒰.map i ≫ coprod.inr ≫ coprod.desc
      (𝒰.openCover.glueMorphisms _ hpositive)
      (𝒰.openCover.glueMorphisms _ hnegative) = _
  rw [coprod.inr_desc]
  exact 𝒰.openCover.ι_glueMorphisms (negative 𝒰 a h2 q) hnegative i

/-- A supplied structural morphism is preserved once its actual chart squares
commute with the fold map to the base. -/
theorem glueIso_hom_comp_fold (p : Y ⟶ X)
    (hp : ∀ i, q i ≫ p = toCoprod 𝒰 a h2 i ≫ coprod.desc (𝟙 X) (𝟙 X)) :
    (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).hom ≫
        coprod.desc (𝟙 X) (𝟙 X) = p := by
  apply (chartCover 𝒰 a q covers).hom_ext
  intro i
  change q i ≫ (_ ≫ _) = q i ≫ p
  rw [← Category.assoc, chart_glueIso_hom]
  exact (hp i).symm

/-- The inverse global splitting also preserves the supplied structural map. -/
theorem glueIso_inv_comp (p : Y ⟶ X)
    (hp : ∀ i, q i ≫ p = toCoprod 𝒰 a h2 i ≫ coprod.desc (𝟙 X) (𝟙 X)) :
    (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).inv ≫ p =
      coprod.desc (𝟙 X) (𝟙 X) := by
  apply (cancel_epi
    (glueIso 𝒰 a h2 q covers hpositive hnegative hforward).hom).mp
  simpa only [Iso.hom_inv_id_assoc] using
    (glueIso_hom_comp_fold 𝒰 a h2 q covers hpositive hnegative hforward p hp).symm

end KltDP.Geometry.SplitQuadraticGluing

namespace KltDP.Geometry

variable {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Rˣ) (b : Sˣ) (hab : f (a : R) = (b : S))
    (hR : IsUnit (2 : R)) (hS : IsUnit (2 : S))

/-- The forward splitting square obtained from the frozen inverse square. -/
theorem splitQuadraticSpecIso_hom_naturality :
    Spec.map (CommRingCat.ofHom (splitQuadraticMap f a b hab)) ≫
        (splitQuadraticSpecIso a hR).hom =
      (splitQuadraticSpecIso b hS).hom ≫
        coprod.map (Spec.map (CommRingCat.ofHom f))
          (Spec.map (CommRingCat.ofHom f)) := by
  have h := congrArg
    (fun k => (splitQuadraticSpecIso b hS).hom ≫ k ≫
      (splitQuadraticSpecIso a hR).hom)
    (splitQuadraticSpecIso_naturality f a b hab hR hS)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h

/-- The forward chart maps agree after an actual base-chart restriction. -/
theorem splitQuadraticToCoprod_restriction {X : Scheme.{u}}
    (xR : Spec (.of R) ⟶ X) (xS : Spec (.of S) ⟶ X)
    (hx : Spec.map (CommRingCat.ofHom f) ≫ xR = xS) :
    Spec.map (CommRingCat.ofHom (splitQuadraticMap f a b hab)) ≫
        (splitQuadraticSpecIso a hR).hom ≫ coprod.map xR xR =
      (splitQuadraticSpecIso b hS).hom ≫ coprod.map xS xS := by
  rw [← Category.assoc, splitQuadraticSpecIso_hom_naturality f a b hab hR hS]
  simp only [Category.assoc, coprod.map_map, hx]

variable {Y : Scheme.{u}}
    (qR : Spec (.of (SplitQuadraticAlgebra a)) ⟶ Y)
    (qS : Spec (.of (SplitQuadraticAlgebra b)) ⟶ Y)
    (hq : Spec.map (CommRingCat.ofHom (splitQuadraticMap f a b hab)) ≫ qR = qS)

include hab hq in
/-- A root-preserving coefficient restriction makes the positive local maps agree. -/
theorem splitQuadraticPositive_restriction :
    Spec.map (CommRingCat.ofHom f) ≫ coprod.inl ≫
        (splitQuadraticSpecIso a hR).inv ≫ qR =
      coprod.inl ≫ (splitQuadraticSpecIso b hS).inv ≫ qS := by
  have h := congrArg
    (fun k => (coprod.inl : Spec (.of S) ⟶ Spec (.of S) ⨿ Spec (.of S)) ≫ k ≫ qR)
    (splitQuadraticSpecIso_naturality f a b hab hR hS).symm
  simpa only [Category.assoc, coprod.inl_map_assoc, hq] using h

include hab hq in
/-- A root-preserving coefficient restriction makes the negative local maps agree. -/
theorem splitQuadraticNegative_restriction :
    Spec.map (CommRingCat.ofHom f) ≫ coprod.inr ≫
        (splitQuadraticSpecIso a hR).inv ≫ qR =
      coprod.inr ≫ (splitQuadraticSpecIso b hS).inv ≫ qS := by
  have h := congrArg
    (fun k => (coprod.inr : Spec (.of S) ⟶ Spec (.of S) ⨿ Spec (.of S)) ≫ k ≫ qR)
    (splitQuadraticSpecIso_naturality f a b hab hR hS).symm
  simpa only [Category.assoc, coprod.inr_map_assoc, hq] using h

end KltDP.Geometry

namespace KltDP.Geometry.SplitQuadraticGluing

variable {X Y : Scheme.{u}} (𝒰 : X.AffineOpenCover)
    (a : ∀ i : 𝒰.J, (𝒰.obj i)ˣ)
    (h2 : ∀ i : 𝒰.J, IsUnit (2 : 𝒰.obj i))
    (q : ∀ i : 𝒰.J, chart 𝒰 a i ⟶ Y) (i j : 𝒰.J)
    (𝒲 : (pullback (𝒰.map i) (𝒰.map j)).AffineOpenCover)
    (b : ∀ k : 𝒲.J, (𝒲.obj k)ˣ)
    (hW : ∀ k : 𝒲.J, IsUnit (2 : 𝒲.obj k))
    (fi : ∀ k : 𝒲.J, 𝒰.obj i →+* 𝒲.obj k)
    (fj : ∀ k : 𝒲.J, 𝒰.obj j →+* 𝒲.obj k)
    (hi : ∀ k, fi k (a i : 𝒰.obj i) = (b k : 𝒲.obj k))
    (hj : ∀ k, fj k (a j : 𝒰.obj j) = (b k : 𝒲.obj k))
    (hfi : ∀ k, Spec.map (CommRingCat.ofHom (fi k)) =
      𝒲.map k ≫ pullback.fst (𝒰.map i) (𝒰.map j))
    (hfj : ∀ k, Spec.map (CommRingCat.ofHom (fj k)) =
      𝒲.map k ≫ pullback.snd (𝒰.map i) (𝒰.map j))
    (hq : ∀ k,
      Spec.map (CommRingCat.ofHom (splitQuadraticMap (fi k) (a i) (b k) (hi k))) ≫ q i =
      Spec.map (CommRingCat.ofHom (splitQuadraticMap (fj k) (a j) (b k) (hj k))) ≫ q j)

include hW hfi hfj hq in
/-- Root compatibility on an affine cover of the actual intersection implies
the positive cocycle used by `glueIso`. -/
theorem positive_compatible_of_restrictions :
    pullback.fst (𝒰.map i) (𝒰.map j) ≫ positive 𝒰 a h2 q i =
      pullback.snd _ _ ≫ positive 𝒰 a h2 q j := by
  apply hom_ext_of_openCover 𝒲.openCover
  intro k
  let qk := Spec.map
    (CommRingCat.ofHom (splitQuadraticMap (fi k) (a i) (b k) (hi k))) ≫ q i
  have hi' := splitQuadraticPositive_restriction (fi k) (a i) (b k) (hi k)
    (h2 i) (hW k) (q i) qk rfl
  have hj' := splitQuadraticPositive_restriction (fj k) (a j) (b k) (hj k)
    (h2 j) (hW k) (q j) qk (hq k).symm
  have h := hi'.trans hj'.symm
  simpa only [positive, hfi k, hfj k, Category.assoc] using h

include hW hfi hfj hq in
/-- The same actual restriction data imply the negative cocycle. -/
theorem negative_compatible_of_restrictions :
    pullback.fst (𝒰.map i) (𝒰.map j) ≫ negative 𝒰 a h2 q i =
      pullback.snd _ _ ≫ negative 𝒰 a h2 q j := by
  apply hom_ext_of_openCover 𝒲.openCover
  intro k
  let qk := Spec.map
    (CommRingCat.ofHom (splitQuadraticMap (fi k) (a i) (b k) (hi k))) ≫ q i
  have hi' := splitQuadraticNegative_restriction (fi k) (a i) (b k) (hi k)
    (h2 i) (hW k) (q i) qk rfl
  have hj' := splitQuadraticNegative_restriction (fj k) (a j) (b k) (hj k)
    (h2 j) (hW k) (q j) qk (hq k).symm
  have h := hi'.trans hj'.symm
  simpa only [negative, hfi k, hfj k, Category.assoc] using h

end KltDP.Geometry.SplitQuadraticGluing

namespace KltDP.Geometry.SplitQuadraticGluing

variable {X Y : Scheme.{u}} (𝒰 : X.AffineOpenCover)
    (a : ∀ i : 𝒰.J, (𝒰.obj i)ˣ)
    (h2 : ∀ i : 𝒰.J, IsUnit (2 : 𝒰.obj i))
    (q : ∀ i : 𝒰.J, chart 𝒰 a i ⟶ Y)

/-- Actual quadratic charts covering a source-chart intersection provide the
forward cocycle. The two base restrictions and their roots must agree. -/
theorem forward_compatible_of_restrictions (i j : 𝒰.J)
    (𝒲 : (pullback (q i) (q j)).OpenCover)
    (S : 𝒲.J → CommRingCat.{u})
    (b : ∀ k : 𝒲.J, (S k)ˣ)
    (hW : ∀ k : 𝒲.J, IsUnit (2 : S k))
    (e : ∀ k : 𝒲.J, 𝒲.obj k ≅ Spec (.of (SplitQuadraticAlgebra (b k))))
    (fi : ∀ k : 𝒲.J, 𝒰.obj i →+* S k)
    (fj : ∀ k : 𝒲.J, 𝒰.obj j →+* S k)
    (hi : ∀ k, fi k (a i : 𝒰.obj i) = (b k : S k))
    (hj : ∀ k, fj k (a j : 𝒰.obj j) = (b k : S k))
    (hfi : ∀ k, (e k).hom ≫
      Spec.map (CommRingCat.ofHom (splitQuadraticMap (fi k) (a i) (b k) (hi k))) =
      𝒲.map k ≫ pullback.fst (q i) (q j))
    (hfj : ∀ k, (e k).hom ≫
      Spec.map (CommRingCat.ofHom (splitQuadraticMap (fj k) (a j) (b k) (hj k))) =
      𝒲.map k ≫ pullback.snd (q i) (q j))
    (hx : ∀ k, Spec.map (CommRingCat.ofHom (fi k)) ≫ 𝒰.map i =
      Spec.map (CommRingCat.ofHom (fj k)) ≫ 𝒰.map j) :
    pullback.fst (q i) (q j) ≫ toCoprod 𝒰 a h2 i =
      pullback.snd _ _ ≫ toCoprod 𝒰 a h2 j := by
  apply hom_ext_of_openCover 𝒲
  intro k
  let xk := Spec.map (CommRingCat.ofHom (fi k)) ≫ 𝒰.map i
  have hi' := splitQuadraticToCoprod_restriction (fi k) (a i) (b k) (hi k)
    (h2 i) (hW k) (𝒰.map i) xk rfl
  have hj' := splitQuadraticToCoprod_restriction (fj k) (a j) (b k) (hj k)
    (h2 j) (hW k) (𝒰.map j) xk (hx k).symm
  have h := congrArg (fun t => (e k).hom ≫ t) (hi'.trans hj'.symm)
  simpa only [toCoprod, ← Category.assoc, hfi k, hfj k] using h

end KltDP.Geometry.SplitQuadraticGluing

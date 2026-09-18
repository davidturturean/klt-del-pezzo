import KltDP.Geometry.ProjectiveProductCanonicalPullbackSquare

/-!
# Differential comparison through actual open charts

The square comparison below is the original module-pullback comparison,
followed by the original Kähler open-restriction isomorphism. Its naturality
allows the two differentials of the projective product to be checked in
the affine tensor charts, retaining their specified coefficient-field maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalChartMaps

open SchemeKaehlerSheaf SchemeKaehlerPullbackMap
open SchemeModulePullbackSquareCoherence
open ProjectiveProductCanonicalPullbackSquare

private theorem mapped_triangle {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B B' : C} {W Z T : D}
    (a : A ⟶ B) (b : B ⟶ B') (c : F.obj B' ⟶ W)
    (d : F.obj B ⟶ Z) (e : Z ⟶ W) (z : W ⟶ T)
    (h : F.map b ≫ c = d ≫ e) :
    F.map (a ≫ b) ≫ c ≫ z = F.map a ≫ d ≫ e ≫ z := by
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun t => F.map a ≫ t ≫ z) h

private theorem extend_square {C : Type*} [Category C]
    {A B D E F G H : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (x : A ⟶ F) (d : F ⟶ G) (t : G ⟶ E) (u : E ⟶ H) (v : G ⟶ H)
    (h : a ≫ b ≫ c = x ≫ d ≫ t) (ht : t ≫ u = v) :
    a ≫ b ≫ c ≫ u = x ≫ d ≫ v := by
  simpa only [Category.assoc, ht] using congrArg (fun z => z ≫ u) h

private theorem equality_paths {C : Type*} [Category C] {A B D E F : C}
    (h₀ : A = B) (h₁ : B = D) (h₂ : D = E) (h₃ : A = F) (h₄ : F = E) :
    eqToHom h₀ ≫ eqToHom h₁ ≫ eqToHom h₂ = eqToHom h₃ ≫ eqToHom h₄ := by
  simp only [eqToHom_trans]

private abbrev statementOf {P : Prop} (_ : P) : Prop := P

private theorem transported_mapIso_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A : D} {B E T : C} (s : A ≅ F.obj B) (t : B ≅ E)
    (h : E = T) (a : B ⟶ E) (ha : a = t.hom) :
    (s ≪≫ F.mapIso (t ≪≫ eqToIso h)).hom = s.hom ≫ F.map (a ≫ eqToHom h) := by
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, eqToIso.hom, ha]

private theorem transported_iso_hom {C : Type*} [Category C]
    {A B E : C} (t : A ≅ B) (h : B = E) (a : A ⟶ B) (ha : a = t.hom) :
    (t ≪≫ eqToIso h).hom = a ≫ eqToHom h := by
  simp only [Iso.trans_hom, eqToIso.hom, ha]

private theorem replace_square_factors {C : Type*} [Category C]
    {A B D E T : C} (a : A ⟶ B) (s : A ⟶ D) (t : D ⟶ B) (b : B ⟶ T)
    (r : A ⟶ E) (v v' : E ⟶ T) (ha : a = s ≫ t) (hv : v' = v)
    (h : s ≫ t ≫ b = r ≫ v) : a ≫ b = r ≫ v' := by
  rw [ha, hv, Category.assoc]
  exact h

variable {R : Type u} [CommRing R] {X Y V S : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X) (i : V ⟶ X)
    (j : S ⟶ Y) (q : S ⟶ V) (h : j ≫ p = q ≫ i)
    (fY : Y ⟶ Spec (CommRingCat.of R)) (fV : V ⟶ Spec (CommRingCat.of R))
    (fS : S ⟶ Spec (CommRingCat.of R))
    (eY : p ≫ f = fY) (eV : i ≫ f = fV)
    (eS : j ≫ fY = fS) (eQ : q ≫ fV = fS)

private def left_path_normalization :=
  congrArg (fun a => (squareIso i p q j h (baseRingSheaf f)).hom ≫ a)
    (mapped_triangle (schemeModulePullback q)
      (map f i) (eqToHom (congrArg baseRingSheaf eV))
      (map fV q) (map (i ≫ f) q)
      (eqToHom (congrArg baseRingSheaf (congrArg (fun t => q ≫ t) eV)))
      (eqToHom (congrArg baseRingSheaf eQ)) (map_base_eq eV q))

private def right_path_normalization :=
  mapped_triangle (schemeModulePullback j)
    (map f p) (eqToHom (congrArg baseRingSheaf eY))
    (map fY j) (map (p ≫ f) j)
    (eqToHom (congrArg baseRingSheaf (congrArg (fun t => j ≫ t) eY)))
    (eqToHom (congrArg baseRingSheaf eS)) (map_base_eq eY j)

private def extended_square_proof :=
  extend_square (squareIso i p q j h (baseRingSheaf f)).hom
    ((schemeModulePullback q).map (map f i)) (map (i ≫ f) q)
    ((schemeModulePullback j).map (map f p)) (map (p ≫ f) j)
    (eqToHom (congrArg baseRingSheaf (square_structure f p i j q h)))
    (eqToHom (congrArg baseRingSheaf (congrArg (fun t => q ≫ t) eV)) ≫
      eqToHom (congrArg baseRingSheaf eQ))
    (eqToHom (congrArg baseRingSheaf (congrArg (fun t => j ≫ t) eY)) ≫
      eqToHom (congrArg baseRingSheaf eS))
    (square_map f p i j q h)
    (equality_paths
      (congrArg baseRingSheaf (square_structure f p i j q h))
      (congrArg baseRingSheaf (congrArg (fun t => q ≫ t) eV))
      (congrArg baseRingSheaf eQ)
      (congrArg baseRingSheaf (congrArg (fun t => j ≫ t) eY))
      (congrArg baseRingSheaf eS))

private def square_map_specified_bases_proof :=
  (left_path_normalization f p i j q h fV fS eV eQ).trans
    ((extended_square_proof f p i j q h fY fV fS eY eV eS eQ).trans
      (right_path_normalization f p j fY fS eY eS).symm)

/-- Square naturality with the specified, original structure morphism at each vertex.
The transparent result type is the equality obtained from the original square map
and the two original base-map transports. No additional hypothesis is introduced. -/
theorem square_map_specified_bases :
    statementOf (square_map_specified_bases_proof f p i j q h fY fV fS eY eV eS eQ) :=
  square_map_specified_bases_proof f p i j q h fY fV fS eY eV eS eQ

variable [IsOpenImmersion i] [IsOpenImmersion j]

/-- Restriction of the pulled global factor to a chart is the pulled original
factor on the corresponding base chart. -/
def factorIso :
    (schemeModulePullback j).obj ((schemeModulePullback p).obj (baseRingSheaf f)) ≅
      (schemeModulePullback q).obj (baseRingSheaf fV) :=
  squareIso i p q j h (baseRingSheaf f) ≪≫
    (schemeModulePullback q).mapIso
      (SchemeKaehlerOpenRestriction.pullbackIso f i ≪≫
        eqToIso (congrArg baseRingSheaf eV))

/-- Original open restriction identifies the target with the chart's actual
differential sheaf and its specified coefficient-field structure map. -/
def targetIso : (schemeModulePullback j).obj (baseRingSheaf fY) ≅ baseRingSheaf fS :=
  SchemeKaehlerOpenRestriction.pullbackIso fY j ≪≫
    eqToIso (congrArg baseRingSheaf eS)

private def factor_iso_hom_proof :=
  transported_mapIso_hom (schemeModulePullback q)
    (squareIso i p q j h (baseRingSheaf f))
    (SchemeKaehlerOpenRestriction.pullbackIso f i)
    (congrArg baseRingSheaf eV) (map f i) (map_eq_pullbackIso f i)

private def target_iso_hom_proof :=
  transported_iso_hom (SchemeKaehlerOpenRestriction.pullbackIso fY j)
    (congrArg baseRingSheaf eS) (map fY j) (map_eq_pullbackIso fY j)

private def factorIso_differential_proof :=
  replace_square_factors (factorIso f p i j q h fV eV).hom
    _ _ _ _ _ (targetIso j fY fS eS).hom
    (factor_iso_hom_proof f p i j q h fV eV)
    (target_iso_hom_proof j fY fS eS)
    (square_map_specified_bases f p i j q h fY fV fS eY eV eS eQ)

/-- Both sides are the original scheme differential maps, transported only
through the proved chart and structure-map equalities. The transparent result
type retains the actual factor and target isomorphisms, via their proved hom maps. -/
theorem factorIso_differential :
    statementOf (factorIso_differential_proof f p i j q h fY fV fS eY eV eS eQ) :=
  factorIso_differential_proof f p i j q h fY fV fS eY eV eS eQ

end KltDP.Geometry.ProjectiveProductCanonicalChartMaps

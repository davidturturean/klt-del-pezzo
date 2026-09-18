import KltDP.Geometry.AffineAdjunctionAmbientScalarSquare
import KltDP.Geometry.AffineModuleTildePullbackCompositionMaps
import KltDP.Geometry.AffineModuleTildePullbackRingTransport
import KltDP.Geometry.AffineModuleTildeTensorPullbackRestriction
import KltDP.Geometry.SchemeModulePullbackSquareCoherence

/-!
# Identify the original ambient restriction with the original quotient square

The two proved affine comparison composition formulas put the original maps
in the same scalar-extension coordinates. The proved original top-form scalar
square identifies those coordinates. Equality transport then gives the original
scheme pullback square; the original ambient restriction is unchanged.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.AffineAdjunctionAmbientPullbackSquare

open AffineModuleTilde AffineModuleTildeSemilinearMap
open AffineDifferentialExteriorPullbackComparison
open KltDP.RingTheory.SmoothPrincipalDeterminantRestriction
open KltDP.RingTheory.SmoothPrincipalTopFormRestriction

private theorem transport_pair {C D : Type*} [Category C] [Category D] {T : Type*}
    (F : T → C ⥤ D) (M : C) {a b c d : T}
    (h₁ : a = b) (h₂ : b = c) (h₃ : d = c) :
    (eqToIso (congrArg (fun t => (F t).obj M) h₁)).hom ≫
        (eqToIso (congrArg (fun t => (F t).obj M) h₂)).hom =
      (eqToIso (congrArg F (h₁.trans (h₂.trans h₃.symm)))).hom.app M ≫
        (eqToIso (congrArg (fun t => (F t).obj M) h₃)).hom := by
  subst b
  subst c
  subst d
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem paste_transport {C : Type*} [Category C] {L₁ L₂ R₁ R₂ W : C}
    (eL : L₁ ≅ L₂) (eR : R₁ ≅ R₂) (e : L₁ ≅ R₁) (t : L₂ ≅ R₂)
    (a : L₂ ⟶ W) (b : R₂ ⟶ W)
    (he : eL.hom ≫ t.hom = e.hom ≫ eR.hom) (ha : a = t.hom ≫ b) :
    eL.hom ≫ a = e.hom ≫ eR.hom ≫ b := by
  rw [ha, ← Category.assoc, he, Category.assoc]

private theorem restriction_word {C : Type*} [Category C] {A B A' B' P K L : C}
    (e : A ≅ B) (e' : A' ≅ B') (t : B ≅ B') (k : K ≅ L)
    (a₁ : A ⟶ P) (a₂ : P ⟶ L) (b : A' ⟶ K) (u : B ⟶ L) (v : B' ⟶ L)
    (ha : a₁ ≫ a₂ = e.hom ≫ u) (hb : b ≫ k.hom = e'.hom ≫ v)
    (hu : u = t.hom ≫ v) :
    a₁ ≫ a₂ ≫ k.inv = (e ≪≫ t ≪≫ e'.symm).hom ≫ b := by
  apply (cancel_mono k.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hb, Iso.inv_hom_id_assoc, ha, hu]

private theorem native_transport {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (h : φ = ψ) (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (a : (ModuleCat.extendScalars φ).obj M ⟶ N)
    (b : (ModuleCat.extendScalars ψ).obj M ⟶ N)
    (ha : a = (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom ≫ b) :
    (pullbackIso φ M).hom ≫ AffineModuleTilde.map a =
      (eqToIso (congrArg
        (fun ρ => (schemeModulePullback (Spec.map (CommRingCat.ofHom ρ))).obj M.tilde) h)).hom ≫
        (pullbackIso ψ M).hom ≫ AffineModuleTilde.map b := by
  rw [ha, AffineModuleTilde.map_comp, ← Category.assoc, ← pullbackIso_ringMap_eqToIso h M]
  exact Category.assoc _ _ _

/-- Equality transport for a family of original maps, before any pullback or scalar functor
is substituted. No naturality premise is needed for equality of indices. -/
private theorem native_middle_word {C E D : Type*} [Category C] [Category E] [Category D]
    {T S : Type*} (F : S → C ⥤ D) (G : E ⥤ D) (L : T → E) (θ : T → S) (M : C)
    (η : ∀ t, (F (θ t)).obj M ⟶ G.obj (L t))
    (ρ ρ' : T) (h : ρ = ρ') (N : E) (j k : S)
    (hj : j = θ ρ) (hk : k = θ ρ') (u : L ρ ⟶ N) (v : L ρ' ⟶ N)
    (hs : u = (eqToIso (congrArg L h)).hom ≫ v) :
    (eqToIso (congrArg (fun s => (F s).obj M) hj)).hom ≫ η ρ ≫ G.map u =
      (eqToIso (congrArg F (hj.trans ((congrArg θ h).trans hk.symm)))).hom.app M ≫
        (eqToIso (congrArg (fun s => (F s).obj M) hk)).hom ≫ η ρ' ≫ G.map v := by
  subst ρ'
  subst j
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hs ⊢
  rw [hs]

/-- Instantiate the checked map-family identity once, with the actual original functors. -/
private def native_middle {A B : Type u} [CommRing A] [CommRing B]
    (ρ ρ' : A →+* B) (h : ρ = ρ') (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (j k : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (hj : j = Spec.map (CommRingCat.ofHom ρ))
    (hk : k = Spec.map (CommRingCat.ofHom ρ'))
    (u : (ModuleCat.extendScalars ρ).obj M ⟶ N)
    (v : (ModuleCat.extendScalars ρ').obj M ⟶ N)
    (hs : u = (eqToIso (congrArg (fun σ => (ModuleCat.extendScalars σ).obj M) h)).hom ≫ v) :=
  native_middle_word schemeModulePullback (AffineModuleTilde.functor B)
    (fun σ : A →+* B => (ModuleCat.extendScalars σ).obj M)
    (fun σ : A →+* B => Spec.map (CommRingCat.ofHom σ)) M.tilde
    (fun σ => (pullbackIso σ M).hom) ρ ρ' h N j k hj hk u v hs

/-- Cancel after the original ambient map has already been normalized. -/
private theorem restriction_map_word {C : Type*} [Category C] {A B A' B' K L : C}
    (e : A ≅ B) (e' : A' ≅ B') (t : B ≅ B') (k : K ≅ L)
    (a : A ⟶ K) (b : A' ⟶ K) (u : B ⟶ L) (v : B' ⟶ L)
    (ha : a ≫ k.hom = e.hom ≫ u) (hb : b ≫ k.hom = e'.hom ≫ v)
    (hu : u = t.hom ≫ v) :
    a = (e ≪≫ t ≪≫ e'.symm).hom ≫ b := by
  apply (cancel_mono k.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ha, hb, Iso.inv_hom_id_assoc, hu]

/-- Normalize only the named original ambient restriction against its original target frame. -/
private theorem ambientRestriction_hom {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (ψ : B →+* B')
    (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M') :
    AffineModuleTildeTensorPullbackRestriction.ambientRestriction φ φ' ψ s ≫
        (pullbackIso φ' M').hom =
      (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map (pullbackIso φ M).hom ≫
        pullbackMap ψ s := by
  simp only [AffineModuleTildeTensorPullbackRestriction.ambientRestriction,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def original_left_comparison {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (ψ : B →+* B')
    (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M') :=
  (ambientRestriction_hom φ φ' ψ M M' s).trans
    (pullbackMap_after_pullbackIso_comp φ ψ M ((ModuleCat.extendScalars φ').obj M') s)

/-- Specialize the passed native transport once, before inserting the original outer maps. -/
private def original_middle_comparison {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M')
    (a : M →ₛₗ[σ] M')
    (hs : (ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ s =
      (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom ≫
        (ModuleCat.extendScalarsComp σ φ').hom.app M ≫
          (ModuleCat.extendScalars φ').map (extendHom σ a)) :=
  native_middle (ψ.comp φ) (φ'.comp σ) h M ((ModuleCat.extendScalars φ').obj M')
    (Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom σ))
    (specMap_comp_eq φ ψ) (specMap_comp_eq σ φ')
    ((ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ s)
    ((ModuleCat.extendScalarsComp σ φ').hom.app M ≫
      (ModuleCat.extendScalars φ').map (extendHom σ a)) hs

/-- Cancel the original square's right comparison before any affine ring is substituted. -/
private theorem original_square_hom_comp {X V Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
    (h : k ≫ g = j ≫ f) (M : Y.Modules) :
    (SchemeModulePullbackSquareCoherence.squareIso f g j k h M).hom ≫
        (schemeModulePullbackCompIso j f).hom.app M =
      (schemeModulePullbackCompIso k g).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback h)).hom.app M := by
  simp only [SchemeModulePullbackSquareCoherence.squareIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- Paste the checked equations against a named square map, without rebuilding its inverse. -/
private theorem named_restriction_square_word {C : Type*} [Category C]
    {A B A' B' K L : C} (a : A ⟶ K) (b : A' ⟶ K) (q : A ⟶ A')
    (e : A ⟶ B) (e' : A' ⟶ B') (t : B ⟶ B') (κ : K ≅ L)
    (u : B ⟶ L) (v : B' ⟶ L)
    (hLeft : a ≫ κ.hom = e ≫ u) (hRight : b ≫ κ.hom = e' ≫ v)
    (hMiddle : u = t ≫ v) (hSquare : q ≫ e' = e ≫ t) :
    a = q ≫ b := by
  apply (cancel_mono κ.hom).mp
  calc
    a ≫ κ.hom = e ≫ u := hLeft
    _ = e ≫ (t ≫ v) := congrArg (fun w => e ≫ w) hMiddle
    _ = (e ≫ t) ≫ v := (Category.assoc e t v).symm
    _ = (q ≫ e') ≫ v := congrArg (fun w => w ≫ v) hSquare.symm
    _ = q ≫ (e' ≫ v) := Category.assoc q e' v
    _ = q ≫ (b ≫ κ.hom) := congrArg (fun w => q ≫ w) hRight.symm
    _ = (q ≫ b) ≫ κ.hom := (Category.assoc q b κ.hom).symm

/-- Apply the original scalar comparison only on the left, without a square inverse. -/
private def original_left_middle_comparison {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M')
    (a : M →ₛₗ[σ] M')
    (hs : (ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ s =
      (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom ≫
        (ModuleCat.extendScalarsComp σ φ').hom.app M ≫
          (ModuleCat.extendScalars φ').map (extendHom σ a)) :=
  (original_left_comparison φ φ' ψ M M' s).trans
    (congrArg (fun z =>
      (schemeModulePullbackCompIso (Spec.map (CommRingCat.ofHom ψ))
        (Spec.map (CommRingCat.ofHom φ))).hom.app M.tilde ≫ z)
      (original_middle_comparison φ φ' σ ψ h M M' s a hs))

private theorem square_right_word {C : Type*} [Category C]
    {A B A' B' K L : C} (q : A ⟶ A') (l : A ⟶ B) (r : A' ⟶ B') (t : B ⟶ B')
    (b : A' ⟶ K) (κ : K ⟶ L) (v : B' ⟶ L)
    (hq : q ≫ r = l ≫ t) (hb : b ≫ κ = r ≫ v) :
    q ≫ (b ≫ κ) = l ≫ t ≫ v := by
  rw [hb, ← Category.assoc q r, hq, Category.assoc]

/-- Assemble two already checked equations with their actual endpoints inferred. -/
private theorem square_right_of_equations {C : Type*} [Category C]
    {A B A' B' K L : C} {q : A ⟶ A'} {l : A ⟶ B} {r : A' ⟶ B'} {t : B ⟶ B'}
    {b : A' ⟶ K} {κ : K ⟶ L} {v : B' ⟶ L}
    (hq : q ≫ r = l ≫ t) (hb : b ≫ κ = r ≫ v) :
    q ≫ (b ≫ κ) = l ≫ t ≫ v :=
  square_right_word q l r t b κ v hq hb

/-- The original scheme square cancellation is checked independently of the native map. -/
private def original_square_comparison {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) :=
  let hSpec := (specMap_comp_eq φ ψ).trans
    ((congrArg (fun ρ => Spec.map (CommRingCat.ofHom ρ)) h).trans
      (specMap_comp_eq σ φ').symm)
  original_square_hom_comp (Spec.map (CommRingCat.ofHom σ))
    (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom φ'))
    (Spec.map (CommRingCat.ofHom ψ)) hSpec M.tilde

/-- Retain the checked right-composition equation with its original inferred scalar endpoint. -/
private def original_right_comparison {A A' B' : Type u}
    [CommRing A] [CommRing A'] [CommRing B']
    (σ : A →+* A') (φ' : A' →+* B')
    (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A') (a : M →ₛₗ[σ] M') :=
  pullbackIso_after_pullbackMap_comp σ φ' M M' a

/-- The original right coordinate comparison uses the two checked equations directly. -/
private def original_square_right_comparison {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (a : M →ₛₗ[σ] M') :=
  square_right_of_equations
    (original_square_comparison φ φ' σ ψ h M)
    (original_right_comparison σ φ' M M' a)

private theorem cancel_frame_word {C : Type*} [Category C] {A A' K L : C}
    (κ : K ≅ L) (a : A ⟶ K) (q : A ⟶ A') (b : A' ⟶ K)
    (h : a ≫ κ.hom = q ≫ (b ≫ κ.hom)) : a = q ≫ b := by
  apply (cancel_mono κ.hom).mp
  exact h.trans (Category.assoc q b κ.hom).symm

/-- Infer the original arrow endpoints from their checked coordinate equation. -/
private theorem cancel_frame_of_equation {C : Type*} [Category C] {A A' K L : C}
    (κ : K ≅ L) {a : A ⟶ K} {q : A ⟶ A'} {b : A' ⟶ K}
    (h : a ≫ κ.hom = q ≫ (b ≫ κ.hom)) : a = q ≫ b :=
  cancel_frame_word κ a q b h

/-- Join the two checked coordinate equations before applying cancellation. -/
private def original_coordinate_equality {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M')
    (a : M →ₛₗ[σ] M')
    (hs : (ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ s =
      (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom ≫
        (ModuleCat.extendScalarsComp σ φ').hom.app M ≫
          (ModuleCat.extendScalars φ').map (extendHom σ a)) :=
  (original_left_middle_comparison φ φ' σ ψ h M M' s a hs).trans
    (original_square_right_comparison φ φ' σ ψ h M M' a).symm

/-- Cancel the actual target frame with its original arrow endpoints inferred. -/
private def ambient_square_proof {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (φ' : A' →+* B') (σ : A →+* A') (ψ : B →+* B')
    (h : ψ.comp φ = φ'.comp σ) (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (s : (ModuleCat.extendScalars φ).obj M →ₛₗ[ψ] (ModuleCat.extendScalars φ').obj M')
    (a : M →ₛₗ[σ] M')
    (hs : (ModuleCat.extendScalarsComp φ ψ).hom.app M ≫ extendHom ψ s =
      (eqToIso (congrArg (fun ρ => (ModuleCat.extendScalars ρ).obj M) h)).hom ≫
        (ModuleCat.extendScalarsComp σ φ').hom.app M ≫
          (ModuleCat.extendScalars φ').map (extendHom σ a)) :=
  cancel_frame_of_equation (pullbackIso φ' M')
    (original_coordinate_equality φ φ' σ ψ h M M' s a hs)

private abbrev statementOf {P : Prop} (_h : P) : Prop := P

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))

/-- The existing ambient restriction is the original scheme-square comparison followed by
pullback of the original native exterior map. The inferred proposition transparently unfolds
`ambientRestriction` and `squareIso`; its sole scalar compatibility is proved, not assumed. -/
theorem ambientRestriction_eq_square :
    statementOf (ambient_square_proof (Ideal.Quotient.mk J) (Ideal.Quotient.mk J')
      (algebraMap A A') (quotientMap A A' J J' hφ)
      (AffineAdjunctionAmbientScalarSquare.quotientMap_comp_mk A A' J J' hφ)
      ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2)
      ((AffineKaehlerTildeDerivation.differentialModule R A').exteriorPower 2)
      (ambientTopTensorMap R A A' J J' hφ) (nativeMap R A A' 2)
      (AffineAdjunctionAmbientScalarSquare.scalar_square R A A' J J' hφ)) :=
  ambient_square_proof (Ideal.Quotient.mk J) (Ideal.Quotient.mk J')
    (algebraMap A A') (quotientMap A A' J J' hφ)
    (AffineAdjunctionAmbientScalarSquare.quotientMap_comp_mk A A' J J' hφ)
    ((AffineKaehlerTildeDerivation.differentialModule R A).exteriorPower 2)
    ((AffineKaehlerTildeDerivation.differentialModule R A').exteriorPower 2)
    (ambientTopTensorMap R A A' J J' hφ) (nativeMap R A A' 2)
    (AffineAdjunctionAmbientScalarSquare.scalar_square R A A' J J' hφ)

end KltDP.Geometry.AffineAdjunctionAmbientPullbackSquare

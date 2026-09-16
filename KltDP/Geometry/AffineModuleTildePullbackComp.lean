import KltDP.Geometry.AffineModuleTildePullback
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Composition of the original affine tilde/pullback comparison

The actual scheme pullback composition and the pinned tensor-extension
composition commute with `AffineModuleTilde.pullbackIso`. The equality
between the composite of the two original Spec maps and Spec of the
original composite ring map is retained explicitly.

The proof uses the original affine and scheme adjunctions. Both routes
send the canonical element to the canonical section of 1 tensor
(1 tensor m). No choice of a new scalar action or comparison is made.

Reuse: the project pin c44e0c8ee63ca166450922a373c7409c5d26b00b
already proves `ModuleCat.extendScalarsComp` and its unit-tensor formula
in Algebra/Category/ModuleCat/ChangeOfRings.lean:907-930. The existing
`SchemeModulePullbackCoherence` proves the needed normalization for the
original scheme composition. The private right-adjunction normalizer
below is the same bounded proof already used there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace KltDP.Geometry.AffineModuleTilde

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem homEquiv_ofNatIsoRight_apply
    {D E : Type*} [Category D] [Category E]
    {F : D ⥤ E} {G H : E ⥤ D} (a : F ⊣ G) (e : G ≅ H)
    (M : D) (N : E) (h : F.obj M ⟶ N) :
    (a.ofNatIsoRight e).homEquiv M N h = a.homEquiv M N h ≫ e.hom.app N := by
  rw [Adjunction.ofNatIsoRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The transported affine transpose retains the actual section carrier. -/
private theorem pulledHomEquiv_apply (φ : A →+* B) (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of B)).Modules)
    (a : (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⟶ N)
    (m : M) :
    (pulledTildeAdjunction φ).homEquiv M N a m =
      (adjunction A).homEquiv M
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj N)
        ((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde N a) m := by
  unfold pulledTildeAdjunction
  rw [homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

-- Normalize the original affine transpose on abstract modules before tensor specialization.
private theorem affineHomEquiv_apply (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of A)).Modules) (a : M.tilde ⟶ N) (m : M) :
    (adjunction A).homEquiv M N a m =
      a.val.app (op ⊤) (ModuleCat.Tilde.toOpen M ⊤ m) := by
  change (globalSectionsFunctor A).map a ((unitNatIso A).hom.app M m) = _
  simpa only [unitNatIso_hom_app] using
    globalSectionsFunctor_map_apply a (ModuleCat.Tilde.toOpen M ⊤ m)

/-- Postcomposition of the actual comparison is fixed on every original
module element by its actual tensor-unit section. -/
theorem pullbackIso_homEquiv_apply (φ : A →+* B) (M : ModuleCat.{u} A)
    (N : (Spec (CommRingCat.of B)).Modules)
    (a : ((ModuleCat.extendScalars φ).obj M).tilde ⟶ N) (m : M) :
    (adjunction A).homEquiv M
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj N)
      ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde N
        ((pullbackIso φ M).hom ≫ a)) m =
      a.val.app (op ⊤)
        (ModuleCat.Tilde.toOpen ((ModuleCat.extendScalars φ).obj M) ⊤
          ((1 : B) ⊗ₜ[A,φ] m)) := by
  have h := congrArg
    (fun f : M ⟶ (globalSectionsFunctor B ⋙ ModuleCat.restrictScalars φ).obj N => f m)
    (Adjunction.homEquiv_naturality_right (pulledTildeAdjunction φ)
      (pullbackIso φ M).hom a)
  calc
    _ = (pulledTildeAdjunction φ).homEquiv M N
        ((pullbackIso φ M).hom ≫ a) m :=
      (pulledHomEquiv_apply φ M N ((pullbackIso φ M).hom ≫ a) m).symm
    _ = a.val.app (op ⊤)
        ((pulledTildeAdjunction φ).homEquiv M
          (((ModuleCat.extendScalars φ).obj M).tilde) (pullbackIso φ M).hom m) := h
    _ = _ := congrArg (fun s => a.val.app (op ⊤) s)
      (pullbackTildeIso_hom_transpose_apply φ M m)

/-- The comparison itself has exactly the original tensor-unit section
as its transpose, without any postcomposition. -/
theorem pullbackIso_homEquiv_unit_apply (φ : A →+* B) (M : ModuleCat.{u} A) (m : M) :
    (adjunction A).homEquiv M
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
        (((ModuleCat.extendScalars φ).obj M).tilde))
      ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde
        (((ModuleCat.extendScalars φ).obj M).tilde) (pullbackIso φ M).hom) m =
      ModuleCat.Tilde.toOpen ((ModuleCat.extendScalars φ).obj M) ⊤
        ((1 : B) ⊗ₜ[A,φ] m) := by
  simpa only [Category.comp_id] using
    pullbackIso_homEquiv_apply φ M (((ModuleCat.extendScalars φ).obj M).tilde) (𝟙 _) m

/-- Equality transport of the original pushforward is the identity on
global section carriers, including when the scalar maps are not definitionally equal. -/
private theorem pushforward_eqToIso_top {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (N : X.Modules) (s : N.val.obj (op ⊤)) :
    (((eqToIso (congrArg schemeModulePushforward h)).hom.app N).val.app (op ⊤)) s = s := by
  subst g
  rfl

/-- The actual adjunction equality transport also retains the original
affine global-section element. -/
private theorem affineHomEquiv_eqToIso_apply
    {f g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)} (h : f = g)
    (M : ModuleCat.{u} A) (N : (Spec (CommRingCat.of B)).Modules)
    (a : (schemeModulePullback g).obj M.tilde ⟶ N) (m : M) :
    (adjunction A).homEquiv M ((schemeModulePushforward f).obj N)
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv M.tilde N
        ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj M.tilde) h)).hom ≫ a)) m =
    (adjunction A).homEquiv M ((schemeModulePushforward g).obj N)
      ((schemeModulePullbackPushforwardAdjunction g).homEquiv M.tilde N a) m := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- Evaluate the transported original comparison after an abstract module map. -/
private theorem affineHomEquiv_eqToIso_map_apply
    (ρ : A →+* C)
    {f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A)}
    (h : f = Spec.map (CommRingCat.ofHom ρ))
    (M : ModuleCat.{u} A) (P : ModuleCat.{u} C)
    (a : (ModuleCat.extendScalars ρ).obj M ⟶ P) (m : M) :
    (adjunction A).homEquiv M ((schemeModulePushforward f).obj P.tilde)
      ((schemeModulePullbackPushforwardAdjunction f).homEquiv M.tilde P.tilde
        ((eqToIso (congrArg (fun k => (schemeModulePullback k).obj M.tilde) h)).hom ≫
          (pullbackIso ρ M).hom ≫ map a)) m =
      ModuleCat.Tilde.toOpen P ⊤ (a ((1 : C) ⊗ₜ[A,ρ] m)) := by
  subst f
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]
  exact (pullbackIso_homEquiv_apply ρ M P.tilde (map a) m).trans
    (map_app_toOpen a ⊤ ((1 : C) ⊗ₜ[A,ρ] m))

/-- The equality is the pinned contravariant Spec composition theorem,
applied to the two original ring homomorphisms. -/
theorem specMap_comp_eq (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) :=
  (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm

/-- Cancel the same hom-set equivalences using equality on original module elements. -/
private theorem eq_of_three_equiv_pointwise
    {R : Type*} [Ring R] {M Q : ModuleCat.{u} R}
    {α β γ : Type*}
    (e₁ : α ≃ β) (e₂ : β ≃ γ) (e₃ : γ ≃ (M ⟶ Q))
    {x y : α}
    (h : ∀ m : M, (e₃ (e₂ (e₁ x))) m = (e₃ (e₂ (e₁ y))) m) :
    x = y := by
  apply e₁.injective
  apply e₂.injective
  apply e₃.injective
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

set_option maxHeartbeats 800000 in
/-- The original iterated route has the original iterated tensor-unit section as transpose. -/
private theorem pullbackIso_comp_left_homEquiv_apply
    (φ : A →+* B) (ψ : B →+* C) (M : ModuleCat.{u} A) (m : M) :
    let N := ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)).tilde
    (adjunction A).homEquiv M
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N))
      ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N)
        ((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom ψ))).homEquiv
          ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde) N
          ((schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map
              (pullbackIso φ M).hom ≫
            (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom))) m =
      ModuleCat.Tilde.toOpen
        ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)) ⊤
        ((1 : C) ⊗ₜ[B,ψ] ((1 : B) ⊗ₜ[A,φ] m)) := by
  dsimp only
  let N := ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)).tilde
  have hnat := Adjunction.homEquiv_naturality_left
    (schemeModulePullbackPushforwardAdjunction (Spec.map (CommRingCat.ofHom ψ)))
    (pullbackIso φ M).hom
    (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom
  have houter := congrArg
    (fun a : (schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde ⟶
        (schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N =>
      (adjunction A).homEquiv M
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
          ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N))
        ((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde
          ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N) a) m)
    hnat
  refine houter.trans ?_
  calc
    _ = ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom ψ))).homEquiv
        (((ModuleCat.extendScalars φ).obj M).tilde) N
        (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom).val.app (op ⊤)
          (ModuleCat.Tilde.toOpen ((ModuleCat.extendScalars φ).obj M) ⊤
            ((1 : B) ⊗ₜ[A,φ] m)) :=
      pullbackIso_homEquiv_apply φ M
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N) _ m
    _ = _ :=
      (affineHomEquiv_apply ((ModuleCat.extendScalars φ).obj M)
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N)
        ((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom ψ))).homEquiv
          (((ModuleCat.extendScalars φ).obj M).tilde) N
          (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom)
        ((1 : B) ⊗ₜ[A,φ] m)).symm.trans
          (pullbackIso_homEquiv_unit_apply ψ ((ModuleCat.extendScalars φ).obj M)
            ((1 : B) ⊗ₜ[A,φ] m))

set_option maxHeartbeats 800000 in
/-- The original composite route has that same section in the same iterated pushforward carrier. -/
private theorem pullbackIso_comp_right_homEquiv_apply
    (φ : A →+* B) (ψ : B →+* C) (M : ModuleCat.{u} A) (m : M) :
    let N := ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)).tilde
    (adjunction A).homEquiv M
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N))
      ((schemeModulePullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N)
        ((schemeModulePullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom ψ))).homEquiv
          ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde) N
          ((schemeModulePullbackCompIso
              (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))).hom.app
                M.tilde ≫
            (eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
              (specMap_comp_eq φ ψ))).hom ≫
            (pullbackIso (ψ.comp φ) M).hom ≫
            map ((ModuleCat.extendScalarsComp φ ψ).hom.app M)))) m =
      ModuleCat.Tilde.toOpen
        ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)) ⊤
        ((1 : C) ⊗ₜ[B,ψ] ((1 : B) ⊗ₜ[A,φ] m)) := by
  dsimp only
  let N := ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)).tilde
  have hcomp := schemeModulePullbackCompIso_homEquiv
    (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ)) M.tilde N
    ((eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
      (specMap_comp_eq φ ψ))).hom ≫
      (pullbackIso (ψ.comp φ) M).hom ≫
      map ((ModuleCat.extendScalarsComp φ ψ).hom.app M))
  have houter := congrArg
    (fun a : M.tilde ⟶
        (schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
          ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N) =>
      (adjunction A).homEquiv M
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
          ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N)) a m)
    hcomp
  have hnormalize := affineHomEquiv_eqToIso_map_apply (ψ.comp φ)
    (f := Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ))
    (specMap_comp_eq φ ψ) M
    ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M))
    ((ModuleCat.extendScalarsComp φ ψ).hom.app M) m
  have htensor := congrArg
    (fun z : (ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M) =>
      ModuleCat.Tilde.toOpen
        ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)) ⊤ z)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul φ ψ M m)
  exact houter.trans (hnormalize.trans htensor)

set_option maxHeartbeats 800000 in
/-- The original affine tilde/pullback comparisons commute with the
original scheme composition and the pinned extension-of-scalars composition. -/
theorem pullbackIso_comp (φ : A →+* B) (ψ : B →+* C) (M : ModuleCat.{u} A) :
    (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ))).map (pullbackIso φ M).hom ≫
        (pullbackIso ψ ((ModuleCat.extendScalars φ).obj M)).hom =
      (schemeModulePullbackCompIso
        (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom φ))).hom.app M.tilde ≫
      (eqToIso (congrArg (fun f => (schemeModulePullback f).obj M.tilde)
        (specMap_comp_eq φ ψ))).hom ≫
      (pullbackIso (ψ.comp φ) M).hom ≫
      map ((ModuleCat.extendScalarsComp φ ψ).hom.app M) := by
  let N := ((ModuleCat.extendScalars ψ).obj ((ModuleCat.extendScalars φ).obj M)).tilde
  exact eq_of_three_equiv_pointwise
    ((schemeModulePullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom ψ))).homEquiv
      ((schemeModulePullback (Spec.map (CommRingCat.ofHom φ))).obj M.tilde) N)
    ((schemeModulePullbackPushforwardAdjunction
      (Spec.map (CommRingCat.ofHom φ))).homEquiv M.tilde
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N))
    ((adjunction A).homEquiv M
      ((schemeModulePushforward (Spec.map (CommRingCat.ofHom φ))).obj
        ((schemeModulePushforward (Spec.map (CommRingCat.ofHom ψ))).obj N)))
    (fun m => (pullbackIso_comp_left_homEquiv_apply φ ψ M m).trans
      (pullbackIso_comp_right_homEquiv_apply φ ψ M m).symm)

end KltDP.Geometry.AffineModuleTilde

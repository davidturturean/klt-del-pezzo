import KltDP.Geometry.SchemeConormalOpenImmersion
import KltDP.Geometry.SchemeConormalSourceIso
import KltDP.Geometry.SchemeKernelOpenPullback
import KltDP.Geometry.SchemeInvertibleSheafPullback
import KltDP.Examples.FrobeniusMultiCentreLocusPicard

/-!
# Kernel ideal modules along an isomorphism of the ambient scheme

For a morphism `ι : Z ⟶ X` and an isomorphism `g : X ≅ Y`, the kernel module of
`ι ≫ g.hom` is the inverse image along `g.inv` of the kernel module of `ι`
(`schemeKernelIsoTransport`), compatibly with the inclusions into the structure sheaves
(`schemeKernelIsoTransport_hom_inclusion`).  The isomorphism is the accepted
`schemeKernelPostcompOpenIso` applied to the open immersion `g.inv`, after rewriting
`(ι ≫ g.hom) ≫ g.inv = ι`.  A source isomorphism `e : Z ≅ Z'` with `e.hom ≫ ι' = ι ≫ g.hom`
is absorbed by the accepted `schemeKernelPrecompIso` (`schemeKernelTransportIso`).

Consequences: the kernel of the transported closed subscheme is invertible whenever the
original one is (`isInvertible_schemeKernelIdeal_transport`), and its Picard class is the
image of the original class under `schemePicardPullbackHom g.inv`, i.e. under lane A1's
`picardEquivOfIso g.inv` (`kernelLine_toPic_transport`, `kernelLine_toPic_transport_equiv`),
also in the additive sign convention used by the class tables
(`neg_kernelLine_toPic_transport`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Geometry.SchemeKernelIdealIsoTransport

open KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {Z Z' X Y : Scheme.{u}}

/-- Kernel modules of equal morphisms. -/
def schemeKernelIdealEqIso {f f' : Z ⟶ X} (h : f = f') :
    schemeKernelIdeal f ≅ schemeKernelIdeal f' :=
  eqToIso (congrArg schemeKernelIdeal h)

theorem schemeKernelIdealEqIso_hom_ι {f f' : Z ⟶ X} (h : f = f') :
    (schemeKernelIdealEqIso h).hom ≫ schemeKernelIdealι f' = schemeKernelIdealι f := by
  subst h
  simp [schemeKernelIdealEqIso]

theorem comp_hom_comp_inv (ι : Z ⟶ X) (g : X ≅ Y) : (ι ≫ g.hom) ≫ g.inv = ι := by
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The kernel of `ι ≫ g.hom` is the inverse image along `g.inv` of the kernel of `ι`.** -/
def schemeKernelIsoTransport (ι : Z ⟶ X) (g : X ≅ Y) :
    schemeKernelIdeal (ι ≫ g.hom) ≅ (schemeModulePullback g.inv).obj (schemeKernelIdeal ι) :=
  (schemeKernelPostcompOpenIso (ι ≫ g.hom) g.inv).symm ≪≫
    (schemeModulePullback g.inv).mapIso (schemeKernelIdealEqIso (comp_hom_comp_inv ι g))

/-- The comparison is compatible with the inclusions into the structure sheaves. -/
theorem schemeKernelIsoTransport_hom_inclusion (ι : Z ⟶ X) (g : X ≅ Y) :
    (schemeKernelIsoTransport ι g).hom ≫ pulledKernelInclusion ι g.inv =
      schemeKernelIdealι (ι ≫ g.hom) := by
  simp only [schemeKernelIsoTransport, pulledKernelInclusion, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, schemeKernelIdealEqIso_hom_ι,
    ← schemeKernelPostcompOpenIso_hom_ι, Iso.inv_hom_id_assoc]

theorem schemeKernelIsoTransport_inv_ι (ι : Z ⟶ X) (g : X ≅ Y) :
    (schemeKernelIsoTransport ι g).inv ≫ schemeKernelIdealι (ι ≫ g.hom) =
      pulledKernelInclusion ι g.inv := by
  rw [Iso.inv_comp_eq, schemeKernelIsoTransport_hom_inclusion]

/-- A closed subscheme `ι' : Z' ⟶ Y` carried by the isomorphism (`e.hom ≫ ι' = ι ≫ g.hom`)
has kernel the inverse image along `g.inv` of the kernel of `ι`. -/
def schemeKernelTransportIso (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom) :
    schemeKernelIdeal ι' ≅ (schemeModulePullback g.inv).obj (schemeKernelIdeal ι) :=
  (schemeKernelPrecompIso e ι').symm ≪≫ schemeKernelIdealEqIso h ≪≫ schemeKernelIsoTransport ι g

theorem schemeKernelTransportIso_hom_inclusion (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom) :
    (schemeKernelTransportIso ι g ι' e h).hom ≫ pulledKernelInclusion ι g.inv =
      schemeKernelIdealι ι' := by
  simp only [schemeKernelTransportIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    schemeKernelIsoTransport_hom_inclusion, schemeKernelIdealEqIso_hom_ι,
    schemeKernelPrecompIso_inv_ι]

/-! ### Invertibility -/

/-- Invertibility of a module sheaf is transported along an isomorphism of module sheaves. -/
theorem isInvertible_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (hM : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M) (e : M ≅ N) :
    KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) N :=
  (InvertibleSheaf.ofIso ⟨M, hM⟩ e).property

/-- The kernel of the transported closed subscheme is invertible whenever the original one is. -/
theorem isInvertible_schemeKernelIdeal_transport (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι)) :
    KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι') :=
  isInvertible_of_iso (schemeModulePullback_isInvertible g.inv (schemeKernelIdeal ι) hι)
    (schemeKernelTransportIso ι g ι' e h).symm

theorem isInvertible_schemeKernelIdeal_comp (ι : Z ⟶ X) (g : X ≅ Y)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι)) :
    KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal (ι ≫ g.hom)) :=
  isInvertible_schemeKernelIdeal_transport ι g (ι ≫ g.hom) (Iso.refl Z) (Category.id_comp _) hι

/-! ### Picard classes -/

/-- Isomorphic invertible sheaves have the same Picard class. -/
theorem toPic_eq_of_iso {X : Scheme.{u}} (L M : InvertibleSheaf X) (e : L.obj ≅ M.obj) :
    L.toPic = M.toPic := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  change (L.toPic : Skeleton X.Modules) = (M.toPic : Skeleton X.Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨e⟩

/-- An invertible sheaf isomorphic to the pullback of `L` along `f` has class the pullback of
the class of `L`. -/
theorem toPic_eq_pullback_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X) (L : InvertibleSheaf X)
    (M : InvertibleSheaf Y) (e : M.obj ≅ (schemeModulePullback f).obj L.obj) :
    M.toPic = schemePicardPullbackHom f L.toPic := by
  rw [schemePicardPullbackHom_toPic]
  exact toPic_eq_of_iso M (pullbackInvertibleSheaf f L) e

/-- The ideal line of the transported closed subscheme. -/
def kernelLineTransport (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι)) :
    InvertibleSheaf Y :=
  ⟨schemeKernelIdeal ι', isInvertible_schemeKernelIdeal_transport ι g ι' e h hι⟩

/-- **The Picard class of the transported kernel line is the pullback along `g.inv` of the
original class.** -/
theorem kernelLine_toPic_transport (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι))
    (hι' : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι')) :
    (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι', hι'⟩ : InvertibleSheaf Y)) =
      schemePicardPullbackHom g.inv
        (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι, hι⟩ : InvertibleSheaf X)) :=
  toPic_eq_pullback_of_iso g.inv ⟨schemeKernelIdeal ι, hι⟩ ⟨schemeKernelIdeal ι', hι'⟩
    (schemeKernelTransportIso ι g ι' e h)

/-- The same statement through lane A1's Picard-group isomorphism `picardEquivOfIso g.inv`. -/
theorem kernelLine_toPic_transport_equiv (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι))
    (hι' : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι')) :
    (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι', hι'⟩ : InvertibleSheaf Y)) =
      KltDP.Examples.FrobeniusMultiCentreLocusPicard.picardEquivOfIso g.inv
        (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι, hι⟩ : InvertibleSheaf X)) :=
  kernelLine_toPic_transport ι g ι' e h hι hι'

/-- The additive (ideal-sheaf sign convention) form of the class transport. -/
theorem neg_kernelLine_toPic_transport (ι : Z ⟶ X) (g : X ≅ Y) (ι' : Z' ⟶ Y) (e : Z ≅ Z')
    (h : e.hom ≫ ι' = ι ≫ g.hom)
    (hι : KltDP.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (schemeKernelIdeal ι))
    (hι' : KltDP.SheafOfModules.IsInvertible (R := Y.ringCatSheaf) (schemeKernelIdeal ι')) :
    -Additive.ofMul (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι', hι'⟩ : InvertibleSheaf Y)) =
      (schemePicardPullbackHom g.inv).toAdditive
        (-Additive.ofMul
          (InvertibleSheaf.toPic (⟨schemeKernelIdeal ι, hι⟩ : InvertibleSheaf X))) := by
  rw [map_neg, kernelLine_toPic_transport ι g ι' e h hι hι']
  rfl

/-- Pullback of Picard classes along a composite is the composite of the pullbacks, in the
additive convention. -/
theorem picardPullback_toAdditive_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (c : Additive X.Pic) :
    (schemePicardPullbackHom (g ≫ f)).toAdditive c =
      (schemePicardPullbackHom g).toAdditive ((schemePicardPullbackHom f).toAdditive c) := by
  change schemePicardPullbackHom (g ≫ f) (Additive.toMul c) =
    schemePicardPullbackHom g (schemePicardPullbackHom f (Additive.toMul c))
  rw [schemePicardPullbackHom_comp]
  rfl

/-- Pullback of Picard classes along the two sides of a commutative square whose vertical
sides are isomorphisms: `g₂.hom ≫ f' = f ≫ g₁.hom` gives `g₂.inv ≫ f = f' ≫ g₁.inv`. -/
theorem picardPullback_inv_square {X X' Y Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X')
    (g₁ : X ≅ X') (g₂ : Y ≅ Y') (h : g₂.hom ≫ f' = f ≫ g₁.hom) (c : X.Pic) :
    schemePicardPullbackHom g₂.inv (schemePicardPullbackHom f c) =
      schemePicardPullbackHom f' (schemePicardPullbackHom g₁.inv c) := by
  have hm : g₂.inv ≫ f = f' ≫ g₁.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change ((schemePicardPullbackHom g₂.inv).comp (schemePicardPullbackHom f)) c =
    ((schemePicardPullbackHom f').comp (schemePicardPullbackHom g₁.inv)) c
  rw [← schemePicardPullbackHom_comp, ← schemePicardPullbackHom_comp, hm]

/-- The additive form of `picardPullback_inv_square`. -/
theorem picardPullback_inv_square_toAdditive {X X' Y Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X')
    (g₁ : X ≅ X') (g₂ : Y ≅ Y') (h : g₂.hom ≫ f' = f ≫ g₁.hom) (c : Additive X.Pic) :
    (schemePicardPullbackHom g₂.inv).toAdditive ((schemePicardPullbackHom f).toAdditive c) =
      (schemePicardPullbackHom f').toAdditive
        ((schemePicardPullbackHom g₁.inv).toAdditive c) :=
  congrArg Additive.ofMul (picardPullback_inv_square f f' g₁ g₂ h (Additive.toMul c))

end KltDP.Geometry.SchemeKernelIdealIsoTransport

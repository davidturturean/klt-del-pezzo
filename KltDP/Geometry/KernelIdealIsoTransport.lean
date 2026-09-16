import KltDP.Geometry.EffectiveCartierOfInvertibleIdeal

/-!
# Transport of kernel ideals along an isomorphism locus, and sections through chart squares

Generic helpers for the tower identity of BRIEF19:
* `Ideal.comap_inv_eq_map_hom`: the comap along the inverse of a ring isomorphism is the map
  along the isomorphism;
* `ker_ideal_of_isPullback_id_restrict`: for a pullback square `IsPullback g' (𝟙 Z) f g` (a closed
  subscheme `g : Z ⟶ Y` whose base change along `f : X ⟶ Y` is `g' : Z ⟶ X` with the same source)
  and an open `V ⊆ Y` over which `f` is an isomorphism, the kernel ideal of `g'` on an affine open
  of `f ⁻¹ᵁ V` is the transport of the kernel ideal of `g` along the restricted isomorphism
  (pinned `ker_ideal_of_isPullback_of_isOpenImmersion` after restricting the square to `V`);
* `appLE_of_chart_square`: `π.appLE` between the images of two affine charts `c`, `c'` with
  `c ≫ π = Spec.map φ ≫ c'` acts on transported ring elements by `φ`;
* `IdealSheafData.ideal_eq_of_nonempty`, `IdealSheafData.ideal_congr`, affine opens of an open
  subscheme as preimages.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

theorem Ideal.comap_inv_eq_map_hom {R S : CommRingCat.{u}} (e : R ≅ S) (I : Ideal R) :
    I.comap e.inv.hom = I.map e.hom.hom := by
  ext x
  rw [Ideal.mem_comap,
    Ideal.mem_map_iff_of_surjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2]
  constructor
  · intro hx
    exact ⟨e.inv x, hx, e.inv_hom_id_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    show e.inv (e.hom y) ∈ I
    rw [e.hom_inv_id_apply]
    exact hy

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h; rfl

theorem eqToHom_toScheme_ι {X : Scheme.{u}} {U V : X.Opens} (h : U = V) :
    eqToHom (congrArg (fun W : X.Opens => (W : Scheme.{u})) h) ≫ V.ι = U.ι := by
  subst h; simp

/-- Kernel ideals of a base-changed closed subscheme over an isomorphism locus. -/
theorem ker_ideal_of_isPullback_id_restrict {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (g' : Z ⟶ X) [QuasiCompact g] [QuasiCompact g'] (H : IsPullback g' (𝟙 Z) f g) (V : Y.Opens)
    [IsIso (f ∣_ V)] (W : (f ⁻¹ᵁ V).toScheme.affineOpens) :
    g'.ker.ideal ⟨(f ⁻¹ᵁ V).ι ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩ =
      (g.ker.ideal ⟨V.ι ''ᵁ ((f ∣_ V) ''ᵁ W.1),
          (W.2.image_of_isOpenImmersion (f ∣_ V)).image_of_isOpenImmersion _⟩).comap
        ((f ∣_ V).appIso W.1).inv.hom := by
  have hgf : g' ≫ f = g := by simpa using H.w
  have hZ : g' ⁻¹ᵁ (f ⁻¹ᵁ V) = g ⁻¹ᵁ V := by rw [← hgf]; rfl
  let φ : (g' ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme ⟶ (g ⁻¹ᵁ V).toScheme :=
    eqToHom (congrArg (fun W : Z.Opens => (W : Scheme.{u})) hZ)
  have hφ : φ ≫ (g ⁻¹ᵁ V).ι = (g' ⁻¹ᵁ (f ⁻¹ᵁ V)).ι := eqToHom_toScheme_ι hZ
  have hleft : IsPullback (g' ⁻¹ᵁ (f ⁻¹ᵁ V)).ι φ (𝟙 Z) (g ⁻¹ᵁ V).ι :=
    (IsPullback.of_horiz_isIso ⟨by rw [hφ, Category.comp_id]⟩).flip
  have hs : IsPullback ((g' ∣_ (f ⁻¹ᵁ V)) ≫ (f ⁻¹ᵁ V).ι) φ f ((g ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι, morphismRestrict_ι]
    exact hleft.paste_horiz H
  have hp : (g' ∣_ (f ⁻¹ᵁ V)) ≫ (f ∣_ V) = φ ≫ (g ∣_ V) := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      morphismRestrict_ι, hgf, ← hφ, Category.assoc]
  have hsq : IsPullback (g' ∣_ (f ⁻¹ᵁ V)) φ (f ∣_ V) (g ∣_ V) :=
    IsPullback.of_right hs hp (isPullback_morphismRestrict f V).flip
  haveI : QuasiCompact (g ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g V).flip inferInstance
  rw [← Scheme.ker_morphismRestrict_ideal g' (f ⁻¹ᵁ V) W,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (g ∣_ V) (g' ∣_ (f ⁻¹ᵁ V)) φ (f ∣_ V) hsq W]
  congr 1
  exact Scheme.ker_morphismRestrict_ideal g V ⟨(f ∣_ V) ''ᵁ W.1, W.2.image_of_isOpenImmersion _⟩

/-- `π.appLE` between the images of two affine charts, through the chart square. -/
theorem appLE_of_chart_square {R R' : CommRingCat.{u}} {S S' : Scheme.{u}}
    (c : Spec R ⟶ S) (c' : Spec R' ⟶ S') [IsOpenImmersion c] [IsOpenImmersion c']
    (π : S ⟶ S') (φ : R' ⟶ R) (hsq : c ≫ π = Spec.map φ ≫ c')
    (h : c ''ᵁ ⊤ ≤ π ⁻¹ᵁ (c' ''ᵁ ⊤)) (x : R') :
    π.appLE (c' ''ᵁ ⊤) (c ''ᵁ ⊤) h ((c'.appIso ⊤).inv ((Scheme.ΓSpecIso R').inv x)) =
      (c.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv (φ x)) := by
  have hmor : π.appLE (c' ''ᵁ ⊤) (c ''ᵁ ⊤) h ≫ (c.appIso ⊤).hom =
      (c'.appIso ⊤).hom ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.appLE_comp_appLE, appLE_congr_hom hsq, Scheme.comp_appLE,
      Scheme.Hom.appIso_hom, Category.assoc]
    congr 1
  have key := congrArg (fun m : Γ(S', c' ''ᵁ ⊤) ⟶ Γ(Spec R, ⊤) =>
    m ((c'.appIso ⊤).inv ((Scheme.ΓSpecIso R').inv x))) hmor
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at key
  rw [← Iso.hom_inv_id_apply (c.appIso ⊤)
    (π.appLE (c' ''ᵁ ⊤) (c ''ᵁ ⊤) h ((c'.appIso ⊤).inv ((Scheme.ΓSpecIso R').inv x))), key]
  congr 1
  have hnat := congrArg (fun m : R' ⟶ Γ(Spec R, ⊤) => m x) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at hnat
  exact hnat.symm

/-- Ideals on the empty affine open agree; so equality can be checked on nonempty opens. -/
theorem IdealSheafData.ideal_eq_of_nonempty {X : Scheme.{u}} (I J : X.IdealSheafData)
    (W : X.affineOpens) (h : Nonempty W.1 → I.ideal W = J.ideal W) : I.ideal W = J.ideal W := by
  by_cases hW : Nonempty W.1
  · exact h hW
  · have hb : W.1 = ⊥ := by
      apply Opens.ext
      rw [Opens.coe_bot]
      exact Set.eq_empty_of_forall_not_mem fun x hx => hW ⟨⟨x, hx⟩⟩
    haveI : Subsingleton Γ(X, W.1) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
    exact Ideal.ext fun x => by rw [Subsingleton.elim x 0]; simp

theorem image_preimage_ι_eq {X : Scheme.{u}} (U : X.Opens) (W : X.Opens) (hW : W ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inter, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hW

theorem isAffineOpen_preimage_ι {X : Scheme.{u}} (U : X.Opens) (W : X.affineOpens)
    (hW : W.1 ≤ U) : IsAffineOpen (U.ι ⁻¹ᵁ W.1) :=
  U.ι.isAffineOpen_iff_of_isOpenImmersion.mp (by rw [image_preimage_ι_eq U W.1 hW]; exact W.2)

/-- A statement about the ideals of two ideal sheaves proved on the images of the affine opens
of an open subscheme `U` holds on every affine open inside `U`. -/
theorem IdealSheafData.ideal_eq_of_image {X : Scheme.{u}} (U : X.Opens) (I J : X.IdealSheafData)
    (key : ∀ W₀ : U.toScheme.affineOpens,
      I.ideal ⟨U.ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
        J.ideal ⟨U.ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩)
    (W : X.affineOpens) (hW : W.1 ≤ U) : I.ideal W = J.ideal W := by
  have e : (⟨U.ι ''ᵁ (U.ι ⁻¹ᵁ W.1),
      (isAffineOpen_preimage_ι U W hW).image_of_isOpenImmersion _⟩ : X.affineOpens) = W :=
    Subtype.ext (image_preimage_ι_eq U W.1 hW)
  rw [← e]
  exact key ⟨U.ι ⁻¹ᵁ W.1, isAffineOpen_preimage_ι U W hW⟩

/-- The same, for affine opens inside `U ⊓ V` when the statement is only known on the images
lying inside `V`. -/
theorem IdealSheafData.ideal_eq_of_image' {X : Scheme.{u}} (U V : X.Opens) (I J : X.IdealSheafData)
    (key : ∀ W₀ : U.toScheme.affineOpens, U.ι ''ᵁ W₀.1 ≤ V →
      I.ideal ⟨U.ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩ =
        J.ideal ⟨U.ι ''ᵁ W₀.1, W₀.2.image_of_isOpenImmersion _⟩)
    (W : X.affineOpens) (hW : W.1 ≤ U ⊓ V) : I.ideal W = J.ideal W := by
  have hU : W.1 ≤ U := hW.trans inf_le_left
  have e : (⟨U.ι ''ᵁ (U.ι ⁻¹ᵁ W.1),
      (isAffineOpen_preimage_ι U W hU).image_of_isOpenImmersion _⟩ : X.affineOpens) = W :=
    Subtype.ext (image_preimage_ι_eq U W.1 hU)
  rw [← e]
  exact key ⟨U.ι ⁻¹ᵁ W.1, isAffineOpen_preimage_ι U W hU⟩
    (by rw [image_preimage_ι_eq U W.1 hU]; exact hW.trans inf_le_right)

end KltDP.Geometry

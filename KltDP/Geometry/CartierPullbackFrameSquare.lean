import KltDP.Geometry.CartierPullbackFrameCharts

/-!
# The chart square of a Cartier pullback, and its effect on local equations

Second module of the general Cartier comparison `π^* I_D ≅ I_{π^*D}`, for a generic-point-preserving
morphism `π : X ⟶ Y` of integral schemes and an effective Cartier divisor `D` on `Y` with regular
equations.  It contains only the **square** and the **top-section bookkeeping** it induces; no
module-level construction appears here, because the single lemma below is `topIso`/`eqToHom`
transport, which is where this development has twice exhausted the heartbeat budget.

For an affine `V` of `Y` and an affine `W ≤ π ⁻¹ᵁ V` of `X`,

* `chartMap π V W hW := X.homOfLE hW ≫ (π ∣_ V)` is the induced morphism `W.toScheme ⟶ V.toScheme`
  and `chartMap_ι` is the square `chartMap ≫ V.ι = W.ι ≫ π` (pinned `Scheme.homOfLE_ι`,
  `morphismRestrict_ι`);
* `chartMap_appTop` is the one statement the frame comparison needs: the induced map carries the
  local equation of `V` (the section transported by `V.topIso.inv`, i.e. the accepted
  `gluedAffineEquation`) to the local equation of `W` belonging to `π.appLE V W`.

The proof is the pinned `Γ_map_morphismRestrict` (in the form used by five accepted modules) for the
restriction factor, and `topIso_inv_homOfLE_appTop` for the `homOfLE` factor: both sides of the
latter are restriction maps of the structure presheaf between the same two opens, and the category of
opens is thin, so they agree.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierPullbackFrameSquare

open KltDP.Geometry

/-! ### Restriction maps of the structure presheaf -/

/-- The category of opens is thin, so any two restriction maps between the same opens agree. -/
private theorem presheaf_map_congr {Z : Scheme.{u}} {A B : (Z.Opens)ᵒᵖ} (i j : A ⟶ B) :
    Z.presheaf.map i = Z.presheaf.map j := by
  have h : i = j := Quiver.Hom.unop_inj (Subsingleton.elim i.unop j.unop)
  rw [h]

set_option maxHeartbeats 4000000 in
/-- The canonical top-section comparison intertwines the inclusion of a smaller open with the
corresponding restriction map of the structure presheaf. -/
theorem topIso_inv_homOfLE_appTop {Z : Scheme.{u}} {A B : Z.Opens} (e : A ≤ B) :
    B.topIso.inv ≫ (Z.homOfLE e).appTop =
      Z.presheaf.map (homOfLE e).op ≫ A.topIso.inv := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    ← Functor.map_comp, ← Functor.map_comp]
  all_goals exact presheaf_map_congr _ _

/-! ### The induced map of charts -/

section Charts

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- The morphism induced by `π` from an affine chart of `X` to an affine chart of `Y` containing
its image. -/
def chartMap (V : Y.affineOpens) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1) :
    W.1.toScheme ⟶ V.1.toScheme :=
  X.homOfLE hW ≫ (π ∣_ V.1)

/-- **The chart square.** -/
theorem chartMap_ι (V : Y.affineOpens) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1) :
    chartMap π V W hW ≫ V.1.ι = W.1.ι ≫ π := by
  rw [chartMap, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

set_option maxHeartbeats 4000000 in
/-- **The induced chart map carries the transported local equation of `V` to the transported
pulled-back equation of `W`.** -/
theorem chartMap_appTop (V : Y.affineOpens) (W : X.affineOpens) (hW : W.1 ≤ π ⁻¹ᵁ V.1)
    (d : Γ(Y, V.1)) :
    (chartMap π V W hW).appTop (gluedAffineEquation V d) =
      gluedAffineEquation W (π.appLE V.1 W.1 hW d) := by
  have hrestrict : (π ∣_ V.1).appTop =
      (V.1.topIso.hom ≫ π.app V.1) ≫ (π ⁻¹ᵁ V.1).topIso.inv := by
    simpa only [Scheme.Γ_map_op, Category.assoc] using Γ_map_morphismRestrict π V.1
  have hres : V.1.topIso.inv ≫ (chartMap π V W hW).appTop =
      π.appLE V.1 W.1 hW ≫ W.1.topIso.inv := by
    rw [chartMap, Scheme.comp_appTop, hrestrict, Scheme.Hom.appLE]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, topIso_inv_homOfLE_appTop hW]
  have happ := congrArg
    (fun m : Γ(Y, V.1) ⟶ Γ(W.1.toScheme, ⊤) => m d) hres
  simpa only [gluedAffineEquation, CommRingCat.comp_apply] using happ

end Charts

end KltDP.Geometry.CartierPullbackFrameSquare

import KltDP.Compatibility.FreeSheafSections

/-!
# A finite free presentation gives a basis of sections on every object of the site

`FreeSheafSections.freeSectionsBasis` bases the sections of `free I` itself. What a consumer
actually has is a sheaf isomorphism `e : free I ≅ M` — a *presentation* of some other sheaf — and
needs the basis of `M`'s sections that `e` carries across, together with its compatibility with
restriction.

* **`transportedBasis`**: `Basis I (R.val.obj W) (M.val.obj W)` for every `W`.
* **`transportedBasis_apply`**: its vectors are the images under `e` of the tautological sections.
* **`transportedBasis_map`**: **the basis is compatible with restriction along every arrow.**

**Why this is a separate module from its two uses, and stated in `M` and `e` as variables.** The
consumer (`ChartKaehlerOpenFrame`) applies it at *concrete* chart data. If the restriction
compatibility were proved there, the statement would name the concrete frame, and the unifier
descends `Basis.map → freeSectionsBasis → freeEvalIso → conePointUniqueUpToIso` and through
`pushforward`'s `restrictScalars` wrapper rather than matching at a head — a deterministic `whnf`
timeout at the default heartbeat budget, which is what happened. With `M` and `e` bound as
variables there is nothing to unfold: `transportedBasis` is an opaque head, and the consumer's
obligation becomes one application of `transportedBasis_map`. This is the recorded countermeasure
"bind the data as local hypotheses so both sides present one opaque head", and it is a shape fix,
not a heartbeat increase.

Nothing is admitted here. Nothing in this module is specific to schemes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open KltDP.Compatibility.FreeSheafSections

universe u v u₁

namespace KltDP.Compatibility.FreeSheafTransportedBasis

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

variable (R) (I : Type u) [Fintype I] [DecidableEq I]
variable (M : _root_.SheafOfModules.{u} R)
  (e : _root_.SheafOfModules.free (R := R) I ≅ M)

/-- **A finite free presentation of a sheaf of modules gives a basis of its sections over every
object of the site.** -/
def transportedBasis (W : Cᵒᵖ) : Basis I (R.val.obj W) (M.val.obj W) :=
  (freeSectionsBasis R I W).map
    ((_root_.SheafOfModules.evaluation R W).mapIso e).toLinearEquiv

/-- The basis vectors are the images under the presentation of the tautological free sections. -/
theorem transportedBasis_apply (W : Cᵒᵖ) (i : I) :
    transportedBasis R I M e W i = e.hom.val.app W (freeSectionsBasis R I W i) := rfl

/-- **The transported basis is compatible with restriction along every arrow of the site.** The
free sheaf's basis is, and the presentation is a morphism of sheaves, so this is its naturality. -/
theorem transportedBasis_map {W W' : Cᵒᵖ} (g : W ⟶ W') (i : I) :
    M.val.map g (transportedBasis R I M e W i) = transportedBasis R I M e W' i := by
  have hnat := PresheafOfModules.naturality_apply e.hom.val g (freeSectionsBasis R I W i)
  rw [freeSectionsBasis_map] at hnat
  rw [transportedBasis_apply, transportedBasis_apply]
  exact hnat.symm

end KltDP.Compatibility.FreeSheafTransportedBasis

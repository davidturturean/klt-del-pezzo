import KltDP.Geometry.OpenAffinizationStructureSheaf
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Transport of the original canonical structure-sheaf isomorphism

Invertibility of the canonical map on structure sheaves is invariant under
an isomorphism of the original scheme arrows. A cartesian square over an
open immersion therefore transports this property to the actual restriction
of the original morphism to the image open.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace KltDP.Geometry.StructureSheafIsoPullbackTransport

/-- Precomposing with a scheme isomorphism preserves the canonical
pushforward structure-sheaf isomorphism. -/
theorem precomp_c_isIso {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    [IsIso g] [IsIso f.c] : IsIso (g ≫ f).c := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  change IsIso ((g ≫ f).app U.unop)
  rw [Scheme.comp_app]
  infer_instance

/-- An isomorphism of actual scheme arrows preserves invertibility of
the original canonical structure-sheaf map. -/
theorem c_isIso_of_arrow_iso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g)
    [IsIso f.c] : IsIso g.c := by
  letI : IsIso (f ≫ e.hom.right).c :=
    OpenAffinizationStructureSheaf.comp_c_isIso f e.hom.right
  rw [Arrow.iso_w' e]
  exact precomp_c_isIso e.inv.left (f ≫ e.hom.right)

/-- The canonical structure-sheaf property depends only on the actual
scheme arrow up to isomorphism. -/
theorem c_isIso_iff_of_arrow_iso {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) :
    IsIso f.c ↔ IsIso g.c := by
  constructor
  · intro hf
    letI := hf
    exact c_isIso_of_arrow_iso e
  · intro hg
    letI := hg
    exact c_isIso_of_arrow_iso e.symm

/-- A cartesian comparison over an original open immersion gives the
canonical structure-sheaf isomorphism for the actual restricted map. -/
theorem restrict_c_isIso_of_isPullback {P X Y Z : Scheme.{u}}
    (a : P ⟶ Y) (b : P ⟶ X) (i : Y ⟶ Z) (f : X ⟶ Z)
    [IsOpenImmersion i] (h : IsPullback a b i f) [IsIso a.c] :
    IsIso (f ∣_ i.opensRange).c := by
  let e : Arrow.mk a ≅ Arrow.mk (pullback.snd f i) :=
    Arrow.isoMk h.flip.isoPullback (Iso.refl Y) (by
      simpa only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id] using
        h.flip.isoPullback_hom_snd)
  letI : IsIso (pullback.snd f i).c := c_isIso_of_arrow_iso e
  exact c_isIso_of_arrow_iso (morphismRestrictOpensRange f i).symm

end KltDP.Geometry.StructureSheafIsoPullbackTransport


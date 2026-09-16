/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license; see docs/SHEAF_MODULE_MONOIDAL_LICENSE.txt.
Authors: Chris Birkbeck

The local injectivity and surjectivity argument is adapted from
CBirkbeck/AINTLIB revision 7ecbba9dbb7fee076a1b77a6cd516fc6de46d684,
projects/ModularCurves/ModularCurves/Picard/InvertibleSheaf.lean, lines 120–150.
The covering-sieve step is generalized from open subsets to an arbitrary
site using the pinned Mathlib definitions of CoversTop and Sieve.ofObjects.
-/

import KltDP.Compatibility.SheafModuleMonoidal
import Mathlib.CategoryTheory.Sites.CoversTop

/-!
# Sheafification of morphisms bijective over a covering family

A morphism of module presheaves is inverted by sheafification when its
component is bijective on every object admitting a map to a member of a
family that covers the site. The proof uses the corresponding covering
sieve directly and requires no terminal object or pullbacks.
-/

open CategoryTheory Opposite

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrp.{u}] [HasWeakSheafify J AddCommGrp.{u}]

/-- Componentwise bijectivity on every object over a covering family
implies that the actual module sheafification inverts the morphism. -/
theorem sheafificationW_of_bijective_on_coversTop
    {A B : PresheafOfModules.{u} R.val} (g : A ⟶ B)
    {ι : Type v} (U : ι → C) (hU : J.CoversTop U)
    (hbij : ∀ (i : ι) (V : C) (_ : V ⟶ U i),
      Function.Bijective (g.app (op V))) :
    sheafificationW (𝟙 R.val) g := by
  apply (sheafificationW_iff_isLocallyBijective (𝟙 R.val) g).mpr
  constructor
  · constructor
    intro X x y hxy
    refine J.superset_covering ?_ (hU X.unop)
    rintro V f ⟨i, ⟨a⟩⟩
    change A.map f.op x = A.map f.op y
    apply (hbij i V a).injective
    exact (naturality_apply g f.op x).trans
      ((congrArg (fun z => B.map f.op z) hxy).trans
        (naturality_apply g f.op y).symm)
  · constructor
    intro X s
    refine J.superset_covering ?_ (hU X)
    rintro V f ⟨i, ⟨a⟩⟩
    exact (hbij i V a).surjective (B.map f.op s)

end PresheafOfModules

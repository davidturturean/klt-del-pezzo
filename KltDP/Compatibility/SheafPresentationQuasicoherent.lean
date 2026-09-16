/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Adapted from official Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:373-403.
The pinned Presentation and original Over functor are retained. Their
colimit preservation is supplied by the already-proved actual adjunction.
-/
import KltDP.Compatibility.SheafPresentationMap

/-!
# Original global presentations give original quasicoherent sheaves

The actual global presentation restricts to every original Over site.
The existing all-object cover and original free-unit comparison give the
pinned quasicoherent-data predicate. Isomorphisms transport that same
data by the original Over maps, retaining both cover and index types.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{u₁} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]
  [∀ U : C, HasSheafify (J.over U) AddCommGrp.{u}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

/-- The original presentation restricts on the original all-object cover. -/
def Presentation.quasicoherentData {M : SheafOfModules.{u} R} (P : M.Presentation) :
    M.QuasicoherentData where
  I := C
  X := id
  coversTop := P.generators.localGeneratorsData.coversTop
  presentation U := P.map (overFunctor R U) (unitOverIso (R := R) U).symm

/-- A genuine global presentation implies the pinned quasicoherent predicate. -/
theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : M.Presentation) :
    M.IsQuasicoherent :=
  ⟨⟨P.quasicoherentData⟩⟩

/-- An actual isomorphism maps every original local presentation on the same cover. -/
def QuasicoherentData.ofIsIso {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [IsIso f] (q : M.QuasicoherentData) : N.QuasicoherentData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  presentation i := (q.presentation i).ofIsIso ((overFunctor R (q.X i)).map f)

/-- The original quasicoherent predicate is invariant under an actual isomorphism. -/
theorem isQuasicoherent_of_isIso {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [IsIso f] [M.IsQuasicoherent] : N.IsQuasicoherent := by
  obtain ⟨q⟩ := IsQuasicoherent.nonempty_quasicoherentData (M := M)
  exact ⟨⟨q.ofIsIso f⟩⟩

end SheafOfModules

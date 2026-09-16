/-
Copyright (c) 2023, 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0; see the complete license text at
docs/reuse_sources/sheaf_finite_type_locality/sources/LICENSE.
Authors of the adapted upstream constructions: Joël Riou, Justus Springer

Bounded adaptations from official Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f:
Sheaf/Quasicoherent.lean:429–449 (generator-data part of bind),
CategoryTheory/Sites/CoversTop/Over.lean:28–33 (cover transitivity),
and CategoryTheory/Sites/Over.lean:565–581 (actual iterated-slice sites).
The original pinned module restrictions, ring maps and finite-index data remain.
-/
import KltDP.Compatibility.SheafGeneratingSectionsMap
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Finite type is local for the original Over restrictions

The actual equivalence between `(C / U) / V` and `C / V.left` transports
the original module sheaf and generating epimorphism. Combining the two
actual covers gives original local generator data with the same finite
generator indices. No locality or coherence conclusion is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- Combining covers in the original over sites gives a cover in the
original site. This uses the actual sieve definition of `CoversTop`. -/
theorem CoversTop.over {I : Type*} {X : I → C} (hX : J.CoversTop X)
    {I' : I → Type w} {Y : (i : I) → I' i → Over (X i)}
    (hY : ∀ i, (J.over (X i)).CoversTop (Y i)) :
    J.CoversTop (fun ij : (i : I) × I' i => (Y ij.1 ij.2).left) := by
  intro W
  refine J.transitive (hX W) _ ?_
  rintro Z f ⟨i, ⟨g⟩⟩
  have h := hY i (Over.mk g)
  change Sieve.overEquiv _ (Sieve.ofObjects (Y i) (Over.mk g)) ∈ J Z at h
  refine J.superset_covering ?_ h
  rintro T a ⟨V, b, c, ⟨j, ⟨d⟩⟩, _⟩
  exact ⟨⟨i, j⟩, ⟨c ≫ d.left⟩⟩

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The inverse of the original iterated-slice equivalence identifies the
two original covering-sieve conditions. -/
instance iteratedSliceBackward_isDenseSubsite {U : C} (V : Over U) :
    (Over.iteratedSliceEquiv V).inverse.IsDenseSubsite
      (J.over V.left) ((J.over U).over V) where
  functorPushforward_mem_iff := by
    simp [GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      ← Over.iteratedSliceBackward_forget_forget V, Sieve.functorPushforward_comp]

instance iteratedSliceForward_isContinuous {U : C} (V : Over U) :
    Functor.IsContinuous.{v} (Over.iteratedSliceForward V)
      ((J.over U).over V) (J.over V.left) :=
  inferInstanceAs (Functor.IsContinuous.{v} (Over.iteratedSliceEquiv V).functor
    ((J.over U).over V) (J.over V.left))

instance iteratedSliceBackward_isContinuous {U : C} (V : Over U) :
    Functor.IsContinuous.{v} (Over.iteratedSliceBackward V)
      (J.over V.left) ((J.over U).over V) :=
  inferInstanceAs (Functor.IsContinuous.{v} (Over.iteratedSliceEquiv V).inverse
    (J.over V.left) ((J.over U).over V))

variable {J} (R : Sheaf J RingCat.{v})

/-- Transport from the nested original Over site to the single original
Over site. Its ring comparison is the identity after the pinned forgetful maps. -/
def iteratedOverFunctor {U : C} (V : Over U) :
    SheafOfModules.{v} ((R.over U).over V) ⥤ SheafOfModules.{v} (R.over V.left) :=
  pushforward (F := Over.iteratedSliceBackward V)
    (J := J.over V.left) (K := (J.over U).over V) (𝟙 (R.over V.left))

/-- The actual iterated-slice site adjunction gives an adjunction of the
original module pushforwards. Its ring equations are restrictions along identities. -/
def iteratedOverAdjunction {U : C} (V : Over U) :
    iteratedOverFunctor R V ⊣
      pushforward (F := Over.iteratedSliceForward V)
        (J := (J.over U).over V) (K := J.over V.left) (𝟙 ((R.over U).over V)) := by
  refine KltDP.SheafModuleAdjunction.pushforwardPushforwardAdj
    (C := Over V.left) (D := Over V)
    (J := J.over V.left) (K := (J.over U).over V)
    (F := Over.iteratedSliceBackward V) (G := Over.iteratedSliceForward V)
    (S := R.over V.left) (R := (R.over U).over V)
    (Over.iteratedSliceEquiv V).symm.toAdjunction
    (𝟙 (R.over V.left)) (𝟙 ((R.over U).over V)) ?_ ?_
  · apply NatTrans.ext
    funext W
    change R.val.map (𝟙 _) = 𝟙 _
    exact R.val.map_id _
  · apply NatTrans.ext
    funext W
    change R.val.map (𝟙 _) = 𝟙 _
    exact R.val.map_id _

/-- In particular the transport preserves the actual coproduct and
generating epimorphism; those preservation conclusions are proved here. -/
instance iteratedOverFunctor_isLeftAdjoint {U : C} (V : Over U) :
    (iteratedOverFunctor R V).IsLeftAdjoint :=
  (iteratedOverAdjunction R V).isLeftAdjoint

/-- Transporting the nested original restriction gives the original single
restriction, with identity section maps. -/
def iteratedOverObjIso (M : SheafOfModules.{v} R) {U : C} (V : Over U) :
    (iteratedOverFunctor R V).obj ((M.over U).over V) ≅ M.over V.left :=
  (fullyFaithfulForget.{v} (R.over V.left)).preimageIso
    (X := (iteratedOverFunctor R V).obj ((M.over U).over V))
    (Y := M.over V.left)
    (PresheafOfModules.isoMk
      (M₁ := ((iteratedOverFunctor R V).obj ((M.over U).over V)).val)
      (M₂ := (M.over V.left).val) (fun _ => Iso.refl _))

variable [HasWeakSheafify J AddCommGrp.{v}]
  [J.WEqualsLocallyBijective AddCommGrp.{v}]
  [J.HasSheafCompose (forget₂ RingCat.{v} AddCommGrp.{v})]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrp.{v}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrp.{v}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat.{v} AddCommGrp.{v})]
  [∀ (U : C) (V : Over U), HasWeakSheafify ((J.over U).over V) AddCommGrp.{v}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrp.{v}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).HasSheafCompose
    (forget₂ RingCat.{v} AddCommGrp.{v})]

/-- The actual unit sheaf is preserved under the iterated-slice transport. -/
def iteratedOverUnitIso {U : C} (V : Over U) :
    unit (R.over V.left) ≅ (iteratedOverFunctor R V).obj (unit ((R.over U).over V)) :=
  Iso.refl _

variable {R}

/-- Flatten actual local generating data on an actual cover. The resulting
generator family is the transported original epimorphism, not a chosen replacement. -/
def LocalGeneratorsData.bind (M : SheafOfModules.{v} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, (M.over (X i)).LocalGeneratorsData) : M.LocalGeneratorsData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over (fun i => (D i).coversTop)
  generators ij :=
    (((D ij.1).generators ij.2).map
      (iteratedOverFunctor R ((D ij.1).X ij.2))
      (iteratedOverUnitIso R ((D ij.1).X ij.2))).ofEpi
        (iteratedOverObjIso R M ((D ij.1).X ij.2)).hom

/-- Flattening retains the original generator index on each local chart. -/
@[simp]
theorem LocalGeneratorsData.bind_generators_I (M : SheafOfModules.{v} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, (M.over (X i)).LocalGeneratorsData) (ij : (i : I) × (D i).I) :
    ((LocalGeneratorsData.bind M X hX D).generators ij).I =
      ((D ij.1).generators ij.2).I := rfl

/-- Finite type on an actual cover, for the original Over restrictions,
implies finite type of the original sheaf. -/
theorem IsFiniteType.of_coversTop (M : SheafOfModules.{v} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsFiniteType (M.over (X i))] :
    IsFiniteType M := by
  let D : ∀ i, (M.over (X i)).LocalGeneratorsData :=
    fun i => (M.over (X i)).localGeneratorsDataOfIsFiniteType
  refine ⟨LocalGeneratorsData.bind M X hX D, ?_⟩
  intro ij
  change Finite ((D ij.1).generators ij.2).I
  dsimp only [D]
  infer_instance

end SheafOfModules

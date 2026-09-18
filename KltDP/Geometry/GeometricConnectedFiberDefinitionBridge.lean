/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.Topology.Connected.Basic

/-!
# Original field-valued pullbacks and geometric fibers

This bounded specialization of the saved Mathlib geometric-property proof
uses only the pinned residue-field factorization and iterated-pullback
isomorphism. All schemes and test fields retain the same universe.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace KltDP.Geometry.GeometricConnectedFiberDefinitionBridge

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change of the original fiber is the original pullback along the
composite field-valued map to the base. -/
def fiberBaseChangeIso (y : Y) {Z : Scheme.{u}}
    (q : Z ⟶ Spec (Y.residueField y)) :
    pullback (f.fiberToSpecResidueField y) q ≅
      pullback f (q ≫ Y.fromSpecResidueField y) :=
  pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) q

/-- Connectedness is unchanged by the original iterated-pullback comparison. -/
theorem connectedSpace_fiberBaseChange_iff (y : Y) {Z : Scheme.{u}}
    (q : Z ⟶ Spec (Y.residueField y)) :
    ConnectedSpace (pullback (f.fiberToSpecResidueField y) q : Scheme.{u}) ↔
      ConnectedSpace (pullback f (q ≫ Y.fromSpecResidueField y) : Scheme.{u}) := by
  let e := Scheme.homeoOfIso (fiberBaseChangeIso f y q)
  constructor
  · intro h
    letI := h
    exact e.surjective.connectedSpace e.continuous
  · intro h
    letI := h
    exact e.symm.surjective.connectedSpace e.symm.continuous

/-- The raw all-field pullback condition is exactly geometric connectedness
of every original residue-field fiber, with no hypotheses on the morphism. -/
theorem forall_field_pullback_connected_iff_fibers :
    (∀ (K : Type u) [Field K] (q : Spec (CommRingCat.of K) ⟶ Y),
      ConnectedSpace (pullback f q : Scheme.{u})) ↔
    (∀ (y : Y) (K : Type u) [Field K]
        (q : Spec (CommRingCat.of K) ⟶ Spec (Y.residueField y)),
      ConnectedSpace (pullback (f.fiberToSpecResidueField y) q : Scheme.{u})) := by
  constructor
  · intro H y K _ q
    exact (connectedSpace_fiberBaseChange_iff f y q).mpr
      (H K (q ≫ Y.fromSpecResidueField y))
  · intro H K _ q
    obtain ⟨⟨y, φ⟩, hq⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective q
    change Spec.map φ ≫ Y.fromSpecResidueField y = q at hq
    rw [← hq]
    exact (connectedSpace_fiberBaseChange_iff f y (Spec.map φ)).mp
      (H y K (Spec.map φ))

end KltDP.Geometry.GeometricConnectedFiberDefinitionBridge

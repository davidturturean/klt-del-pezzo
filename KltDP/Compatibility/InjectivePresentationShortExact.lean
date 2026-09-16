/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison

Adapted from Mathlib 5aedf732b6987e8c26ab3c9ebc855314f82b045f,
CategoryTheory/Abelian/Injective/Resolution.lean:315–321.
The pinned cokernel universal property supplies the missing exact_cokernel API.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The short exact sequence of an actual injective presentation

The original presentation map and its actual categorical cokernel form the
sequence. Injectivity belongs to the given presentation; neither exactness
nor the cokernel is supplied as an additional assumption.
-/

noncomputable section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.InjectivePresentation

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The original monomorphism into an injective object, followed by its cokernel. -/
abbrev shortComplex (ip : InjectivePresentation X) : ShortComplex C :=
  ShortComplex.mk ip.f (cokernel.π ip.f) (cokernel.condition ip.f)

/-- Exactness follows from the actual cokernel universal property. -/
theorem shortExact_shortComplex (ip : InjectivePresentation X) :
    ip.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ip.f)
  mono_f := ip.mono
  epi_g := by
    change Epi (cokernel.π ip.f)
    infer_instance

end CategoryTheory.InjectivePresentation

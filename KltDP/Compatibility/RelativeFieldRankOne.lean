/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Only the four missing rank-one equivalences from official Mathlib commit
59e84018b299993f5d4ca6d8cb4012b08bc55241, Relrank.lean lines 96-102 and
338-342, are ported. Existing relative ranks and tower formulas are reused.
The original arbitrary subfields and intermediate fields are retained.
-/

noncomputable section
open Module Cardinal

namespace Subfield
variable {E : Type*} [Field E] {A B : Subfield E}

theorem relrank_eq_one_iff : relrank A B = 1 ↔ B ≤ A := by
  rw [relrank, IntermediateField.rank_eq_one_iff, ← IntermediateField.toSubfield_inj,
    extendScalars_toSubfield, IntermediateField.bot_toSubfield]
  change B = (A ⊓ B).subtype.fieldRange ↔ B ≤ A
  rw [fieldRange_subtype, right_eq_inf]

theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B ≤ A := by
  rw [relfinrank_eq_toNat_relrank, toNat_eq_one, relrank_eq_one_iff]

end Subfield

namespace IntermediateField
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {A B : IntermediateField F E}

theorem relrank_eq_one_iff : relrank A B = 1 ↔ B ≤ A :=
  Subfield.relrank_eq_one_iff

theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B ≤ A :=
  Subfield.relfinrank_eq_one_iff

end IntermediateField

#print axioms IntermediateField.relfinrank_eq_one_iff

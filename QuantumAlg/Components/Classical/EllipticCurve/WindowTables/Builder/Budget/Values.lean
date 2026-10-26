/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Budget

/-!
# Concrete parameter values of the independent table-construction ceiling

Only the sixteen binary levels and four tail levels are simplified here.
The table rows themselves remain behind the generic actual-loop bound.
These values cover one five-array build; window-base preparation and the
outer repeated schedule remain separately paid operations.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

/-- The zero-bit table contains only its five explicitly cleared identity entries. -/
lemma constructionBudget_zero (fieldWidth : Nat) : constructionBudget fieldWidth 0 = 5 := by
  simp [constructionBudget, BatchFrame.eventBudget]

/-- One full sixteen-bit five-array build over 256-bit field words. -/
lemma constructionBudget_full16 : constructionBudget 256 16 = 9087409 := by
  norm_num [constructionBudget, layerBudget, seedBudget, BatchFrame.eventBudget,
    Fin.sum_univ_succ]

/-- One four-bit tail five-array build over the same 256-bit field words. -/
lemma constructionBudget_tail4 : constructionBudget 256 4 = 56221 := by
  norm_num [constructionBudget, layerBudget, seedBudget, BatchFrame.eventBudget,
    Fin.sum_univ_succ]

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Resources
import Mathlib.Algebra.BigOperators.Fin

/-!
# Independent native-operation ceilings for five-array construction

These parameter formulas depend only on the public field and window widths.
They preserve the true empty batch, one initial seed, paid noninitial seed
doubling, every denominator/extension row and every final conversion write.
No bound is projected from a selected circuit's execution.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open scoped BigOperators

/-- A first seed is two paid writes; each later seed executes the actual shared-modulus doubling. -/
def seedBudget (fieldWidth level : Nat) : Nat :=
  if level = 0 then 2 else 30 * fieldWidth + 127

/-- Each nonseed row pays subtraction/write, its shared batch and actual affine extension. -/
def layerBudget (fieldWidth level : Nat) : Nat :=
  let count := 2 ^ level - 1
  seedBudget fieldWidth level + count * 7 + BatchFrame.eventBudget fieldWidth count + count * 41

/-- Complete independent ceiling for all actual layers and the final five-column conversion. -/
def constructionBudget (fieldWidth window : Nat) : Nat :=
  let count := 2 ^ window - 1
  (∑ level : Fin window, layerBudget fieldWidth level.val) + count * 12 +
    BatchFrame.eventBudget fieldWidth count + count * 53 + 5

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

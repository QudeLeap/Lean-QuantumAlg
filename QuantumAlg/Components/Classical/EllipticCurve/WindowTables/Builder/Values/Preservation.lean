/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Values

/-!
# Original certified table values survive protected complete-column reads

The certificate is about the actual returned Store. A subsequent actual
record that retains all five complete column values retains every original
row and the same original group-table certificate. No regenerated array
or mathematical replacement table is substituted for an executable read.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

/-- Equal whole original columns retain the same actual certified group table in the new Store. -/
lemma TableValue.of_column_reads {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width length : Nat} (curve : CurveSpec width) (frame : TableFrame ctx width length)
    (point : Point curve) (before after : Store ctx) (values : TableValue curve frame point before)
    (columns : ∀ column,
      after.read (.storage (frame.finishColumns column).toCStorageRef) =
        before.read (.storage (frame.finishColumns column).toCStorageRef)) :
    TableValue curve frame point after := by
  intro row column
  have retained := congrArg (fun value => value.get row) (columns column)
  exact retained.trans (values row column)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

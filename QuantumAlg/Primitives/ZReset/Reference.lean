/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Semantics
import all QuantumAlg.Primitives.ZReset.Semantics
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Measure.Instrument

/-!
# External reference preservation under the actual reset circuit

The circuit's measurement, classical write and read, and selected correction
preserve every entry of the external reference marginal. The proof uses the
same complete execution as the reset state theorem. It imposes no separation
between the selected system, other live systems, and the external reference.

The calculation combines the local projective measurement rule
[dW19, qcnotes.tex:5409,5420] with unitary conjugation
[dW19, qcnotes.tex:5405]. The reference observation traces out local systems,
including entangled inputs [dW19, qcnotes.tex:6827].

When the runtime has no borrowed classical cells or quantum systems, its
borrowed observation still retains the entire external reference. The final
lemma proves that actual observation is restored. It makes no claim about
resetting a borrowed target or restoring a nonempty borrowed interface.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual reset execution preserves every external reference matrix entry,
including off-diagonal correlations, after tracing out the live local systems. -/
public theorem zReset_reference_entry {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (refLeft refRight : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((circuit wire output).execute Reference state).quantumMarginal.matrix
        (basis, refLeft) (basis, refRight)) =
      ∑ basis : ctx.register.Index,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  rw [circuit_quantumMarginal]
  refine (ExecutionState.applyLocalUnitary_reference_entry
    (R := ctx.register) (Reference := Reference) _ _ refLeft refRight).trans ?_
  exact ExecutionState.measureZ_reference_entry ctx.quantumLayout wire state refLeft refRight

/-- In a context with no borrowed cells or wires, the reset circuit restores
the actual joint borrowed observation, which includes the full reference. -/
theorem zReset_borrowedRestored_noBorrowed {ctx : RuntimeCtx .quantum}
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = []) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    (circuit wire output).BorrowedRestored Reference state
      ((circuit wire output).execute Reference state) := by
  rw [Circuit.BorrowedRestored, Execution.observeBorrowedAfter_sameContext]
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [Execution.observeBorrowed_empty_entry noClassical noQuantum,
    Execution.observeBorrowed_empty_entry noClassical noQuantum]
  exact zReset_reference_entry wire output state refLeft refRight

end

end QuantumAlg.ZReset

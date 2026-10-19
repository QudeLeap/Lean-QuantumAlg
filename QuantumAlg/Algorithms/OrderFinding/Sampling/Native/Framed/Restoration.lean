/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Preservation of an existing classical input and its reference

The complete source sample acts only on fresh owned qubits and writable
classical cells. The original borrowed classical values remain correlated
with any external quantum reference exactly as at input.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

private lemma noBorrowedQuantum (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) : ctx.borrowedQuantumWires = [] := by
  have subset := ctx.borrowedQuantumWires_sublist
  rw [noQuantum] at subset
  exact List.sublist_nil.mp subset

/-- Every actual source-sample execution preserves the full borrowed joint state. -/
public lemma code_borrowedRestored (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat)
    (environment : (model t width).Environment) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((model t width).HiddenState × History)) :
    (code ctx noQuantum t width).BorrowedRestored Reference state
      ((code ctx noQuantum t width).execute environment Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code ctx noQuantum t width) environment
    (noBorrowedQuantum ctx noQuantum) Reference state

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed

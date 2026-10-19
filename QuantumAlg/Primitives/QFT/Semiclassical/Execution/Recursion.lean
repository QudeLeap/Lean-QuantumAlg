/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# The actual Fourier recursion executes its real stored measurement stage

Only mathematical path histories are reassociated. The complete physical
bank, original storage, all writable result cells and arbitrary reference
remain in the exact final-store equation. No alternative Fourier executor
or execution certificate is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum}

/-- The empty native recursion preserves each full stored quantum-reference block. -/
lemma code_zero_store {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool)
    (wires : Fin 0 ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (ExecutionState.filterClassical
      (((code inverse 0 wires qubits outputs).execute environment) Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical state
        (fun entry => entry.1 = stored)).quantumMarginal := by
  rw [code, Circuit.execute_id]
  calc
    _ = (ExecutionState.filterClassical
        (state.mapHistory (fun record => (record.1, (record.2, ()))))
        (fun entry => entry.1 = stored)).quantumMarginal := by
      apply congrArg (fun result : State ctx Reference
        (ClassicalOracleModel.empty.HiddenState × (History × Unit)) =>
          (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal)
      exact ExecutionState.executionState_mapClassical_congr state rfl
    _ = _ := State.mapHistory_store_marginal _ _ _

/-- The three literal native instructions already present in Construction. -/
def stageCode (inverse : Bool) {n : Nat} (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension)) :
    Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
  (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
    (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit)).seq
    ((Circuit.measureZ head result).seq (feedbackCode inverse tail tailQubits result))

/-- Literal stage plus continuation has the same full final-store state as the native schedule. -/
lemma stageCode_continuation_store {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount) (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    (continuation : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (ExecutionState.filterClassical
      ((((Circuit.unitary (allowAllocation := false)
          (operations := .empty) (classicalOracles := .empty)
          (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit)).seq
        ((Circuit.measureZ head result).seq
          ((feedbackCode inverse tail tailQubits result).seq continuation))).execute environment)
        Reference state) (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical
        ((continuation.execute environment) Reference
          (((stageCode inverse head headQubit tail tailQubits result).execute environment)
            Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal := by
  let leading : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
    .unitary (Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp head headQubit)
  let measured : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx false :=
    .measureZ head result
  let feedback := feedbackCode inverse tail tailQubits result
  calc
    _ = (ExecutionState.filterClassical
        (((measured.seq (feedback.seq continuation)).execute environment) Reference
          ((leading.execute environment) Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_store_marginal leading (measured.seq (feedback.seq continuation)) environment
        state stored
    _ = (ExecutionState.filterClassical
        ((((measured.seq feedback).seq continuation).execute environment) Reference
          ((leading.execute environment) Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_assoc_store_marginal measured feedback continuation environment
        ((leading.execute environment) Reference state) stored
    _ = (ExecutionState.filterClassical
        (((leading.seq ((measured.seq feedback).seq continuation)).execute environment)
          Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal :=
      (Circuit.seq_store_marginal leading ((measured.seq feedback).seq continuation) environment
        state stored).symm
    _ = (ExecutionState.filterClassical
        ((((leading.seq (measured.seq feedback)).seq continuation).execute environment)
          Reference state)
        (fun entry => entry.1 = stored)).quantumMarginal :=
      Circuit.seq_assoc_store_marginal leading (measured.seq feedback) continuation environment
        state stored
    _ = _ := Circuit.seq_store_marginal
      (leading.seq (measured.seq feedback)) continuation environment state stored

/-- One actual recursive call consumes the real head-stage output, with every cell retained. -/
lemma code_succ_store {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    let tail : Fin n ↪ Fin ctx.systemCount :=
      ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
    (ExecutionState.filterClassical
      (((code inverse (n + 1) wires qubits outputs).execute environment) Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      (ExecutionState.filterClassical
        (((code inverse n tail (fun i
          => qubits i.succ) (fun i => outputs i.succ)).execute environment)
          Reference (((stageCode inverse (wires 0) (qubits 0) tail
            (fun i => qubits i.succ) (outputs 0)).execute environment) Reference state))
        (fun entry => entry.1 = stored)).quantumMarginal := by
  dsimp only [code]
  exact stageCode_continuation_store inverse _ _ _ _ _ _ state stored

end

end QuantumAlg.QuantumFourierTransform.Semiclassical

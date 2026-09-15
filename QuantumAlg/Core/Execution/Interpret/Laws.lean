/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Measure.Instrument
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Control
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Classical.Call
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact equations for the single circuit interpreter

These equations expose the existing interpreter's actual state updates. Unitary
execution conjugates every complete quantum-reference block by the supplied
operator tensored with the reference identity [dW19, qcnotes.tex:5405]. Z
measurement retains the full projected block [dW19, qcnotes.tex:5409], writes its
observed value, and records that same outcome. Classical branches partition the
input by its actual stored values before interpreting their selected bodies.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem recordUnit_key_eq {C H : Type} (left : C × H) (value : C) (history : H) :
    (left.1, (left.2, ())) = (value, (history, ())) ↔ left = (value, history) := by
  constructor
  · intro equality
    exact Prod.ext (congrArg (fun input : C × (H × Unit) => input.1) equality)
      (congrArg (fun input : C × (H × Unit) => input.2.1) equality)
  · intro equality
    exact congrArg (fun input : C × H => (input.1, (input.2, ()))) equality

private theorem recordUnit_block {C H : Type} [Fintype C] [Fintype H]
    {R : Register} (state : ExecutionState (C × H) R) (value : C) (history : H) :
    (state.mapClassical fun input => (input.1, (input.2, ()))).block
      (value, (history, ())) = state.block (value, history) := by
  apply DensityOperator.ext
  change (∑ input : C × H,
    if (input.1, (input.2, ())) = (value, (history, ())) then
      (state.block input).matrix else 0) = (state.block (value, history)).matrix
  simp only [recordUnit_key_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H : Type} [Fintype H]

/-- Identity execution preserves live values and records its unique path. -/
theorem execute_id (state : State ctx Reference H) :
    (Circuit.id ctx).execute Reference state = state.skip := rfl

/-- The identity instruction preserves each complete quantum-reference block. -/
theorem execute_id_block (state : State ctx Reference H) (store : Store ctx) (history : H) :
    ((Circuit.id ctx).execute Reference state).block (store, (history, ())) =
      state.block (store, history) := by
  rw [execute_id]
  apply DensityOperator.ext
  simp only [State.skip, State.mapHistory, ExecutionState.mapClassical]
  rw [Finset.sum_eq_single (store, history)]
  · exact if_pos rfl
  · intro other _ different
    split
    · rename_i equality
      exact False.elim (different (Prod.ext
        (congrArg (fun input : Store ctx × (H × Unit) => input.1) equality)
        (congrArg (fun input : Store ctx × (H × Unit) => input.2.1) equality)))
    · rfl
  · intro absent
    exact False.elim (absent (Finset.mem_univ (store, history)))

/-- The public identity equation preserves every complete input block. -/
public theorem circuit_execute_id_block (state : State ctx Reference H)
    (store : Store ctx) (history : H) :
    ((Circuit.id ctx).execute Reference state).block (store, (history, ())) =
      state.block (store, history) := execute_id_block state store history

/-- Atomic classical execution uses the operation's actual read and write behavior. -/
theorem execute_classical (state : State ctx Reference H) {input output : CShape}
    (op : ClassicalOp input output ctx ctx) :
    (Circuit.classical op).execute Reference state = state.classicalStep op := rfl

/-- Overwritten classical values contribute their complete blocks to the written result. -/
theorem execute_classical_block_matrix (state : State ctx Reference H)
    {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (result : Store ctx × (H × Unit)) :
    (((Circuit.classical op).execute Reference state).block result).matrix =
      ∑ value : Store ctx × H,
        if (value.1.applyOp op, (value.2, ())) = result then
          (state.block value).matrix else 0 := rfl

open Classical in
/-- A public classical instruction equation reads and writes its actual typed references. -/
public theorem circuit_execute_classical_block_matrix (state : State ctx Reference H)
    {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (result : Store ctx × (H × Unit)) :
    (((Circuit.classical op).execute Reference state).block result).matrix =
      ∑ value : Store ctx × H,
        if (value.1.write op.outputRef (op.eval (value.1.read op.inputRef)),
          (value.2, ())) = result then (state.block value).matrix else 0 :=
  execute_classical_block_matrix state op result

/-- A declared classical instruction uses the same finite storage boundary as its declaration. -/
theorem execute_declaredCall (state : State ctx Reference H) {input output : CShape}
    (call : DeclaredClassicalCall ctx input output) :
    (Circuit.declaredCall call).execute Reference state = state.declaredStep call := rfl

/-- Conditional execution sums exactly the bodies selected by actual classical reads.
Each summand starts from the corresponding read fiber of the original state. -/
theorem execute_branch_block_matrix {post : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef ctx shape) (body : shape.Value → Circuit ctx post)
    (state : State ctx Reference H)
    (result : Store post × (H × (Circuit.branch input body).Path)) :
    (((Circuit.branch input body).execute Reference state).block result).matrix =
      ∑ value : shape.Value,
        ((((body value).execute Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).mapHistory
            (fun history => (history.1, ⟨value, history.2⟩))).block result).matrix := rfl

/-- Retaining a result cell uses its actual initialized store extension. -/
theorem execute_retain (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (Circuit.retain ctx key shape fresh).execute Reference state =
      state.mapClassical (fun value =>
        (value.1.pushRetained key shape fresh, (value.2, ()))) := rfl

/-- Composition executes both actual bodies and only reassociates the path record. -/
theorem execute_seq {middle post : RuntimeCtx kind}
    (first : Circuit ctx middle) (second : Circuit middle post) (state : State ctx Reference H) :
    (Circuit.seq first second).execute Reference state =
      (second.execute Reference (first.execute Reference state)).mapHistory
        (fun history => (history.1.1, (history.1.2, history.2))) := by
  simp only [execute, interpret]

section Quantum

variable {ctx : RuntimeCtx .quantum}

/-- The unitary instruction executes the supplied certified pure circuit. -/
theorem execute_unitary (state : State ctx Reference H)
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx) :
    (Circuit.unitary program placement).execute Reference state = state.unitary program := rfl

/-- The supplied unitary acts beside the identity on an arbitrary correlated reference. -/
theorem execute_unitary_block (state : State ctx Reference H)
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    (store : Store ctx) (history : H) :
    ((Circuit.unitary program placement).execute Reference state).block
      (store, (history, ())) =
        DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
          (state.block (store, history)) :=
  recordUnit_block (state.applyUnitary fun _ =>
    UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)) store history

/-- The complete output matrix is the exact lifted unitary conjugation.
The input may be mixed and entangled with the reference. -/
theorem execute_unitary_block_matrix (state : State ctx Reference H)
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    (store : Store ctx) (history : H) :
    (((Circuit.unitary program placement).execute Reference state).block
      (store, (history, ()))).matrix =
        let operator :=
          UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
        (operator : HilbertOperator (Register.prod ctx.register Reference)) *
          (state.block (store, history)).matrix *
            (operator : HilbertOperator (Register.prod ctx.register Reference)).conjTranspose := by
  rw [execute_unitary_block]
  exact DensityOperator.applyUnitary_matrix _ _

/-- Public exact unitary evolution keeps the complete external reference. -/
public theorem circuit_execute_unitary_block_matrix (state : State ctx Reference H)
    (program : UnitaryCircuit ctx.register) (placement : program.physical_idx = ctx.physicalIdx)
    (store : Store ctx) (history : H) :
    (((Circuit.unitary program placement).execute Reference state).block
      (store, (history, ()))).matrix =
        let operator :=
          UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)
        (operator : HilbertOperator (Register.prod ctx.register Reference)) *
          (state.block (store, history)).matrix *
            (operator : HilbertOperator (Register.prod ctx.register Reference)).conjTranspose :=
  execute_unitary_block_matrix state program placement store history

/-- Z execution measures the selected wire and writes the same observed result. -/
theorem execute_measureZ (state : State ctx Reference H) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    (Circuit.measureZ wire output).execute Reference state = State.measureZ state wire output := rfl

/-- Each measured output block sums precisely the input records that write that result.
The readout touches only the selected physical wire; the full reference remains in every block. -/
theorem execute_measureZ_block_matrix (state : State ctx Reference H)
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (result : Store ctx × (H × Fin (ctx.quantumLayout.wire wire).dimension)) :
    (((Circuit.measureZ wire output).execute Reference state).block result).matrix =
      ∑ value : (Store ctx × H) × Fin (ctx.quantumLayout.wire wire).dimension,
        if (value.1.1.write output (.finite value.2), (value.1.2, value.2)) = result then
          (ZMeasurement.branch (R := Register.prod ctx.register Reference)
            (fun basis => basis.1 wire) value.2 (state.block value.1)).matrix else 0 := rfl

open Classical in
/-- Public Z execution records exactly the outcome written to the actual classical register. -/
public theorem circuit_execute_measureZ_block_matrix (state : State ctx Reference H)
    (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (result : Store ctx × (H × Fin (ctx.quantumLayout.wire wire).dimension)) :
    (((Circuit.measureZ wire output).execute Reference state).block result).matrix =
      ∑ value : (Store ctx × H) × Fin (ctx.quantumLayout.wire wire).dimension,
        if (value.1.1.write output (.finite value.2), (value.1.2, value.2)) = result then
          (ZMeasurement.branch (R := Register.prod ctx.register Reference)
            (fun basis => basis.1 wire) value.2 (state.block value.1)).matrix else 0 :=
  execute_measureZ_block_matrix state wire output result

end Quantum

end

end QuantumAlg.Circuit

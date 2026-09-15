/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Random

/-!
# Context-bound instruction state updates

The live context determines the classical store and the complete quantum
register together. A finite mathematical history records execution choices;
physical memory consists exactly of the context's entries. Each primitive
below preserves probability mass and performs its actual typed storage update.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- One complete context-bound state with a finite mathematical execution history. -/
public abbrev State {kind : ProblemKind} (ctx : RuntimeCtx kind) (Reference : Register)
    (History : Type) [Fintype History] :=
  ExecutionState (Store ctx × History) (Register.prod ctx.register Reference)

namespace State

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Reorganize only the mathematical execution history. -/
def mapHistory (state : State ctx Reference H) (f : H → K) : State ctx Reference K :=
  state.mapClassical fun value => (value.1, f value.2)

theorem mapHistory_mass (state : State ctx Reference H) (f : H → K) :
    (state.mapHistory f).mass = state.mass :=
  state.mapClassical_mass _

/-- Record the unique path of a deterministic instruction without changing any live value. -/
def skip (state : State ctx Reference H) : State ctx Reference (H × Unit) :=
  state.mapHistory fun history => (history, ())

theorem skip_mass (state : State ctx Reference H) : (skip state).mass = state.mass :=
  mapHistory_mass state _

/-- Atomic classical execution reads its actual operands and writes the computed result. -/
def classicalStep (state : State ctx Reference H) {input output : CShape}
    (op : ClassicalOp input output ctx ctx) : State ctx Reference (H × Unit) :=
  state.mapClassical fun value => (value.1.applyOp op, (value.2, ()))

theorem classicalStep_mass (state : State ctx Reference H) {input output : CShape}
    (op : ClassicalOp input output ctx ctx) :
    (classicalStep state op).mass = state.mass :=
  state.mapClassical_mass _

/-- A declared call uses the same typed read and write boundary as an atomic operation. -/
def declaredStep (state : State ctx Reference H) {input output : CShape}
    (call : DeclaredClassicalCall ctx input output) : State ctx Reference (H × Unit) :=
  state.mapClassical fun value =>
    (value.1.write call.outputRef (call.eval (value.1.read call.inputRef)), (value.2, ()))

theorem declaredStep_mass (state : State ctx Reference H) {input output : CShape}
    (call : DeclaredClassicalCall ctx input output) :
    (declaredStep state call).mass = state.mass :=
  state.mapClassical_mass _

/-- Allocate a retained classical cell while preserving the entire existing quantum register. -/
def retain (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    State (ctx.addRetained key shape fresh) Reference (H × Unit) :=
  state.mapClassical fun value => (value.1.pushRetained key shape fresh, (value.2, ()))

theorem retain_mass (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (retain state key shape fresh).mass = state.mass :=
  state.mapClassical_mass _

/-- Enter a lexical classical workspace, keeping the same quantum register and history. -/
def pushWorkspace (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    State (ctx.addWorkspace key shape fresh) Reference H :=
  state.mapClassical fun value => (value.1.pushWorkspace key shape fresh, value.2)

theorem pushWorkspace_mass (state : State ctx Reference H)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (pushWorkspace state key shape fresh).mass = state.mass :=
  state.mapClassical_mass _

/-- Exit the exact classical workspace; summing overwritten cells retains their probabilities. -/
def popWorkspace (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference H) : State ctx Reference H :=
  state.mapClassical fun value => (Store.popWorkspace key shape fresh value.1, value.2)

theorem popWorkspace_mass (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference H) :
    (popWorkspace key shape fresh state).mass = state.mass :=
  state.mapClassical_mass _

/-- Generate and store the actual uniform bit string, recording its finite outcome. -/
def randomBits (state : State ctx Reference H)
    (width : Nat) (output : CWriteRef ctx (.bits width)) :
    State ctx Reference (H × Fin (2 ^ width)) :=
  (uniformChoice state ⟨2 ^ width, Nat.two_pow_pos width⟩).mapClassical fun value =>
    (value.1.1.write output (.bits fun index => value.2.val.testBit (width - 1 - index.val)),
      (value.1.2, value.2))

theorem randomBits_mass (state : State ctx Reference H) (width : Nat)
    (output : CWriteRef ctx (.bits width)) :
    (randomBits state width output).mass = state.mass := by
  exact (ExecutionState.mapClassical_mass _ _).trans
    (uniformChoice_mass state ⟨2 ^ width, Nat.two_pow_pos width⟩)

section Quantum

variable {ctx : RuntimeCtx .quantum}

/-- Apply the instruction's actual unitary to the complete context register. -/
def unitary (state : State ctx Reference H) (program : UnitaryCircuit ctx.register) :
    State ctx Reference (H × Unit) :=
  (state.applyUnitary fun _ =>
    UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference)).mapClassical
      fun value => (value.1, (value.2, ()))

theorem unitary_mass (state : State ctx Reference H) (program : UnitaryCircuit ctx.register) :
    (unitary state program).mass = state.mass := by
  simp only [unitary, ExecutionState.mapClassical_mass, ExecutionState.applyUnitary_mass]

/-- Measure the actual wire, write its actual result, and retain every quantum system. -/
def measureZ (state : State ctx Reference H) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    State ctx Reference (H × Fin (ctx.quantumLayout.wire wire).dimension) :=
  (ExecutionState.measureZ state fun basis => basis.1 wire).mapClassical fun value =>
    (value.1.1.write output (.finite value.2), (value.1.2, value.2))

theorem measureZ_mass (state : State ctx Reference H) (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension)) :
    (measureZ state wire output).mass = state.mass := by
  simp only [measureZ, ExecutionState.mapClassical_mass, ExecutionState.measureZ_mass]

/-- Prepare disjoint systems and identify their exact tensor coordinates with the new context. -/
def prepare (state : State ctx Reference H) (key : StorageKey) {systemCount : Nat}
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    State (ctx.addOwnedLayout key layout fresh disjoint) Reference (H × Unit) :=
  (prepareContext state key layout fresh disjoint preparation.normalized).mapClassical
    fun value => (value.1.pushOwnedLayout key layout fresh disjoint, (value.2, ()))

theorem prepare_mass (state : State ctx Reference H) (key : StorageKey) {systemCount : Nat}
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    (prepare state key layout fresh disjoint preparation).mass = state.mass := by
  exact (ExecutionState.mapClassical_mass _ _).trans
    (prepareContext_mass state key layout fresh disjoint preparation.normalized)

end Quantum

end State

end

end QuantumAlg.Execution

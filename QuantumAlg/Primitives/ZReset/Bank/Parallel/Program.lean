/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Bank.Parallel.Scope
public import QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction
public import QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Scope
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Bank reset with parent storage and one selected parallel correction

The fixed body writes every bank outcome to its own supplied scalar cell,
then reads that actual vector to select one disjoint native X layer. Only
the parent owns allocation: it opens one scratch scope per bank wire and
removes all scratch after correction. No original classical cell is
modified. A zero-width bank is the actual identity with no scratch.
-/

namespace QuantumAlg.ZReset.BankParallel

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {width : Nat} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- A fixed measurement body writes all outcomes into the distinct supplied real cells. -/
@[implicit_reducible]
def measure {allowAllocation : Bool}
    (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx allowAllocation :=
  Circuit.measurementSequence (allowAllocation := allowAllocation)
    (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells)

/-- Real stored outcomes select the parallel native correction on the same physical bank. -/
@[implicit_reducible]
def selected {allowAllocation : Bool}
    (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx allowAllocation :=
  .branch (QubitReadouts.input cells) (fun value =>
    .unitary (Correction.program ctx.quantumLayout qubits oracles
      (fun wire => QubitReadouts.mask value (positions.symm wire))))

/-- The allocation-free child consumes parent-provided scalar result storage. -/
@[implicit_reducible]
def body {allowAllocation : Bool}
    (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx allowAllocation :=
  .seq (measure (allowAllocation := allowAllocation) positions qubits cells)
    (selected (allowAllocation := allowAllocation) positions qubits cells)

/-- All qubit dimensions survive the parent's actual scalar workspace scopes. -/
lemma work_qubits (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (wire : Fin (Workspace.context ctx ctx.systemCount).systemCount) :
    ((Workspace.context ctx ctx.systemCount).quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (Workspace.wireEquiv ctx ctx.systemCount).surjective wire
  exact (congrArg QuantumWire.dimension
    (Workspace.wireEquiv_preserved ctx ctx.systemCount original)).trans (qubits original)

/-- The parent scopes precede the entire fixed body and preserve all original live entries. -/
def code (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx :=
  if ctx.systemCount = 0 then
    .id (model := .quantum AlgorithmGate.model oracles operations services) ctx
  else
    Workspace.scope (model := .quantum AlgorithmGate.model oracles operations services)
      ctx ctx.systemCount
      (body (allowAllocation := true) (Workspace.wireEquiv ctx ctx.systemCount)
        (work_qubits qubits) (Workspace.reference ctx ctx.systemCount))

/-- Every original bank wire and classical result remains in the complete final manifest. -/
def run (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    AlgorithmRun (.quantum AlgorithmGate.model oracles operations services) ctx ctx .unit where
  code := code (oracles := oracles) qubits operations services
  output := Output.all ctx .unit

/-- The empty bank has neither a lexical scratch allocation nor an artificial correction. -/
lemma code_zero (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (empty : ctx.systemCount = 0) :
    code (oracles := oracles) qubits operations services =
      .id (model := .quantum AlgorithmGate.model oracles operations services) ctx := by
  simp only [code, if_pos empty]

/-- A nonempty parent executes its real scalar scopes and the complete fixed reset body. -/
lemma code_nonzero (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) (nonempty : ctx.systemCount ≠ 0) :
    code (oracles := oracles) qubits operations services =
      Workspace.scope (model := .quantum AlgorithmGate.model oracles operations services)
        ctx ctx.systemCount
        (body (allowAllocation := true) (Workspace.wireEquiv ctx ctx.systemCount)
          (work_qubits qubits) (Workspace.reference ctx ctx.systemCount)) := by
  simp only [code, if_neg nonempty]

/-- Scope exit removes only parent-owned scratch from the output listing. -/
lemma output_listing (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2) :
    (run (oracles := oracles) qubits operations services).output.listing = ctx.keys := rfl

end

end QuantumAlg.ZReset.BankParallel

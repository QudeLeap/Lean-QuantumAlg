/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax

/-!
# Actual chronological Store and native paths of retained adder outcomes

Each vent writes its actual finite physical outcome into the supplied existing
cell. Each later phase path contains the value read from the resulting Store.
The full chronological paths remain retained even if later measurements
overwrite a cell. No extra execution state or storage allocation is introduced
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Only a vent contributes a physical outcome; native and selected-phase instructions are fixed. -/
def PhysicalOutcome (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Instruction encoding records → Type
  | .native _ => Unit
  | .vent target _ => Fin (ctx.quantumLayout.wire
      (EncodedBit.MeasuredUncompute.placedWire target physical ctx sameWires)).dimension
  | .phase _ _ => Unit

instance physicalOutcomeFintype (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (instruction : Instruction encoding records) :
    Fintype (instruction.PhysicalOutcome physical sameWires) := by
  cases instruction <;> dsimp [PhysicalOutcome] <;> infer_instance

/-- The exact real Store update and full native Path for one retained physical outcome. -/
def actualRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (instruction : Instruction encoding records) (store : Store ctx) :
    instruction.PhysicalOutcome physical sameWires → Store ctx ×
      (instruction.circuit (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output).Path :=
  match instruction with
  | .native _ => fun _ => (store, ())
  | .vent target record => fun outcome =>
      (store.write (finiteOutput
        (EncodedBit.MeasuredUncompute.placedWire_qubit target physical ctx sameWires)
        (output record)) (.finite outcome), ((), (outcome, ⟨.finite outcome, ()⟩)))
  | .phase _ record => fun _ =>
      (store, ⟨store.read (.storage (output record).toCStorageRef), ()⟩)

/-- Exactly the physical outcomes of the supplied native instruction word, in source order. -/
def WordOutcomes (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    List (Instruction encoding records) → Type
  | [] => Unit
  | instruction :: rest =>
      instruction.PhysicalOutcome physical sameWires × WordOutcomes physical sameWires rest

instance wordOutcomesFintype (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    (word : List (Instruction encoding records)) →
      Fintype (WordOutcomes physical sameWires word)
  | [] => inferInstanceAs (Fintype Unit)
  | instruction :: rest =>
      @instFintypeProd _ _ (physicalOutcomeFintype physical sameWires instruction)
        (wordOutcomesFintype physical sameWires rest)

/-- Every phase consumes the Store left by the preceding actual chronological writes. -/
def wordActualRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    (word : List (Instruction encoding records)) → Store ctx →
      WordOutcomes physical sameWires word → Store ctx ×
        (wordCircuit (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output word).Path
  | [], store, _ => (store, ())
  | instruction :: rest, store, outcomes =>
      let first := instruction.actualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output store outcomes.1
      let next := wordActualRecord physical sameWires output rest first.1 outcomes.2
      (next.1, (first.2, next.2))

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

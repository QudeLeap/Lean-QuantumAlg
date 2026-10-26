/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage.Finite

/-!
# Actual measured words preserve every separate retained classical cell

Only the supplied physical vent bank is overwritten. Every actual original
Store and chronological measurement record therefore preserves reads from
all other original cells, including earlier retained exponent outputs
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every real record leaves a read from a physically different cell unchanged. -/
lemma wordActualRecord_read_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    {shape : CShape} (observed : CStorageRef ctx shape)
    (separate : ∀ index, (output index).key ≠ observed.key) :
    ∀ (word : List (Instruction encoding records)) (store : Store ctx)
      (measured : WordOutcomes physical sameWires word),
    (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output word store measured).1.read (.storage observed) =
        store.read (.storage observed) := by
  intro word
  induction word with
  | nil => intro store measured; rfl
  | cons instruction rest ih =>
      intro store measured
      rw [wordActualRecord]
      change (wordActualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output rest
          (instruction.actualRecord (oracles := oracles) (operations := operations)
            (services := services) physical sameWires output store measured.1).1 measured.2).1.read
              (.storage observed) = _
      rw [ih]
      cases instruction with
      | native gates => rfl
      | phase target record => rfl
      | vent target record =>
          exact Store.read_write_other store _ observed _ (by
            rw [finiteOutput_key]
            exact separate record)

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

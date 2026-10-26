/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage.Finite

/-!
# Actual chronological physical outcome writes of a compiled instruction word

Only actual vent instructions change classical storage. Each retained physical
outcome is cast to the declared qubit value in the same supplied cell. Native
and Store-selected phase instructions retain that Store exactly. No condition
on an original caller Store is imposed [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- The actual physical measurement values and their supplied record indices, in word order. -/
def outcomeWrites (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    (word : List (Instruction encoding records)) →
      WordOutcomes physical sameWires word → List (Fin records × Fin 2)
  | [], _ => []
  | .native _ :: rest, outcomes => outcomeWrites physical sameWires rest outcomes.2
  | .vent target record :: rest, outcomes =>
      (record,
        EncodedBit.MeasuredUncompute.placedOutcome target physical ctx sameWires outcomes.1) ::
        outcomeWrites physical sameWires rest outcomes.2
  | .phase _ _ :: rest, outcomes => outcomeWrites physical sameWires rest outcomes.2

/-- Apply the same chronological finite-value writes to the same supplied existing cells. -/
def writeOutcomes (output : Fin records → CWriteRef ctx (.finite 2)) :
    Store ctx → List (Fin records × Fin 2) → Store ctx
  | store, [] => store
  | store, pair :: rest =>
      writeOutcomes output (store.write (output pair.1) (.finite pair.2)) rest

/-- The actual retained word record has precisely its chronological physical outcome Store. -/
lemma wordActualRecord_store (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2)) :
    ∀ (word : List (Instruction encoding records)) (store : Store ctx)
      (outcomes : WordOutcomes physical sameWires word),
    (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output word store outcomes).1 =
      writeOutcomes output store (outcomeWrites physical sameWires word outcomes) := by
  intro word
  induction word with
  | nil => intro store outcomes; rfl
  | cons instruction rest ih =>
      intro store outcomes
      change (wordActualRecord (oracles := oracles) (operations := operations)
        (services := services) physical sameWires output rest
        (instruction.actualRecord (oracles := oracles) (operations := operations)
          (services := services) physical sameWires output store outcomes.1).1 outcomes.2).1 = _
      rw [ih]
      cases instruction with
      | native gates => rfl
      | vent target record =>
          rw [actualRecord_vent_store]
          rfl
      | phase target record => rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

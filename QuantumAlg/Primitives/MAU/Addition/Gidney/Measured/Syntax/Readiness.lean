/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Transport
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Paid phase reads are supplied by preceding actual measurements

The readiness condition is syntactic: a phase reads only a cell already
written, or a cell explicitly known at entry. Actual physical measurement
outcomes and distinct destination keys then establish the chronological
operator-consistency condition for every original caller Store
[G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Every paid phase reads a preceding physical measurement or an explicitly available cell. -/
def ReadyWord : (Fin records → Prop) → List (Instruction encoding records) → Prop
  | _, [] => True
  | ready, .native _ :: rest => ReadyWord ready rest
  | ready, .vent _ record :: rest =>
      ReadyWord (fun index => index = record ∨ ready index) rest
  | ready, .phase _ record :: rest => ready record ∧ ReadyWord ready rest

/-- Actual physical writes and syntactic readiness establish every actual stored phase selection. -/
lemma wordConsistent_of_ready (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx records) (outcome : Fin records → Fin 2) :
    ∀ (word : List (Instruction encoding records)) (store : Store ctx)
      (measured : WordOutcomes physical sameWires word) (ready : Fin records → Prop),
    ReadyWord ready word →
    (∀ index, ready index →
      (store.read (.storage (bank.output index).toCStorageRef)).toFin = outcome index) →
    (∀ entry ∈ outcomeWrites physical sameWires word measured, entry.2 = outcome entry.1) →
    WordConsistent (oracles := oracles) (operations := operations) (services := services)
      physical sameWires bank.output outcome word store measured := by
  intro word
  induction word with
  | nil => intro store measured ready _ _ _; trivial
  | cons instruction rest ih =>
      intro store measured ready available reads consistent
      change instruction.PhysicalOutcome physical sameWires ×
        WordOutcomes physical sameWires rest at measured
      rcases measured with ⟨firstMeasured, restMeasured⟩
      cases instruction with
      | native gates =>
          refine ⟨trivial, ?_⟩
          exact ih store restMeasured ready available reads consistent
      | vent target record =>
          let value := EncodedBit.MeasuredUncompute.placedOutcome target physical ctx sameWires
            firstMeasured
          have sameValue : value = outcome record :=
            consistent (record, value) (List.mem_cons_self)
          refine ⟨sameValue, ?_⟩
          change WordConsistent (oracles := oracles) (operations := operations)
            (services := services) physical sameWires bank.output outcome rest
            ((Instruction.vent target record).actualRecord (oracles := oracles)
              (operations := operations) (services := services) physical sameWires bank.output
                store firstMeasured).1 restMeasured
          rw [actualRecord_vent_store]
          apply ih _ restMeasured (fun index => index = record ∨ ready index) available
          · intro index accessible
            by_cases same : record = index
            · subst index
              rw [bank.read_write_same]
              exact sameValue
            · rw [bank.read_write_other store record index same]
              exact reads index (accessible.resolve_left (Ne.symm same))
          · intro entry present
            exact consistent entry (List.mem_cons_of_mem _ present)
      | phase target record =>
          refine ⟨reads record available.1, ?_⟩
          exact ih store restMeasured ready available.2 reads consistent

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

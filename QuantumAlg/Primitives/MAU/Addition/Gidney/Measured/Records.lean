/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Records
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Assignment
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Readiness
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Records

/-!
# Every actual chronological measured-adder record uses its own retained assignment

The complete literal word writes each record exactly once before either paid
phase pass. Distinct physical bank keys and the actual physical outcome list
therefore discharge all Store-read consistency conditions on every original
caller Store. No assumption on old bank values is introduced
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open Execution Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Proof-side retained values extracted from the actual chronological physical measurement word. -/
def retainedOutcome (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : WordOutcomes physical sameWires (layout.adderWord wide constant)) :
    Fin (width - 2) → Fin 2 :=
  retainedAssignment (outcomeWrites physical sameWires (layout.adderWord wide constant) measured)

/-- Every actual physical outcome word is consistent with all subsequent actual paid phase reads. -/
lemma adderWord_consistent (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (bank : RecordBank ctx (width - 2)) (store : Store ctx)
    (measured : WordOutcomes physical sameWires (layout.adderWord wide constant)) :
    WordConsistent (oracles := oracles) (operations := operations) (services := services)
      physical sameWires bank.output
        (layout.retainedOutcome wide constant physical sameWires measured)
        (layout.adderWord wide constant) store measured := by
  apply wordConsistent_of_ready physical sameWires bank _ _ store measured (fun _ => False)
    (adderWord_ready layout wide constant)
  · intro index impossible
    exact impossible.elim
  · apply retainedAssignment_consistent
    rw [outcomeWrites_indices, adderWord_ventIndices]
    exact List.nodup_ofFn_ofInjective (fun _ _ same => same)

/-- The actual complete source word has precisely two outcomes per original physical vent. -/
lemma adderWord_outcomes_card (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    Fintype.card (WordOutcomes physical sameWires (layout.adderWord wide constant)) =
      2 ^ (width - 2) := by
  rw [wordOutcomes_card, adderWord_ventIndices, List.length_ofFn]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Execution
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record

/-!
# Actual chronological outcome and Store composition at instruction-word append

Each subword retains its own physical measurement outcomes. Its successor
starts from the actual Store left by that subword, including overwritten
record cells. The operator factorization therefore permits physical record
reuse without identifying different measurements or supplying a free phase
assignment [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open Execution

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Join the two actual outcome words in their original physical source order. -/
def appendOutcomes (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    (first second : List (Instruction encoding records)) →
      WordOutcomes physical sameWires first → WordOutcomes physical sameWires second →
        WordOutcomes physical sameWires (first ++ second)
  | [], _, _, second => second
  | _instruction :: rest, second, firstOutcomes, secondOutcomes =>
      (firstOutcomes.1, appendOutcomes physical sameWires rest second
        firstOutcomes.2 secondOutcomes)

/-- Split a real concatenated outcome word at its original source boundary. -/
def splitOutcomes (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) :
    (first second : List (Instruction encoding records)) →
      WordOutcomes physical sameWires (first ++ second) →
        WordOutcomes physical sameWires first × WordOutcomes physical sameWires second
  | [], _, outcomes => ((), outcomes)
  | _instruction :: rest, second, outcomes =>
      let lower := splitOutcomes physical sameWires rest second outcomes.2
      ((outcomes.1, lower.1), lower.2)

/-- Splitting preserves every individual chronological physical outcome of both subwords. -/
lemma splitOutcomes_appendOutcomes (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (first second : List (Instruction encoding records))
    (firstOutcomes : WordOutcomes physical sameWires first)
    (secondOutcomes : WordOutcomes physical sameWires second) :
    splitOutcomes physical sameWires first second
        (appendOutcomes physical sameWires first second firstOutcomes secondOutcomes) =
      (firstOutcomes, secondOutcomes) := by
  induction first with
  | nil =>
      change Unit at firstOutcomes
      cases firstOutcomes
      rfl
  | cons instruction rest ih =>
      change ((firstOutcomes.1,
        (splitOutcomes physical sameWires rest second
          (appendOutcomes physical sameWires rest second firstOutcomes.2 secondOutcomes)).1),
        (splitOutcomes physical sameWires rest second
          (appendOutcomes physical sameWires rest second firstOutcomes.2 secondOutcomes)).2) = _
      rw [ih]
      rfl

/-- Every real concatenated outcome is exactly the join of its two chronological parts. -/
lemma appendOutcomes_splitOutcomes (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (first second : List (Instruction encoding records))
    (outcomes : WordOutcomes physical sameWires (first ++ second)) :
    appendOutcomes physical sameWires first second
      (splitOutcomes physical sameWires first second outcomes).1
      (splitOutcomes physical sameWires first second outcomes).2 = outcomes := by
  induction first with
  | nil => rfl
  | cons instruction rest ih =>
      change (outcomes.1,
        appendOutcomes physical sameWires rest second
          (splitOutcomes physical sameWires rest second outcomes.2).1
          (splitOutcomes physical sameWires rest second outcomes.2).2) = outcomes
      rw [ih]
      rfl

/-- The finite actual outcome family is the exact product of its chronological subfamilies. -/
def appendOutcomesEquiv (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (first second : List (Instruction encoding records)) :
    WordOutcomes physical sameWires first × WordOutcomes physical sameWires second ≃
      WordOutcomes physical sameWires (first ++ second) where
  toFun outcomes := appendOutcomes physical sameWires first second outcomes.1 outcomes.2
  invFun := splitOutcomes physical sameWires first second
  left_inv _outcomes := splitOutcomes_appendOutcomes physical sameWires first second _ _
  right_inv := appendOutcomes_splitOutcomes physical sameWires first second

/-- The second actual subword starts with the Store left by the first actual physical record. -/
lemma wordActualRecord_append_store (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (first second : List (Instruction encoding records)) (store : Store ctx)
    (firstOutcomes : WordOutcomes physical sameWires first)
    (secondOutcomes : WordOutcomes physical sameWires second) :
    (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output (first ++ second) store
      (appendOutcomes physical sameWires first second firstOutcomes secondOutcomes)).1 =
    (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
      physical sameWires output second
      (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output first store firstOutcomes).1 secondOutcomes).1 := by
  induction first generalizing store with
  | nil => rfl
  | cons instruction rest ih =>
      exact ih _ firstOutcomes.2

/-- Exact retained native products compose at the same actual intermediate Store. -/
lemma wordActualKraus_append (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin records → CWriteRef ctx (.finite 2))
    (environment : oracles.Interpretation) (Reference : Register)
    (first second : List (Instruction encoding records)) (store : Store ctx)
    (firstOutcomes : WordOutcomes physical sameWires first)
    (secondOutcomes : WordOutcomes physical sameWires second) :
    wordActualKraus (operations := operations) (services := services)
      physical sameWires output environment Reference (first ++ second) store
      (appendOutcomes physical sameWires first second firstOutcomes secondOutcomes) =
    wordActualKraus (operations := operations) (services := services)
      physical sameWires output environment Reference second
      (wordActualRecord (oracles := oracles) (operations := operations) (services := services)
        physical sameWires output first store firstOutcomes).1 secondOutcomes *
      wordActualKraus (operations := operations) (services := services)
        physical sameWires output environment Reference first store firstOutcomes := by
  induction first generalizing store with
  | nil =>
      simp only [List.nil_append, appendOutcomes, wordActualRecord, wordActualKraus, mul_one]
  | cons instruction rest ih =>
      simp only [List.cons_append, appendOutcomes, wordActualKraus, wordActualRecord]
      rw [ih]
      exact mul_assoc _ _ _

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

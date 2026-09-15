/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ShiftResources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources

/-!
# Independent native initialization resource bounds

The emitted source initialization first performs the real comparison
and fold, retaining Iter, then measures the current folded payload's
binary length with reversible zero predicates and writes the original
finite length register [LYL+26, sec_EEA/sub_4phase.tex:104-117]. No input
label is used to prefill its length or choose which candidates to emit.

The bounds count every actual leading-position candidate and every
selected bit of its fixed length label. The source ordering correction
and the actual original-width gate lists are unchanged by this owner.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitializationResources

noncomputable section

open EncodedBit

/-- A full leading-one length write tests all positions and at most every length-label bit. -/
def lengthBound (width : Nat) : Nat := width * (width.size * (12 * width + 2))

/-- Independent envelope for the actual comparison, flag X, bi-flip, and complete length writer. -/
def bound (width : Nat) : Nat :=
  Addition.Gidney.comparisonEventBound (width + 3) + 1 +
    Addition.Gidney.biFlipEventBound (width + 3) + lengthBound width

private theorem prefix_length (width count : Nat) (within : count ≤ width)
    (output : Fin width.size) :
    (InitialLengthPredicate.gates width output count within).length ≤ 6 * count + 1 := by
  cases count with
  | zero =>
    simp only [InitialLengthPredicate.gates, List.length_cons, List.length_nil]
    omega
  | succ previous =>
    cases previous with
    | zero =>
      simp only [InitialLengthPredicate.gates, List.length_cons, List.length_nil]
      omega
    | succ tail =>
      rw [InitialLengthPredicate.gates, Word.ZeroTestLayout.borrowedZeroGates_length]
      split_ifs <;> omega

private theorem firstOne_length (width : Nat) (index : Fin width) (output : Fin width.size) :
    (InitialLengthPredicate.firstOneGates width index output).length ≤ 12 * width + 2 := by
  have first := prefix_length width index.val index.isLt.le output
  have second := prefix_length width (index.val + 1) index.isLt output
  have within := index.isLt
  rw [InitialLengthPredicate.firstOneGates, List.length_append]
  omega

private theorem bits_length (width : Nat) (index : Fin width) (bits : List (Fin width.size)) :
    (bits.flatMap fun bit => InitialLengthPredicate.firstOneGates width index bit.rev).length ≤
      bits.length * (12 * width + 2) := by
  induction bits with
  | nil => simp
  | cons bit rest inductionHypothesis =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have current := firstOne_length width index bit.rev
    omega

private theorem position_length (width : Nat) (index : Fin width) :
    (InitialLengthWrite.positionGates width index).length ≤ width.size * (12 * width + 2) :=
  (bits_length width index _).trans
    (Nat.mul_le_mul_right (12 * width + 2)
      (Word.constantOneIndices_length_le (InitialLengthWrite.positionConstant width index)))

private theorem positions_length (width : Nat) (indices : List (Fin width)) :
    (indices.flatMap (InitialLengthWrite.positionGates width)).length ≤
      indices.length * (width.size * (12 * width + 2)) := by
  induction indices with
  | nil => simp
  | cons index rest inductionHypothesis =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have current := position_length width index
    omega

/-- Every emitted native leading-bit predicate and output-bit toggle is counted. -/
theorem length_gates_le (width : Nat) :
    (InitialLengthWrite.gates width).length ≤ lengthBound width := by
  have actual := positions_length width (List.ofFn fun index : Fin width => index)
  simpa only [List.length_ofFn, InitialLengthWrite.gates, lengthBound] using actual

/-- The actual fold retains the complete comparison and reflected-word event ledgers. -/
theorem fold_trace_le (modulus : Nat) :
    (FoldSourceProgram.program modulus).eventTrace.length ≤
      Addition.Gidney.comparisonEventBound (modulus.size + 3) + 1 +
        Addition.Gidney.biFlipEventBound (modulus.size + 3) := by
  have comparison := Addition.Gidney.gidneyComparison_event_count_bound
    (FoldSourceProgram.wordWidth modulus) (FoldSourceProgram.comparisonPivot modulus)
  have reflection := Addition.Gidney.gidneyBiFlip_event_count_bound
    (FoldSourceProgram.wordWidth modulus) (FoldSourceProgram.reflectionPivot modulus)
  rw [ShiftResources.trace_count, FoldSourceProgram.program_eventCost,
    Multiset.card_add, Multiset.card_add, Addition.Gidney.gidneyFlagFlip_eventCost]
  simp only [ResourcePool.singleton, Multiset.card_replicate]
  change _ ≤ Addition.Gidney.comparisonEventBound (FoldSourceProgram.wordWidth modulus) + 1 +
    Addition.Gidney.biFlipEventBound (FoldSourceProgram.wordWidth modulus)
  omega

/-- Independent resource envelope for the same actual initial fold and current-length write. -/
theorem program_trace_le (modulus : Nat) :
    (InitialFrame.program modulus).eventTrace.length ≤ bound modulus.size := by
  have fold := fold_trace_le modulus
  have write := length_gates_le modulus.size
  rw [InitialFrame.program_eventTrace, List.length_append, InitialLengthWrite.program,
    GateSpec.programList_eventTrace, List.length_map, bound]
  omega

/-- Strict unit depth and literal event pool both meet the independent initialization bound. -/
theorem program_resources (modulus : Nat) :
    (InitialFrame.program modulus).eventCost.card ≤ bound modulus.size ∧
      (InitialFrame.program modulus).evaluatedEventDepth (fun _ => 1) ≤ bound modulus.size := by
  have count := (ShiftResources.trace_count (InitialFrame.program modulus)).symm.le.trans
    (program_trace_le modulus)
  exact ⟨count, (ShiftResources.unitDepth_le_count _).trans count⟩

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitializationResources

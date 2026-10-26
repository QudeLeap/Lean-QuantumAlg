/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Predicates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Length.Write

/-!
# Exact native coordinates of the actual initial leading-length writer

Every possible leading payload position executes two complete physical
zero-prefix tests for every set bit of its fixed length label. Numerical
evaluation visits these public indices and constant bits, without
expanding the actual native gate list or assuming an input-dependent flag.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

open EncodedBit

/-- Exact Toffoli coordinate of a literal restored dirty-work zero-prefix word. -/
def prefixToffoli : Nat → Nat
  | 0 => 0
  | 1 => 0
  | tail + 2 => if tail = 0 then 1 else 4 * tail

/-- Only the actual one-bit zero-prefix test contains a CNOT. -/
def prefixCnot (count : Nat) : Nat := if count = 1 then 1 else 0

/-- Empty and one-bit predicates have one X; wider predicates retain both complete masks. -/
def prefixSingleQubit (count : Nat) : Nat := if count ≤ 1 then 1 else 2 * count

private lemma prefix_counts (width count : Nat) (within : count ≤ width)
    (output : Fin width.size) :
    ((InitialLengthPredicate.gates width output count within).map
        GateSpec.toffoliMultiplicity).sum = prefixToffoli count ∧
      ((InitialLengthPredicate.gates width output count within).map
        GateSpec.cnotMultiplicity).sum = prefixCnot count ∧
      ((InitialLengthPredicate.gates width output count within).map
        GateSpec.xMultiplicity).sum = prefixSingleQubit count := by
  cases count with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ previous =>
      cases previous with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ tail =>
          have actual := borrowed_zero_counts
            (InitialLengthPredicate.longLayout width tail within output)
          simpa only [InitialLengthPredicate.gates, prefixToffoli, prefixCnot,
            prefixSingleQubit, show ¬tail + 2 = 1 by omega,
            show ¬tail + 2 ≤ 1 by omega, if_false] using actual

private lemma flatMap_weight {Index Gate : Type} (indices : List Index)
    (word : Index → List Gate) (weight : Gate → Nat) :
    ((indices.flatMap word).map weight).sum =
      (indices.map fun index => ((word index).map weight).sum).sum := by
  induction indices with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]

private lemma position_weight (width : Nat) (index : Fin width)
    (weight : GateSpec (SharedEEA.encoding width) → Nat) (prefixCount : Nat → Nat)
    (actual : ∀ output : Fin width.size, ∀ count : Nat, ∀ within : count ≤ width,
      ((InitialLengthPredicate.gates width output count within).map weight).sum =
        prefixCount count) :
    ((InitialLengthWrite.positionGates width index).map weight).sum =
      (Word.constantOneIndices (InitialLengthWrite.positionConstant width index)).length *
        (prefixCount index.val + prefixCount (index.val + 1)) := by
  rw [InitialLengthWrite.positionGates, flatMap_weight]
  simp only [InitialLengthPredicate.firstOneGates, List.map_append, List.sum_append, actual]
  simp

/-- One candidate's numerical contribution, with its fixed binary length bits retained. -/
def initialLengthTerm (width : Nat) (prefixCount : Nat → Nat) (index : Nat) : Nat :=
  (Word.constantOneIndices
    (InitialLengthWrite.constant width (width - index) (Nat.sub_le _ _))).length *
      (prefixCount index + prefixCount (index + 1))

/-- Numerical sum over actual leading positions and set bits of each fixed length. -/
def initialLengthCount (width : Nat) (prefixCount : Nat → Nat) : Nat :=
  ((List.ofFn fun index : Fin width => index).map fun index =>
    initialLengthTerm width prefixCount index.val).sum

private lemma initialLengthCount_sum (width : Nat) (prefixCount : Nat → Nat) :
    initialLengthCount width prefixCount =
      ∑ index ∈ Finset.range width, initialLengthTerm width prefixCount index := by
  rw [initialLengthCount, List.map_ofFn, Fin.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (initialLengthTerm width prefixCount) width

private lemma block_sum (value : Nat → Nat) (width blocks : Nat) :
    (∑ index ∈ Finset.range (width * blocks), value index) =
      ∑ block ∈ Finset.range blocks,
        ∑ index ∈ Finset.range width, value (width * block + index) := by
  induction blocks with
  | zero => simp
  | succ blocks inductionHypothesis =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, inductionHypothesis]

/-- Every native occurrence follows the actual candidate traversal, independently of input. -/
lemma initial_length_source_counts (width : Nat) :
    ((InitialLengthWrite.gates width).map GateSpec.toffoliMultiplicity).sum =
        initialLengthCount width prefixToffoli ∧
      ((InitialLengthWrite.gates width).map GateSpec.cnotMultiplicity).sum =
        initialLengthCount width prefixCnot ∧
      ((InitialLengthWrite.gates width).map GateSpec.xMultiplicity).sum =
        initialLengthCount width prefixSingleQubit := by
  simp only [InitialLengthWrite.gates, flatMap_weight, initialLengthCount]
  refine ⟨?_, ?_, ?_⟩
  · simp only [position_weight _ _ _ prefixToffoli
      (fun output count within => (prefix_counts width count within output).1),
      initialLengthTerm, InitialLengthWrite.positionConstant]
  · simp only [position_weight _ _ _ prefixCnot
      (fun output count within => (prefix_counts width count within output).2.1),
      initialLengthTerm, InitialLengthWrite.positionConstant]
  · simp only [position_weight _ _ _ prefixSingleQubit
      (fun output count within => (prefix_counts width count within output).2.2),
      initialLengthTerm, InitialLengthWrite.positionConstant]

/-- Closed exact native coordinates of the complete actual width-256 initial writer. -/
lemma p256_initial_length_source_counts :
    ((InitialLengthWrite.gates 256).map GateSpec.toffoliMultiplicity).sum = 909871 ∧
      ((InitialLengthWrite.gates 256).map GateSpec.cnotMultiplicity).sum = 9 ∧
      ((InitialLengthWrite.gates 256).map GateSpec.xMultiplicity).sum = 463098 := by
  have actual := initial_length_source_counts 256
  have numeric : initialLengthCount 256 prefixToffoli = 909871 ∧
      initialLengthCount 256 prefixCnot = 9 ∧
      initialLengthCount 256 prefixSingleQubit = 463098 := by
    simp only [initialLengthCount_sum]
    rw [block_sum (initialLengthTerm 256 prefixToffoli) 32 8,
      block_sum (initialLengthTerm 256 prefixCnot) 32 8,
      block_sum (initialLengthTerm 256 prefixSingleQubit) 32 8]
    decide
  simpa only [numeric.1, numeric.2.1, numeric.2.2] using actual

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

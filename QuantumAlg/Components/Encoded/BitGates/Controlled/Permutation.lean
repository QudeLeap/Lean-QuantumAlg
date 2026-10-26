/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin
import all QuantumAlg.Util.Permutation.Transpositions

/-!
# Native controlled finite wire permutations

Every static transposition is a one-Toffoli, two-CNOT Fredkin on original
positions. The common quantum control creates actual sequential dependencies;
neither a free wire permutation nor a fresh workspace is introduced.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

open Permutation

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- Original target positions and their separate original quantum control. -/
structure PermutationFrame (encoding : BinaryLabelEncoding Data) (size : Nat) where
  control : EncodedBit encoding
  bit : Fin size → EncodedBit encoding
  distinct : Function.Injective (fun index => (bit index).wire)
  separate : ∀ index, control.wire ≠ (bit index).wire

namespace PermutationFrame

private lemma targets_ne (frame : PermutationFrame encoding size)
    (exchange : Transposition (Fin size)) :
    (frame.bit exchange.first).wire ≠ (frame.bit exchange.second).wire :=
  fun same => exchange.different (frame.distinct same)

/-- Literal native Fredkin words in the static factor order. -/
def gates (frame : PermutationFrame encoding size) :
    List (Transposition (Fin size)) → List (GateSpec encoding)
  | [] => []
  | exchange :: rest =>
      fredkinGates frame.control (frame.bit exchange.first) (frame.bit exchange.second)
        (frame.separate _) (frame.separate _) (frame.targets_ne exchange) ++ frame.gates rest

/-- Unconditional mathematical action of the same ordered coordinate exchanges. -/
def swapAction (frame : PermutationFrame encoding size) :
    List (Transposition (Fin size)) → Data → Data
  | [] => id
  | exchange :: rest => fun state =>
      frame.swapAction rest (swapStep (frame.bit exchange.first) (frame.bit exchange.second)
        (frame.targets_ne exchange) state)

private lemma swap_get (frame : PermutationFrame encoding size)
    (exchange : Transposition (Fin size)) (index : Fin size) (state : Data) :
    (frame.bit index).get (swapStep (frame.bit exchange.first) (frame.bit exchange.second)
      (frame.targets_ne exchange) state) =
        (frame.bit (exchange.permutation index)).get state := by
  by_cases first : index = exchange.first
  · subst index
    simpa only [Transposition.permutation, Equiv.swap_apply_left] using
      swapStep_get_left _ _ (frame.targets_ne exchange) state
  · by_cases second : index = exchange.second
    · subst index
      simpa only [Transposition.permutation, Equiv.swap_apply_right] using
        swapStep_get_right _ _ (frame.targets_ne exchange) state
    · rw [swapStep_get_observed_of_swap_ne _ _ _ (frame.targets_ne exchange)
        (fun same => first (frame.distinct same).symm)
        (fun same => second (frame.distinct same).symm)]
      rw [Transposition.permutation, Equiv.swap_apply_of_ne_of_ne first second]

/-- The readout product keeps the same chronological order as the native gate list. -/
lemma swapAction_get (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (index : Fin size) (state : Data) :
    (frame.bit index).get (frame.swapAction exchanges state) =
      (frame.bit ((exchanges.map Transposition.permutation).prod index)).get state := by
  induction exchanges generalizing index state with
  | nil => rfl
  | cons exchange rest ih =>
      change (frame.bit index).get (frame.swapAction rest _) = _
      rw [ih, frame.swap_get]
      rfl

/-- Lowering acts exactly as the full ordered permutation on the selected control branch. -/
lemma gates_step (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (state : Data) :
    GateSpec.stepList (frame.gates exchanges) state =
      if frame.control.get state then frame.swapAction exchanges state else state := by
  induction exchanges generalizing state with
  | nil => simp [gates, swapAction, GateSpec.stepList]
  | cons exchange rest ih =>
      rw [gates, GateSpec.stepList_append, fredkin_step_eq_if]
      split
      next selected =>
        rw [ih, swapStep_get_observed_of_swap_ne _ _ _ (frame.targets_ne exchange)
          (frame.separate _).symm (frame.separate _).symm, if_pos selected]
        rfl
      next inactive => rw [ih, if_neg inactive]

/-- Complete ket semantics follow from the actual emitted elementary instructions. -/
lemma realizes (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size)))
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList physical oracles (frame.gates exchanges)) environment
      (fun state => if frame.control.get state then frame.swapAction exchanges state else state) :=
  GateSpec.realizesList_congrStep physical oracles _ (frame.gates_step exchanges) environment

/-- Full quantum control selects the requested fixed permutation without truncating any index. -/
lemma fixed_permutation_get (frame : PermutationFrame encoding size)
    (permutation : Equiv.Perm (Fin size)) (index : Fin size) (state : Data) :
    (frame.bit index).get (GateSpec.stepList (frame.gates (transpositions permutation)) state) =
      if frame.control.get state then (frame.bit (permutation index)).get state
      else (frame.bit index).get state := by
  rw [frame.gates_step]
  split
  · rw [frame.swapAction_get, transpositions_product]
  · rfl

/-- The common-control sequence charges one Toffoli and two CNOTs per actual exchange. -/
lemma gates_counts (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) :
    ((frame.gates exchanges).map GateSpec.toffoliMultiplicity).sum = exchanges.length ∧
      ((frame.gates exchanges).map GateSpec.cnotMultiplicity).sum = 2 * exchanges.length ∧
      (frame.gates exchanges).length = 3 * exchanges.length := by
  induction exchanges with
  | nil => simp [gates]
  | cons exchange rest ih =>
      constructor
      · rw [gates, List.map_append, List.sum_append, fredkin_toffoli_count, ih.1]
        simp [Nat.add_comm]
      constructor
      · rw [gates, List.map_append, List.sum_append, fredkin_cnot_count, ih.2.1]
        simp only [List.length_cons]
        omega
      · rw [gates, List.length_append, ih.2.2]
        change 3 + 3 * rest.length = 3 * (rest.length + 1)
        omega

/-- The actual fixed permutation word has linear native size on the unchanged carrier. -/
lemma fixed_length_le (frame : PermutationFrame encoding size)
    (permutation : Equiv.Perm (Fin size)) :
    (frame.gates (transpositions permutation)).length ≤ 3 * size := by
  rw [(frame.gates_counts _).2.2]
  exact Nat.mul_le_mul_left 3 (by simpa using transpositions_length_le permutation)

end PermutationFrame

end

end QuantumAlg.EncodedBit

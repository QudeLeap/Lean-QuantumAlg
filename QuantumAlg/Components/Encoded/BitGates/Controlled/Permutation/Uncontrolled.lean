/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Preservation
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# Paid unconditional permutations on the same original physical word

The frame supplies its existing target coordinates and their separation.
Its control is not read or written by this three-CNOT lowering. Every
transposition is emitted and charged, including public unit rotations.
-/

namespace QuantumAlg.EncodedBit.PermutationFrame

noncomputable section

open Permutation

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- The actual three-CNOT word for each static exchange, in chronological order. -/
def uncontrolledGates (frame : PermutationFrame encoding size) :
    List (Transposition (Fin size)) → List (GateSpec encoding)
  | [] => []
  | exchange :: rest =>
      swapGates (frame.bit exchange.first) (frame.bit exchange.second)
        (frame.targets_ne exchange) ++ frame.uncontrolledGates rest

/-- All original labels follow the complete exchange action of the actual native instructions. -/
lemma uncontrolledGates_step (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (state : Data) :
    GateSpec.stepList (frame.uncontrolledGates exchanges) state =
      frame.swapAction exchanges state := by
  induction exchanges generalizing state with
  | nil => rfl
  | cons exchange rest ih =>
      rw [uncontrolledGates, GateSpec.stepList_append, ih]
      rfl

/-- Each original output position reads exactly the requested public permutation. -/
lemma uncontrolled_fixed_get (frame : PermutationFrame encoding size)
    (permutation : Equiv.Perm (Fin size)) (index : Fin size) (state : Data) :
    (frame.bit index).get
        (GateSpec.stepList (frame.uncontrolledGates (transpositions permutation)) state) =
      (frame.bit (permutation index)).get state := by
  rw [frame.uncontrolledGates_step, frame.swapAction_get, transpositions_product]

/-- Every original position outside the complete target word retains its arbitrary value. -/
lemma uncontrolled_get_outside (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList (frame.uncontrolledGates exchanges) state) =
      observed.get state := by
  rw [frame.uncontrolledGates_step]
  exact frame.swapAction_get_outside exchanges observed outside state

/-- Public permutation lowering emits three CNOTs and no Toffolis per actual exchange. -/
lemma uncontrolled_counts (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) :
    ((frame.uncontrolledGates exchanges).map GateSpec.toffoliMultiplicity).sum = 0 ∧
      ((frame.uncontrolledGates exchanges).map GateSpec.cnotMultiplicity).sum =
        3 * exchanges.length ∧
      (frame.uncontrolledGates exchanges).length = 3 * exchanges.length := by
  induction exchanges with
  | nil => simp [uncontrolledGates]
  | cons exchange rest ih =>
      simp only [uncontrolledGates, List.map_append, List.sum_append, List.length_append,
        swapGates, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        GateSpec.toffoliMultiplicity_cnot, GateSpec.cnotMultiplicity_cnot, List.length_cons,
        List.length_nil, ih.1, ih.2.1, ih.2.2]
      omega

/-- The fixed native word pays its own gates and sequential duration on the unchanged carrier. -/
lemma uncontrolled_resources (frame : PermutationFrame encoding size)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (GateSpec.programList physical oracles
          (frame.uncontrolledGates (transpositions permutation))).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (GateSpec.programList physical oracles
          (frame.uncontrolledGates (transpositions permutation))).eventCost ≤ 3 * size ∧
      (GateSpec.programList physical oracles
        (frame.uncontrolledGates (transpositions permutation))).evaluatedEventDepth
          Resource.Event.quantumDuration ≤ 3 * size := by
  rw [GateSpec.programList_toffoli_count_eq_sum, GateSpec.programList_cnot_count_eq_sum,
    GateSpec.programList_quantumTime]
  have counts := frame.uncontrolled_counts (transpositions permutation)
  have bounded : (transpositions permutation).length ≤ size := by
    simpa only [Fintype.card_fin] using transpositions_length_le permutation
  exact ⟨counts.1, counts.2.1.trans_le (Nat.mul_le_mul_left 3 bounded),
    counts.2.2.trans_le (Nat.mul_le_mul_left 3 bounded)⟩

end

end QuantumAlg.EncodedBit.PermutationFrame

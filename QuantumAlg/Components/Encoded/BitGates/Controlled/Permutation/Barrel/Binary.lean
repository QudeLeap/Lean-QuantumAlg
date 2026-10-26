/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Readout
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Resources
import all QuantumAlg.Util.Nat.FixedWidth.BitSum

/-! # Actual binary barrel stages retain the complete original metadata displacement -/

namespace QuantumAlg.EncodedBit.PermutationBarrel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- Exactly one real controlled public power for every original little-endian metadata bit. -/
def binaryStages (controls : Nat) : List (Fin controls × Nat) :=
  (List.finRange controls).map (fun index => (index, 2 ^ index.val))

private lemma amount_eq_sum (barrel : PermutationBarrel encoding size controls)
    (stages : List (Fin controls × Nat)) (state : Data) :
    barrel.amount stages state =
      (stages.map
        (fun stage => if (barrel.control stage.1).get state then stage.2 else 0)).sum := by
  induction stages with
  | nil => rfl
  | cons stage rest ih => simp only [amount, List.map_cons, List.sum_cons, ih]

/-- Complete finite metadata, including values outside algorithm trajectories, are untruncated. -/
lemma binary_amount (barrel : PermutationBarrel encoding size controls)
    (word : BitVec controls) (state : Data)
    (reads : ∀ index, (barrel.control index).get state = word.getLsbD index.val) :
    barrel.amount (binaryStages controls) state = word.toNat := by
  rw [amount_eq_sum, binaryStages, List.map_map]
  simp only [Function.comp_def, reads, BitVec.getLsbD]
  have indices := List.map_coe_finRange_eq_range (n := controls)
  have mapped := congrArg
    (fun entries : List Nat =>
      entries.map (fun index => if word.toNat.testBit index then 2 ^ index else 0)) indices
  rw [List.map_map] at mapped
  simp only [Function.comp_def] at mapped
  rw [mapped, ← Nat.FixedWidth.BitSum.prefix_eq_range_sum, Nat.FixedWidth.BitSum.prefix_toNat]

/-- Every real output coordinate has exactly the full finite original binary displacement. -/
lemma binary_bit_get (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (word : BitVec controls) (state : Data)
    (reads : ∀ index, (barrel.control index).get state = word.getLsbD index.val)
    (index : Fin size) :
    (barrel.bit index).get
        (GateSpec.stepList (barrel.gates permutation (binaryStages controls)) state) =
      (barrel.bit ((permutation ^ word.toNat) index)).get state := by
  rw [barrel.gates_bit_get, barrel.binary_amount word state reads]

/-- The same binary word charges all native stages and their actual sequential duration. -/
lemma binary_resources (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (barrel.program permutation (binaryStages controls) physical oracles).eventCost
        ≤ size * controls ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (barrel.program permutation (binaryStages controls) physical oracles).eventCost
        ≤ 2 * size * controls ∧
      (barrel.program permutation (binaryStages controls) physical oracles).evaluatedEventDepth
        Resource.Event.quantumDuration ≤ 3 * size * controls := by
  simpa only [binaryStages, List.length_map, List.length_finRange] using
    barrel.program_resources permutation (binaryStages controls) physical oracles

end

end QuantumAlg.EncodedBit.PermutationBarrel

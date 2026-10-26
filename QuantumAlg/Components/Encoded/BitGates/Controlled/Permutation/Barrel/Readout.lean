/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel

/-! # Complete readouts and untouched complements of actual native barrel permutations -/

namespace QuantumAlg.EncodedBit.PermutationBarrel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- Every coordinate outside the complete word survives each actual stage. -/
lemma stage_get_outside (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat)
    (observed : EncodedBit encoding)
    (outside : ∀ index, (barrel.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList (barrel.stageGates permutation stage) state) =
      observed.get state :=
  (barrel.frame stage.1).gates_get_outside _ observed outside state

/-- Original controls are retained even when the same control occurs in several stages. -/
lemma stage_control_get (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat)
    (index : Fin controls) (state : Data) :
    (barrel.control index).get (GateSpec.stepList (barrel.stageGates permutation stage) state) =
      (barrel.control index).get state :=
  barrel.stage_get_outside permutation stage _ (fun word => (barrel.separate index word).symm)
    state

/-- The full original metadata displacement does not change during any executed stage. -/
lemma amount_stage (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat)
    (stages : List (Fin controls × Nat)) (state : Data) :
    barrel.amount stages (GateSpec.stepList (barrel.stageGates permutation stage) state) =
      barrel.amount stages state := by
  induction stages with
  | nil => rfl
  | cons current rest ih => rw [amount, amount, barrel.stage_control_get, ih]

/-- Every original outside bit survives the entire actual native barrel word. -/
lemma gates_get_outside (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (observed : EncodedBit encoding)
    (outside : ∀ index, (barrel.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList (barrel.gates permutation stages) state) =
      observed.get state := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage rest ih =>
      rw [gates, GateSpec.stepList_append, ih, barrel.stage_get_outside]
      exact outside

/-- Every output word bit reads exactly the original bit at the full controlled displacement. -/
lemma gates_bit_get (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (index : Fin size) (state : Data) :
    (barrel.bit index).get (GateSpec.stepList (barrel.gates permutation stages) state) =
      (barrel.bit ((permutation ^ barrel.amount stages state) index)).get state := by
  induction stages generalizing index state with
  | nil => rfl
  | cons stage rest ih =>
      rw [gates, GateSpec.stepList_append, ih, barrel.amount_stage]
      have current : (barrel.bit ((permutation ^ barrel.amount rest state) index)).get
          (GateSpec.stepList (barrel.stageGates permutation stage) state) =
          if (barrel.control stage.1).get state then
            (barrel.bit ((permutation ^ stage.2)
              ((permutation ^ barrel.amount rest state) index))).get state
          else (barrel.bit ((permutation ^ barrel.amount rest state) index)).get state :=
        (barrel.frame stage.1).fixed_permutation_get (permutation ^ stage.2) _ state
      rw [current]
      by_cases selected : (barrel.control stage.1).get state = true
      · simp only [selected, if_true, amount, pow_add, Equiv.Perm.mul_apply]
      · rw [if_neg selected, amount, if_neg selected, Nat.zero_add]

end

end QuantumAlg.EncodedBit.PermutationBarrel

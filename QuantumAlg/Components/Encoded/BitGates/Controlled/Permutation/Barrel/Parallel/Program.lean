/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Parallel.Frame

/-! # Actual two-word barrel interleave with full original metadata and operator semantics -/

namespace QuantumAlg.EncodedBit.PermutationBarrelParallel.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

def stageProgram (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (frame.pairFrame stage.1).program physical oracles
    (Permutation.transpositions (permutation ^ stage.2))

/-- All declared stages execute at runtime, retaining their full original control values. -/
def program (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) : List (Fin controls × Nat) →
      UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model oracles physical.toQuantum
  | stage :: rest => (frame.stageProgram physical oracles permutation stage).seq
      (frame.program physical oracles permutation rest)

private lemma left_gates_right_stage_comm (frame : Frame encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (stage : Fin controls × Nat) (state : Data) :
    GateSpec.stepList (frame.left.gates permutation stages)
        (GateSpec.stepList (frame.rightBarrel.stageGates permutation stage) state) =
      GateSpec.stepList (frame.rightBarrel.stageGates permutation stage)
        (GateSpec.stepList (frame.left.gates permutation stages) state) := by
  induction stages generalizing state with
  | nil => rfl
  | cons head rest ih =>
      have one := (frame.left.frame head.1).gates_comm (frame.rightBarrel.frame stage.1)
        (Permutation.transpositions (permutation ^ head.2))
        (Permutation.transpositions (permutation ^ stage.2)) frame.cross
        (frame.rightControl head.1) (frame.left.separate stage.1) state
      change GateSpec.stepList (frame.left.stageGates permutation head)
          (GateSpec.stepList (frame.rightBarrel.stageGates permutation stage) state) =
        GateSpec.stepList (frame.rightBarrel.stageGates permutation stage)
          (GateSpec.stepList (frame.left.stageGates permutation head) state) at one
      simp only [PermutationBarrel.gates, GateSpec.stepList_append]
      rw [one]
      exact ih _

/-- Two complete original words retain every bit, control and complementary quantum amplitude. -/
lemma program_realizes (frame : Frame encoding size controls)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles permutation stages)
      environment (GateSpec.stepList (frame.serialGates permutation stages)) := by
  induction stages with
  | nil => exact UnitaryCircuit.Realizes.identityAt _ _ encoding physical environment
  | cons stage rest ih =>
      have head := (frame.pairFrame stage.1).program_realizes physical oracles
        (Permutation.transpositions (permutation ^ stage.2)) environment
      rw [frame.stage_source permutation stage] at head
      apply (head.seq ih).congrStep
      intro state
      have commute := left_gates_right_stage_comm frame permutation rest stage
        (GateSpec.stepList (frame.left.stageGates permutation stage) state)
      have actual := congrArg
        (GateSpec.stepList (frame.rightBarrel.gates permutation rest)) commute
      simpa only [serialGates, PermutationBarrel.gates, GateSpec.stepList_append] using actual

end

end QuantumAlg.EncodedBit.PermutationBarrelParallel.Frame

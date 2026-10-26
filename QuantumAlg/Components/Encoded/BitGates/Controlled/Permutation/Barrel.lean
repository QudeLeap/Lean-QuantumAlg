/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Preservation

/-!
# Native barrel permutations controlled by unchanged quantum metadata

Each public stage contains an original control coordinate and a fixed
power of one public wire permutation. Its actual Fredkin word executes
regardless of the control value. The controls may repeat; every control
is physically outside the complete permuted word. No address decoding,
host selection, workspace allocation, or free permutation is introduced.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

/-- A complete original word and original quantum controls outside all of its positions. -/
structure PermutationBarrel {Data : Type} (encoding : BinaryLabelEncoding Data)
    (size controls : Nat) where
  bit : Fin size → EncodedBit encoding
  control : Fin controls → EncodedBit encoding
  distinct : Function.Injective (fun index => (bit index).wire)
  separate : ∀ controlIndex wordIndex, (control controlIndex).wire ≠ (bit wordIndex).wire

namespace PermutationBarrel

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- Each stage uses the same complete physical word and its actual original control. -/
def frame (barrel : PermutationBarrel encoding size controls) (index : Fin controls) :
    PermutationFrame encoding size where
  bit := barrel.bit
  control := barrel.control index
  distinct := barrel.distinct
  separate := barrel.separate index

/-- Every fixed power is compiled to the actual ordered Fredkin transposition word. -/
def stageGates (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat) :
    List (GateSpec encoding) :=
  (barrel.frame stage.1).gates (Permutation.transpositions (permutation ^ stage.2))

/-- All stages execute in their declared public order on the same physical systems. -/
def gates (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) : List (Fin controls × Nat) → List (GateSpec encoding)
  | [] => []
  | stage :: rest => barrel.stageGates permutation stage ++ barrel.gates permutation rest

/-- Independent natural displacement reads the complete original quantum controls. -/
def amount (barrel : PermutationBarrel encoding size controls) :
    List (Fin controls × Nat) → Data → Nat
  | [], _ => 0
  | stage :: rest, state =>
      (if (barrel.control stage.1).get state then stage.2 else 0) + barrel.amount rest state

/-- Literal native execution without any newly allocated system. -/
def program (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (barrel.gates permutation stages)

/-- The exact full-state action is that of every emitted elementary instruction. -/
lemma program_realizes (barrel : PermutationBarrel encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat))
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (barrel.program permutation stages physical oracles)
      environment (GateSpec.stepList (barrel.gates permutation stages)) :=
  GateSpec.realizesList physical oracles _ environment

end PermutationBarrel

end

end QuantumAlg.EncodedBit

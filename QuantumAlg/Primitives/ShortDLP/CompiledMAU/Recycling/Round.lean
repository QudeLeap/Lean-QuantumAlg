/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.SuffixResources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Weighted

/-!
# One stored-parameter member with paid packing and complete same-bank restart

The classical frame
already contains its parameter and distinct packed-result destination.
The branch reads that real parameter, executes both recycled-control streams
on the persistent accumulator, materializes the frequency-ordered bits with
one actual classical instruction, then measures and reloads the whole bank.
The reset's temporary classical capacity remains a separate charged peak.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Round

noncomputable section

variable {environment : model.Environment}

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The existing stored parameter selects actual arithmetic, rather than a supplied sample. -/
def selected {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ) :
    Circuit model (Context base noQuantum m ell width) (Context base noQuantum m ell width) :=
  .branch parameter fun value =>
    member base noQuantum m ell width N (generator value) (target value)

/-- Exactly the real member and real width-indexed pack precede restart. -/
def sampled {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell))) :
    Circuit model (Context base noQuantum m ell width) (Context base noQuantum m ell width) :=
  (selected base noQuantum m ell width parameter N generator target).seq
    (Packing.code base noQuantum m ell width result)

/-- Every round actually resets and reloads after packing, including the final round. -/
def code {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell))) :
    Circuit model (Context base noQuantum m ell width) (Context base noQuantum m ell width) :=
  (sampled base noQuantum m ell width parameter N generator target result).seq
    (Reload.resetReload base noQuantum m ell width N)

/-- An independent complete quantum allowance includes arithmetic, feedback, reset and reload. -/
def quantumTimeLimit (m ell width N : Nat) : Nat :=
  Resources.memberTime m ell width +
    (1 + EncodedBit.Word.BasisLoad.xCount (seedLabel width N))

/-- The same complete live output observes the actual charged result destination. -/
def run {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell))) :
    AlgorithmRun model (Context base noQuantum m ell width) (Context base noQuantum m ell width)
      (.bits (resultBits m ell)) where
  code := code base noQuantum m ell width parameter N generator target result
  output := Output.all (Context base noQuantum m ell width)
    (.read (.storage result.toCStorageRef))

/-- All syntactic branches pay the same source-only member allowance. -/
lemma selected_quantumTime {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (path : (selected base noQuantum m ell width parameter N generator target).Path) :
    (selected base noQuantum m ell width parameter N generator target).quantumTime path ≤
      Resources.memberTime m ell width :=
  Resources.member_time base noQuantum m ell width N
    (generator path.1) (target path.1) path.2

/-- The paid pack adds an actual classical event and zero quantum time. -/
lemma sampled_quantumTime {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    (path : (sampled base noQuantum m ell width parameter N generator target result).Path) :
    (sampled base noQuantum m ell width parameter N generator target result).quantumTime path ≤
      Resources.memberTime m ell width := by
  have memberBound := selected_quantumTime base noQuantum m ell width
    parameter N generator target path.1
  have packingTime := Packing.recyclingPacking_quantumTime base noQuantum m ell width
    result path.2
  change (selected base noQuantum m ell width parameter N generator target).quantumTime path.1 +
    (Packing.code base noQuantum m ell width result).quantumTime path.2 ≤ _
  rw [packingTime, Nat.add_zero]
  exact memberBound

/-- Sequential whole-round time includes full-bank restart after both exponent streams. -/
lemma code_quantumTime {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    (path : (code base noQuantum m ell width parameter N generator target result).Path) :
    (code base noQuantum m ell width parameter N generator target result).quantumTime path ≤
      quantumTimeLimit m ell width N :=
  Nat.add_le_add (sampled_quantumTime base noQuantum m ell width
    parameter N generator target result path.1)
    (Reload.recyclingResetReload_quantumTime base noQuantum m ell width N path.2)

/-- Every branch and incoming mixed state ends with the internally established same-bank seed. -/
lemma code_seeded {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (Reload.seed base noQuantum m ell width N)
      ((code base noQuantum m ell width parameter N generator target result).execute environment
        Reference state) :=
  BasisSeeded.seq (environment := environment)
    (sampled base noQuantum m ell width parameter N generator target result)
    (Reload.resetReload base noQuantum m ell width N)
    (Reload.seed base noQuantum m ell width N) state
    (Reload.recyclingResetReload_seeded base noQuantum m ell width N _)

/-- Reset does not alter any stored-outcome-weighted reference block produced by paid packing. -/
lemma code_referenceFiberSum_afterPack {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (weight : Store (Context base noQuantum m ell width) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width parameter N generator target result).execute environment
        Reference state) (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((sampled base noQuantum m ell width parameter N generator target result).execute
          environment
          Reference state) (fun entry _ => weight entry.1) leftRef rightRef := by
  rw [code, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  exact Reload.recyclingResetReload_referenceFiberSum base noQuantum m ell width N _
    weight leftRef rightRef

/-- The complete result manifest lists every parameter, packed outcome, result bit and bank wire. -/
lemma output_listing {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell))) :
    (run base noQuantum m ell width parameter N generator target result).output.listing =
      (Context base noQuantum m ell width).keys := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Round

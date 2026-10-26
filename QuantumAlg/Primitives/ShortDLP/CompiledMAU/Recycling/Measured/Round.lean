/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Reload
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Weighted

/-!
# One actual selected measured member, paid packing and complete same-bank restart

The stored classical parameter selects its real member program. Both original
exponent streams execute on the same frame. A paid native instruction writes
their frequency bits into the caller's real destination before the entire
bank is measured and reloaded, including after the final member. Reset
scratch cells are real parent lexical storage [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MeasuredRoundCtx := context base noQuantum m ell width

/-- The real stored parameter selects actual static measured arithmetic and the same output bank. -/
def selected {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ) :
    Circuit model (MeasuredRoundCtx base noQuantum m ell width)
      (MeasuredRoundCtx base noQuantum m ell width) :=
  .branch parameter fun value =>
    .embed (ContextEmbedding.identity (MeasuredRoundCtx base noQuantum m ell width))
      (member base noQuantum m ell width wide modulus (generator value) (target value))

/-- Exactly the real selected member and the paid native packing precede reset. -/
def sampled {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell))) :
    Circuit model (MeasuredRoundCtx base noQuantum m ell width)
      (MeasuredRoundCtx base noQuantum m ell width) :=
  (selected base noQuantum m ell width parameter wide modulus generator target).seq
    (Packing.code base noQuantum m ell width result)

/-- Every actual round resets and reloads the complete existing bank after writing its result. -/
def code {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell))) :
    Circuit model (MeasuredRoundCtx base noQuantum m ell width)
      (MeasuredRoundCtx base noQuantum m ell width) :=
  (sampled base noQuantum m ell width parameter wide modulus generator target result).seq
    (Reload.resetReload base noQuantum m ell width modulus.toNat)

/-- The complete final output observes the actual paid packed destination. -/
def run {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell))) :
    AlgorithmRun model (MeasuredRoundCtx base noQuantum m ell width)
      (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell)) where
  code := code base noQuantum m ell width parameter wide modulus generator target result
  output := Output.all (MeasuredRoundCtx base noQuantum m ell width)
    (.read (.storage result.toCStorageRef))

/-- Actual full reset and native reload establish the next seed for every original mixed state. -/
lemma measuredRound_seeded {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredRoundCtx base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat)
      ((code base noQuantum m ell width parameter wide modulus generator target result).execute
        environment Reference state) :=
  BasisSeeded.seq (environment := environment)
    (sampled base noQuantum m ell width parameter wide modulus generator target result)
    (Reload.resetReload base noQuantum m ell width modulus.toNat)
    (preparedSeed base noQuantum m ell width modulus.toNat) state
    (Reload.measuredResetReload_seeded base noQuantum m ell width modulus.toNat _)

/-- Full reset/reload preserves every previously packed classical observation with its reference. -/
lemma measuredRound_reference_afterPack {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredRoundCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (weight : Store (MeasuredRoundCtx base noQuantum m ell width) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width parameter wide modulus generator target result).execute
        environment Reference state) (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum
        ((sampled base noQuantum m ell width parameter wide modulus generator target result).execute
          environment Reference state) (fun entry _ => weight entry.1) left right := by
  rw [code, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  exact Reload.measuredResetReload_referenceFiberSum base noQuantum m ell width modulus.toNat _
    weight left right

/-- Every live parameter, packed destination, measured output, vent cell and qubit is listed. -/
lemma measuredRound_output_listing {shape : CShape}
    (parameter : CInputRef (MeasuredRoundCtx base noQuantum m ell width) shape)
    (wide : 2 ≤ width) (modulus : BitVec width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef (MeasuredRoundCtx base noQuantum m ell width) (.bits (resultBits m ell))) :
    (run base noQuantum m ell width parameter wide modulus generator target result).output.listing =
      (MeasuredRoundCtx base noQuantum m ell width).keys := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

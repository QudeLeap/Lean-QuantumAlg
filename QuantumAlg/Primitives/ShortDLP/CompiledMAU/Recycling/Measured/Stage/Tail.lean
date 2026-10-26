/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Components

/-!
# Actual stored-feedback and readout suffix with every retained block

The suffix reads its real input Store and overwrites only the actual measured
output cell. Its full interpreter equation retains every feedback selection,
measurement outcome, original history and coherent reference block
[G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Literal final stored-feedback/H/MZ/reset suffix of the original stage. -/
abbrev stageTail (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) :
    Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) false :=
  (feedbackPrefix base noQuantum m ell width inverse outputs position position.val le_rfl).seq
    (readout base noQuantum m ell width (outputs position))

/-- The actual Store/path of the literal suffix, including every prior-output selection. -/
def stageTailRecord (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (store : Store (Context base noQuantum m ell width))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Store (Context base noQuantum m ell width) ×
      (stageTail base noQuantum m ell width inverse outputs position).Path :=
  Execution.Instrument.sequenceRetainedRecord
    (feedbackPrefix base noQuantum m ell width inverse outputs position position.val le_rfl)
    (readout base noQuantum m ell width (outputs position))
    (fun original (_ : Unit) => (original,
      feedbackPath base noQuantum m ell width inverse outputs position position.val le_rfl
        original))
    (readoutRecord base noQuantum m ell width (outputs position)) store () outcome

/-- The same suffix's actual chronological native matrices, beside the reference identity. -/
def stageTailKraus (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (environment : model.Environment) (Reference : Register)
    (store : Store (Context base noQuantum m ell width))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  krausOperator (oracles := .empty) (control base noQuantum m ell width)
      (control_qubit base noQuantum m ell width) environment.quantum outcome Reference *
    (UnitaryOperator.prodTensor
      (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position
        position.val le_rfl store) (1 : UnitaryOperator Reference) :
          HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))

/-- Full retained interpreter equation for the actual final suffix of every measured stage. -/
lemma stageTail_block_matrix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (result : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (stageTail base noQuantum m ell width inverse outputs position).Path))) :
    (((stageTail base noQuantum m ell width inverse outputs position).execute environment Reference
      state).block result).matrix =
      ∑ original : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome,
          if Execution.Instrument.retainedRecord (stageTailRecord base noQuantum m ell width
            inverse outputs position)
              original outcome = result then
            stageTailKraus base noQuantum m ell width inverse outputs position environment Reference
                original.1 outcome * (state.block original).matrix *
              (stageTailKraus base noQuantum m ell width inverse outputs position environment
                Reference original.1 outcome).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (feedbackPrefix base noQuantum m ell width inverse outputs position position.val le_rfl)
    (readout base noQuantum m ell width (outputs position))
    (fun store (_ : Unit) => (store,
      feedbackPath base noQuantum m ell width inverse outputs position position.val le_rfl store))
    (readoutRecord base noQuantum m ell width (outputs position))
    (fun reference store (_ : Unit) =>
      (UnitaryOperator.prodTensor
        (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position
          position.val le_rfl store) (1 : UnitaryOperator reference) :
            HilbertOperator ((Context base noQuantum m ell width).register.prod reference)))
    (fun reference _ outcome => krausOperator (oracles := .empty)
      (control base noQuantum m ell width) (control_qubit base noQuantum m ell width)
      environment.quantum outcome reference)
    environment
    (fun reference _ _ original selected => feedbackPrefix_block_matrix base noQuantum m ell width
      inverse outputs position position.val le_rfl environment reference original selected)
    (fun reference _ _ original selected => readout_retained_matrix base noQuantum m ell width
      (outputs position) environment reference original selected)
    Reference state result
  refine actual.trans ?_
  simp only [Fintype.sum_unique]
  rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

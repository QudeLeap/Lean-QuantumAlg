/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Execution

/-!
# Full actual retained instrument of both measured exponent streams

The second stream receives the exact first stream Store and complete quantum
posterior. Both streams use the original shared accumulator and reference;
all reused arithmetic cells remain distinct in the chronological paths
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberInstrCtx := context base noQuantum m ell width

variable (modulus : BitVec width) (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Every chronological arithmetic and exponent outcome in the same actual two-stream member. -/
abbrev MemberOutcomes :=
  ExponentOutcomes base noQuantum m ell width modulus wide (bits := ell + m) generator (ell + m) 0
      (by omega) ×
    ExponentOutcomes base noQuantum m ell width modulus wide (bits := ell) target⁻¹ ell 0
      (by omega)

/-- The original complete first Store feeds the original complete second retained record. -/
def memberActualRecord (store : Store (MemberInstrCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    Store (MemberInstrCtx base noQuantum m ell width) ×
      (member base noQuantum m ell width wide modulus generator target).Path :=
  Execution.Instrument.sequenceRetainedRecord
    (exponentCode base noQuantum m ell width wide true (firstCell base noQuantum m ell width)
      modulus generator)
    (exponentCode base noQuantum m ell width wide true (secondCell base noQuantum m ell width)
      modulus target⁻¹)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega))
    (exponentActualRecord base noQuantum m ell width modulus wide target⁻¹ true
      (secondCell base noQuantum m ell width) ell 0 (by omega))
    store outcomes.1 outcomes.2

/-- The literal chronological second native product acts on the first full actual posterior. -/
def memberActualKraus (environment : model.Environment) (Reference : Register)
    (store : Store (MemberInstrCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    HilbertOperator ((MemberInstrCtx base noQuantum m ell width).register.prod Reference) :=
  exponentActualKraus base noQuantum m ell width modulus wide target⁻¹ true
      (secondCell base noQuantum m ell width) environment Reference ell 0 (by omega)
      (exponentActualRecord base noQuantum m ell width modulus wide generator true
        (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store outcomes.1).1
      outcomes.2 *
    exponentActualKraus base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) environment Reference (ell + m) 0 (by omega) store
      outcomes.1

/-- The actual two-stream interpreter preserves every original Store and chronological block. -/
lemma member_block_matrix (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (MemberInstrCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (result : Store (MemberInstrCtx base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (member base noQuantum m ell width wide modulus generator target).Path))) :
    (((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state).block result).matrix =
      ∑ original : Store (MemberInstrCtx base noQuantum m ell width) ×
          (model.HiddenState × History),
        ∑ outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target,
          if Execution.Instrument.retainedRecord
              (memberActualRecord base noQuantum m ell width modulus wide generator target)
              original outcomes = result then
            memberActualKraus base noQuantum m ell width modulus wide generator target environment
                Reference original.1 outcomes * (state.block original).matrix *
              (memberActualKraus base noQuantum m ell width modulus wide generator target
                environment Reference original.1 outcomes).conjTranspose
          else 0 := by
  have actual := Execution.Instrument.execute_sequenceRetainedBlocks
    (exponentCode base noQuantum m ell width wide true (firstCell base noQuantum m ell width)
      modulus generator)
    (exponentCode base noQuantum m ell width wide true (secondCell base noQuantum m ell width)
      modulus target⁻¹)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega))
    (exponentActualRecord base noQuantum m ell width modulus wide target⁻¹ true
      (secondCell base noQuantum m ell width) ell 0 (by omega))
    (fun reference store outcomes => exponentActualKraus base noQuantum m ell width modulus wide
      generator true (firstCell base noQuantum m ell width) environment reference (ell + m) 0
      (by omega) store outcomes)
    (fun reference store outcomes => exponentActualKraus base noQuantum m ell width modulus wide
      target⁻¹ true (secondCell base noQuantum m ell width) environment reference ell 0
      (by omega) store outcomes)
    environment
    (by
      intro reference history historyFinite original selected
      have proved := exponentSuffix_block_matrix base noQuantum m ell width modulus wide generator
        true (firstCell base noQuantum m ell width) environment (ell + m) 0 (by omega) reference
        original selected
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro entry _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs with first second third
      · rfl
      · exact False.elim (second first)
      · exact False.elim (first third)
      · rfl)
    (by
      intro reference history historyFinite original selected
      have proved := exponentSuffix_block_matrix base noQuantum m ell width modulus wide target⁻¹
        true (secondCell base noQuantum m ell width) environment ell 0 (by omega) reference
        original selected
      refine proved.trans ?_
      apply Finset.sum_congr rfl
      intro entry _
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs with first second third
      · rfl
      · exact False.elim (second first)
      · exact False.elim (first third)
      · rfl)
    Reference state result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro firstOutcome _
  apply Finset.sum_congr rfl
  intro secondOutcome _
  split_ifs with first second third
  · rfl
  · exact False.elim (second first)
  · exact False.elim (first third)
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

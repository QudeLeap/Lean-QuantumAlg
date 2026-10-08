/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction.Cancellation

/-!
# A literal conjunction circuit with arbitrary borrowed work

Two compute-Toffoli-inverse sandwiches cancel every incoming work value.
Their full encoded action flips only the output by the source conjunction.
This supplies elementary multi-control gates for the source zero-reflection
construction [dW19, qcnotes.tex:1335-1337].
-/

namespace QuantumAlg.EncodedBit.Word.ZeroTestLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}
variable (layout : ZeroTestLayout (encoding := encoding) tail)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- An actual conjunction computation, one output Toffoli, and its literal inverse. -/
def conjunctionSandwich (compute : List (GateSpec encoding)) : List (GateSpec encoding) :=
  compute ++ [finalGate layout] ++ compute.reverse

/-- The full and shortened literal sandwiches use the same arbitrary incoming work bits. -/
def dirtyConjunctionGates : List (GateSpec encoding) :=
  conjunctionSandwich layout (andGates layout) ++
    conjunctionSandwich layout (andGates layout).tail

private theorem andGates_cons (positive : 0 < tail) :
    andGates layout = andGateAt layout ⟨0, positive⟩ :: (andGates layout).tail := by
  have nonempty : andGates layout ≠ [] := by
    intro empty
    have sizes := congrArg List.length empty
    simp only [andGates, List.length_ofFn, List.length_nil] at sizes
    omega
  have head : (andGates layout).head nonempty = andGateAt layout ⟨0, positive⟩ := by
    exact List.head_ofFn nonempty
  rw [← head]
  exact (List.cons_head_tail nonempty).symm

private theorem shortened_step (positive : 0 < tail) (state : Data) :
    GateSpec.stepList (andGates layout).tail state =
      andStageIndexStep layout ((andGateAt layout ⟨0, positive⟩).step state) := by
  rw [← andGates_stepList_eq_indexStep, andGates_cons layout positive]
  simp only [List.tail_cons, GateSpec.stepList, GateSpec.step_step]

private theorem finalControl_output_flip (state : Data) :
    finalControl layout (layout.output.flip state) = finalControl layout state := by
  unfold finalControl
  split
  · rw [EncodedBit.get_flip_of_wire_ne _ _ (layout.source_output_ne 0).symm,
      EncodedBit.get_flip_of_wire_ne _ _ (layout.source_output_ne 1).symm]
  · rw [EncodedBit.get_flip_of_wire_ne _ _ (layout.work_output_ne _).symm,
      EncodedBit.get_flip_of_wire_ne _ _ (layout.source_output_ne _).symm]

private theorem computeControl_output_flip (compute : List (GateSpec encoding))
    (disjoint : ∀ gate, gate ∈ compute → GateSpec.bitDisjoint layout.output gate)
    (state : Data) :
    finalControl layout (GateSpec.stepList compute (layout.output.flip state)) =
      finalControl layout (GateSpec.stepList compute state) := by
  rw [GateSpec.stepList_flip_comm_of_bitDisjoint compute layout.output disjoint,
    finalControl_output_flip]

private theorem paired_sandwiches (first second : List (GateSpec encoding))
    (firstDisjoint : ∀ gate, gate ∈ first → GateSpec.bitDisjoint layout.output gate)
    (secondDisjoint : ∀ gate, gate ∈ second → GateSpec.bitDisjoint layout.output gate)
    (state : Data) :
    GateSpec.stepList (conjunctionSandwich layout first ++ conjunctionSandwich layout second)
        state =
      if finalControl layout (GateSpec.stepList second state) ^^
          finalControl layout (GateSpec.stepList first state)
      then layout.output.flip state else state := by
  rw [GateSpec.stepList_append]
  simp only [conjunctionSandwich]
  rw [dirtyConjunction_sandwich layout first firstDisjoint]
  cases firstValue : finalControl layout (GateSpec.stepList first state)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [dirtyConjunction_sandwich layout second secondDisjoint]
    simp
  · simp only [↓reduceIte]
    rw [dirtyConjunction_sandwich layout second secondDisjoint,
      computeControl_output_flip layout second secondDisjoint]
    cases secondValue : finalControl layout (GateSpec.stepList second state) <;>
      simp [EncodedBit.flip_flip]

/-- All borrowed coordinates return exactly, with no restriction on their initial values. -/
theorem dirtyConjunctionGates_step (positive : 0 < tail) (state : Data) :
    GateSpec.stepList (dirtyConjunctionGates layout) state =
      if sourceConjunction layout state (tail + 2) then layout.output.flip state else state := by
  have shortenedDisjoint : ∀ gate, gate ∈ (andGates layout).tail →
      GateSpec.bitDisjoint layout.output gate := by
    intro gate present
    exact andGates_output_bitDisjoint layout gate (List.mem_of_mem_tail present)
  rw [dirtyConjunctionGates, paired_sandwiches layout _ _
    (andGates_output_bitDisjoint layout) shortenedDisjoint,
    shortened_step layout positive, andGates_stepList_eq_indexStep,
    dirtyFinal_firstGate_difference]

/-- Exact number of elementary Toffoli leaves when there is at least one borrowed work bit. -/
theorem dirtyConjunctionGates_length (positive : 0 < tail) :
    (dirtyConjunctionGates layout).length = 4 * tail := by
  simp only [dirtyConjunctionGates, conjunctionSandwich, List.length_append,
    List.length_singleton, List.length_reverse, List.length_tail, andGates, List.length_ofFn]
  omega

/-- The actual elementary circuit agrees on every computational label, including dirty work. -/
theorem dirtyConjunctionGates_realizes (positive : 0 < tail) :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList physical oracles (dirtyConjunctionGates layout))
      (fun state => if sourceConjunction layout state (tail + 2)
        then layout.output.flip state else state) := by
  exact GateSpec.realizesList_congrStep physical oracles (dirtyConjunctionGates layout)
    (dirtyConjunctionGates_step layout positive)

end

end QuantumAlg.EncodedBit.Word.ZeroTestLayout

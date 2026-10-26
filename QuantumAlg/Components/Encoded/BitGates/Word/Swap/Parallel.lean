/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Resources
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Three physical layers for a complete word swap

Every CNOT layer checks both controls and targets. All word bits are arbitrary;
the three emitted layers exchange the same numerical positions and preserve
every other physical position.
-/

namespace QuantumAlg.EncodedBit.Word.ParallelSwap

noncomputable section

open WindowLookup
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Two complete, mutually disjoint lists of actual physical bit lenses. -/
structure Frame (encoding : BinaryLabelEncoding Data) (width : Nat) where
  left : Word encoding width
  right : Word encoding width
  leftDistinct : Function.Injective (fun index => (left.bit index).wire)
  rightDistinct : Function.Injective (fun index => (right.bit index).wire)
  cross : ∀ first second, (left.bit first).wire ≠ (right.bit second).wire

namespace Frame

variable (frame : Frame encoding width)

def reverse : Frame encoding width where
  left := frame.right
  right := frame.left
  leftDistinct := frame.rightDistinct
  rightDistinct := frame.leftDistinct
  cross first second := Ne.symm (frame.cross second first)

def edge (index : Fin width) : CnotEdge encoding where
  control := frame.left.bit index
  target := frame.right.bit index
  different := frame.cross index index

private lemma support_disjoint (first second : Fin width) (different : first ≠ second) :
    Disjoint (frame.edge first).support (frame.edge second).support := by
  apply Finset.disjoint_left.mpr
  intro wire firstPresent secondPresent
  simp only [CnotEdge.support, edge, Finset.mem_insert, Finset.mem_singleton]
    at firstPresent secondPresent
  rcases firstPresent with firstControl | firstTarget <;>
    rcases secondPresent with secondControl | secondTarget
  · exact different (frame.leftDistinct (firstControl.symm.trans secondControl))
  · exact frame.cross first second (firstControl.symm.trans secondTarget)
  · exact frame.cross second first (secondControl.symm.trans firstTarget)
  · exact different (frame.rightDistinct (firstTarget.symm.trans secondTarget))

def layer : CnotLayer encoding where
  edges := List.ofFn frame.edge
  separate := by
    rw [List.pairwise_ofFn]
    intro first second ordered
    exact frame.support_disjoint first second (Fin.ne_of_lt ordered)

lemma layer_gates : frame.layer.gates =
    xorIntoGates frame.left frame.right (fun index => frame.cross index index) := by
  simp only [CnotLayer.gates, layer, List.map_ofFn, xorIntoGates]
  rfl

lemma layer_length : frame.layer.edges.length = width := by
  simp only [layer, List.length_ofFn]

def forward : Data → Data :=
  xorIntoStep frame.left frame.right (fun index => frame.cross index index)

def step (state : Data) : Data :=
  frame.forward (frame.reverse.forward (frame.forward state))

lemma forward_left (index : Fin width) (state : Data) :
    (frame.left.bit index).get (frame.forward state) = (frame.left.bit index).get state :=
  xorIntoStep_get_observed_of_target_ne _ _ _ _
    (fun other => Ne.symm (frame.cross index other)) state

lemma forward_right (index : Fin width) (state : Data) :
    (frame.right.bit index).get (frame.forward state) =
      ((frame.right.bit index).get state ^^ (frame.left.bit index).get state) :=
  xorIntoStep_get_target _ _ _ index
    (fun _other different same => different (frame.rightDistinct same))
    (fun other => Ne.symm (frame.cross index other)) state

lemma step_left (index : Fin width) (state : Data) :
    (frame.left.bit index).get (frame.step state) = (frame.right.bit index).get state := by
  change (frame.left.bit index).get
    (frame.forward (frame.reverse.forward (frame.forward state))) = _
  rw [frame.forward_left]
  have backward := frame.reverse.forward_right index (frame.forward state)
  change (frame.left.bit index).get (frame.reverse.forward (frame.forward state)) =
    ((frame.left.bit index).get (frame.forward state) ^^
      (frame.right.bit index).get (frame.forward state)) at backward
  rw [backward, frame.forward_left, frame.forward_right]
  cases (frame.left.bit index).get state <;> cases (frame.right.bit index).get state <;> rfl

lemma step_right (index : Fin width) (state : Data) :
    (frame.right.bit index).get (frame.step state) = (frame.left.bit index).get state := by
  change (frame.right.bit index).get
    (frame.forward (frame.reverse.forward (frame.forward state))) = _
  rw [frame.forward_right]
  have backwardLeft := frame.reverse.forward_right index (frame.forward state)
  have backwardRight := frame.reverse.forward_left index (frame.forward state)
  change (frame.left.bit index).get (frame.reverse.forward (frame.forward state)) =
    ((frame.left.bit index).get (frame.forward state) ^^
      (frame.right.bit index).get (frame.forward state)) at backwardLeft
  change (frame.right.bit index).get (frame.reverse.forward (frame.forward state)) =
    (frame.right.bit index).get (frame.forward state) at backwardRight
  rw [backwardLeft, backwardRight, frame.forward_left, frame.forward_right]
  cases (frame.left.bit index).get state <;> cases (frame.right.bit index).get state <;> rfl

lemma step_other (observed : EncodedBit encoding)
    (outsideLeft : ∀ index, (frame.left.bit index).wire ≠ observed.wire)
    (outsideRight : ∀ index, (frame.right.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (frame.step state) = observed.get state := by
  have forwardOther (value : Data) : observed.get (frame.forward value) = observed.get value :=
    xorIntoStep_get_observed_of_target_ne _ _ _ _ outsideRight value
  have backwardOther (value : Data) :
      observed.get (frame.reverse.forward value) = observed.get value :=
    xorIntoStep_get_observed_of_target_ne _ _ _ _ outsideLeft value
  exact (forwardOther _).trans ((backwardOther _).trans (forwardOther state))

private lemma get_eq_of_wire_eq (first second : EncodedBit encoding)
    (same : first.wire = second.wire) : first.get = second.get := by
  funext state
  rw [← first.get_eq, ← second.get_eq, same]

/-- The complete arbitrary-input action agrees with the original word swap. -/
lemma step_eq_swapStep (onto : Function.Surjective encoding.encode) :
    frame.step = swapStep frame.left frame.right (fun index => frame.cross index index) := by
  funext state
  apply state_eq_of_get_eq onto
  intro observed
  by_cases leftPresent : ∃ index, (frame.left.bit index).wire = observed.wire
  · obtain ⟨index, same⟩ := leftPresent
    rw [← get_eq_of_wire_eq _ _ same, frame.step_left]
    exact (swapStep_get_left _ _ _ index
      (fun other different equal => different (frame.leftDistinct equal))
      (fun other => Ne.symm (frame.cross index other))
      (fun other => frame.cross other index)
      (fun other different equal => different (frame.rightDistinct equal)) state).symm
  · by_cases rightPresent : ∃ index, (frame.right.bit index).wire = observed.wire
    · obtain ⟨index, same⟩ := rightPresent
      rw [← get_eq_of_wire_eq _ _ same, frame.step_right]
      exact (swapStep_get_right _ _ _ index
        (fun other different equal => different (frame.leftDistinct equal))
        (fun other => Ne.symm (frame.cross index other))
        (fun other => frame.cross other index)
        (fun other different equal => different (frame.rightDistinct equal)) state).symm
    · have leftOutside : ∀ index, (frame.left.bit index).wire ≠ observed.wire := by
        intro index equal
        exact leftPresent ⟨index, equal⟩
      have rightOutside : ∀ index, (frame.right.bit index).wire ≠ observed.wire := by
        intro index equal
        exact rightPresent ⟨index, equal⟩
      rw [frame.step_other observed leftOutside rightOutside,
        swapStep_get_observed_of_swap_ne _ _ _ _ leftOutside rightOutside]

def program (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  .seq (frame.layer.program physical oracles)
    (.seq (frame.reverse.layer.program physical oracles) (frame.layer.program physical oracles))

lemma program_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles) environment frame.step := by
  have first := frame.layer.program_realizes physical oracles environment
  have second := frame.reverse.layer.program_realizes physical oracles environment
  rw [frame.layer_gates] at first
  rw [frame.reverse.layer_gates] at second
  exact first.seq (second.seq first)

lemma program_apply (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) (state : Data) :
    (frame.program physical oracles).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
        NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode (frame.step state))) :=
  (frame.program_realizes physical oracles environment).apply_encoded_ket state

/-- The same generic three-layer program keeps arbitrary full-label and Reference coherence. -/
lemma program_reference (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (states : Index → Data)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (UnitaryOperator.prodTensor ((frame.program physical oracles).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket
        (R := physical.toQuantum.register.prod Reference)
        (physical.basisEquiv.symm (encoding.encode (states index)), reference index)).vec) =
      ∑ index, amplitude index • (NormalizedVector.ket
        (R := physical.toQuantum.register.prod Reference)
        (physical.basisEquiv.symm (encoding.encode (frame.step (states index))),
          reference index)).vec := by
  change HilbertOperator.applyVec _ _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  apply congrArg (fun vector => amplitude index • vector)
  have pure := congrArg NormalizedVector.vec
    (frame.program_apply physical oracles environment (states index))
  change ((frame.program physical oracles).matrix environment).applyVec
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode (states index)))).vec =
    (NormalizedVector.ket
      (physical.basisEquiv.symm (encoding.encode (frame.step (states index))))).vec at pure
  change (UnitaryOperator.prodTensor ((frame.program physical oracles).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    pure, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

lemma program_eventTrace (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (frame.program physical oracles).eventTrace = List.replicate (3 * width) (.gate .cnot) := by
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    CnotLayer.program_eventTrace_exact, CnotLayer.program_eventTrace_exact,
    frame.layer_length, frame.reverse.layer_length]
  rw [← List.replicate_add, ← List.replicate_add]
  congr 1
  omega

lemma program_cnot_count (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (frame.program physical oracles).eventCost = 3 * width := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, frame.program_eventTrace,
    ResourcePool.ofList_replicate, ResourcePool.count_scale, ResourcePool.count_singleton_self,
    Nat.mul_one]

lemma program_quantumTime (physical : QubitLayout encoding.width) (oracles : OracleModel) :
    (frame.program physical oracles).evaluatedEventDepth Resource.Event.quantumDuration =
      if width = 0 then 0 else 3 := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    CnotLayer.program_quantumTime, CnotLayer.program_quantumTime]
  have empty : frame.layer.edges = [] ↔ width = 0 := by
    rw [← List.length_eq_zero_iff, frame.layer_length]
  have reverseEmpty : frame.reverse.layer.edges = [] ↔ width = 0 := by
    rw [← List.length_eq_zero_iff, frame.reverse.layer_length]
  simp only [empty, reverseEmpty]
  split <;> rfl

end Frame

end

end QuantumAlg.EncodedBit.Word.ParallelSwap

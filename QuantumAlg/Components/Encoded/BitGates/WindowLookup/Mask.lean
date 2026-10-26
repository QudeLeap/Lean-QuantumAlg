/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Parallel
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import Mathlib.Data.List.Perm.Basic

/-!
# Physical masked-X propagation

CNOT layers include both their control and target wires in the independence
check. Their action propagates an X mask without assuming that any target is
clean. Conjugating one selector-controlled X by these layers will implement
arbitrary-target XOR lookup [Gid19, main.tex:192-205]. The scheduling and exact
native counts are derived from the same physical programs.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Flip each actual bit in list order. No initial value is required. -/
def flipBits : List (EncodedBit encoding) → Data → Data
  | [], state => state
  | bit :: rest, state => flipBits rest (bit.flip state)

/-- A split mask acts by composing its two actual sequences of flips. -/
lemma flipBits_append (first second : List (EncodedBit encoding)) (state : Data) :
    flipBits (first ++ second) state = flipBits second (flipBits first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons bit rest ih => exact ih (bit.flip state)

/-- Bit flips commute on the full encoded state, including every other wire. -/
lemma flipBits_flip (bits : List (EncodedBit encoding)) (bit : EncodedBit encoding)
    (state : Data) : flipBits bits (bit.flip state) = bit.flip (flipBits bits state) := by
  induction bits generalizing state with
  | nil => rfl
  | cons first rest ih =>
      change flipBits rest (first.flip (bit.flip state)) =
        bit.flip (flipBits rest (first.flip state))
      rw [EncodedBit.flip_comm first bit state]
      exact ih (first.flip state)

/-- The same multiset of physical flips has the same exact action. -/
lemma flipBits_perm {first second : List (EncodedBit encoding)} (same : first.Perm second)
    (state : Data) : flipBits first state = flipBits second state := by
  induction same generalizing state with
  | nil => rfl
  | cons bit _ ih => exact ih (bit.flip state)
  | swap first second rest =>
      simp only [flipBits]
      rw [EncodedBit.flip_comm]
  | trans _ _ left right => exact (left state).trans (right state)

/-- A semantic bit flip is fixed by its actual encoded wire. -/
lemma flip_eq_of_wire_eq (first second : EncodedBit encoding)
    (same : first.wire = second.wire) (state : Data) : first.flip state = second.flip state := by
  apply encoding.encode_injective
  rw [first.encode_flip, second.encode_flip, same]

/-- CNOT commutes with X on any wire other than its control, including its target. -/
lemma cnotStep_flip_comm (control target observed : EncodedBit encoding)
    (different : observed.wire ≠ control.wire) (state : Data) :
    cnotStep control target (observed.flip state) =
      observed.flip (cnotStep control target state) := by
  unfold cnotStep
  rw [EncodedBit.get_flip_of_wire_ne observed control different]
  split
  · exact EncodedBit.flip_comm target observed state
  · rfl

/-- CNOT propagates a control X to exactly its control and target. -/
lemma cnotStep_flip_control (control target : EncodedBit encoding) (state : Data) :
    cnotStep control target (control.flip state) =
      target.flip (control.flip (cnotStep control target state)) := by
  unfold cnotStep
  rw [EncodedBit.get_flip_self]
  cases value : control.get state
  · simp only [Bool.not_false, Bool.false_eq_true, if_true, if_false]
  · simp only [Bool.not_true, Bool.false_eq_true, if_true, if_false]
    rw [EncodedBit.flip_comm control target, EncodedBit.flip_flip]


/-- A CNOT commutes with a mask omitting its control. -/
lemma cnotStep_flipBits_comm (control target : EncodedBit encoding)
    (bits : List (EncodedBit encoding))
    (different : ∀ bit ∈ bits, bit.wire ≠ control.wire) (state : Data) :
    cnotStep control target (flipBits bits state) =
      flipBits bits (cnotStep control target state) := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      rw [flipBits, ih (fun next member => different next (by simp [member])),
        cnotStep_flip_comm control target bit (different bit (by simp))]
      rfl

/-- One occurrence of the control in a duplicate-free mask adds exactly the target X. -/
lemma cnotStep_flipBits (control target : EncodedBit encoding)
    (bits : List (EncodedBit encoding)) (distinct : (bits.map EncodedBit.wire).Nodup)
    (present : control.wire ∈ bits.map EncodedBit.wire) (state : Data) :
    cnotStep control target (flipBits bits state) =
      target.flip (flipBits bits (cnotStep control target state)) := by
  induction bits generalizing state with
  | nil => simp at present
  | cons bit rest ih =>
      obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
      by_cases same : bit.wire = control.wire
      · have restDifferent : ∀ other ∈ rest, other.wire ≠ control.wire := by
          intro other member equal
          apply absent
          exact List.mem_map.mpr ⟨other, member, equal.trans same.symm⟩
        rw [flipBits, cnotStep_flipBits_comm control target rest restDifferent,
          flip_eq_of_wire_eq bit control same, cnotStep_flip_control,
          flipBits_flip, flipBits_flip]
        rw [flipBits, flip_eq_of_wire_eq bit control same, flipBits_flip]
      · have nextPresent : control.wire ∈ rest.map EncodedBit.wire :=
          (List.mem_cons.mp present).resolve_left (Ne.symm same)
        rw [flipBits, ih restDistinct nextPresent,
          cnotStep_flip_comm control target bit same]
        rfl

/-- One real CNOT with both actual positions and their required inequality. -/
structure CnotEdge (encoding : BinaryLabelEncoding Data) where
  control : EncodedBit encoding
  target : EncodedBit encoding
  different : control.wire ≠ target.wire

namespace CnotEdge

/-- The native gate is the declared CNOT on these two original wires. -/
def gate (edge : CnotEdge encoding) : GateSpec encoding :=
  .cnot edge.control edge.target edge.different

/-- Both read and written positions belong to the support. -/
def support (edge : CnotEdge encoding) : Finset (Fin encoding.width) :=
  {edge.control.wire, edge.target.wire}

end CnotEdge

/-- An actual parallel layer requires disjoint complete CNOT supports. -/
structure CnotLayer (encoding : BinaryLabelEncoding Data) where
  edges : List (CnotEdge encoding)
  separate : edges.Pairwise (fun first second => Disjoint first.support second.support)

namespace CnotLayer

/-- The exact source instructions of this physical layer. -/
def gates (layer : CnotLayer encoding) : List (GateSpec encoding) := layer.edges.map CnotEdge.gate

private lemma physical_separate (layer : CnotLayer encoding)
    (physical : QubitLayout encoding.width) :
    layer.gates.Pairwise (fun first second =>
      Disjoint (GateSpec.physicalSupport physical first)
        (GateSpec.physicalSupport physical second)) := by
  apply List.pairwise_map.mpr
  apply layer.separate.imp
  intro first second separate
  simpa only [CnotEdge.gate, GateSpec.physicalSupport_cnot, CnotEdge.support] using separate

/-- The layer compiles to the actual Core native parallel constructor. -/
def program (layer : CnotLayer encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.parallelProgramList physical oracles layer.gates (layer.physical_separate physical)

/-- Parallel execution retains the exact arbitrary-input encoded action. -/
lemma program_realizes (layer : CnotLayer encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding (layer.program physical oracles) environment
      (GateSpec.stepList layer.gates) :=
  GateSpec.parallelProgramList_realizes physical oracles layer.gates
    (layer.physical_separate physical) environment

/-- Exactly the actual CNOT instructions are retained in the event trace. -/
lemma program_eventTrace (layer : CnotLayer encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (layer.program physical oracles).eventTrace = layer.gates.map (GateSpec.event oracles) := by
  rw [program, GateSpec.parallelProgramList_eventTrace, GateSpec.programList_eventTrace]

/-- Every nonempty physically independent layer takes one native quantum step. -/
lemma program_quantumTime (layer : CnotLayer encoding) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (layer.program physical oracles).evaluatedEventDepth Resource.Event.quantumDuration =
      if layer.edges = [] then 0 else 1 := by
  rw [program, GateSpec.parallelProgramList_quantumTime]
  simp only [gates, List.map_eq_nil_iff]

end CnotLayer

end

end QuantumAlg.EncodedBit.WindowLookup

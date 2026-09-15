/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Conjunction
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.SubLayouts
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.ZeroTest
import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction.Program
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import Mathlib.Data.List.Basic

/-!
# Exact elementary resources of the one-dirty conjunction

The arithmetic count is specified independently of any circuit. Every gate
in the actual borrowed conjunction subcalls is a Toffoli. Consequently the
literal balanced schedule has precisely that Toffoli multiplicity, while
zero and one controls retain their actual single X and CNOT respectively.
-/

namespace QuantumAlg.EncodedBit.Word

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

namespace ZeroTestLayout

variable {tail : Nat} (layout : ZeroTestLayout (encoding := encoding) tail)

private theorem finalGate_event :
    (layout.finalGate).event = .gate (.builtin "toffoli") := by
  unfold finalGate
  split <;> rfl

private theorem andGates_event (gate : GateSpec encoding) (present : gate ∈ layout.andGates) :
    gate.event = .gate (.builtin "toffoli") := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rfl

private theorem sandwich_event (compute : List (GateSpec encoding))
    (allToffoli : ∀ gate ∈ compute, gate.event = .gate (.builtin "toffoli"))
    (gate : GateSpec encoding) (present : gate ∈ layout.conjunctionSandwich compute) :
    gate.event = .gate (.builtin "toffoli") := by
  simp only [conjunctionSandwich, List.mem_append, List.mem_singleton,
    List.mem_reverse] at present
  rcases present with (present | same) | present
  · exact allToffoli gate present
  · subst gate
    exact finalGate_event layout
  · exact allToffoli gate present

/-- A borrowed conjunction contains only the source's literal Toffoli leaves. -/
theorem borrowedAndGates_event (gate : GateSpec encoding)
    (present : gate ∈ layout.borrowedAndGates) :
    gate.event = .gate (.builtin "toffoli") := by
  by_cases empty : tail = 0
  · rw [borrowedAndGates, if_pos empty] at present
    obtain rfl := List.mem_singleton.mp present
    exact finalGate_event layout
  · rw [borrowedAndGates, if_neg empty, dirtyConjunctionGates] at present
    rcases List.mem_append.mp present with first | second
    · exact sandwich_event layout _ (andGates_event layout) gate first
    · exact sandwich_event layout _
        (fun item member => andGates_event layout item (List.mem_of_mem_tail member)) gate second

end ZeroTestLayout

namespace OneDirtyLayout

/-- Arithmetic length of the balanced construction, independent of a gate list or layout. -/
public def gateCount (controls : Nat) : Nat :=
  if controls < 3 then 1 else
    2 * ((if (controls + 1) / 2 - 2 = 0 then 1 else 4 * ((controls + 1) / 2 - 2)) +
      (if controls - (controls + 1) / 2 - 1 = 0 then 1
        else 4 * (controls - (controls + 1) / 2 - 1)))

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)

/-- The independent formula counts the actual elementary schedule. -/
theorem gates_length : layout.gates.length = gateCount controls := by
  by_cases small : controls < 3
  · rw [layout.gates_length_of_small small, gateCount, if_pos small]
  · rw [layout.gates_length_of_large (Nat.le_of_not_gt small), gateCount, if_neg small]
    rfl

private theorem balancedGates_event (large : 3 ≤ controls) (gate : GateSpec encoding)
    (present : gate ∈ layout.balancedGates large) :
    gate.event = .gate (.builtin "toffoli") := by
  simp only [balancedGates, List.mem_append] at present
  rcases present with ((first | second) | first) | second
  · exact (layout.firstSubLayout large).borrowedAndGates_event gate first
  · exact (layout.secondSubLayout large).borrowedAndGates_event gate second
  · exact (layout.firstSubLayout large).borrowedAndGates_event gate first
  · exact (layout.secondSubLayout large).borrowedAndGates_event gate second

private theorem gates_event_of_two_le (large : 2 ≤ controls) (gate : GateSpec encoding)
    (present : gate ∈ layout.gates) :
    gate.event = .gate (.builtin "toffoli") := by
  cases controls with
  | zero => omega
  | succ controls =>
    cases controls with
    | zero => omega
    | succ controls =>
      cases controls with
      | zero =>
        obtain rfl := List.mem_singleton.mp present
        rfl
      | succ controls => exact layout.balancedGates_event (by omega) gate present

/-- The actual schedule consists of exactly the independently counted Toffoli events. -/
theorem gates_events_of_two_le (large : 2 ≤ controls) :
    layout.gates.map GateSpec.event =
      List.replicate (gateCount controls) (.gate (.builtin "toffoli")) := by
  apply List.eq_replicate_iff.mpr
  constructor
  · rw [List.length_map, gates_length]
  · intro event present
    obtain ⟨gate, member, rfl⟩ := List.mem_map.mp present
    exact layout.gates_event_of_two_le large gate member

/-- Every width retains its actual elementary gate family. -/
theorem gates_events : layout.gates.map GateSpec.event =
    if controls = 0 then [.gate (.builtin "x")]
    else if controls = 1 then [.gate (.builtin "cnot")]
    else List.replicate (gateCount controls) (.gate (.builtin "toffoli")) := by
  cases controls with
  | zero => rfl
  | succ controls =>
    cases controls with
    | zero => rfl
    | succ controls =>
      rw [if_neg (by omega), if_neg (by omega)]
      exact layout.gates_events_of_two_le (by omega)

/-- The sequential elementary program has exactly the same independent unit-event depth. -/
theorem gates_program_depth :
    (GateSpec.programList layout.gates).evaluatedEventDepth (fun _ => 1) = gateCount controls := by
  rw [GateSpec.programList_evaluatedEventDepth_unit, gates_length]

/-- The small nontrivial balanced schedules have four and ten actual Toffoli gates. -/
theorem gateCount_three : gateCount 3 = 4 := rfl

theorem gateCount_four : gateCount 4 = 10 := rfl

/-- From five controls onward the arithmetic formula is exactly linear. -/
theorem gateCount_of_five_le (large : 5 ≤ controls) :
    gateCount controls = 8 * (controls - 3) := by
  have partition := width_partition controls
  change firstWidth controls + secondWidth controls = controls at partition
  rw [gateCount, if_neg (by omega : ¬controls < 3)]
  change 2 * ((if firstWidth controls - 2 = 0 then 1 else 4 * (firstWidth controls - 2)) +
    (if secondWidth controls - 1 = 0 then 1 else 4 * (secondWidth controls - 1))) = _
  have firstPositive : firstWidth controls - 2 ≠ 0 := by
    dsimp only [firstWidth]
    omega
  have secondPositive : secondWidth controls - 1 ≠ 0 := by
    dsimp only [secondWidth, firstWidth]
    omega
  rw [if_neg firstPositive, if_neg secondPositive]
  omega

end OneDirtyLayout

end

end QuantumAlg.EncodedBit.Word

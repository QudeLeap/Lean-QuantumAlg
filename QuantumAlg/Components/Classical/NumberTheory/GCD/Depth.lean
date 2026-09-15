/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction

/-!
# Native dependency depth of the expanded Euclidean circuit

Every arithmetic dependency remains serial. An inactive selected arm has
zero event duration. The independent bound retains arbitrary durations for
each actual native operation and specializes to an explicit linear unit-cost
bound; no inactive operation is inserted into the circuit to attain it.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open ClassicalAlgorithms.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent duration of the four actual initialization instructions. -/
def initializationDuration (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.wordUnary .copy width)) +
    (duration (.classicalOperation (.wordUnary .copy width)) +
      (duration (.classicalOperation (.wordBinary .equal width)) +
        duration (.classicalOperation (.bit .not))))

/-- Independent duration of the five actual instructions in a genuine remainder step. -/
def remainderDuration (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  duration (.classicalOperation (.divRem width width)) +
    (duration (.classicalOperation (.wordUnary .copy width)) +
      (duration (.classicalOperation (.wordUnary .copy width)) +
        (duration (.classicalOperation (.wordBinary .equal width)) +
          duration (.classicalOperation (.bit .not)))))

/-- Fixed duration allowance for initialization, the public schedule and the final copy. -/
def nativeDepthLimit (width : Nat) (duration : Resource.Event kind → Nat) : Nat :=
  initializationDuration width duration +
    (Euclid.gcdFuel width * remainderDuration width duration +
      duration (.classicalOperation (.wordUnary .copy width)))

/-- The actual selected loop arm respects the duration of its full dependent instruction chain. -/
theorem gcdGuardedRemainder_depth_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat)
    (path : (guardedRemainder first second zero active).Path) :
    (guardedRemainder first second zero active).depth duration path ≤
      remainderDuration width duration := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit bit =>
      cases bit
      · exact Nat.zero_le _
      · exact le_rfl

/-- Sequential iteration adds each selected body's actual native dependency depth. -/
theorem gcdLoop_depth_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) (duration : Resource.Event kind → Nat)
    (path : (Circuit.iterate count (guardedRemainder first second zero active)).Path) :
    (Circuit.iterate count (guardedRemainder first second zero active)).depth duration path ≤
      count * remainderDuration width duration := by
  change 0 + ∑ index : Fin count,
    (guardedRemainder first second zero active).depth duration (path index) ≤ _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin count, remainderDuration width duration :=
      Finset.sum_le_sum (fun index _ =>
        gcdGuardedRemainder_depth_le first second zero active duration (path index))
    _ = count * remainderDuration width duration := by simp

/-- The initialized schedule includes its final result-copy dependency. -/
theorem gcdScheduled_depth_le (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event kind → Nat)
    (path : (scheduledBody input first second active result).Path) :
    (scheduledBody input first second active result).depth duration path ≤
      nativeDepthLimit width duration := by
  change initializationDuration width duration +
    ((Circuit.iterate (Euclid.gcdFuel width)
      (guardedRemainder first second (cellRead result) active)).depth duration path.2.1 +
      duration (.classicalOperation (.wordUnary .copy width))) ≤ _
  exact Nat.add_le_add_left (Nat.add_le_add_right
    (gcdLoop_depth_le first second (cellRead result) active (Euclid.gcdFuel width)
      duration path.2.1) _) _

/-- Entering and releasing the actual classical scopes adds no hidden event duration. -/
theorem gcdLexical_depth_le (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (lexicalBody input result).Path) :
    (lexicalBody input result).depth duration path ≤ nativeDepthLimit width duration :=
  gcdScheduled_depth_le (underLoop input width) (currentCell ctx width) (previousCell ctx width)
    (conditionCell ctx width) (writeUnderLoop result width) duration path

/-- The entire retained circuit satisfies the same independent native duration allowance. -/
theorem gcdRetained_depth_le (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).depth duration path ≤ nativeDepthLimit width duration := by
  change 0 + (lexicalBody (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)).depth duration path.2 ≤ _
  rw [Nat.zero_add]
  exact gcdLexical_depth_le _ _ duration path.2

/-- Unit duration yields an explicit linear upper bound, including width zero. -/
theorem gcdNativeDepthLimit_unit (kind : ProblemKind) (width : Nat) :
    nativeDepthLimit width (fun _ : Resource.Event kind => 1) = 10 * width + 10 := by
  simp only [nativeDepthLimit, initializationDuration, remainderDuration, Euclid.gcdFuel]
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD

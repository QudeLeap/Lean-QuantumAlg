/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Shift

/-!
# Original native loading of the lattice power-of-two coordinates

One actual increment precedes the requested number of actual left shifts.
This is the original loading sequence for the two nonzero coordinates in
rows two and three of the initial basis. The store equation allows any
incoming word, including width zero. Fresh basis allocation will supply
zero internally when this sequence is connected to the source basis.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.PowerOfTwo

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original first instruction increments the actual destination word. -/
def incrementOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (.storage output.toCStorageRef) output

/-- Each subsequent instruction doubles the same actual word with fixed-width truncation. -/
def shiftOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftLeft width ctx (.storage output.toCStorageRef) output

/-- Actual repetition performs precisely the original number of one-bit left shifts. -/
def shifts (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .iterate count (.classical (shiftOp output))

/-- The original increment followed by the real finite left-shift loop. -/
def code (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (incrementOp output)) (shifts count output)

/-- The loop records exactly its actual native store updates. -/
def shiftsStore (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  (fun current => current.applyOp (shiftOp output))^[count] store

/-- The complete recorded store follows the actual increment and shift order. -/
def storeStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  shiftsStore count output (store.applyOp (incrementOp output))

/-- Independent literal allowance charges one increment and every actual left shift. -/
def nativeEnvelope (kind : ProblemKind) (width count : Nat) : ResourcePool kind :=
  ResourcePool.ofList
    (.classicalOperation (.wordUnary .increment width) ::
      List.replicate count (.classicalOperation (.wordUnary .shiftLeft width)))

/-- Every actual path records the same original chronological sequence of instructions. -/
theorem nativeLattice_powerOfTwo_trace (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (path : (code count output).Path) :
    (code count output).eventTrace path =
      .classicalOperation (.wordUnary .increment width) ::
        List.replicate count (.classicalOperation (.wordUnary .shiftLeft width)) := by
  exact congrArg (List.cons
    (.classicalOperation (.wordUnary .increment width) : Resource.Event kind))
    (TerminalShift.flatten_repeated_singleton count
      (.classicalOperation (.wordUnary .shiftLeft width) : Resource.Event kind))

/-- The actual native multiplicities equal the independent instruction allowance. -/
theorem nativeLattice_powerOfTwo_pool (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (path : (code count output).Path) :
    (code count output).resourcePool path = nativeEnvelope kind width count :=
  congrArg ResourcePool.ofList (nativeLattice_powerOfTwo_trace count output path)

/-- The actual dependency chain charges its first increment and all following shifts. -/
theorem nativeLattice_powerOfTwo_depth (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (code count output).Path) :
    (code count output).depth duration path =
      duration (.classicalOperation (.wordUnary .increment width)) +
        count * duration (.classicalOperation (.wordUnary .shiftLeft width)) := by
  change duration (.classicalOperation (.wordUnary .increment width)) +
    (0 + ∑ _ : Fin count, duration (.classicalOperation (.wordUnary .shiftLeft width))) = _
  simp

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem shifts_execute (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (shifts count output).execute Reference state = state.mapClassical (fun entry =>
      (shiftsStore count output entry.1, (entry.2, fun _ : Fin count => ()))) := by
  refine (Circuit.execute_iterate_mapClassical (.classical (shiftOp output))
    (fun current => (current.applyOp (shiftOp output), ()))
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical (shiftOp output) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).symm)
    count Reference state).trans ?_
  dsimp only [shiftsStore]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (Fin count → Unit)))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (Fin count → Unit)))
    (R := Register.prod ctx.register Reference) _ state _).symm

/-- Every store-keyed quantum-reference block follows the recorded native loading sequence. -/
theorem nativeLattice_powerOfTwo_execute (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code count output).execute Reference state = state.mapClassical (fun entry =>
      (storeStep count output entry.1, (entry.2, ((), fun _ : Fin count => ())))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (incrementOp output))
    (shifts count output) (fun current => (current.applyOp (incrementOp output), ()))
    (fun current => (shiftsStore count output current, fun _ : Fin count => ()))
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical
        (incrementOp output) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (shifts_execute count output reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (Fin count → Unit)))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (Fin count → Unit)))
        (R := Register.prod ctx.register reference) _ current _).symm)
    Reference state).trans ?_
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code count output).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code count output).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

/-- The real loading sequence restores the complete borrowed interface for every reference. -/
theorem nativeLattice_powerOfTwo_borrowedRestored (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code count output).BorrowedRestored Reference state
      ((code count output).execute Reference state) :=
  Circuit.borrowedRestored_seq (.classical (incrementOp output)) (shifts count output) state
    (Circuit.borrowedRestored_classical (incrementOp output) state)
    (Circuit.borrowedRestored_iterate (.classical (shiftOp output)) Reference
      (fun {_} _ current => Circuit.borrowedRestored_classical (shiftOp output) current) count _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.PowerOfTwo

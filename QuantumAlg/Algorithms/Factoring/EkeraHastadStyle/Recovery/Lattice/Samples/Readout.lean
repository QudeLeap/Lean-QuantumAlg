/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Samples.Layout.Store
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split.Frame

/-!
# Actual pair decoding equals the original two retained source samples

The first actual decoder preserves the retained second terminal. The second
actual decoder preserves both already materialized first-sample fields.
Consequently the four real words are exactly the ordered source samples
read from the original retained store. All separation follows from the four
actual fresh positions, with no caller condition or initialized output.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- Both actual decoders leave every original structural source unchanged. -/
theorem nativeLattice_sample_decode_read_original
    (first second : CInputRef ctx (.bits ((ell + m) + ell)))
    {shape : CShape} (other : CInputRef ctx shape) (store : Store (context ctx m ell)) :
    (decodeStep first second store).1.read (underRead other m ell) =
      store.read (underRead other m ell) :=
  (TerminalSplit.nativeRecovery_terminal_split_read_other
    (underRead second m ell) (secondRefs ctx m ell) (underRead other m ell)
    (original_free other m ell 1) (original_free other m ell 0) _).trans
    (TerminalSplit.nativeRecovery_terminal_split_read_other
      (underRead first m ell) (firstRefs ctx m ell) (underRead other m ell)
      (original_free other m ell 3) (original_free other m ell 2) store)

/-- The actual ordered decoder prefix stores exactly both original source samples. -/
theorem nativeLattice_sample_decode_source
    (first second : CInputRef ctx (.bits ((ell + m) + ell))) (store : Store ctx) :
    let firstSample := BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read first))
    let secondSample := BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read second))
    let final := (decodeStep first second (pushStore m ell store)).1
    (((final.read (.storage (firstRefs ctx m ell).j.toCStorageRef)).toNat,
      (final.read (.storage (firstRefs ctx m ell).k.toCStorageRef)).toNat),
      ((final.read (.storage (secondRefs ctx m ell).j.toCStorageRef)).toNat,
        (final.read (.storage (secondRefs ctx m ell).k.toCStorageRef)).toNat)) =
      ((firstSample.1.val, firstSample.2.val), (secondSample.1.val, secondSample.2.val)) := by
  let entered : Store (context ctx m ell) := pushStore m ell store
  let firstDone : Store (context ctx m ell) :=
    (TerminalSplit.step (underRead first m ell) (firstRefs ctx m ell) entered).1
  let firstSample := BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read first))
  have firstValues :
      ((firstDone.read (.storage (firstRefs ctx m ell).j.toCStorageRef)).toNat,
        (firstDone.read (.storage (firstRefs ctx m ell).k.toCStorageRef)).toNat) =
      (firstSample.1.val, firstSample.2.val) :=
    (TerminalSplit.nativeRecovery_terminal_split_read (underRead first m ell)
      (firstRefs ctx m ell) (nativeLattice_sample_first_separated ctx m ell) entered).trans
      (congrArg (fun value : CShape.Value (.bits ((ell + m) + ell)) =>
        let sample := BatchRecovery.decodeTerminalSample m ell (terminalValue value)
        (sample.1.val, sample.2.val)) (nativeLattice_sample_push_read first m ell store))
  have secondInput : firstDone.read (underRead second m ell) = store.read second :=
    (TerminalSplit.nativeRecovery_terminal_split_read_other
      (underRead first m ell) (firstRefs ctx m ell) (underRead second m ell)
      (original_free second m ell 3) (original_free second m ell 2) entered).trans
      (nativeLattice_sample_push_read second m ell store)
  have secondValues :=
    (TerminalSplit.nativeRecovery_terminal_split_read (underRead second m ell)
      (secondRefs ctx m ell) (nativeLattice_sample_second_separated ctx m ell) firstDone).trans
      (congrArg (fun value : CShape.Value (.bits ((ell + m) + ell)) =>
        let sample := BatchRecovery.decodeTerminalSample m ell (terminalValue value)
        (sample.1.val, sample.2.val)) secondInput)
  have firstJ := TerminalSplit.nativeRecovery_terminal_split_read_other
    (underRead second m ell) (secondRefs ctx m ell)
    (.storage (firstRefs ctx m ell).j.toCStorageRef)
    (fun present => cellKey_ne ctx m ell 1 3 (by decide) (List.mem_singleton.mp present))
    (fun present => cellKey_ne ctx m ell 0 3 (by decide) (List.mem_singleton.mp present)) firstDone
  have firstK := TerminalSplit.nativeRecovery_terminal_split_read_other
    (underRead second m ell) (secondRefs ctx m ell)
    (.storage (firstRefs ctx m ell).k.toCStorageRef)
    (fun present => cellKey_ne ctx m ell 1 2 (by decide) (List.mem_singleton.mp present))
    (fun present => cellKey_ne ctx m ell 0 2 (by decide) (List.mem_singleton.mp present)) firstDone
  exact congrArg₂ Prod.mk
    ((congrArg₂ Prod.mk (congrArg CShape.Value.toNat firstJ)
      (congrArg CShape.Value.toNat firstK)).trans firstValues) secondValues

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout

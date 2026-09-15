/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.FirstRow.Readout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Constants.PowerOfTwo.Readout
import all QuantumAlg.Util.RSA.ShortLog.WidthBounds

/-!
# Actual source target preimage loading

Each original k word is resized into its actual wide preimage cell and
shifted left exactly m times. The common native shift loop is reused from
the basis loader. Its all-width modular equation needs no initial output
value; the original recovery width then makes the scaled source value exact.
Both preimages are loaded before the separate centered-coordinate phase.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetScale

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The original actual resize precedes the prescribed number of real one-bit shifts. -/
def code (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) : Circuit ctx ctx :=
  .seq (.classical (FirstRow.resizeOp input output)) (PowerOfTwo.shifts count output)

/-- The recorded store follows exactly the actual resize and the shared native shift loop. -/
def storeStep (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) (store : Store ctx) : Store ctx :=
  PowerOfTwo.shiftsStore count output (store.applyOp (FirstRow.resizeOp input output))

/-- The independent preimage budget counts the actual resize and every required shift. -/
def nativeEnvelope (kind : ProblemKind) (sourceWidth width count : Nat) : ResourcePool kind :=
  ResourcePool.ofList
    (.classicalOperation (.wordResize sourceWidth width) ::
      List.replicate count (.classicalOperation (.wordUnary .shiftLeft width)))

/-- The actual preimage path exposes precisely its chronological native instruction list. -/
theorem nativeLattice_targetScale_trace (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat)
    (path : (code input output count).Path) :
    (code input output count).eventTrace path =
      .classicalOperation (.wordResize sourceWidth width) ::
        List.replicate count (.classicalOperation (.wordUnary .shiftLeft width)) := by
  exact congrArg (List.cons
    (.classicalOperation (.wordResize sourceWidth width) : Resource.Event kind))
    (TerminalShift.flatten_repeated_singleton count
      (.classicalOperation (.wordUnary .shiftLeft width) : Resource.Event kind))

/-- Exact actual preimage multiplicities equal the independent native allowance. -/
theorem nativeLattice_targetScale_pool (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat)
    (path : (code input output count).Path) :
    (code input output count).resourcePool path =
      nativeEnvelope kind sourceWidth width count :=
  congrArg ResourcePool.ofList (nativeLattice_targetScale_trace input output count path)

/-- Actual serial depth includes the resize followed by the complete left-shift loop. -/
theorem nativeLattice_targetScale_depth (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat)
    (duration : Resource.Event kind → Nat) (path : (code input output count).Path) :
    (code input output count).depth duration path =
      duration (.classicalOperation (.wordResize sourceWidth width)) +
        count * duration (.classicalOperation (.wordUnary .shiftLeft width)) := by
  change duration (.classicalOperation (.wordResize sourceWidth width)) +
    (0 + ∑ _ : Fin count, duration (.classicalOperation (.wordUnary .shiftLeft width))) = _
  simp

/-- For all input and output widths the actual result is the correctly truncated source product. -/
theorem nativeLattice_targetScale_read (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) (store : Store ctx) :
    ((storeStep input output count store).read (.storage output.toCStorageRef)).toNat =
      (2 ^ count * (store.read input).toNat) % 2 ^ width := by
  have resized : ((store.applyOp (FirstRow.resizeOp input output)).read
      (.storage output.toCStorageRef)).toNat = (store.read input).toNat % 2 ^ width :=
    congrArg CShape.Value.toNat
      (Store.read_applyOp_output store (FirstRow.resizeOp input output))
  refine (PowerOfTwo.shifts_read count output
    (store.applyOp (FirstRow.resizeOp input output))).trans ?_
  rw [resized, Nat.mul_mod_mod]

/-- The original recovery width contains the exact source preimage without any caller premise. -/
theorem nativeLattice_targetScale_exact (N m ell : Nat)
    (input : CInputRef ctx (.unsignedWord ell))
    (output : CWriteRef ctx (.unsignedWord (RSA.ShortLogWidths.coordinateWidth N m ell)))
    (store : Store ctx) :
    ((storeStep input output m store).read (.storage output.toCStorageRef)).toNat =
      2 ^ m * (store.read input).toNat := by
  have sourceBound : 2 ^ m * (store.read input).toNat < 2 ^ (ell + m) := by
    calc
      2 ^ m * (store.read input).toNat < 2 ^ m * 2 ^ ell :=
        Nat.mul_lt_mul_of_pos_left (store.read input).toNat_lt (Nat.two_pow_pos m)
      _ = 2 ^ (m + ell) := (pow_add 2 m ell).symm
      _ = 2 ^ (ell + m) := congrArg (fun exponent : Nat => 2 ^ exponent) (Nat.add_comm m ell)
  exact (nativeLattice_targetScale_read input output m store).trans
    (Nat.mod_eq_of_lt (sourceBound.trans
      (RSA.ShortLogWidths.shortLog_sourceModulus_lt_coordinateCapacity N m ell)))

/-- The actual preimage load preserves every structural read outside its written destination. -/
theorem nativeLattice_targetScale_read_other
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) {shape : CShape}
    (other : CInputRef ctx shape) (different : output.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep input output count store).read other = store.read other :=
  (PowerOfTwo.shifts_read_other count output other different
    (store.applyOp (FirstRow.resizeOp input output))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (FirstRow.resizeOp input output) other different)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetScale

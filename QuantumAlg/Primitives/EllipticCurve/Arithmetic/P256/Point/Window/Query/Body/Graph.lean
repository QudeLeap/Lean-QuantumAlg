/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Body

/-!
# Original table graph and full pool at the actual query-body endpoints

Both concrete native body endpoints change only the selected arithmetic
target. Complete original source/address readouts retain the same table
graph, and every bit of the original scan pool has its old value. These
are direct consumers of the full-label coordinates, rather than extra
graph or restoration assumptions for a final point endpoint.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

lemma ordinaryStep_graph (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ 256))
    (graph : (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph
      table state) :
    (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph table
      (ordinaryStep stream (highRemaining + lowWidth) bounded ports state) := by
  let prepared := arithmeticSource stream (highRemaining + lowWidth) bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  have original :
      (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph table
        (arithmeticInput stream (highRemaining + lowWidth) bounded ports
          (ports.source.value prepared) (ports.target.value prepared)
          (ports.multiplier.value prepared) retained state.2) :=
    (state_eq_arithmeticInput stream _ bounded ports state clean) ▸ graph
  exact arithmeticInput_graph_update stream highRemaining lowWidth bounded lowBound ports
    (ports.source.value prepared) (ports.target.value prepared)
    (if (Native.BorrowedControl.controlBit ports).get retained then
      ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared)
    (ports.multiplier.value prepared) retained state.2 table original

lemma exceptionalStep_graph (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ 256))
    (graph : (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph
      table state) :
    (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph table
      (exceptionalStep stream (highRemaining + lowWidth) bounded ports state) := by
  let prepared := arithmeticSource stream (highRemaining + lowWidth) bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  have original :
      (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph table
        (arithmeticInput stream (highRemaining + lowWidth) bounded ports
          (ports.source.value prepared) (ports.target.value prepared)
          (ports.multiplier.value prepared) retained state.2) :=
    (state_eq_arithmeticInput stream _ bounded ports state clean) ▸ graph
  exact arithmeticInput_graph_update stream highRemaining lowWidth bounded lowBound ports
    (ports.source.value prepared) (ports.target.value prepared)
    (if (Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained) then
      ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared)
    (ports.multiplier.value prepared) retained state.2 table original

lemma ordinaryStep_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    Frame.CleanPool (ordinaryStep stream width bounded ports state).1 := by
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  have original : Frame.CleanPool
      (arithmeticInput stream width bounded ports (ports.source.value prepared)
        (ports.target.value prepared) (ports.multiplier.value prepared) retained state.2).1 :=
    (state_eq_arithmeticInput stream width bounded ports state clean) ▸ clean
  exact arithmeticInput_cleanPool_update stream width bounded ports
    (ports.source.value prepared) (ports.target.value prepared)
    (if (Native.BorrowedControl.controlBit ports).get retained then
      ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared)
    (ports.multiplier.value prepared) retained state.2 original

lemma exceptionalStep_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    Frame.CleanPool (exceptionalStep stream width bounded ports state).1 := by
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  have original : Frame.CleanPool
      (arithmeticInput stream width bounded ports (ports.source.value prepared)
        (ports.target.value prepared) (ports.multiplier.value prepared) retained state.2).1 :=
    (state_eq_arithmeticInput stream width bounded ports state clean) ▸ clean
  exact arithmeticInput_cleanPool_update stream width bounded ports
    (ports.source.value prepared) (ports.target.value prepared)
    (if (Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained) then
      ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared)
    (ports.multiplier.value prepared) retained state.2 original

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

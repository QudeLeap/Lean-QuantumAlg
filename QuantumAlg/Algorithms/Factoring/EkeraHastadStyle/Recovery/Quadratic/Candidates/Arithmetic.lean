/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Execution
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Readout
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Separation
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.StoreSemantics

/-!
# Actual quadratic words equal the original source candidates

Each equality below follows the real store update that produced the next
operand. Source word bounds discharge every modular arithmetic capacity
condition; the actual lexical layout discharges the internal key separation.
The resulting two words are the original lower and upper candidates for
every represented logarithm and modulus, before either divisor is accepted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem op_read_cell {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (.storage other.toCStorageRef) =
      store.read (.storage other.toCStorageRef) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

/-- Both actually materialized words are precisely the original source candidate pair. -/
theorem nativeQuadratic_candidates_read (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (separated : Separated modulus refs) (store : Store ctx) :
    (((candidatesStep input modulus refs store).1.read (.storage refs.first.toCStorageRef)).toNat,
      ((candidatesStep input modulus refs store).1.read
        (.storage refs.second.toCStorageRef)).toNat) =
        RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat := by
  let widened := store.applyOp (widenOp input refs)
  let centered := widened.applyOp (centerOp refs)
  let squared := centered.applyOp (squareOp refs)
  let reduced := NativeSub.intoStep (.storage refs.root.toCStorageRef) modulus refs.root squared
  let rooted := NativeSqrt.intoStep (.storage refs.root.toCStorageRef) refs.root reduced.1
  let lower := NativeSub.intoStep (.storage refs.center.toCStorageRef)
    (.storage refs.root.toCStorageRef) refs.first rooted.1
  have widenedValue := nativeQuadratic_widen_read input refs store
  have centerFits : (widened.read (.storage refs.center.toCStorageRef)).toNat + 1 <
      2 ^ RSA.quadraticWordWidth width := by
    rw [widenedValue]
    exact RSA.quadraticCenter_lt_wordCapacity (store.read input).toNat_lt
  have centerValue : (centered.read (.storage refs.center.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat :=
    (nativeQuadratic_center_read_of_fits refs widened centerFits).trans
      (congrArg (fun value : Nat => value + 1) widenedValue)
  have squareFits : (centered.read (.storage refs.center.toCStorageRef)).toNat ^ 2 <
      2 ^ RSA.quadraticWordWidth width := by
    rw [centerValue]
    exact RSA.quadraticSquare_lt_wordCapacity (store.read input).toNat_lt
  have squareValue : (squared.read (.storage refs.root.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat ^ 2 :=
    (nativeQuadratic_square_read_of_fits refs centered squareFits).trans
      (congrArg (fun value : Nat => value ^ 2) centerValue)
  have modulusWidened : widened.read modulus = store.read modulus :=
    Store.read_applyOp_of_not_mem_storageKeys store (widenOp input refs) modulus
      (separated.modulusFree refs.center.key (by simp [writeKeys]))
  have modulusCentered : centered.read modulus = store.read modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys widened (centerOp refs) modulus
      (separated.modulusFree refs.center.key (by simp [writeKeys]))).trans modulusWidened
  have modulusSquared : squared.read modulus = store.read modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys centered (squareOp refs) modulus
      (separated.modulusFree refs.root.key (by simp [writeKeys]))).trans modulusCentered
  have discriminantValue : (reduced.1.read (.storage refs.root.toCStorageRef)).toNat =
      RSA.quadraticDiscriminant (store.read modulus).toNat (store.read input).toNat :=
    (NativeSub.nativeSub_into_read_output
      (.storage refs.root.toCStorageRef) modulus refs.root squared).trans
      (congrArg₂ (fun first second : Nat => first - second)
        squareValue (congrArg CShape.Value.toNat modulusSquared))
  have centerSquared : (squared.read (.storage refs.center.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat :=
    (congrArg CShape.Value.toNat
      (op_read_cell (squareOp refs) refs.center separated.centerRoot.symm centered)).trans
      centerValue
  have centerReduced : (reduced.1.read (.storage refs.center.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat :=
    (congrArg CShape.Value.toNat
      (NativeSub.nativeSub_into_read_unchanged (.storage refs.root.toCStorageRef) modulus refs.root
        (.storage refs.center.toCStorageRef)
        (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separated.centerRoot.symm)
        squared)).trans centerSquared
  have rootValue : (rooted.1.read (.storage refs.root.toCStorageRef)).toNat =
      Nat.sqrt (RSA.quadraticDiscriminant (store.read modulus).toNat (store.read input).toNat) :=
    (NativeSqrt.nativeSqrt_into_read_output
      (.storage refs.root.toCStorageRef) refs.root reduced.1).trans
      (congrArg Nat.sqrt discriminantValue)
  have centerRooted : (rooted.1.read (.storage refs.center.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat :=
    (congrArg CShape.Value.toNat
      (NativeSqrt.nativeSqrt_into_read_unchanged (.storage refs.root.toCStorageRef) refs.root
        (.storage refs.center.toCStorageRef)
        (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separated.centerRoot.symm)
        reduced.1)).trans centerReduced
  have firstValue : (lower.1.read (.storage refs.first.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat -
        Nat.sqrt (RSA.quadraticDiscriminant (store.read modulus).toNat (store.read input).toNat) :=
    (NativeSub.nativeSub_into_read_output (.storage refs.center.toCStorageRef)
      (.storage refs.root.toCStorageRef) refs.first rooted.1).trans
      (congrArg₂ (fun first second : Nat => first - second) centerRooted rootValue)
  have centerLowered : (lower.1.read (.storage refs.center.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat :=
    (congrArg CShape.Value.toNat
      (NativeSub.nativeSub_into_read_unchanged (.storage refs.center.toCStorageRef)
        (.storage refs.root.toCStorageRef) refs.first (.storage refs.center.toCStorageRef)
        (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separated.centerFirst.symm)
        rooted.1)).trans centerRooted
  have rootLowered : (lower.1.read (.storage refs.root.toCStorageRef)).toNat =
      Nat.sqrt (RSA.quadraticDiscriminant (store.read modulus).toNat (store.read input).toNat) :=
    (congrArg CShape.Value.toNat
      (NativeSub.nativeSub_into_read_unchanged (.storage refs.center.toCStorageRef)
        (.storage refs.root.toCStorageRef) refs.first (.storage refs.root.toCStorageRef)
        (by simpa only [CInputRef.storageKeys, List.mem_singleton] using separated.rootFirst.symm)
        rooted.1)).trans rootValue
  have secondFits : (lower.1.read (.storage refs.center.toCStorageRef)).toNat +
      (lower.1.read (.storage refs.root.toCStorageRef)).toNat <
        2 ^ RSA.quadraticWordWidth width := by
    rw [centerLowered, rootLowered]
    exact RSA.quadraticSecond_lt_wordCapacity (store.read modulus).toNat (store.read input).toNat_lt
  have secondValue : ((lower.1.applyOp (secondOp refs)).read
      (.storage refs.second.toCStorageRef)).toNat =
      RSA.quadraticCenter (store.read input).toNat +
        Nat.sqrt (RSA.quadraticDiscriminant (store.read modulus).toNat (store.read input).toNat) :=
    (nativeQuadratic_second_read_of_fits refs lower.1 secondFits).trans
      (congrArg₂ (fun first second : Nat => first + second) centerLowered rootLowered)
  have firstFinal := (congrArg CShape.Value.toNat
    (op_read_cell (secondOp refs) refs.first separated.firstSecond.symm lower.1)).trans firstValue
  rw [RSA.quadraticFactorCandidates_eq]
  exact Prod.ext firstFinal secondValue

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

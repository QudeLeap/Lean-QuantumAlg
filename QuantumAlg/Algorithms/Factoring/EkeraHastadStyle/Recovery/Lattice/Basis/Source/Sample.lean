/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Source.Integer
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Samples.Readout

/-!
# Original integer basis from the actual retained terminal pair

The two original terminal values are read before any temporary cells are
entered. Their actual decoder steps materialize both samples, and actual
basis loading then reads those j cells. The resulting signed interpretation
is exactly the original short-log source basis for those terminal values.
This connects the source model to the actual store updates; full execution
laws of the two prefixes are supplied by their separate native owners.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- Actual decoding followed by native basis loading yields the original source integer basis. -/
theorem nativeLattice_sample_basis_source (N : Nat)
    (first second : CInputRef ctx (.bits ((ell + m) + ell))) (store : Store ctx) :
    let samples :=
      (BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read first)),
        BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read second)))
    let sampleContext := SampleLayout.context ctx m ell
    let decoded := (SampleLayout.decodeStep first second (SampleLayout.pushStore m ell store)).1
    let firstJ : CInputRef sampleContext (.unsignedWord (ell + m)) :=
      .storage (SampleLayout.firstRefs ctx m ell).j.toCStorageRef
    let secondJ : CInputRef sampleContext (.unsignedWord (ell + m)) :=
      .storage (SampleLayout.secondRefs ctx m ell).j.toCStorageRef
    let width := RSA.ShortLogWidths.coordinateWidth N m ell
    let result := storeStep firstJ secondJ width (ell + m) (BasisLayout.pushStore width decoded)
    BasisLayout.integerBasis sampleContext width result = RSA.shortLogLatticeBasis m ell samples ∧
      BasisLayout.integerRow (BasisLayout.target sampleContext width) result = (0, 0, 0) := by
  let samples :=
    (BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read first)),
      BatchRecovery.decodeTerminalSample m ell (terminalValue (store.read second)))
  let sampleContext := SampleLayout.context ctx m ell
  let decoded : Store sampleContext :=
    (SampleLayout.decodeStep first second (SampleLayout.pushStore m ell store)).1
  let firstJ : CInputRef sampleContext (.unsignedWord (ell + m)) :=
    .storage (SampleLayout.firstRefs ctx m ell).j.toCStorageRef
  let secondJ : CInputRef sampleContext (.unsignedWord (ell + m)) :=
    .storage (SampleLayout.secondRefs ctx m ell).j.toCStorageRef
  have source := SampleLayout.nativeLattice_sample_decode_source first second store
  have firstValue : (decoded.read firstJ).toNat = samples.1.1.val :=
    congrArg (fun values : (Nat × Nat) × (Nat × Nat) => values.1.1) source
  have secondValue : (decoded.read secondJ).toNat = samples.2.1.val :=
    congrArg (fun values : (Nat × Nat) × (Nat × Nat) => values.2.1) source
  have firstRow : (((decoded.read firstJ).toNat : Int),
      ((decoded.read secondJ).toNat : Int), (1 : Int)) =
      ((samples.1.1.val : Int), (samples.2.1.val : Int), (1 : Int)) :=
    Prod.ext (congrArg (fun value : Nat => (value : Int)) firstValue)
      (Prod.ext (congrArg (fun value : Nat => (value : Int)) secondValue) rfl)
  have sourceBasis :
      ({ first := ((decoded.read firstJ).toNat, (decoded.read secondJ).toNat, 1)
         second := ((2 ^ (ell + m) : Nat), 0, 0)
         third := (0, (2 ^ (ell + m) : Nat), 0) } : NumberTheory.IntegerBasis3) =
        RSA.shortLogLatticeBasis m ell samples := by
    exact congrArg (fun row : NumberTheory.IntegerPoint3 =>
      (NumberTheory.IntegerBasis3.mk row ((2 ^ (ell + m) : Nat), 0, 0)
        (0, (2 ^ (ell + m) : Nat), 0))) firstRow
  have actual := nativeLattice_basis_initialization_integer_source N m ell firstJ secondJ decoded
  exact ⟨actual.1.trans sourceBasis, actual.2⟩

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

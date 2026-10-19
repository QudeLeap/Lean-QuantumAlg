/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Stages
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Semantics
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Primitives.ShortDLP.Oracle.Stage.Readout
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Actual old preparation and complete two-bank inverse-Fourier rows

These are entries of the existing native
preparationCircuit, compiledGroupActionProgram and readoutCircuit. Preparation
keeps every supplied workspace basis label. Both readout factors are the actual
complete Native.inverseCircuit, including their SWAPs. The source units below
describe the internally prepared clean span; no external input certificate or
new unitary circuit is introduced.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordStages

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumFourierTransform.Semiclassical
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Actual Hadamards prepare both exponent words and preserve every workspace basis label. -/
lemma preparation_column (params : RegisterParameters)
    (first : Fin (2 ^ firstBits params)) (second : Fin (2 ^ params.ell))
    (workspace seed : Fin (2 ^ params.workspaceBits)) :
    ((preparationCircuit params).binaryMatrix environment) (tripleIndex params first second
      workspace)
        (tripleIndex params 0 0 seed) =
      WalshHadamard.invSqrtCard (firstBits params) * WalshHadamard.invSqrtCard params.ell *
        (if workspace = seed then 1 else 0) := by
  have prepared := congrArg
    (fun state : HilbertVector (Qubits (totalQubits params)) =>
      state (tripleIndex params first second workspace))
    (preparationCircuit_apply_basisWorkspace (environment := environment) params seed)
  change ((preparationCircuit params).binaryMatrix environment).applyVec
    (NormalizedVector.ket (R := Qubits (totalQubits params))
      (tripleIndex params 0 0 seed) : HilbertVector (Qubits (totalQubits params)))
        (tripleIndex params first second workspace) = _ at prepared
  simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    HilbertVector.tensor_apply, tripleIndex, Equiv.symm_apply_apply,
    WalshHadamard.uniformState_apply, NormalizedVector.ket_apply] using prepared

/-- The normalization is identical to the shared literal all-bank Hadamard preparation. -/
lemma normalization (bits : Nat) :
    WalshHadamard.invSqrtCard bits = NormalizedVector.invSqrt2 ^ bits := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (WalshHadamard.Native.normalization_product bits).symm

/-- The actual readout is the two complete native inverse-QFT matrices, with workspace identity. -/
lemma readout_entry (params : RegisterParameters)
    (first sourceFirst : Fin (2 ^ firstBits params))
    (second sourceSecond : Fin (2 ^ params.ell))
    (workspace sourceWorkspace : Fin (2 ^ params.workspaceBits)) :
    ((readoutCircuit params).binaryMatrix environment) (tripleIndex params first second workspace)
        (tripleIndex params sourceFirst sourceSecond sourceWorkspace) =
      ((QuantumFourierTransform.Native.inverseCircuit .empty (firstBits params)).binaryMatrix
        environment)
          first sourceFirst *
        ((QuantumFourierTransform.Native.inverseCircuit .empty params.ell).binaryMatrix environment)
          second sourceSecond *
        (if workspace = sourceWorkspace then 1 else 0) := by
  rw [readoutCircuit, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    DeclaredStage.readoutPair_binaryMatrix]
  simp only [UnitaryOperator.tensor_apply, tripleIndex, Equiv.symm_apply_apply,
    Matrix.UnitaryGroup.one_apply, Matrix.one_apply]

/-- The exact row used by the shared partner theorem is extracted from this old readout. -/
lemma readout_fullRows (params : RegisterParameters)
    (first sourceFirst : Fin (2 ^ firstBits params))
    (second sourceSecond : Fin (2 ^ params.ell))
    (workspace sourceWorkspace : Fin (2 ^ params.workspaceBits)) :
    ((readoutCircuit params).binaryMatrix environment) (tripleIndex params first second workspace)
        (tripleIndex params sourceFirst sourceSecond sourceWorkspace) =
      Partner.fullRows true (firstBits params) first ((binaryEquiv _).symm sourceFirst) *
        Partner.fullRows true params.ell second ((binaryEquiv _).symm sourceSecond) *
        (if workspace = sourceWorkspace then 1 else 0) := by
  cases Subsingleton.elim environment OracleModel.emptyInterpretation
  rw [readout_entry]
  simp only [Partner.fullRows, ↓reduceIte, Equiv.apply_symm_apply]
  rfl

variable (m ell width N : Nat) [NeZero N] (nontrivial : 1 < N) (fits : N < 2 ^ width)

include nontrivial fits in
omit [NeZero N] in
/-- Every canonical unit partner is prepared uniformly; no seed-one specialization is used. -/
lemma preparation_clean_column
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (value seed : (ZMod N)ˣ) :
    ((preparationCircuit (registerParameters m ell width)).binaryMatrix environment)
        (cleanLabel m ell width N first second value) (cleanLabel m ell width N 0 0 seed) =
      NormalizedVector.invSqrt2 ^ (ell + m) * NormalizedVector.invSqrt2 ^ ell *
        (if value = seed then 1 else 0) := by
  rw [cleanLabel_eq_tripleIndex, cleanLabel_eq_tripleIndex, preparation_column]
  simp only [(cleanUnitLabel_injective width N nontrivial fits).eq_iff, normalization]
  rfl

include nontrivial fits in
omit [NeZero N] in
/-- Both complete native Fourier rows preserve all clean-unit coherences exactly. -/
lemma readout_clean_entry
    (first sourceFirst : Fin (2 ^ (ell + m)))
    (second sourceSecond : Fin (2 ^ ell)) (value seed : (ZMod N)ˣ) :
    ((readoutCircuit (registerParameters m ell width)).binaryMatrix environment)
        (cleanLabel m ell width N first second value)
        (cleanLabel m ell width N sourceFirst sourceSecond seed) =
      Partner.fullRows true (ell + m) first ((binaryEquiv _).symm sourceFirst) *
        Partner.fullRows true ell second ((binaryEquiv _).symm sourceSecond) *
        (if value = seed then 1 else 0) := by
  rw [cleanLabel_eq_tripleIndex, cleanLabel_eq_tripleIndex, readout_fullRows]
  simp only [(cleanUnitLabel_injective width N nontrivial fits).eq_iff]
  rfl

include nontrivial fits in
omit [NeZero N] in
/-- The original compiled exponent circuits provide this column for every clean partner seed. -/
lemma group_clean_column (generator target : (ZMod N)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (seed : (ZMod N)ˣ) (output : Fin (2 ^ totalQubits (registerParameters m ell width))) :
    ((compiledGroupActionProgram m ell width N generator target).binaryMatrix environment) output
        (cleanLabel m ell width N first second seed) =
      if output = cleanLabel m ell width N first second
        (oracleValue generator target first.val second.val * seed) then 1 else 0 := by
  let basis := (QubitLayout.canonical
    (totalQubits (registerParameters m ell width))).basisEquiv
  have actual := congrArg
    (fun state : NormalizedVector
        (QubitLayout.canonical
          (totalQubits (registerParameters m ell width))).toQuantum.register =>
      state (basis.symm output))
    (compiledGroupActionProgram_applyLabel_clean (environment := environment) m ell width N
      generator target first second seed
      nontrivial fits)
  simp only [UnitaryCircuit.applyNormalized, UnitaryOperator.apply_coe,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] at actual
  change ((compiledGroupActionProgram m ell width N generator target).binaryMatrix environment)
    output
    (cleanLabel m ell width N first second seed) =
      if basis.symm output = basis.symm (cleanLabel m ell width N first second
        (oracleValue generator target first.val second.val * seed)) then 1 else 0 at actual
  simpa only [basis.symm.injective.eq_iff] using actual

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordStages

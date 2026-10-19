/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Core.Execution.Prepare
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Util.FinPow

/-!
# Fresh owned qubits before a supplied owned input

The input systems occupy a fixed physical suffix. Preparation allocates only
the disjoint prefix. Both words are owned, so the algorithm may change the
input; every live system remains in its output and contributes to resident
and owned auxiliary space. The basis map uses the actual preparation tensor
coordinates and the original ordered input wires.
-/

namespace QuantumAlg.Execution.OwnedQubitPrefix

noncomputable section

/-- Physical qubits reserved for the fresh prefix. -/
def prefixLayout (freshWidth : Nat) : QubitLayout freshWidth :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

/-- The supplied input begins immediately after the reserved prefix. -/
def inputLayout (freshWidth width : Nat) : QubitLayout width :=
  { physical_idx := fun index => freshWidth + index.val
    physical_idx_injective := fun _left _right equal =>
      Fin.ext (Nat.add_left_cancel equal) }

/-- Only the supplied input is live initially; its ownership permits an actual state change. -/
@[reducible] public def pre (freshWidth width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨1⟩ (inputLayout freshWidth width).toQuantumLayout
    (by decide) (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

lemma prefix_fresh (freshWidth width : Nat) :
    (⟨0⟩ : StorageKey) ∉ (pre freshWidth width).keys := by
  change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]
  decide

lemma prefix_disjoint (freshWidth width : Nat) :
    List.Disjoint (prefixLayout freshWidth).toQuantumLayout.identities
      (pre freshWidth width).physicalIdx := by
  change List.Disjoint (List.ofFn (fun index : Fin freshWidth => index.val))
    (((List.ofFn (fun index : Fin width =>
      ({ identity := freshWidth + index.val, dimension := 2 } : QuantumWire))) ++ []).map
        QuantumWire.identity)
  simp only [List.append_nil, List.map_ofFn]
  apply List.disjoint_left.mpr
  intro wire inPrefix inInput
  obtain ⟨prefixIndex, rfl⟩ := List.mem_ofFn.mp inPrefix
  obtain ⟨inputIndex, same⟩ := List.mem_ofFn.mp inInput
  have bound := prefixIndex.isLt
  change freshWidth + inputIndex.val = prefixIndex.val at same
  omega

/-- Both actual words remain live after the single prefix preparation. -/
@[reducible] public def post (freshWidth width : Nat) : RuntimeCtx .quantum :=
  (pre freshWidth width).addOwnedLayout ⟨0⟩ (prefixLayout freshWidth).toQuantumLayout
    (prefix_fresh freshWidth width) (prefix_disjoint freshWidth width)

private lemma input_wires (freshWidth width : Nat) :
    (inputLayout freshWidth width).toQuantumLayout.wires =
      (pre freshWidth width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change _ = (inputLayout freshWidth width).toQuantumLayout.wires ++ []
  exact (List.append_nil _).symm

/-- Big-endian values of exactly the original supplied physical systems. -/
public def inputBasisEquiv (freshWidth width : Nat) :
    (pre freshWidth width).register.Index ≃ (Qubits width).Index :=
  (basisOfEqualWires (inputLayout freshWidth width).toQuantumLayout
    (pre freshWidth width).quantumLayout (input_wires freshWidth width)).symm.trans
      (inputLayout freshWidth width).binaryIndexEquiv

/-- The interpreter's real tensor coordinates for fresh and original systems. -/
def assembly (freshWidth width : Nat) :
    ((prefixLayout freshWidth).toQuantumLayout.register.Index ×
      (pre freshWidth width).register.Index) ≃
      (post freshWidth width).register.Index :=
  preparedLocalBasisEquiv (pre freshWidth width) ⟨0⟩ (prefixLayout freshWidth).toQuantumLayout
    (prefix_fresh freshWidth width) (prefix_disjoint freshWidth width)

/-- The complete binary frame records the actual fresh prefix followed by the original input. -/
def basisEquiv (freshWidth width : Nat) :
    (post freshWidth width).register.Index ≃ (Qubits (freshWidth + width)).Index :=
  (assembly freshWidth width).symm.trans
    (((prefixLayout freshWidth).binaryIndexEquiv.prodCongr (inputBasisEquiv freshWidth width)).trans
      prodEquiv)

/-- Actual preparation has exactly the claimed prefix/input binary concatenation. -/
lemma basisEquiv_assembly (freshWidth width : Nat)
    (fresh : (prefixLayout freshWidth).toQuantumLayout.register.Index)
    (original : (pre freshWidth width).register.Index) :
    basisEquiv freshWidth width (assembly freshWidth width (fresh, original)) =
      prodEquiv ((prefixLayout freshWidth).binaryIndexEquiv fresh,
        inputBasisEquiv freshWidth width original) := by
  let encodePair (pair : (prefixLayout freshWidth).toQuantumLayout.register.Index ×
      (pre freshWidth width).register.Index) : Fin (2 ^ (freshWidth + width)) :=
    prodEquiv ((prefixLayout freshWidth).binaryIndexEquiv pair.1,
      inputBasisEquiv freshWidth width pair.2)
  change encodePair
    ((assembly freshWidth width).symm (assembly freshWidth width (fresh, original))) =
    encodePair (fresh, original)
  exact congrArg encodePair ((assembly freshWidth width).symm_apply_apply (fresh, original))

/-- The canonical full physical interface follows from the actual ordered wire records. -/
lemma post_physicalIdx (freshWidth width : Nat) :
    (post freshWidth width).physicalIdx = List.range (freshWidth + width) := by
  change ((List.ofFn (fun index : Fin freshWidth =>
      ({ identity := index.val, dimension := 2 } : QuantumWire))) ++
      ((List.ofFn (fun index : Fin width =>
        ({ identity := freshWidth + index.val, dimension := 2 } : QuantumWire))) ++ [])).map
      QuantumWire.identity = _
  simp only [List.append_nil, List.map_append, List.map_ofFn]
  calc
    _ = List.ofFn (fun index : Fin (freshWidth + width) => index.val) := by
      rw [List.ofFn_add]
      rfl
    _ = _ := by
      apply List.ext_getElem
      · simp
      · intro index _left _right
        simp

/-- No input value is disguised as borrowed storage in this destructive-input frame. -/
lemma pre_noBorrowedQuantum (freshWidth width : Nat) :
    (pre freshWidth width).borrowedQuantumWires = [] :=
  rfl

lemma post_noBorrowedQuantum (freshWidth width : Nat) :
    (post freshWidth width).borrowedQuantumWires = [] := rfl

/-- The actual zero vector of the reserved physical prefix. -/
def zeroPreparation (freshWidth : Nat) :
    BasisPreparation (prefixLayout freshWidth).toQuantumLayout :=
  BasisPreparation.zero (prefixLayout freshWidth).toQuantumLayout

/-- Allocate exactly the reserved prefix through the fixed zero-preparation instruction. -/
def prepareCode (gates : GateModel) (oracles : OracleModel) (freshWidth width : Nat)
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty) :
    Circuit (.quantum gates oracles operations services)
      (pre freshWidth width) (post freshWidth width) :=
  .prepareZero (pre freshWidth width) ⟨0⟩ (prefixLayout freshWidth).toQuantumLayout
    (prefix_fresh freshWidth width) (prefix_disjoint freshWidth width)

/-- Preparation pays once per physical prefix qubit and nothing for an empty prefix. -/
lemma prepareCode_events (gates : GateModel) (oracles : OracleModel) (freshWidth width : Nat)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (path : (prepareCode gates oracles freshWidth width operations services).Path) :
    (prepareCode gates oracles freshWidth width operations services).eventTrace path =
      List.replicate freshWidth
        (.preparation (model := .quantum gates oracles operations services) (2 : ℕ+)) := by
  exact ZeroPreparation.zeroPreparation_uniform_trace gates oracles
    (prefixLayout freshWidth).toQuantumLayout 2 (fun _ => rfl) operations services

/-- The prepared word is exactly the canonical prefix followed by the original input wires. -/
lemma post_canonical_wires (freshWidth width : Nat) :
    (QuantumSignature.qubits (freshWidth + width)).canonicalPlacement.layout.wires =
      (post freshWidth width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change List.ofFn (fun index : Fin (freshWidth + width) =>
      ({ identity := index.val, dimension := 2 } : QuantumWire)) =
    List.ofFn (fun index : Fin freshWidth =>
      ({ identity := index.val, dimension := 2 } : QuantumWire)) ++
      (List.ofFn (fun index : Fin width =>
        ({ identity := freshWidth + index.val, dimension := 2 } : QuantumWire)) ++ [])
  rw [List.append_nil, List.ofFn_add]
  rfl

end

end QuantumAlg.Execution.OwnedQubitPrefix

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Execution.Input
public import QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Mathematics
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Store

/-!
# The actual borrowed modular base of general order finding

The caller supplies the original canonical-residue cell. Input validity binds
each positive-probability classical block to that same reduced base and cannot
constrain an external reference. The source base is subsequently read through
its structural reference, rather than reconstructed as a replacement runtime input.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

open QuantumAlg.Execution

/-- The original borrowed base's physical storage identity. -/
def baseKey : StorageKey := ⟨0⟩

theorem baseFresh :
    baseKey ∉ (RuntimeCtx.empty : RuntimeCtx .quantum).keys := by decide

/-- The original caller-owned canonical-residue cell remains in the runtime input. -/
@[reducible] public def pre (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput baseKey (.canonicalResidue width) baseFresh

/-- Read the actual borrowed modular-base cell. -/
public def baseSourceRef (width : Nat) : CInputRef (pre width) (.canonicalResidue width) :=
  .storage (CStorageRef.borrowedInputHead RuntimeCtx.empty baseKey
    (.canonicalResidue width) baseFresh)

/-- The sole initial entry has the source's original borrowed storage role and width. -/
theorem pre_entries (width : Nat) :
    (pre width).entries = [.storage baseKey .borrowedInput (.canonicalResidue width)] := rfl

theorem pre_quantumWires (width : Nat) : (pre width).quantumWires = [] := rfl

private def borrowedValues (width : Nat) (value : CShape.Value (.canonicalResidue width)) :
    ∀ key role shape,
      RuntimeEntry.storage key role shape ∈ (pre width).entries → CShape.Value shape := by
  intro key role shape present
  have same : RuntimeEntry.storage key role shape =
      RuntimeEntry.storage baseKey .borrowedInput (.canonicalResidue width) :=
    List.mem_singleton.mp present
  exact (RuntimeEntry.storage.inj same).2.2.symm ▸ value

/-- Initialize only the actual pre-existing borrowed cell with a supplied raw residue encoding. -/
def storeOfBase (width : Nat) (value : CShape.Value (.canonicalResidue width)) :
    Store (pre width) :=
  Store.ofValues (pre width) (borrowedValues width value)

/-- Reading the initialized borrowed cell returns the actual supplied value. -/
theorem storeOfBase_read (width : Nat) (value : CShape.Value (.canonicalResidue width)) :
    (storeOfBase width value).read (baseSourceRef width) = value := by
  rw [storeOfBase, baseSourceRef, Store.read_ofValues]
  rfl

/-- The original source base represented at its actual nominal classical width. -/
def encodedBase {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) : CShape.Value (.canonicalResidue width) :=
  .canonicalResidue ⟨(baseResidue hinput A).val,
    lt_of_lt_of_le (baseResidue hinput A).isLt A.register_fits⟩

/-- A canonical concrete input store is available without supplying workspace or execution data. -/
def inputStore {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) : Store (pre width) :=
  storeOfBase width (encodedBase hinput A)

theorem inputStore_read_base {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    (inputStore hinput A).read (baseSourceRef width) = encodedBase hinput A :=
  storeOfBase_read width (encodedBase hinput A)

/-- The original canonical-base restriction, applied to actual local classical block support. -/
def HasCanonicalBase {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width)
    (state : ExecutionState (Store (pre width)) (pre width).register) : Prop :=
  ∀ store, 0 < (state.block store).mass →
    store.read (baseSourceRef width) = encodedBase hinput A

/-- Local validity constrains the same supported store in every external-reference extension. -/
theorem canonicalBase_read_of_supported {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState)
    (store : Store (pre width)) (supported : 0 < (input.state.block store).mass) :
    store.read (baseSourceRef width) = encodedBase hinput A := by
  apply valid store
  rw [Execution.Input.localState_block_mass]
  exact supported

end

end QuantumAlg.OrderFinding.ShorSourceJoint

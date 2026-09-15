/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Core.Execution.Store

/-!
# Original borrowed ECDLP input context

The original two public point keys, identity-inclusive values and structural
reads are retained in the actual store carrier. These are caller-supplied
inputs. No allocation instruction, quantum initialization, or recovery
workspace is part of this context.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Runtime.Context

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- First deterministic borrowed-input key. -/
def baseKey : StorageKey :=
  RuntimeCtx.canonicalFreshKey (RuntimeCtx.empty : RuntimeCtx .quantum)

theorem baseFresh :
    baseKey ∉ (RuntimeCtx.empty : RuntimeCtx .quantum).keys :=
  RuntimeCtx.canonicalFreshKey_fresh _

/-- Context after admitting the canonical base point. -/
abbrev baseInputCtx (E : PrimeFieldShortWeierstrass p) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput baseKey (PointShape E) baseFresh

/-- Second deterministic borrowed-input key. -/
def targetKey (E : PrimeFieldShortWeierstrass p) : StorageKey :=
  RuntimeCtx.canonicalFreshKey (baseInputCtx E)

theorem targetFresh (E : PrimeFieldShortWeierstrass p) :
    targetKey E ∉ (baseInputCtx E).keys :=
  RuntimeCtx.canonicalFreshKey_fresh _

/-- Initial runtime context containing exactly the public base and target.  The
instance parameter keeps this context aligned with the instance-specific inputs. -/
@[nolint unusedArguments, reducible] public def pre (_I : ECDLPInstance E) : RuntimeCtx .quantum :=
  (baseInputCtx E).addBorrowedInput (targetKey E) (PointShape E)
    (targetFresh E)

/-- Initial store for the public ECDLP instance. -/
def inputStore (I : ECDLPInstance E) : Execution.Store (pre I) :=
  ⟨targetValue I, baseValue I, ()⟩

/-- Structural read of the canonical base point. -/
def baseRef (I : ECDLPInstance E) : CInputRef (pre I) (PointShape E) :=
  .storage
    ((CStorageRef.borrowedInputHead RuntimeCtx.empty baseKey (PointShape E)
      baseFresh).underBorrowedInput (targetKey E) (PointShape E) (targetFresh E))

/-- Structural read of the canonical target point. -/
def targetRef (I : ECDLPInstance E) : CInputRef (pre I) (PointShape E) :=
  .storage
    (CStorageRef.borrowedInputHead (baseInputCtx E) (targetKey E)
      (PointShape E) (targetFresh E))

@[simp] theorem inputStore_base (I : ECDLPInstance E) :
    (inputStore I).read (baseRef I) = baseValue I := by
  rfl

@[simp] theorem inputStore_target (I : ECDLPInstance E) :
    (inputStore I).read (targetRef I) = targetValue I := by
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.Runtime.Context

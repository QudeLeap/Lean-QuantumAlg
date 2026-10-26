/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.ScanMetadata

/-! # Public minimal supplied-tree height for ordinary and carry-width source words -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

open NumberTheory.SharedEEA

/-- The ordinary case uses metadata height; near its power boundary one carry level is needed. -/
def height (width : Nat) : Nat :=
  if width + 3 < 2 ^ width.size then width.size else ScanMetadata.addressWidth width

/-- No branch consumes an unsupplied prefix level. -/
lemma height_fits (width : Nat) : height width ≤ ScanMetadata.addressWidth width := by
  unfold height ScanMetadata.addressWidth
  split <;> omega

/-- The selected public tree includes the whole original work word. -/
lemma height_capacity (width : Nat)
    (full : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) :
    width + 3 ≤ 2 ^ height width := by
  unfold height
  split
  · rename_i narrow
    exact narrow.le
  · exact full

/-- The actual P-256 tree uses nine levels and retains the unused tenth supplied prefix. -/
lemma p256_height : height 256 = 9 := by decide

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

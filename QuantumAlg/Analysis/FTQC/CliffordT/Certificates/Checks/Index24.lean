/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word24Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word24State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word24Step0 :
    word24Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word24State1 := by decide +kernel

private def word24Chunk1 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word24State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word24Step1 :
    word24Chunk1.foldl (fun acc a => a.applyPacked acc)
      word24State1 = word24State2 := by decide +kernel

private def word24Chunk2 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word24State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word24Step2 :
    word24Chunk2.foldl (fun acc a => a.applyPacked acc)
      word24State2 = word24State3 := by decide +kernel

private def word24Chunk3 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word24State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word24Step3 :
    word24Chunk3.foldl (fun acc a => a.applyPacked acc)
      word24State3 = word24State4 := by decide +kernel

private def word24Chunk4 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word24State5 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word24Step4 :
    word24Chunk4.foldl (fun acc a => a.applyPacked acc)
      word24State4 = word24State5 := by decide +kernel

private def word24Chunk5 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word24State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word24Step5 :
    word24Chunk5.foldl (fun acc a => a.applyPacked acc)
      word24State5 = word24State6 := by decide +kernel

private def word24Chunk6 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word24State7 : PackedMat2 :=
    ⟨⟨⟨((15 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((25 : Dyadic) * half ^ 6)⟩,
       ⟨((13 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-47 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((33 : Dyadic) * half ^ 6),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((-19 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word24Step6 :
    word24Chunk6.foldl (fun acc a => a.applyPacked acc)
      word24State6 = word24State7 := by decide +kernel

private def word24Chunk7 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word24State8 : PackedMat2 :=
    ⟨⟨⟨((-11 : Dyadic) * half ^ 5),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-51 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((23 : Dyadic) * half ^ 6),
        ((45 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 6),
        ((17 : Dyadic) * half ^ 6)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word24Step7 :
    word24Chunk7.foldl (fun acc a => a.applyPacked acc)
      word24State7 = word24State8 := by decide +kernel

private def word24Chunk8 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word24State9 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 5),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((-91 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 7),
        ((-9 : Dyadic) * half ^ 8)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((85 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 8)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((85 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((41 : Dyadic) * half ^ 8)⟩,
       ⟨((91 : Dyadic) * half ^ 7),
        ((-37 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word24Step8 :
    word24Chunk8.foldl (fun acc a => a.applyPacked acc)
      word24State8 = word24State9 := by decide +kernel

private def word24Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word24State10 : PackedMat2 :=
    ⟨⟨⟨((-31 : Dyadic) * half ^ 7),
        ((173 : Dyadic) * half ^ 9)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((121 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((93 : Dyadic) * half ^ 8),
        ((39 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((237 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((69 : Dyadic) * half ^ 7),
        ((101 : Dyadic) * half ^ 9)⟩,
       ⟨((-99 : Dyadic) * half ^ 8),
        ((85 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-147 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 9)⟩,
       ⟨((-13 : Dyadic) * half ^ 7),
        ((105 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word24Step9 :
    word24Chunk9.foldl (fun acc a => a.applyPacked acc)
      word24State9 = word24State10 := by decide +kernel

private def word24Chunk10 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word24State11 : PackedMat2 :=
    ⟨⟨⟨((183 : Dyadic) * half ^ 9),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((-57 : Dyadic) * half ^ 9),
        ((59 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-347 : Dyadic) * half ^ 9),
        ((-43 : Dyadic) * half ^ 8)⟩,
       ⟨((197 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((347 : Dyadic) * half ^ 9),
        ((43 : Dyadic) * half ^ 8)⟩,
       ⟨((197 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((183 : Dyadic) * half ^ 9),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((57 : Dyadic) * half ^ 9),
        ((-59 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word24Step10 :
    word24Chunk10.foldl (fun acc a => a.applyPacked acc)
      word24State10 = word24State11 := by decide +kernel

private def word24Chunk11 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word24State12 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 9),
        ((-61 : Dyadic) * half ^ 7)⟩,
       ⟨((41 : Dyadic) * half ^ 8),
        ((85 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-57 : Dyadic) * half ^ 9),
        ((-9 : Dyadic) * half ^ 7)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((-177 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((213 : Dyadic) * half ^ 9),
        ((-43 : Dyadic) * half ^ 10)⟩,
       ⟨((-141 : Dyadic) * half ^ 9),
        ((157 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-37 : Dyadic) * half ^ 8),
        ((75 : Dyadic) * half ^ 10)⟩,
       ⟨((-207 : Dyadic) * half ^ 8),
        ((-89 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word24Step11 :
    word24Chunk11.foldl (fun acc a => a.applyPacked acc)
      word24State11 = word24State12 := by decide +kernel

private def word24Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word24State13 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 6),
        ((131 : Dyadic) * half ^ 11)⟩,
       ⟨((-63 : Dyadic) * half ^ 10),
        ((-1107 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 10),
        ((-219 : Dyadic) * half ^ 11)⟩,
       ⟨((-113 : Dyadic) * half ^ 8),
        ((-15 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 10),
        ((-219 : Dyadic) * half ^ 11)⟩,
       ⟨((113 : Dyadic) * half ^ 8),
        ((15 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 6),
        ((-131 : Dyadic) * half ^ 11)⟩,
       ⟨((-63 : Dyadic) * half ^ 10),
        ((-1107 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word24Step12 :
    word24Chunk12.foldl (fun acc a => a.applyPacked acc)
      word24State12 = word24State13 := by decide +kernel

private def word24Chunk13 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word24State14 : PackedMat2 :=
    ⟨⟨⟨((103 : Dyadic) * half ^ 11),
        ((231 : Dyadic) * half ^ 11)⟩,
       ⟨((-1991 : Dyadic) * half ^ 11),
        ((-5 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-199 : Dyadic) * half ^ 11),
        ((41 : Dyadic) * half ^ 9)⟩,
       ⟨((139 : Dyadic) * half ^ 11),
        ((-1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-43 : Dyadic) * half ^ 9),
        ((169 : Dyadic) * half ^ 11)⟩,
       ⟨((39 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((59 : Dyadic) * half ^ 9),
        ((1047 : Dyadic) * half ^ 11)⟩,
       ⟨((-113 : Dyadic) * half ^ 10),
        ((59 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word24Step13 :
    word24Chunk13.foldl (fun acc a => a.applyPacked acc)
      word24State13 = word24State14 := by decide +kernel

private def word24Chunk14 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word24State15 : PackedMat2 :=
    ⟨⟨⟨((-1245 : Dyadic) * half ^ 12),
        ((1299 : Dyadic) * half ^ 12)⟩,
       ⟨((-499 : Dyadic) * half ^ 12),
        ((-113 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-499 : Dyadic) * half ^ 12),
        ((305 : Dyadic) * half ^ 10)⟩,
       ⟨((1159 : Dyadic) * half ^ 12),
        ((117 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-499 : Dyadic) * half ^ 12),
        ((305 : Dyadic) * half ^ 10)⟩,
       ⟨((-1159 : Dyadic) * half ^ 12),
        ((-117 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1245 : Dyadic) * half ^ 12),
        ((-1299 : Dyadic) * half ^ 12)⟩,
       ⟨((-499 : Dyadic) * half ^ 12),
        ((-113 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word24Step14 :
    word24Chunk14.foldl (fun acc a => a.applyPacked acc)
      word24State14 = word24State15 := by decide +kernel

private def word24Chunk15 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word24State16 : PackedMat2 :=
    ⟨⟨⟨((-155 : Dyadic) * half ^ 11),
        ((609 : Dyadic) * half ^ 10)⟩,
       ⟨((1753 : Dyadic) * half ^ 12),
        ((133 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-105 : Dyadic) * half ^ 9),
        ((315 : Dyadic) * half ^ 12)⟩,
       ⟨((283 : Dyadic) * half ^ 12),
        ((77 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((623 : Dyadic) * half ^ 12),
        ((-557 : Dyadic) * half ^ 13)⟩,
       ⟨((7 : Dyadic) * half ^ 12),
        ((-1123 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-371 : Dyadic) * half ^ 9),
        ((-1443 : Dyadic) * half ^ 13)⟩,
       ⟨((-119 : Dyadic) * half ^ 8),
        ((2063 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word24Step15 :
    word24Chunk15.foldl (fun acc a => a.applyPacked acc)
      word24State15 = word24State16 := by decide +kernel

private def word24Chunk16 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word24State17 : PackedMat2 :=
    ⟨⟨⟨((1871 : Dyadic) * half ^ 12),
        ((-2241 : Dyadic) * half ^ 14)⟩,
       ⟨((761 : Dyadic) * half ^ 13),
        ((7255 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2621 : Dyadic) * half ^ 13),
        ((-3739 : Dyadic) * half ^ 14)⟩,
       ⟨((-133 : Dyadic) * half ^ 9),
        ((3259 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((2621 : Dyadic) * half ^ 13),
        ((3739 : Dyadic) * half ^ 14)⟩,
       ⟨((-133 : Dyadic) * half ^ 9),
        ((3259 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((1871 : Dyadic) * half ^ 12),
        ((-2241 : Dyadic) * half ^ 14)⟩,
       ⟨((-761 : Dyadic) * half ^ 13),
        ((-7255 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word24Step16 :
    word24Chunk16.foldl (fun acc a => a.applyPacked acc)
      word24State16 = word24State17 := by decide +kernel

private def word24Chunk17 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word24State18 : PackedMat2 :=
    ⟨⟨⟨((-719 : Dyadic) * half ^ 11),
        ((-385 : Dyadic) * half ^ 13)⟩,
       ⟨((41 : Dyadic) * half ^ 7),
        ((-4871 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1749 : Dyadic) * half ^ 13),
        ((371 : Dyadic) * half ^ 12)⟩,
       ⟨((-405 : Dyadic) * half ^ 11),
        ((-8125 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((9609 : Dyadic) * half ^ 14),
        ((-129 : Dyadic) * half ^ 14)⟩,
       ⟨((6641 : Dyadic) * half ^ 14),
        ((3369 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4101 : Dyadic) * half ^ 14),
        ((1375 : Dyadic) * half ^ 12)⟩,
       ⟨((-5641 : Dyadic) * half ^ 14),
        ((-63 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word24Step17 :
    word24Chunk17.foldl (fun acc a => a.applyPacked acc)
      word24State17 = word24State18 := by decide +kernel

private def word24Chunk18 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word24State19 : PackedMat2 :=
    ⟨⟨⟨((12343 : Dyadic) * half ^ 15),
        ((-10643 : Dyadic) * half ^ 15)⟩,
       ⟨((19367 : Dyadic) * half ^ 15),
        ((4867 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((1677 : Dyadic) * half ^ 15),
        ((1187 : Dyadic) * half ^ 12)⟩,
       ⟨((-3399 : Dyadic) * half ^ 15),
        ((-779 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1677 : Dyadic) * half ^ 15),
        ((-1187 : Dyadic) * half ^ 12)⟩,
       ⟨((-3399 : Dyadic) * half ^ 15),
        ((-779 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((12343 : Dyadic) * half ^ 15),
        ((-10643 : Dyadic) * half ^ 15)⟩,
       ⟨((-19367 : Dyadic) * half ^ 15),
        ((-4867 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word24Step18 :
    word24Chunk18.foldl (fun acc a => a.applyPacked acc)
      word24State18 = word24State19 := by decide +kernel

private def word24Chunk19 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word24State20 : PackedMat2 :=
    ⟨⟨⟨((-48897 : Dyadic) * half ^ 16),
        ((-113 : Dyadic) * half ^ 10)⟩,
       ⟨((-16199 : Dyadic) * half ^ 16),
        ((-5887 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((29793 : Dyadic) * half ^ 16),
        ((-11369 : Dyadic) * half ^ 16)⟩,
       ⟨((-11027 : Dyadic) * half ^ 16),
        ((625 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-21369 : Dyadic) * half ^ 16),
        ((10205 : Dyadic) * half ^ 15)⟩,
       ⟨((1369 : Dyadic) * half ^ 16),
        ((-9383 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((1345 : Dyadic) * half ^ 16),
        ((16349 : Dyadic) * half ^ 16)⟩,
       ⟨((-13119 : Dyadic) * half ^ 16),
        ((-8137 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word24Step19 :
    word24Chunk19.foldl (fun acc a => a.applyPacked acc)
      word24State19 = word24State20 := by decide +kernel

private def word24Chunk20 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word24State21 : PackedMat2 :=
    ⟨⟨⟨((-23593 : Dyadic) * half ^ 16),
        ((-12255 : Dyadic) * half ^ 16)⟩,
       ⟨((-665 : Dyadic) * half ^ 10),
        ((2955 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((26285 : Dyadic) * half ^ 16),
        ((10281 : Dyadic) * half ^ 16)⟩,
       ⟨((5185 : Dyadic) * half ^ 14),
        ((-2715 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((3783 : Dyadic) * half ^ 15),
        ((47025 : Dyadic) * half ^ 17)⟩,
       ⟨((3249 : Dyadic) * half ^ 14),
        ((5545 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((435 : Dyadic) * half ^ 16),
        ((66153 : Dyadic) * half ^ 17)⟩,
       ⟨((24075 : Dyadic) * half ^ 16),
        ((-18967 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word24Step20 :
    word24Chunk20.foldl (fun acc a => a.applyPacked acc)
      word24State20 = word24State21 := by decide +kernel

private def word24Chunk21 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word24State22 : PackedMat2 :=
    ⟨⟨⟨((-18421 : Dyadic) * half ^ 17),
        ((227 : Dyadic) * half ^ 13)⟩,
       ⟨((-1927 : Dyadic) * half ^ 12),
        ((-6781 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((53511 : Dyadic) * half ^ 17),
        ((771 : Dyadic) * half ^ 14)⟩,
       ⟨((49715 : Dyadic) * half ^ 16),
        ((-1713 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-49715 : Dyadic) * half ^ 16),
        ((1713 : Dyadic) * half ^ 15)⟩,
       ⟨((-53511 : Dyadic) * half ^ 17),
        ((-771 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1927 : Dyadic) * half ^ 12),
        ((-6781 : Dyadic) * half ^ 17)⟩,
       ⟨((-18421 : Dyadic) * half ^ 17),
        ((227 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word24Step21 :
    word24Chunk21.foldl (fun acc a => a.applyPacked acc)
      word24State21 = word24State22 := by decide +kernel

private def word24Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word24State23 : PackedMat2 :=
    ⟨⟨⟨((-2233 : Dyadic) * half ^ 16),
        ((63245 : Dyadic) * half ^ 19)⟩,
       ⟨((-13417 : Dyadic) * half ^ 18),
        ((-71595 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-201585 : Dyadic) * half ^ 18),
        ((-58113 : Dyadic) * half ^ 19)⟩,
       ⟨((-127 : Dyadic) * half ^ 9),
        ((186245 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((32033 : Dyadic) * half ^ 17),
        ((-266609 : Dyadic) * half ^ 19)⟩,
       ⟨((-122179 : Dyadic) * half ^ 18),
        ((-136561 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((4175 : Dyadic) * half ^ 18),
        ((22349 : Dyadic) * half ^ 19)⟩,
       ⟨((-16855 : Dyadic) * half ^ 16),
        ((-4485 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word24Step22 :
    word24Chunk22.foldl (fun acc a => a.applyPacked acc)
      word24State22 = word24State23 := by decide +kernel

private def word24Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word24State24 : PackedMat2 :=
    ⟨⟨⟨((319007 : Dyadic) * half ^ 19),
        ((70067 : Dyadic) * half ^ 18)⟩,
       ⟨((53045 : Dyadic) * half ^ 19),
        ((-73737 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-207163 : Dyadic) * half ^ 19),
        ((138113 : Dyadic) * half ^ 19)⟩,
       ⟨((-169611 : Dyadic) * half ^ 19),
        ((35907 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-169611 : Dyadic) * half ^ 19),
        ((35907 : Dyadic) * half ^ 18)⟩,
       ⟨((-207163 : Dyadic) * half ^ 19),
        ((138113 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-53045 : Dyadic) * half ^ 19),
        ((73737 : Dyadic) * half ^ 19)⟩,
       ⟨((-319007 : Dyadic) * half ^ 19),
        ((-70067 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word24Step23 :
    word24Chunk23.foldl (fun acc a => a.applyPacked acc)
      word24State23 = word24State24 := by decide +kernel

private def word24Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word24State25 : PackedMat2 :=
    ⟨⟨⟨((-29185 : Dyadic) * half ^ 20),
        ((74461 : Dyadic) * half ^ 19)⟩,
       ⟨((-316583 : Dyadic) * half ^ 20),
        ((210839 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-40131 : Dyadic) * half ^ 20),
        ((529945 : Dyadic) * half ^ 20)⟩,
       ⟨((-274407 : Dyadic) * half ^ 20),
        ((-168293 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((866531 : Dyadic) * half ^ 20),
        ((58569 : Dyadic) * half ^ 19)⟩,
       ⟨((-193359 : Dyadic) * half ^ 20),
        ((157269 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((61917 : Dyadic) * half ^ 20),
        ((-143699 : Dyadic) * half ^ 20)⟩,
       ⟨((359761 : Dyadic) * half ^ 20),
        ((-43221 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word24Step24 :
    word24Chunk24.foldl (fun acc a => a.applyPacked acc)
      word24State24 = word24State25 := by decide +kernel

private def word24Chunk25 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word24State26 : PackedMat2 :=
    ⟨⟨⟨((327279 : Dyadic) * half ^ 20),
        ((-769969 : Dyadic) * half ^ 21)⟩,
       ⟨((59043 : Dyadic) * half ^ 20),
        ((-504247 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((163139 : Dyadic) * half ^ 18),
        ((445377 : Dyadic) * half ^ 21)⟩,
       ⟨((-24795 : Dyadic) * half ^ 17),
        ((44699 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-24795 : Dyadic) * half ^ 17),
        ((44699 : Dyadic) * half ^ 21)⟩,
       ⟨((163139 : Dyadic) * half ^ 18),
        ((445377 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-59043 : Dyadic) * half ^ 20),
        ((504247 : Dyadic) * half ^ 21)⟩,
       ⟨((-327279 : Dyadic) * half ^ 20),
        ((769969 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word24Step25 :
    word24Chunk25.foldl (fun acc a => a.applyPacked acc)
      word24State25 = word24State26 := by decide +kernel

private def word24Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word24State27 : PackedMat2 :=
    ⟨⟨⟨((-90685 : Dyadic) * half ^ 21),
        ((-413307 : Dyadic) * half ^ 21)⟩,
       ⟨((-88303 : Dyadic) * half ^ 18),
        ((218007 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((791329 : Dyadic) * half ^ 21),
        ((551205 : Dyadic) * half ^ 21)⟩,
       ⟨((58523 : Dyadic) * half ^ 19),
        ((608121 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-58523 : Dyadic) * half ^ 19),
        ((-608121 : Dyadic) * half ^ 21)⟩,
       ⟨((-791329 : Dyadic) * half ^ 21),
        ((-551205 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-88303 : Dyadic) * half ^ 18),
        ((218007 : Dyadic) * half ^ 19)⟩,
       ⟨((-90685 : Dyadic) * half ^ 21),
        ((-413307 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word24Step26 :
    word24Chunk26.foldl (fun acc a => a.applyPacked acc)
      word24State26 = word24State27 := by decide +kernel

private def word24Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word24State28 : PackedMat2 :=
    ⟨⟨⟨((1401249 : Dyadic) * half ^ 22),
        ((1049163 : Dyadic) * half ^ 22)⟩,
       ⟨((-2282767 : Dyadic) * half ^ 22),
        ((850395 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-736033 : Dyadic) * half ^ 22),
        ((212589 : Dyadic) * half ^ 20)⟩,
       ⟨((756087 : Dyadic) * half ^ 22),
        ((725449 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-300271 : Dyadic) * half ^ 21),
        ((-186515 : Dyadic) * half ^ 20)⟩,
       ⟨((-1150627 : Dyadic) * half ^ 21),
        ((-10027 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-12423 : Dyadic) * half ^ 18),
        ((-230251 : Dyadic) * half ^ 19)⟩,
       ⟨((949779 : Dyadic) * half ^ 21),
        ((-440759 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word24Step27 :
    word24Chunk27.foldl (fun acc a => a.applyPacked acc)
      word24State27 = word24State28 := by decide +kernel

private def word24Chunk28 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word24State29 : PackedMat2 :=
    ⟨⟨⟨((-12849 : Dyadic) * half ^ 15),
        ((406857 : Dyadic) * half ^ 20)⟩,
       ⟨((123165 : Dyadic) * half ^ 22),
        ((-622129 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1516513 : Dyadic) * half ^ 22),
        ((-303561 : Dyadic) * half ^ 21)⟩,
       ⟨((2253037 : Dyadic) * half ^ 22),
        ((1592685 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((2806929 : Dyadic) * half ^ 23),
        ((1884775 : Dyadic) * half ^ 22)⟩,
       ⟨((378441 : Dyadic) * half ^ 23),
        ((184131 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((3876985 : Dyadic) * half ^ 23),
        ((-1767837 : Dyadic) * half ^ 23)⟩,
       ⟨((-2632727 : Dyadic) * half ^ 23),
        ((1521507 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word24Step28 :
    word24Chunk28.foldl (fun acc a => a.applyPacked acc)
      word24State28 = word24State29 := by decide +kernel

private def word24Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word24State30 : PackedMat2 :=
    ⟨⟨⟨((-3578891 : Dyadic) * half ^ 24),
        ((445875 : Dyadic) * half ^ 20)⟩,
       ⟨((4534985 : Dyadic) * half ^ 24),
        ((-531743 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-9294639 : Dyadic) * half ^ 24),
        ((-3677547 : Dyadic) * half ^ 24)⟩,
       ⟨((-994339 : Dyadic) * half ^ 24),
        ((3848557 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-9294639 : Dyadic) * half ^ 24),
        ((-3677547 : Dyadic) * half ^ 24)⟩,
       ⟨((994339 : Dyadic) * half ^ 24),
        ((-3848557 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((3578891 : Dyadic) * half ^ 24),
        ((-445875 : Dyadic) * half ^ 20)⟩,
       ⟨((4534985 : Dyadic) * half ^ 24),
        ((-531743 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word24Step29 :
    word24Chunk29.foldl (fun acc a => a.applyPacked acc)
      word24State29 = word24State30 := by decide +kernel

private def word24Chunk30 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word24State31 : PackedMat2 :=
    ⟨⟨⟨((7251277 : Dyadic) * half ^ 25),
        ((1544135 : Dyadic) * half ^ 22)⟩,
       ⟨((-8235731 : Dyadic) * half ^ 25),
        ((13976009 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-11708181 : Dyadic) * half ^ 25),
        ((-5536593 : Dyadic) * half ^ 25)⟩,
       ⟨((-7297859 : Dyadic) * half ^ 25),
        ((2692323 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((10921239 : Dyadic) * half ^ 25),
        ((2205161 : Dyadic) * half ^ 25)⟩,
       ⟨((-151947 : Dyadic) * half ^ 25),
        ((-2375755 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1622929 : Dyadic) * half ^ 25),
        ((483969 : Dyadic) * half ^ 21)⟩,
       ⟨((-26329089 : Dyadic) * half ^ 25),
        ((492227 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word24Step30 :
    word24Chunk30.foldl (fun acc a => a.applyPacked acc)
      word24State30 = word24State31 := by decide +kernel

private def word24Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word24State32 : PackedMat2 :=
    ⟨⟨⟨((10616855 : Dyadic) * half ^ 25),
        ((-12261325 : Dyadic) * half ^ 26)⟩,
       ⟨((21250577 : Dyadic) * half ^ 25),
        ((-1267297 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-2756651 : Dyadic) * half ^ 24),
        ((-29445907 : Dyadic) * half ^ 26)⟩,
       ⟨((-2293655 : Dyadic) * half ^ 24),
        ((1141557 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((2293655 : Dyadic) * half ^ 24),
        ((-1141557 : Dyadic) * half ^ 26)⟩,
       ⟨((2756651 : Dyadic) * half ^ 24),
        ((29445907 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((21250577 : Dyadic) * half ^ 25),
        ((-1267297 : Dyadic) * half ^ 26)⟩,
       ⟨((10616855 : Dyadic) * half ^ 25),
        ((-12261325 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word24Step31 :
    word24Chunk31.foldl (fun acc a => a.applyPacked acc)
      word24State31 = word24State32 := by decide +kernel

private def word24Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word24State33 : PackedMat2 :=
    ⟨⟨⟨((-9109085 : Dyadic) * half ^ 25),
        ((23426999 : Dyadic) * half ^ 27)⟩,
       ⟨((-4802617 : Dyadic) * half ^ 26),
        ((20139217 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-30355611 : Dyadic) * half ^ 26),
        ((-22801883 : Dyadic) * half ^ 27)⟩,
       ⟨((1196283 : Dyadic) * half ^ 25),
        ((-70487959 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-30355611 : Dyadic) * half ^ 26),
        ((-22801883 : Dyadic) * half ^ 27)⟩,
       ⟨((-1196283 : Dyadic) * half ^ 25),
        ((70487959 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((9109085 : Dyadic) * half ^ 25),
        ((-23426999 : Dyadic) * half ^ 27)⟩,
       ⟨((-4802617 : Dyadic) * half ^ 26),
        ((20139217 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word24Step32 :
    word24Chunk32.foldl (fun acc a => a.applyPacked acc)
      word24State32 = word24State33 := by decide +kernel

private def word24Chunk33 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word24State34 : PackedMat2 :=
    ⟨⟨⟨((-101161115 : Dyadic) * half ^ 27),
        ((-40468513 : Dyadic) * half ^ 28)⟩,
       ⟨((-734145 : Dyadic) * half ^ 23),
        ((44113325 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((10230353 : Dyadic) * half ^ 25),
        ((-89444977 : Dyadic) * half ^ 28)⟩,
       ⟨((-4835193 : Dyadic) * half ^ 27),
        ((-17485153 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((53465065 : Dyadic) * half ^ 27),
        ((-36086219 : Dyadic) * half ^ 28)⟩,
       ⟨((4497489 : Dyadic) * half ^ 24),
        ((-45756605 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((911203 : Dyadic) * half ^ 26),
        ((-112907435 : Dyadic) * half ^ 28)⟩,
       ⟨((-42290919 : Dyadic) * half ^ 27),
        ((-89414795 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word24Step33 :
    word24Chunk33.foldl (fun acc a => a.applyPacked acc)
      word24State33 = word24State34 := by decide +kernel

private def word24Chunk34 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word24State35 : PackedMat2 :=
    ⟨⟨⟨((-70528727 : Dyadic) * half ^ 27),
        ((-80701527 : Dyadic) * half ^ 28)⟩,
       ⟨((-26649107 : Dyadic) * half ^ 26),
        ((34704053 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-4765433 : Dyadic) * half ^ 27),
        ((38516915 : Dyadic) * half ^ 28)⟩,
       ⟨((57178525 : Dyadic) * half ^ 27),
        ((-15817985 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((70152885 : Dyadic) * half ^ 28),
        ((-30971979 : Dyadic) * half ^ 27)⟩,
       ⟨((-6880945 : Dyadic) * half ^ 28),
        ((-13103273 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((150109633 : Dyadic) * half ^ 28),
        ((17230513 : Dyadic) * half ^ 28)⟩,
       ⟨((-11293421 : Dyadic) * half ^ 28),
        ((-123826941 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word24Step34 :
    word24Chunk34.foldl (fun acc a => a.applyPacked acc)
      word24State34 = word24State35 := by decide +kernel

private def word24Chunk35 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word24State36 : PackedMat2 :=
    ⟨⟨⟨((-143647011 : Dyadic) * half ^ 29),
        ((-78098091 : Dyadic) * half ^ 28)⟩,
       ⟨((-411585769 : Dyadic) * half ^ 29),
        ((2067159 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((153396193 : Dyadic) * half ^ 29),
        ((-31236671 : Dyadic) * half ^ 29)⟩,
       ⟨((141816043 : Dyadic) * half ^ 29),
        ((-28434841 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-153396193 : Dyadic) * half ^ 29),
        ((31236671 : Dyadic) * half ^ 29)⟩,
       ⟨((141816043 : Dyadic) * half ^ 29),
        ((-28434841 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-143647011 : Dyadic) * half ^ 29),
        ((-78098091 : Dyadic) * half ^ 28)⟩,
       ⟨((411585769 : Dyadic) * half ^ 29),
        ((-2067159 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word24Step35 :
    word24Chunk35.foldl (fun acc a => a.applyPacked acc)
      word24State35 = word24State36 := by decide +kernel

private def word24Chunk36 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word24State37 : PackedMat2 :=
    ⟨⟨⟨((-616331107 : Dyadic) * half ^ 30),
        ((7229347 : Dyadic) * half ^ 25)⟩,
       ⟨((-447512115 : Dyadic) * half ^ 30),
        ((-45623899 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-260573443 : Dyadic) * half ^ 30),
        ((-228338027 : Dyadic) * half ^ 30)⟩,
       ⟨((4196577 : Dyadic) * half ^ 30),
        ((336862651 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-260573443 : Dyadic) * half ^ 30),
        ((-228338027 : Dyadic) * half ^ 30)⟩,
       ⟨((-4196577 : Dyadic) * half ^ 30),
        ((-336862651 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((616331107 : Dyadic) * half ^ 30),
        ((-7229347 : Dyadic) * half ^ 25)⟩,
       ⟨((-447512115 : Dyadic) * half ^ 30),
        ((-45623899 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word24Step36 :
    word24Chunk36.foldl (fun acc a => a.applyPacked acc)
      word24State36 = word24State37 := by decide +kernel

private def word24Chunk37 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word24State38 : PackedMat2 :=
    ⟨⟨⟨((-292117775 : Dyadic) * half ^ 31),
        ((43871953 : Dyadic) * half ^ 30)⟩,
       ⟨((-104655553 : Dyadic) * half ^ 31),
        ((-665851571 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-729669255 : Dyadic) * half ^ 31),
        ((203522813 : Dyadic) * half ^ 31)⟩,
       ⟨((-85514493 : Dyadic) * half ^ 31),
        ((-406548223 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((729669255 : Dyadic) * half ^ 31),
        ((-203522813 : Dyadic) * half ^ 31)⟩,
       ⟨((-85514493 : Dyadic) * half ^ 31),
        ((-406548223 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-292117775 : Dyadic) * half ^ 31),
        ((43871953 : Dyadic) * half ^ 30)⟩,
       ⟨((104655553 : Dyadic) * half ^ 31),
        ((665851571 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word24Step37 :
    word24Chunk37.foldl (fun acc a => a.applyPacked acc)
      word24State37 = word24State38 := by decide +kernel

private def word24Chunk38 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word24State39 : PackedMat2 :=
    ⟨⟨⟨((2756832587 : Dyadic) * half ^ 32),
        ((-49258905 : Dyadic) * half ^ 30)⟩,
       ⟨((-1146955061 : Dyadic) * half ^ 32),
        ((-87622615 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((498384627 : Dyadic) * half ^ 32),
        ((-1148871345 : Dyadic) * half ^ 32)⟩,
       ⟨((1560546815 : Dyadic) * half ^ 32),
        ((-315410719 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((498384627 : Dyadic) * half ^ 32),
        ((-1148871345 : Dyadic) * half ^ 32)⟩,
       ⟨((-1560546815 : Dyadic) * half ^ 32),
        ((315410719 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2756832587 : Dyadic) * half ^ 32),
        ((49258905 : Dyadic) * half ^ 30)⟩,
       ⟨((-1146955061 : Dyadic) * half ^ 32),
        ((-87622615 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word24Step38 :
    word24Chunk38.foldl (fun acc a => a.applyPacked acc)
      word24State38 = word24State39 := by decide +kernel

private def word24Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word24State40 : PackedMat2 :=
    ⟨⟨⟨((2217165885 : Dyadic) * half ^ 33),
        ((1564664353 : Dyadic) * half ^ 32)⟩,
       ⟨((786369533 : Dyadic) * half ^ 33),
        ((-812909587 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-5457286965 : Dyadic) * half ^ 33),
        ((1618734109 : Dyadic) * half ^ 33)⟩,
       ⟨((1072489409 : Dyadic) * half ^ 33),
        ((1181784647 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1072489409 : Dyadic) * half ^ 33),
        ((1181784647 : Dyadic) * half ^ 32)⟩,
       ⟨((-5457286965 : Dyadic) * half ^ 33),
        ((1618734109 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-786369533 : Dyadic) * half ^ 33),
        ((812909587 : Dyadic) * half ^ 33)⟩,
       ⟨((-2217165885 : Dyadic) * half ^ 33),
        ((-1564664353 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word24Step39 :
    word24Chunk39.foldl (fun acc a => a.applyPacked acc)
      word24State39 = word24State40 := by decide +kernel

private def word24Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word24State41 : PackedMat2 :=
    ⟨⟨⟨((3230682997 : Dyadic) * half ^ 34),
        ((3278654693 : Dyadic) * half ^ 33)⟩,
       ⟨((4750079855 : Dyadic) * half ^ 34),
        ((-6155996057 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1302587901 : Dyadic) * half ^ 34),
        ((618910847 : Dyadic) * half ^ 34)⟩,
       ⟨((-1277523705 : Dyadic) * half ^ 34),
        ((-867211961 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((7556606535 : Dyadic) * half ^ 34),
        ((-6266049 : Dyadic) * half ^ 33)⟩,
       ⟨((6318784841 : Dyadic) * half ^ 34),
        ((1290055803 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-12713305443 : Dyadic) * half ^ 34),
        ((759698429 : Dyadic) * half ^ 34)⟩,
       ⟨((401313329 : Dyadic) * half ^ 34),
        ((1995190713 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word24Step40 :
    word24Chunk40.foldl (fun acc a => a.applyPacked acc)
      word24State40 = word24State41 := by decide +kernel

private def word24Chunk41 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word24State42 : PackedMat2 :=
    ⟨⟨⟨((882743877 : Dyadic) * half ^ 32),
        ((10005589901 : Dyadic) * half ^ 35)⟩,
       ⟨((-1950946353 : Dyadic) * half ^ 33),
        ((18245084929 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-357668799 : Dyadic) * half ^ 34),
        ((-922201599 : Dyadic) * half ^ 35)⟩,
       ⟨((-5213949711 : Dyadic) * half ^ 34),
        ((-6814608915 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3868405257 : Dyadic) * half ^ 34),
        ((-2785809255 : Dyadic) * half ^ 34)⟩,
       ⟨((1473101829 : Dyadic) * half ^ 33),
        ((303517557 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-14125337415 : Dyadic) * half ^ 34),
        ((185458599 : Dyadic) * half ^ 34)⟩,
       ⟨((2059873757 : Dyadic) * half ^ 33),
        ((-3716434107 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word24Step41 :
    word24Chunk41.foldl (fun acc a => a.applyPacked acc)
      word24State41 = word24State42 := by decide +kernel

private def word24Chunk42 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word24State43 : PackedMat2 :=
    ⟨⟨⟨((-4764374105 : Dyadic) * half ^ 35),
        ((1620965659 : Dyadic) * half ^ 34)⟩,
       ⟨((48029339 : Dyadic) * half ^ 30),
        ((18623471153 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4191415271 : Dyadic) * half ^ 35),
        ((-103192813 : Dyadic) * half ^ 34)⟩,
       ⟨((423570649 : Dyadic) * half ^ 34),
        ((-7266978273 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-423570649 : Dyadic) * half ^ 34),
        ((7266978273 : Dyadic) * half ^ 34)⟩,
       ⟨((-4191415271 : Dyadic) * half ^ 35),
        ((103192813 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((48029339 : Dyadic) * half ^ 30),
        ((18623471153 : Dyadic) * half ^ 35)⟩,
       ⟨((-4764374105 : Dyadic) * half ^ 35),
        ((1620965659 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word24Step42 :
    word24Chunk42.foldl (fun acc a => a.applyPacked acc)
      word24State42 = word24State43 := by decide +kernel

private def word24Chunk43 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word24State44 : PackedMat2 :=
    ⟨⟨⟨((512850963 : Dyadic) * half ^ 31),
        ((-63058428019 : Dyadic) * half ^ 37)⟩,
       ⟨((16345519849 : Dyadic) * half ^ 36),
        ((49619346643 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-12933007047 : Dyadic) * half ^ 36),
        ((-3553243897 : Dyadic) * half ^ 37)⟩,
       ⟨((-2262320123 : Dyadic) * half ^ 35),
        ((-39308820953 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-21431032425 : Dyadic) * half ^ 36),
        ((-17457647293 : Dyadic) * half ^ 37)⟩,
       ⟨((1117361783 : Dyadic) * half ^ 32),
        ((-8408366801 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((419971293 : Dyadic) * half ^ 32),
        ((-32756750665 : Dyadic) * half ^ 37)⟩,
       ⟨((56338887331 : Dyadic) * half ^ 36),
        ((-65710967 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word24Step43 :
    word24Chunk43.foldl (fun acc a => a.applyPacked acc)
      word24State43 = word24State44 := by decide +kernel

private def word24Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word24State45 : PackedMat2 :=
    ⟨⟨⟨((-37439653811 : Dyadic) * half ^ 36),
        ((11255967971 : Dyadic) * half ^ 37)⟩,
       ⟨((39481792253 : Dyadic) * half ^ 36),
        ((-3351768053 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((8658458099 : Dyadic) * half ^ 36),
        ((31531076751 : Dyadic) * half ^ 37)⟩,
       ⟨((-559853081 : Dyadic) * half ^ 31),
        ((-9457619051 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-69361552955 : Dyadic) * half ^ 37),
        ((-26573756691 : Dyadic) * half ^ 37)⟩,
       ⟨((-6299399453 : Dyadic) * half ^ 37),
        ((-9256840493 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((24663040183 : Dyadic) * half ^ 37),
        ((-4807590379 : Dyadic) * half ^ 33)⟩,
       ⟨((2151104241 : Dyadic) * half ^ 37),
        ((-1021069221 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word24Step44 :
    word24Chunk44.foldl (fun acc a => a.applyPacked acc)
      word24State44 = word24State45 := by decide +kernel

private def word24Chunk45 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word24State46 : PackedMat2 :=
    ⟨⟨⟨((-76186578559 : Dyadic) * half ^ 38),
        ((-72639859437 : Dyadic) * half ^ 38)⟩,
       ⟨((17473781687 : Dyadic) * half ^ 38),
        ((-111624089465 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((66534782307 : Dyadic) * half ^ 38),
        ((-50335526565 : Dyadic) * half ^ 37)⟩,
       ⟨((-56405949551 : Dyadic) * half ^ 38),
        ((-27607364491 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((66534782307 : Dyadic) * half ^ 38),
        ((-50335526565 : Dyadic) * half ^ 37)⟩,
       ⟨((56405949551 : Dyadic) * half ^ 38),
        ((27607364491 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((76186578559 : Dyadic) * half ^ 38),
        ((72639859437 : Dyadic) * half ^ 38)⟩,
       ⟨((17473781687 : Dyadic) * half ^ 38),
        ((-111624089465 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word24Step45 :
    word24Chunk45.foldl (fun acc a => a.applyPacked acc)
      word24State45 = word24State46 := by decide +kernel

private def word24Chunk46 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word24State47 : PackedMat2 :=
    ⟨⟨⟨((-117297176413 : Dyadic) * half ^ 39),
        ((-26032855023 : Dyadic) * half ^ 39)⟩,
       ⟨((-455320539601 : Dyadic) * half ^ 39),
        ((-12525415343 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-105951926681 : Dyadic) * half ^ 39),
        ((37459665583 : Dyadic) * half ^ 38)⟩,
       ⟨((140369273245 : Dyadic) * half ^ 39),
        ((-127720604245 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-202639935411 : Dyadic) * half ^ 39),
        ((123160599963 : Dyadic) * half ^ 39)⟩,
       ⟨((-52801273079 : Dyadic) * half ^ 39),
        ((8604336641 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((24068806349 : Dyadic) * half ^ 39),
        ((84505840797 : Dyadic) * half ^ 38)⟩,
       ⟨((76134516395 : Dyadic) * half ^ 39),
        ((286308858007 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word24Step46 :
    word24Chunk46.foldl (fun acc a => a.applyPacked acc)
      word24State46 = word24State47 := by decide +kernel

private def word24Chunk47 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word24State48 : PackedMat2 :=
    ⟨⟨⟨((-163897121489 : Dyadic) * half ^ 40),
        ((4847823263 : Dyadic) * half ^ 34)⟩,
       ⟨((-381690983975 : Dyadic) * half ^ 40),
        ((-313207849305 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((490548039509 : Dyadic) * half ^ 40),
        ((-266360058157 : Dyadic) * half ^ 40)⟩,
       ⟨((481689177429 : Dyadic) * half ^ 40),
        ((64320135117 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-395000328391 : Dyadic) * half ^ 40),
        ((17302465 : Dyadic) * half ^ 32)⟩,
       ⟨((137719787923 : Dyadic) * half ^ 40),
        ((-486118608469 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-623468538137 : Dyadic) * half ^ 40),
        ((-108896931243 : Dyadic) * half ^ 40)⟩,
       ⟨((-2947160473 : Dyadic) * half ^ 40),
        ((-68198513183 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word24Step47 :
    word24Chunk47.foldl (fun acc a => a.applyPacked acc)
      word24State47 = word24State48 := by decide +kernel

private def word24Chunk48 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word24State49 : PackedMat2 :=
    ⟨⟨⟨((370975384767 : Dyadic) * half ^ 39),
        ((138975499025 : Dyadic) * half ^ 40)⟩,
       ⟨((-149882390295 : Dyadic) * half ^ 40),
        ((-84447588325 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-79089788721 : Dyadic) * half ^ 38),
        ((168778904645 : Dyadic) * half ^ 39)⟩,
       ⟨((455862850733 : Dyadic) * half ^ 40),
        ((-11866446195 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((455862850733 : Dyadic) * half ^ 40),
        ((-11866446195 : Dyadic) * half ^ 38)⟩,
       ⟨((-79089788721 : Dyadic) * half ^ 38),
        ((168778904645 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((149882390295 : Dyadic) * half ^ 40),
        ((84447588325 : Dyadic) * half ^ 39)⟩,
       ⟨((-370975384767 : Dyadic) * half ^ 39),
        ((-138975499025 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word24Step48 :
    word24Chunk48.foldl (fun acc a => a.applyPacked acc)
      word24State48 = word24State49 := by decide +kernel

private def word24Chunk49 : List Letter := [.t, .h, .t, .h]
private def word24State50 : PackedMat2 :=
    ⟨⟨⟨((348438696255 : Dyadic) * half ^ 41),
        ((654280445519 : Dyadic) * half ^ 40)⟩,
       ⟨((-345572894143 : Dyadic) * half ^ 41),
        ((122178322837 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-365415654673 : Dyadic) * half ^ 41),
        ((258387887371 : Dyadic) * half ^ 41)⟩,
       ⟨((625992162573 : Dyadic) * half ^ 41),
        ((-442643303125 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((365415654673 : Dyadic) * half ^ 41),
        ((-258387887371 : Dyadic) * half ^ 41)⟩,
       ⟨((625992162573 : Dyadic) * half ^ 41),
        ((-442643303125 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((348438696255 : Dyadic) * half ^ 41),
        ((654280445519 : Dyadic) * half ^ 40)⟩,
       ⟨((345572894143 : Dyadic) * half ^ 41),
        ((-122178322837 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word24Step49 :
    word24Chunk49.foldl (fun acc a => a.applyPacked acc)
      word24State49 = word24State50 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word24_check : check word24 24 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word24 = word24State50.toMatrix := by
    unfold evalRingPacked
    change ((
      word24Chunk0 ++ word24Chunk1 ++ word24Chunk2 ++ word24Chunk3 ++
      word24Chunk4 ++ word24Chunk5 ++ word24Chunk6 ++ word24Chunk7 ++
      word24Chunk8 ++ word24Chunk9 ++ word24Chunk10 ++ word24Chunk11 ++
      word24Chunk12 ++ word24Chunk13 ++ word24Chunk14 ++ word24Chunk15 ++
      word24Chunk16 ++ word24Chunk17 ++ word24Chunk18 ++ word24Chunk19 ++
      word24Chunk20 ++ word24Chunk21 ++ word24Chunk22 ++ word24Chunk23 ++
      word24Chunk24 ++ word24Chunk25 ++ word24Chunk26 ++ word24Chunk27 ++
      word24Chunk28 ++ word24Chunk29 ++ word24Chunk30 ++ word24Chunk31 ++
      word24Chunk32 ++ word24Chunk33 ++ word24Chunk34 ++ word24Chunk35 ++
      word24Chunk36 ++ word24Chunk37 ++ word24Chunk38 ++ word24Chunk39 ++
      word24Chunk40 ++ word24Chunk41 ++ word24Chunk42 ++ word24Chunk43 ++
      word24Chunk44 ++ word24Chunk45 ++ word24Chunk46 ++ word24Chunk47 ++
      word24Chunk48 ++ word24Chunk49
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word24Step0, word24Step1, word24Step2, word24Step3, word24Step4,
      word24Step5, word24Step6, word24Step7, word24Step8, word24Step9,
      word24Step10, word24Step11, word24Step12, word24Step13, word24Step14,
      word24Step15, word24Step16, word24Step17, word24Step18, word24Step19,
      word24Step20, word24Step21, word24Step22, word24Step23, word24Step24,
      word24Step25, word24Step26, word24Step27, word24Step28, word24Step29,
      word24Step30, word24Step31, word24Step32, word24Step33, word24Step34,
      word24Step35, word24Step36, word24Step37, word24Step38, word24Step39,
      word24Step40, word24Step41, word24Step42, word24Step43, word24Step44,
      word24Step45, word24Step46, word24Step47, word24Step48, word24Step49]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

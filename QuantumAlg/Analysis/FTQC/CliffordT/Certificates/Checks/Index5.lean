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
private def word5Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word5State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step0 :
    word5Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word5State1 := by decide +kernel

private def word5Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word5State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step1 :
    word5Chunk1.foldl (fun acc a => a.applyPacked acc)
      word5State1 = word5State2 := by decide +kernel

private def word5Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word5State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step2 :
    word5Chunk2.foldl (fun acc a => a.applyPacked acc)
      word5State2 = word5State3 := by decide +kernel

private def word5Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word5State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step3 :
    word5Chunk3.foldl (fun acc a => a.applyPacked acc)
      word5State3 = word5State4 := by decide +kernel

private def word5Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .t, .h]
private def word5State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word5Step4 :
    word5Chunk4.foldl (fun acc a => a.applyPacked acc)
      word5State4 = word5State5 := by decide +kernel

private def word5Chunk5 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word5State6 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step5 :
    word5Chunk5.foldl (fun acc a => a.applyPacked acc)
      word5State5 = word5State6 := by decide +kernel

private def word5Chunk6 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word5State7 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩⟩
private lemma word5Step6 :
    word5Chunk6.foldl (fun acc a => a.applyPacked acc)
      word5State6 = word5State7 := by decide +kernel

private def word5Chunk7 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word5State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word5Step7 :
    word5Chunk7.foldl (fun acc a => a.applyPacked acc)
      word5State7 = word5State8 := by decide +kernel

private def word5Chunk8 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word5State9 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((15 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word5Step8 :
    word5Chunk8.foldl (fun acc a => a.applyPacked acc)
      word5State8 = word5State9 := by decide +kernel

private def word5Chunk9 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word5State10 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((31 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-31 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word5Step9 :
    word5Chunk9.foldl (fun acc a => a.applyPacked acc)
      word5State9 = word5State10 := by decide +kernel

private def word5Chunk10 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word5State11 : PackedMat2 :=
    ⟨⟨⟨((-31 : Dyadic) * half ^ 6),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((27 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-29 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-17 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-29 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word5Step10 :
    word5Chunk10.foldl (fun acc a => a.applyPacked acc)
      word5State10 = word5State11 := by decide +kernel

private def word5Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word5State12 : PackedMat2 :=
    ⟨⟨⟨((-75 : Dyadic) * half ^ 7),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-47 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 7),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((-51 : Dyadic) * half ^ 7),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 7),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((51 : Dyadic) * half ^ 7),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((75 : Dyadic) * half ^ 7),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((-47 : Dyadic) * half ^ 7),
        ((9 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word5Step11 :
    word5Chunk11.foldl (fun acc a => a.applyPacked acc)
      word5State11 = word5State12 := by decide +kernel

private def word5Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word5State13 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-45 : Dyadic) * half ^ 7),
        ((-21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-79 : Dyadic) * half ^ 7),
        ((61 : Dyadic) * half ^ 8)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((-21 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((35 : Dyadic) * half ^ 8)⟩,
       ⟨((37 : Dyadic) * half ^ 6),
        ((55 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word5Step12 :
    word5Chunk12.foldl (fun acc a => a.applyPacked acc)
      word5State12 = word5State13 := by decide +kernel

private def word5Chunk13 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word5State14 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 7),
        ((-53 : Dyadic) * half ^ 9)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((-135 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((177 : Dyadic) * half ^ 8),
        ((-45 : Dyadic) * half ^ 9)⟩,
       ⟨((101 : Dyadic) * half ^ 8),
        ((-57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((177 : Dyadic) * half ^ 8),
        ((-45 : Dyadic) * half ^ 9)⟩,
       ⟨((-101 : Dyadic) * half ^ 8),
        ((57 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 7),
        ((53 : Dyadic) * half ^ 9)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((-135 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word5Step13 :
    word5Chunk13.foldl (fun acc a => a.applyPacked acc)
      word5State13 = word5State14 := by decide +kernel

private def word5Chunk14 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State15 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((425 : Dyadic) * half ^ 10)⟩,
       ⟨((-123 : Dyadic) * half ^ 9),
        ((-185 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((509 : Dyadic) * half ^ 10)⟩,
       ⟨((79 : Dyadic) * half ^ 9),
        ((47 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-231 : Dyadic) * half ^ 9),
        ((131 : Dyadic) * half ^ 10)⟩,
       ⟨((139 : Dyadic) * half ^ 8),
        ((27 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((305 : Dyadic) * half ^ 9),
        ((123 : Dyadic) * half ^ 10)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((123 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word5Step14 :
    word5Chunk14.foldl (fun acc a => a.applyPacked acc)
      word5State14 = word5State15 := by decide +kernel

private def word5Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State16 : PackedMat2 :=
    ⟨⟨⟨((31 : Dyadic) * half ^ 6),
        ((347 : Dyadic) * half ^ 10)⟩,
       ⟨((-33 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((215 : Dyadic) * half ^ 9),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((241 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-241 : Dyadic) * half ^ 10)⟩,
       ⟨((-215 : Dyadic) * half ^ 9),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 7),
        ((33 : Dyadic) * half ^ 9)⟩,
       ⟨((31 : Dyadic) * half ^ 6),
        ((347 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word5Step15 :
    word5Chunk15.foldl (fun acc a => a.applyPacked acc)
      word5State15 = word5State16 := by decide +kernel

private def word5Chunk16 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word5State17 : PackedMat2 :=
    ⟨⟨⟨((177 : Dyadic) * half ^ 11),
        ((-137 : Dyadic) * half ^ 10)⟩,
       ⟨((743 : Dyadic) * half ^ 11),
        ((685 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1095 : Dyadic) * half ^ 11),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((1007 : Dyadic) * half ^ 11),
        ((-31 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((361 : Dyadic) * half ^ 11),
        ((-11 : Dyadic) * half ^ 9)⟩,
       ⟨((423 : Dyadic) * half ^ 11),
        ((-1051 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-411 : Dyadic) * half ^ 11),
        ((-115 : Dyadic) * half ^ 9)⟩,
       ⟨((959 : Dyadic) * half ^ 11),
        ((283 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word5Step16 :
    word5Chunk16.foldl (fun acc a => a.applyPacked acc)
      word5State16 = word5State17 := by decide +kernel

private def word5Chunk17 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word5State18 : PackedMat2 :=
    ⟨⟨⟨((-1259 : Dyadic) * half ^ 12),
        ((235 : Dyadic) * half ^ 12)⟩,
       ⟨((-239 : Dyadic) * half ^ 12),
        ((173 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-735 : Dyadic) * half ^ 12),
        ((-1951 : Dyadic) * half ^ 12)⟩,
       ⟨((2361 : Dyadic) * half ^ 12),
        ((-103 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((2363 : Dyadic) * half ^ 12),
        ((-813 : Dyadic) * half ^ 12)⟩,
       ⟨((1539 : Dyadic) * half ^ 12),
        ((387 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((927 : Dyadic) * half ^ 12),
        ((-749 : Dyadic) * half ^ 12)⟩,
       ⟨((-457 : Dyadic) * half ^ 12),
        ((-255 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word5Step17 :
    word5Chunk17.foldl (fun acc a => a.applyPacked acc)
      word5State17 = word5State18 := by decide +kernel

private def word5Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word5State19 : PackedMat2 :=
    ⟨⟨⟨((851 : Dyadic) * half ^ 11),
        ((-1125 : Dyadic) * half ^ 12)⟩,
       ⟨((723 : Dyadic) * half ^ 12),
        ((171 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1119 : Dyadic) * half ^ 12),
        ((33 : Dyadic) * half ^ 12)⟩,
       ⟨((-1479 : Dyadic) * half ^ 11),
        ((-309 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1119 : Dyadic) * half ^ 12),
        ((33 : Dyadic) * half ^ 12)⟩,
       ⟨((1479 : Dyadic) * half ^ 11),
        ((309 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-851 : Dyadic) * half ^ 11),
        ((1125 : Dyadic) * half ^ 12)⟩,
       ⟨((723 : Dyadic) * half ^ 12),
        ((171 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word5Step18 :
    word5Chunk18.foldl (fun acc a => a.applyPacked acc)
      word5State18 = word5State19 := by decide +kernel

private def word5Chunk19 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word5State20 : PackedMat2 :=
    ⟨⟨⟨((-453 : Dyadic) * half ^ 10),
        ((1223 : Dyadic) * half ^ 14)⟩,
       ⟨((1459 : Dyadic) * half ^ 13),
        ((-4881 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 7),
        ((-23 : Dyadic) * half ^ 14)⟩,
       ⟨((-1401 : Dyadic) * half ^ 13),
        ((-8275 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2063 : Dyadic) * half ^ 12),
        ((-3129 : Dyadic) * half ^ 14)⟩,
       ⟨((-4149 : Dyadic) * half ^ 13),
        ((327 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((763 : Dyadic) * half ^ 11),
        ((-5083 : Dyadic) * half ^ 14)⟩,
       ⟨((1829 : Dyadic) * half ^ 13),
        ((2165 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word5Step19 :
    word5Chunk19.foldl (fun acc a => a.applyPacked acc)
      word5State19 = word5State20 := by decide +kernel

private def word5Chunk20 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word5State21 : PackedMat2 :=
    ⟨⟨⟨((-2763 : Dyadic) * half ^ 14),
        ((903 : Dyadic) * half ^ 13)⟩,
       ⟨((-9343 : Dyadic) * half ^ 14),
        ((-213 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-2849 : Dyadic) * half ^ 14),
        ((3207 : Dyadic) * half ^ 14)⟩,
       ⟨((-747 : Dyadic) * half ^ 14),
        ((-8255 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((631 : Dyadic) * half ^ 11),
        ((899 : Dyadic) * half ^ 13)⟩,
       ⟨((-5731 : Dyadic) * half ^ 13),
        ((1051 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((477 : Dyadic) * half ^ 13),
        ((-6053 : Dyadic) * half ^ 14)⟩,
       ⟨((1329 : Dyadic) * half ^ 13),
        ((1645 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word5Step20 :
    word5Chunk20.foldl (fun acc a => a.applyPacked acc)
      word5State20 = word5State21 := by decide +kernel

private def word5Chunk21 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word5State22 : PackedMat2 :=
    ⟨⟨⟨((17613 : Dyadic) * half ^ 15),
        ((-871 : Dyadic) * half ^ 15)⟩,
       ⟨((6787 : Dyadic) * half ^ 15),
        ((-5825 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((12295 : Dyadic) * half ^ 15),
        ((5803 : Dyadic) * half ^ 15)⟩,
       ⟨((2193 : Dyadic) * half ^ 15),
        ((2629 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((16319 : Dyadic) * half ^ 15),
        ((1811 : Dyadic) * half ^ 13)⟩,
       ⟨((-4713 : Dyadic) * half ^ 15),
        ((5051 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((12521 : Dyadic) * half ^ 15),
        ((-1525 : Dyadic) * half ^ 12)⟩,
       ⟨((-10779 : Dyadic) * half ^ 15),
        ((-5413 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word5Step21 :
    word5Chunk21.foldl (fun acc a => a.applyPacked acc)
      word5State21 = word5State22 := by decide +kernel

private def word5Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word5State23 : PackedMat2 :=
    ⟨⟨⟨((52389 : Dyadic) * half ^ 16),
        ((5015 : Dyadic) * half ^ 16)⟩,
       ⟨((-7951 : Dyadic) * half ^ 16),
        ((1213 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-8535 : Dyadic) * half ^ 16),
        ((14981 : Dyadic) * half ^ 16)⟩,
       ⟨((12529 : Dyadic) * half ^ 16),
        ((97 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-16533 : Dyadic) * half ^ 16),
        ((-1997 : Dyadic) * half ^ 16)⟩,
       ⟨((-13429 : Dyadic) * half ^ 16),
        ((2633 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((24423 : Dyadic) * half ^ 16),
        ((22219 : Dyadic) * half ^ 16)⟩,
       ⟨((-14393 : Dyadic) * half ^ 16),
        ((15085 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word5Step22 :
    word5Chunk22.foldl (fun acc a => a.applyPacked acc)
      word5State22 = word5State23 := by decide +kernel

private def word5Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word5State24 : PackedMat2 :=
    ⟨⟨⟨((4723 : Dyadic) * half ^ 16),
        ((23981 : Dyadic) * half ^ 16)⟩,
       ⟨((19669 : Dyadic) * half ^ 15),
        ((-561 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-8739 : Dyadic) * half ^ 15),
        ((-7551 : Dyadic) * half ^ 16)⟩,
       ⟨((-6691 : Dyadic) * half ^ 16),
        ((23459 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-8739 : Dyadic) * half ^ 15),
        ((-7551 : Dyadic) * half ^ 16)⟩,
       ⟨((6691 : Dyadic) * half ^ 16),
        ((-23459 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-4723 : Dyadic) * half ^ 16),
        ((-23981 : Dyadic) * half ^ 16)⟩,
       ⟨((19669 : Dyadic) * half ^ 15),
        ((-561 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word5Step23 :
    word5Chunk23.foldl (fun acc a => a.applyPacked acc)
      word5State23 = word5State24 := by decide +kernel

private def word5Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word5State25 : PackedMat2 :=
    ⟨⟨⟨((19817 : Dyadic) * half ^ 16),
        ((24721 : Dyadic) * half ^ 18)⟩,
       ⟨((16143 : Dyadic) * half ^ 17),
        ((102469 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((8907 : Dyadic) * half ^ 16),
        ((-116489 : Dyadic) * half ^ 18)⟩,
       ⟨((7703 : Dyadic) * half ^ 17),
        ((-72545 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((5493 : Dyadic) * half ^ 15),
        ((-10111 : Dyadic) * half ^ 18)⟩,
       ⟨((-94517 : Dyadic) * half ^ 17),
        ((25517 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-19437 : Dyadic) * half ^ 16),
        ((23491 : Dyadic) * half ^ 18)⟩,
       ⟨((-63595 : Dyadic) * half ^ 17),
        ((-55777 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word5Step24 :
    word5Chunk24.foldl (fun acc a => a.applyPacked acc)
      word5State24 = word5State25 := by decide +kernel

private def word5Chunk25 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State26 : PackedMat2 :=
    ⟨⟨⟨((3299 : Dyadic) * half ^ 15),
        ((-69845 : Dyadic) * half ^ 18)⟩,
       ⟨((525 : Dyadic) * half ^ 10),
        ((8097 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-81913 : Dyadic) * half ^ 17),
        ((20863 : Dyadic) * half ^ 17)⟩,
       ⟨((-9647 : Dyadic) * half ^ 16),
        ((693 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((9647 : Dyadic) * half ^ 16),
        ((-693 : Dyadic) * half ^ 18)⟩,
       ⟨((81913 : Dyadic) * half ^ 17),
        ((-20863 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((525 : Dyadic) * half ^ 10),
        ((8097 : Dyadic) * half ^ 15)⟩,
       ⟨((3299 : Dyadic) * half ^ 15),
        ((-69845 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word5Step25 :
    word5Chunk25.foldl (fun acc a => a.applyPacked acc)
      word5State25 = word5State26 := by decide +kernel

private def word5Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word5State27 : PackedMat2 :=
    ⟨⟨⟨((-276903 : Dyadic) * half ^ 19),
        ((-12499 : Dyadic) * half ^ 19)⟩,
       ⟨((334001 : Dyadic) * half ^ 19),
        ((24121 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-109211 : Dyadic) * half ^ 19),
        ((9671 : Dyadic) * half ^ 19)⟩,
       ⟨((-109047 : Dyadic) * half ^ 19),
        ((84907 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-109211 : Dyadic) * half ^ 19),
        ((9671 : Dyadic) * half ^ 19)⟩,
       ⟨((109047 : Dyadic) * half ^ 19),
        ((-84907 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((276903 : Dyadic) * half ^ 19),
        ((12499 : Dyadic) * half ^ 19)⟩,
       ⟨((334001 : Dyadic) * half ^ 19),
        ((24121 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word5Step26 :
    word5Chunk26.foldl (fun acc a => a.applyPacked acc)
      word5State26 = word5State27 := by decide +kernel

private def word5Chunk27 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word5State28 : PackedMat2 :=
    ⟨⟨⟨((-138991 : Dyadic) * half ^ 19),
        ((-341277 : Dyadic) * half ^ 20)⟩,
       ⟨((-377323 : Dyadic) * half ^ 19),
        ((76937 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((14857 : Dyadic) * half ^ 17),
        ((125885 : Dyadic) * half ^ 20)⟩,
       ⟨((26883 : Dyadic) * half ^ 17),
        ((-240723 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-14857 : Dyadic) * half ^ 17),
        ((-125885 : Dyadic) * half ^ 20)⟩,
       ⟨((26883 : Dyadic) * half ^ 17),
        ((-240723 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-138991 : Dyadic) * half ^ 19),
        ((-341277 : Dyadic) * half ^ 20)⟩,
       ⟨((377323 : Dyadic) * half ^ 19),
        ((-76937 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word5Step27 :
    word5Chunk27.foldl (fun acc a => a.applyPacked acc)
      word5State27 = word5State28 := by decide +kernel

private def word5Chunk28 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State29 : PackedMat2 :=
    ⟨⟨⟨((93465 : Dyadic) * half ^ 20),
        ((-521879 : Dyadic) * half ^ 21)⟩,
       ⟨((-122679 : Dyadic) * half ^ 19),
        ((-1047819 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-113817 : Dyadic) * half ^ 20),
        ((-156735 : Dyadic) * half ^ 21)⟩,
       ⟨((-195201 : Dyadic) * half ^ 19),
        ((579281 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-46001 : Dyadic) * half ^ 17),
        ((276585 : Dyadic) * half ^ 21)⟩,
       ⟨((-211273 : Dyadic) * half ^ 20),
        ((504219 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-131485 : Dyadic) * half ^ 19),
        ((-338823 : Dyadic) * half ^ 21)⟩,
       ⟨((-784849 : Dyadic) * half ^ 20),
        ((-151893 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word5Step28 :
    word5Chunk28.foldl (fun acc a => a.applyPacked acc)
      word5State28 = word5State29 := by decide +kernel

private def word5Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State30 : PackedMat2 :=
    ⟨⟨⟨((-195169 : Dyadic) * half ^ 20),
        ((539007 : Dyadic) * half ^ 21)⟩,
       ⟨((-35247 : Dyadic) * half ^ 17),
        ((-397969 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((70101 : Dyadic) * half ^ 20),
        ((-71259 : Dyadic) * half ^ 20)⟩,
       ⟨((110053 : Dyadic) * half ^ 20),
        ((-992679 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((110053 : Dyadic) * half ^ 20),
        ((-992679 : Dyadic) * half ^ 21)⟩,
       ⟨((70101 : Dyadic) * half ^ 20),
        ((-71259 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((35247 : Dyadic) * half ^ 17),
        ((397969 : Dyadic) * half ^ 20)⟩,
       ⟨((195169 : Dyadic) * half ^ 20),
        ((-539007 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word5Step29 :
    word5Chunk29.foldl (fun acc a => a.applyPacked acc)
      word5State29 = word5State30 := by decide +kernel

private def word5Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State31 : PackedMat2 :=
    ⟨⟨⟨((791805 : Dyadic) * half ^ 22),
        ((27847 : Dyadic) * half ^ 18)⟩,
       ⟨((-3117411 : Dyadic) * half ^ 22),
        ((155209 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((829803 : Dyadic) * half ^ 22),
        ((152461 : Dyadic) * half ^ 19)⟩,
       ⟨((-1588225 : Dyadic) * half ^ 22),
        ((554733 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1774421 : Dyadic) * half ^ 22),
        ((379211 : Dyadic) * half ^ 22)⟩,
       ⟨((-664955 : Dyadic) * half ^ 22),
        ((-604507 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((600761 : Dyadic) * half ^ 22),
        ((-1162803 : Dyadic) * half ^ 22)⟩,
       ⟨((290343 : Dyadic) * half ^ 22),
        ((122163 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word5Step30 :
    word5Chunk30.foldl (fun acc a => a.applyPacked acc)
      word5State30 = word5State31 := by decide +kernel

private def word5Chunk31 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State32 : PackedMat2 :=
    ⟨⟨⟨((1399185 : Dyadic) * half ^ 21),
        ((81863 : Dyadic) * half ^ 23)⟩,
       ⟨((68105 : Dyadic) * half ^ 21),
        ((-3891547 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((455095 : Dyadic) * half ^ 22),
        ((430279 : Dyadic) * half ^ 23)⟩,
       ⟨((1365537 : Dyadic) * half ^ 22),
        ((77015 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((455095 : Dyadic) * half ^ 22),
        ((430279 : Dyadic) * half ^ 23)⟩,
       ⟨((-1365537 : Dyadic) * half ^ 22),
        ((-77015 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1399185 : Dyadic) * half ^ 21),
        ((-81863 : Dyadic) * half ^ 23)⟩,
       ⟨((68105 : Dyadic) * half ^ 21),
        ((-3891547 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word5Step31 :
    word5Chunk31.foldl (fun acc a => a.applyPacked acc)
      word5State31 = word5State32 := by decide +kernel

private def word5Chunk32 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State33 : PackedMat2 :=
    ⟨⟨⟨((49825 : Dyadic) * half ^ 21),
        ((11308919 : Dyadic) * half ^ 24)⟩,
       ⟨((-916545 : Dyadic) * half ^ 23),
        ((-556159 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((60599 : Dyadic) * half ^ 19),
        ((-2101405 : Dyadic) * half ^ 24)⟩,
       ⟨((-1454595 : Dyadic) * half ^ 23),
        ((499193 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1300299 : Dyadic) * half ^ 23),
        ((-2424179 : Dyadic) * half ^ 24)⟩,
       ⟨((-400553 : Dyadic) * half ^ 22),
        ((-485011 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((5932539 : Dyadic) * half ^ 23),
        ((1115845 : Dyadic) * half ^ 24)⟩,
       ⟨((-1344095 : Dyadic) * half ^ 21),
        ((717245 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word5Step32 :
    word5Chunk32.foldl (fun acc a => a.applyPacked acc)
      word5State32 = word5State33 := by decide +kernel

private def word5Chunk33 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State34 : PackedMat2 :=
    ⟨⟨⟨((1649381 : Dyadic) * half ^ 21),
        ((-573323 : Dyadic) * half ^ 24)⟩,
       ⟨((137217 : Dyadic) * half ^ 21),
        ((2244159 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-423055 : Dyadic) * half ^ 23),
        ((-616809 : Dyadic) * half ^ 21)⟩,
       ⟨((69029 : Dyadic) * half ^ 21),
        ((-2783377 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-69029 : Dyadic) * half ^ 21),
        ((2783377 : Dyadic) * half ^ 24)⟩,
       ⟨((423055 : Dyadic) * half ^ 23),
        ((616809 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((137217 : Dyadic) * half ^ 21),
        ((2244159 : Dyadic) * half ^ 23)⟩,
       ⟨((1649381 : Dyadic) * half ^ 21),
        ((-573323 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word5Step33 :
    word5Chunk33.foldl (fun acc a => a.applyPacked acc)
      word5State33 = word5State34 := by decide +kernel

private def word5Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word5State35 : PackedMat2 :=
    ⟨⟨⟨((-4395477 : Dyadic) * half ^ 25),
        ((8007559 : Dyadic) * half ^ 25)⟩,
       ⟨((29889533 : Dyadic) * half ^ 25),
        ((83919 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-5359535 : Dyadic) * half ^ 25),
        ((-4111389 : Dyadic) * half ^ 25)⟩,
       ⟨((-2497869 : Dyadic) * half ^ 25),
        ((345519 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-5359535 : Dyadic) * half ^ 25),
        ((-4111389 : Dyadic) * half ^ 25)⟩,
       ⟨((2497869 : Dyadic) * half ^ 25),
        ((-345519 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((4395477 : Dyadic) * half ^ 25),
        ((-8007559 : Dyadic) * half ^ 25)⟩,
       ⟨((29889533 : Dyadic) * half ^ 25),
        ((83919 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word5Step34 :
    word5Chunk34.foldl (fun acc a => a.applyPacked acc)
      word5State34 = word5State35 := by decide +kernel

private def word5Chunk35 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word5State36 : PackedMat2 :=
    ⟨⟨⟨((13869661 : Dyadic) * half ^ 26),
        ((-16932677 : Dyadic) * half ^ 25)⟩,
       ⟨((34993525 : Dyadic) * half ^ 26),
        ((8803739 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-4433449 : Dyadic) * half ^ 26),
        ((-1162941 : Dyadic) * half ^ 25)⟩,
       ⟨((9390587 : Dyadic) * half ^ 26),
        ((16113523 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((4433449 : Dyadic) * half ^ 26),
        ((1162941 : Dyadic) * half ^ 25)⟩,
       ⟨((9390587 : Dyadic) * half ^ 26),
        ((16113523 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((13869661 : Dyadic) * half ^ 26),
        ((-16932677 : Dyadic) * half ^ 25)⟩,
       ⟨((-34993525 : Dyadic) * half ^ 26),
        ((-8803739 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word5Step35 :
    word5Chunk35.foldl (fun acc a => a.applyPacked acc)
      word5State35 = word5State36 := by decide +kernel

private def word5Chunk36 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word5State37 : PackedMat2 :=
    ⟨⟨⟨((-17803339 : Dyadic) * half ^ 27),
        ((-29153075 : Dyadic) * half ^ 27)⟩,
       ⟨((-29772945 : Dyadic) * half ^ 27),
        ((16072521 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-76501645 : Dyadic) * half ^ 27),
        ((-19113207 : Dyadic) * half ^ 27)⟩,
       ⟨((-14861555 : Dyadic) * half ^ 27),
        ((564449 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-14597615 : Dyadic) * half ^ 27),
        ((-713775 : Dyadic) * half ^ 21)⟩,
       ⟨((-23628799 : Dyadic) * half ^ 27),
        ((-30820045 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-35137009 : Dyadic) * half ^ 27),
        ((11894071 : Dyadic) * half ^ 26)⟩,
       ⟨((93443159 : Dyadic) * half ^ 27),
        ((-5984803 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word5Step36 :
    word5Chunk36.foldl (fun acc a => a.applyPacked acc)
      word5State36 = word5State37 := by decide +kernel

private def word5Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word5State38 : PackedMat2 :=
    ⟨⟨⟨((-5424345 : Dyadic) * half ^ 25),
        ((-77577831 : Dyadic) * half ^ 28)⟩,
       ⟨((2142199 : Dyadic) * half ^ 24),
        ((-78039227 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((3204043 : Dyadic) * half ^ 27),
        ((-145307321 : Dyadic) * half ^ 28)⟩,
       ⟨((-24833561 : Dyadic) * half ^ 27),
        ((-4821687 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-3204043 : Dyadic) * half ^ 27),
        ((145307321 : Dyadic) * half ^ 28)⟩,
       ⟨((-24833561 : Dyadic) * half ^ 27),
        ((-4821687 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-5424345 : Dyadic) * half ^ 25),
        ((-77577831 : Dyadic) * half ^ 28)⟩,
       ⟨((-2142199 : Dyadic) * half ^ 24),
        ((78039227 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word5Step37 :
    word5Chunk37.foldl (fun acc a => a.applyPacked acc)
      word5State37 = word5State38 := by decide +kernel

private def word5Chunk38 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State39 : PackedMat2 :=
    ⟨⟨⟨((-169779927 : Dyadic) * half ^ 28),
        ((13014949 : Dyadic) * half ^ 29)⟩,
       ⟨((-5311857 : Dyadic) * half ^ 23),
        ((-15265043 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-42665231 : Dyadic) * half ^ 28),
        ((15789561 : Dyadic) * half ^ 29)⟩,
       ⟨((-924171 : Dyadic) * half ^ 27),
        ((-156139471 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((21491129 : Dyadic) * half ^ 26),
        ((-40816889 : Dyadic) * half ^ 29)⟩,
       ⟨((70174955 : Dyadic) * half ^ 28),
        ((44513573 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-3534999 : Dyadic) * half ^ 26),
        ((-199497 : Dyadic) * half ^ 29)⟩,
       ⟨((-1125047 : Dyadic) * half ^ 28),
        ((-339759351 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word5Step38 :
    word5Chunk38.foldl (fun acc a => a.applyPacked acc)
      word5State38 = word5State39 := by decide +kernel

private def word5Chunk39 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State40 : PackedMat2 :=
    ⟨⟨⟨((56414901 : Dyadic) * half ^ 27),
        ((-85021093 : Dyadic) * half ^ 28)⟩,
       ⟨((-182513 : Dyadic) * half ^ 19),
        ((-241541685 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-19017753 : Dyadic) * half ^ 26),
        ((41911979 : Dyadic) * half ^ 29)⟩,
       ⟨((-14412639 : Dyadic) * half ^ 28),
        ((854935 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-14412639 : Dyadic) * half ^ 28),
        ((854935 : Dyadic) * half ^ 25)⟩,
       ⟨((-19017753 : Dyadic) * half ^ 26),
        ((41911979 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((182513 : Dyadic) * half ^ 19),
        ((241541685 : Dyadic) * half ^ 29)⟩,
       ⟨((-56414901 : Dyadic) * half ^ 27),
        ((85021093 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word5Step39 :
    word5Chunk39.foldl (fun acc a => a.applyPacked acc)
      word5State39 = word5State40 := by decide +kernel

private def word5Chunk40 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word5State41 : PackedMat2 :=
    ⟨⟨⟨((407761663 : Dyadic) * half ^ 30),
        ((32701015 : Dyadic) * half ^ 29)⟩,
       ⟨((-836474187 : Dyadic) * half ^ 30),
        ((6023457 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((371888551 : Dyadic) * half ^ 30),
        ((109746141 : Dyadic) * half ^ 30)⟩,
       ⟨((309820331 : Dyadic) * half ^ 30),
        ((-87709039 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-309820331 : Dyadic) * half ^ 30),
        ((87709039 : Dyadic) * half ^ 30)⟩,
       ⟨((-371888551 : Dyadic) * half ^ 30),
        ((-109746141 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-836474187 : Dyadic) * half ^ 30),
        ((6023457 : Dyadic) * half ^ 27)⟩,
       ⟨((407761663 : Dyadic) * half ^ 30),
        ((32701015 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word5Step40 :
    word5Chunk40.foldl (fun acc a => a.applyPacked acc)
      word5State40 = word5State41 := by decide +kernel

private def word5Chunk41 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word5State42 : PackedMat2 :=
    ⟨⟨⟨((1667645867 : Dyadic) * half ^ 31),
        ((-284850927 : Dyadic) * half ^ 31)⟩,
       ⟨((-74038347 : Dyadic) * half ^ 31),
        ((-199391049 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((920579509 : Dyadic) * half ^ 31),
        ((490121965 : Dyadic) * half ^ 31)⟩,
       ⟨((76492039 : Dyadic) * half ^ 31),
        ((-37199519 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((415722927 : Dyadic) * half ^ 31),
        ((249267887 : Dyadic) * half ^ 30)⟩,
       ⟨((564521003 : Dyadic) * half ^ 31),
        ((422043735 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((683633025 : Dyadic) * half ^ 31),
        ((-49800235 : Dyadic) * half ^ 27)⟩,
       ⟨((-113931171 : Dyadic) * half ^ 31),
        ((-870842107 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word5Step41 :
    word5Chunk41.foldl (fun acc a => a.applyPacked acc)
      word5State41 = word5State42 := by decide +kernel

private def word5Chunk42 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word5State43 : PackedMat2 :=
    ⟨⟨⟨((-531976711 : Dyadic) * half ^ 31),
        ((1026505453 : Dyadic) * half ^ 31)⟩,
       ⟨((50705381 : Dyadic) * half ^ 27),
        ((666389333 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((15692655 : Dyadic) * half ^ 28),
        ((-98810369 : Dyadic) * half ^ 29)⟩,
       ⟨((572939613 : Dyadic) * half ^ 31),
        ((96107335 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-15692655 : Dyadic) * half ^ 28),
        ((98810369 : Dyadic) * half ^ 29)⟩,
       ⟨((572939613 : Dyadic) * half ^ 31),
        ((96107335 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-531976711 : Dyadic) * half ^ 31),
        ((1026505453 : Dyadic) * half ^ 31)⟩,
       ⟨((-50705381 : Dyadic) * half ^ 27),
        ((-666389333 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word5Step42 :
    word5Chunk42.foldl (fun acc a => a.applyPacked acc)
      word5State42 = word5State43 := by decide +kernel

private def word5Chunk43 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word5State44 : PackedMat2 :=
    ⟨⟨⟨((-120617471 : Dyadic) * half ^ 32),
        ((-9001913 : Dyadic) * half ^ 28)⟩,
       ⟨((927709541 : Dyadic) * half ^ 30),
        ((225752489 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((463972213 : Dyadic) * half ^ 31),
        ((-39638513 : Dyadic) * half ^ 31)⟩,
       ⟨((-1808697167 : Dyadic) * half ^ 32),
        ((27006279 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((463972213 : Dyadic) * half ^ 31),
        ((-39638513 : Dyadic) * half ^ 31)⟩,
       ⟨((1808697167 : Dyadic) * half ^ 32),
        ((-27006279 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((120617471 : Dyadic) * half ^ 32),
        ((9001913 : Dyadic) * half ^ 28)⟩,
       ⟨((927709541 : Dyadic) * half ^ 30),
        ((225752489 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word5Step43 :
    word5Chunk43.foldl (fun acc a => a.applyPacked acc)
      word5State43 = word5State44 := by decide +kernel

private def word5Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word5State45 : PackedMat2 :=
    ⟨⟨⟨((-2175861409 : Dyadic) * half ^ 32),
        ((188012821 : Dyadic) * half ^ 34)⟩,
       ⟨((842264997 : Dyadic) * half ^ 33),
        ((4396973519 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((432966249 : Dyadic) * half ^ 31),
        ((4581908617 : Dyadic) * half ^ 34)⟩,
       ⟨((1422362257 : Dyadic) * half ^ 33),
        ((-7607404021 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6094656319 : Dyadic) * half ^ 33),
        ((-309502739 : Dyadic) * half ^ 34)⟩,
       ⟨((-756373851 : Dyadic) * half ^ 32),
        ((3154227253 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2104480349 : Dyadic) * half ^ 33),
        ((-5193987815 : Dyadic) * half ^ 34)⟩,
       ⟨((-1146246585 : Dyadic) * half ^ 32),
        ((3509457821 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word5Step44 :
    word5Chunk44.foldl (fun acc a => a.applyPacked acc)
      word5State44 = word5State45 := by decide +kernel

private def word5Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word5State46 : PackedMat2 :=
    ⟨⟨⟨((-596529293 : Dyadic) * half ^ 32),
        ((-4420581943 : Dyadic) * half ^ 33)⟩,
       ⟨((733806479 : Dyadic) * half ^ 33),
        ((-2867430603 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-596088229 : Dyadic) * half ^ 33),
        ((5629573417 : Dyadic) * half ^ 34)⟩,
       ⟨((-3358902011 : Dyadic) * half ^ 33),
        ((757414903 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-7144403223 : Dyadic) * half ^ 34),
        ((123593445 : Dyadic) * half ^ 29)⟩,
       ⟨((-4114743611 : Dyadic) * half ^ 34),
        ((-1381406891 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-11708594489 : Dyadic) * half ^ 34),
        ((-459252107 : Dyadic) * half ^ 34)⟩,
       ⟨((-5973733283 : Dyadic) * half ^ 34),
        ((-1926865065 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word5Step45 :
    word5Chunk45.foldl (fun acc a => a.applyPacked acc)
      word5State45 = word5State46 := by decide +kernel

private def word5Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word5State47 : PackedMat2 :=
    ⟨⟨⟨((7451399341 : Dyadic) * half ^ 35),
        ((-43277527 : Dyadic) * half ^ 27)⟩,
       ⟨((-6970106339 : Dyadic) * half ^ 35),
        ((-4626019589 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-13302623081 : Dyadic) * half ^ 35),
        ((-2983682811 : Dyadic) * half ^ 35)⟩,
       ⟨((1421208001 : Dyadic) * half ^ 35),
        ((-15215297041 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((1421208001 : Dyadic) * half ^ 35),
        ((-15215297041 : Dyadic) * half ^ 35)⟩,
       ⟨((-13302623081 : Dyadic) * half ^ 35),
        ((-2983682811 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((6970106339 : Dyadic) * half ^ 35),
        ((4626019589 : Dyadic) * half ^ 34)⟩,
       ⟨((-7451399341 : Dyadic) * half ^ 35),
        ((43277527 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word5Step46 :
    word5Chunk46.foldl (fun acc a => a.applyPacked acc)
      word5State46 = word5State47 := by decide +kernel

private def word5Chunk47 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word5State48 : PackedMat2 :=
    ⟨⟨⟨((3010992367 : Dyadic) * half ^ 36),
        ((22644146059 : Dyadic) * half ^ 36)⟩,
       ⟨((-23284293245 : Dyadic) * half ^ 36),
        ((-5343618855 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-27719659713 : Dyadic) * half ^ 36),
        ((2153320461 : Dyadic) * half ^ 36)⟩,
       ⟨((-45560224897 : Dyadic) * half ^ 36),
        ((2824139015 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-7801598491 : Dyadic) * half ^ 36),
        ((36639942305 : Dyadic) * half ^ 36)⟩,
       ⟨((3494957569 : Dyadic) * half ^ 36),
        ((-278758831 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((11956908349 : Dyadic) * half ^ 36),
        ((-10136650439 : Dyadic) * half ^ 36)⟩,
       ⟨((33331383769 : Dyadic) * half ^ 36),
        ((6573821403 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word5Step47 :
    word5Chunk47.foldl (fun acc a => a.applyPacked acc)
      word5State47 = word5State48 := by decide +kernel

private def word5Chunk48 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word5State49 : PackedMat2 :=
    ⟨⟨⟨((28533202565 : Dyadic) * half ^ 35),
        ((8049952047 : Dyadic) * half ^ 37)⟩,
       ⟨((2339044165 : Dyadic) * half ^ 35),
        ((-2793467647 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((13291286287 : Dyadic) * half ^ 36),
        ((-44055175453 : Dyadic) * half ^ 37)⟩,
       ⟨((-6706055643 : Dyadic) * half ^ 36),
        ((-20762758377 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-5823104269 : Dyadic) * half ^ 35),
        ((9998670965 : Dyadic) * half ^ 36)⟩,
       ⟨((32408966915 : Dyadic) * half ^ 36),
        ((-1646307661 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-5421709847 : Dyadic) * half ^ 36),
        ((-409283725 : Dyadic) * half ^ 30)⟩,
       ⟨((328530275 : Dyadic) * half ^ 33),
        ((15436123365 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word5Step48 :
    word5Chunk48.foldl (fun acc a => a.applyPacked acc)
      word5State48 = word5State49 := by decide +kernel

private def word5Chunk49 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word5State50 : PackedMat2 :=
    ⟨⟨⟨((-8274344821 : Dyadic) * half ^ 37),
        ((136923619837 : Dyadic) * half ^ 38)⟩,
       ⟨((43340952199 : Dyadic) * half ^ 36),
        ((10820898063 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-42770829657 : Dyadic) * half ^ 37),
        ((-5042985849 : Dyadic) * half ^ 38)⟩,
       ⟨((-2421614945 : Dyadic) * half ^ 36),
        ((4277206721 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-2421614945 : Dyadic) * half ^ 36),
        ((4277206721 : Dyadic) * half ^ 38)⟩,
       ⟨((-42770829657 : Dyadic) * half ^ 37),
        ((-5042985849 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-43340952199 : Dyadic) * half ^ 36),
        ((-10820898063 : Dyadic) * half ^ 38)⟩,
       ⟨((8274344821 : Dyadic) * half ^ 37),
        ((-136923619837 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word5Step49 :
    word5Chunk49.foldl (fun acc a => a.applyPacked acc)
      word5State49 = word5State50 := by decide +kernel

private def word5Chunk50 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word5State51 : PackedMat2 :=
    ⟨⟨⟨((75176265231 : Dyadic) * half ^ 38),
        ((-112992014121 : Dyadic) * half ^ 39)⟩,
       ⟨((84163450335 : Dyadic) * half ^ 37),
        ((-40349072073 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-75219958239 : Dyadic) * half ^ 38),
        ((-194021422789 : Dyadic) * half ^ 39)⟩,
       ⟨((-2462133957 : Dyadic) * half ^ 37),
        ((-140501808985 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-13379903451 : Dyadic) * half ^ 37),
        ((-70295690325 : Dyadic) * half ^ 39)⟩,
       ⟨((167261615887 : Dyadic) * half ^ 38),
        ((80144226153 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((2270091939 : Dyadic) * half ^ 34),
        ((93150635439 : Dyadic) * half ^ 39)⟩,
       ⟨((-76670543097 : Dyadic) * half ^ 38),
        ((243503165901 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word5Step50 :
    word5Chunk50.foldl (fun acc a => a.applyPacked acc)
      word5State50 = word5State51 := by decide +kernel

private def word5Chunk51 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word5State52 : PackedMat2 :=
    ⟨⟨⟨((-306584443827 : Dyadic) * half ^ 39),
        ((-5052619785 : Dyadic) * half ^ 39)⟩,
       ⟨((-2559562649 : Dyadic) * half ^ 39),
        ((125502225003 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((89705890275 : Dyadic) * half ^ 39),
        ((44672272111 : Dyadic) * half ^ 37)⟩,
       ⟨((-314227849309 : Dyadic) * half ^ 39),
        ((13729915743 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-314227849309 : Dyadic) * half ^ 39),
        ((13729915743 : Dyadic) * half ^ 37)⟩,
       ⟨((89705890275 : Dyadic) * half ^ 39),
        ((44672272111 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((2559562649 : Dyadic) * half ^ 39),
        ((-125502225003 : Dyadic) * half ^ 39)⟩,
       ⟨((306584443827 : Dyadic) * half ^ 39),
        ((5052619785 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word5Step51 :
    word5Chunk51.foldl (fun acc a => a.applyPacked acc)
      word5State51 = word5State52 := by decide +kernel

private def word5Chunk52 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word5State53 : PackedMat2 :=
    ⟨⟨⟨((116223748551 : Dyadic) * half ^ 40),
        ((-115059899519 : Dyadic) * half ^ 39)⟩,
       ⟨((-289188745237 : Dyadic) * half ^ 40),
        ((104648797083 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((802160870985 : Dyadic) * half ^ 40),
        ((46699666973 : Dyadic) * half ^ 38)⟩,
       ⟨((319994821437 : Dyadic) * half ^ 40),
        ((-290110764103 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-802160870985 : Dyadic) * half ^ 40),
        ((-46699666973 : Dyadic) * half ^ 38)⟩,
       ⟨((319994821437 : Dyadic) * half ^ 40),
        ((-290110764103 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((116223748551 : Dyadic) * half ^ 40),
        ((-115059899519 : Dyadic) * half ^ 39)⟩,
       ⟨((289188745237 : Dyadic) * half ^ 40),
        ((-104648797083 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word5Step52 :
    word5Chunk52.foldl (fun acc a => a.applyPacked acc)
      word5State52 = word5State53 := by decide +kernel

private def word5Chunk53 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word5State54 : PackedMat2 :=
    ⟨⟨⟨((-60825732739 : Dyadic) * half ^ 37),
        ((-21902964553 : Dyadic) * half ^ 38)⟩,
       ⟨((322758082077 : Dyadic) * half ^ 40),
        ((-404709654189 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((84913131449 : Dyadic) * half ^ 40),
        ((431075918025 : Dyadic) * half ^ 40)⟩,
       ⟨((31945505501 : Dyadic) * half ^ 37),
        ((201072346123 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((115001785951 : Dyadic) * half ^ 39),
        ((-170650912559 : Dyadic) * half ^ 41)⟩,
       ⟨((-158037066037 : Dyadic) * half ^ 38),
        ((-340477175457 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-317097795977 : Dyadic) * half ^ 40),
        ((809363943989 : Dyadic) * half ^ 41)⟩,
       ⟨((-492321512401 : Dyadic) * half ^ 40),
        ((-163847779835 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word5Step53 :
    word5Chunk53.foldl (fun acc a => a.applyPacked acc)
      word5State53 = word5State54 := by decide +kernel

private def word5Chunk54 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word5State55 : PackedMat2 :=
    ⟨⟨⟨((-267978226599 : Dyadic) * half ^ 41),
        ((-334443328005 : Dyadic) * half ^ 42)⟩,
       ⟨((-964086717219 : Dyadic) * half ^ 40),
        ((129815272273 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((289489996065 : Dyadic) * half ^ 41),
        ((577045514641 : Dyadic) * half ^ 42)⟩,
       ⟨((-2631844353 : Dyadic) * half ^ 40),
        ((1209432144231 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-2631844353 : Dyadic) * half ^ 40),
        ((1209432144231 : Dyadic) * half ^ 42)⟩,
       ⟨((289489996065 : Dyadic) * half ^ 41),
        ((577045514641 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((964086717219 : Dyadic) * half ^ 40),
        ((-129815272273 : Dyadic) * half ^ 42)⟩,
       ⟨((267978226599 : Dyadic) * half ^ 41),
        ((334443328005 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word5Step54 :
    word5Chunk54.foldl (fun acc a => a.applyPacked acc)
      word5State54 = word5State55 := by decide +kernel

private def word5Chunk55 : List Letter := [.h, .s, .t, .h, .s, .t, .h]
private def word5State56 : PackedMat2 :=
    ⟨⟨⟨((1428630595167 : Dyadic) * half ^ 41),
        ((1074524785465 : Dyadic) * half ^ 42)⟩,
       ⟨((620843932589 : Dyadic) * half ^ 41),
        ((-73926768017 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-31131599643 : Dyadic) * half ^ 38),
        ((88053460867 : Dyadic) * half ^ 40)⟩,
       ⟨((710060907173 : Dyadic) * half ^ 41),
        ((-1004177765035 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((31131599643 : Dyadic) * half ^ 38),
        ((-88053460867 : Dyadic) * half ^ 40)⟩,
       ⟨((710060907173 : Dyadic) * half ^ 41),
        ((-1004177765035 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1428630595167 : Dyadic) * half ^ 41),
        ((1074524785465 : Dyadic) * half ^ 42)⟩,
       ⟨((-620843932589 : Dyadic) * half ^ 41),
        ((73926768017 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word5Step55 :
    word5Chunk55.foldl (fun acc a => a.applyPacked acc)
      word5State55 = word5State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word5_check : check word5 5 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word5 = word5State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word5Chunk0 ++ word5Chunk1 ++ word5Chunk2 ++ word5Chunk3 ++
      word5Chunk4 ++ word5Chunk5 ++ word5Chunk6 ++ word5Chunk7 ++
      word5Chunk8 ++ word5Chunk9 ++ word5Chunk10 ++ word5Chunk11 ++
      word5Chunk12 ++ word5Chunk13 ++ word5Chunk14 ++ word5Chunk15 ++
      word5Chunk16 ++ word5Chunk17 ++ word5Chunk18 ++ word5Chunk19 ++
      word5Chunk20 ++ word5Chunk21 ++ word5Chunk22 ++ word5Chunk23 ++
      word5Chunk24 ++ word5Chunk25 ++ word5Chunk26 ++ word5Chunk27 ++
      word5Chunk28 ++ word5Chunk29 ++ word5Chunk30 ++ word5Chunk31 ++
      word5Chunk32 ++ word5Chunk33 ++ word5Chunk34 ++ word5Chunk35 ++
      word5Chunk36 ++ word5Chunk37 ++ word5Chunk38 ++ word5Chunk39 ++
      word5Chunk40 ++ word5Chunk41 ++ word5Chunk42 ++ word5Chunk43 ++
      word5Chunk44 ++ word5Chunk45 ++ word5Chunk46 ++ word5Chunk47 ++
      word5Chunk48 ++ word5Chunk49 ++ word5Chunk50 ++ word5Chunk51 ++
      word5Chunk52 ++ word5Chunk53 ++ word5Chunk54 ++ word5Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word5Step0, word5Step1, word5Step2, word5Step3, word5Step4,
      word5Step5, word5Step6, word5Step7, word5Step8, word5Step9,
      word5Step10, word5Step11, word5Step12, word5Step13, word5Step14,
      word5Step15, word5Step16, word5Step17, word5Step18, word5Step19,
      word5Step20, word5Step21, word5Step22, word5Step23, word5Step24,
      word5Step25, word5Step26, word5Step27, word5Step28, word5Step29,
      word5Step30, word5Step31, word5Step32, word5Step33, word5Step34,
      word5Step35, word5Step36, word5Step37, word5Step38, word5Step39,
      word5Step40, word5Step41, word5Step42, word5Step43, word5Step44,
      word5Step45, word5Step46, word5Step47, word5Step48, word5Step49,
      word5Step50, word5Step51, word5Step52, word5Step53, word5Step54,
      word5Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

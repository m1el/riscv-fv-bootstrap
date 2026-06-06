(** * General refinement for hex1 in Coq -- mirror of lean/Hex1/Refine.lean.

    Target (the Coq port of the campaign theorem, cf. Refine.v for hex0):

      core1_refines : forall inp cap, WellFormed1 inp cap ->
        runOn1-style observation of the real core1 bytes = coreSpec1 inp cap

    proved by genuine induction (no vm_compute on the general statement),
    over the THREE loops of core1 (init / pass 1 / pass 2) and the label
    table region.

    STATUS: IN PROGRESS -- engine layer (chunk 1).
    - fetch at a code offset (Image1) + the 16 per-instruction step lemmas
      (hex0's 12 + SUB SRLI LD SD);
    - storeWord/loadWord state projections, per-byte reads, the frame
      lemma, and the 8-digit reassembly [loadWord_storeWord];
    - the wsub/wshr arithmetic bridges.
    The generic toolkit (state projections, wrap_small/wadd_id/toS_small/
    sltb_small, runUntil composition incl. runUntil_stab) is REUSED from
    the hex0 port (Hex0Coq.Refine) -- those lemmas are Image-independent. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
From Hex0Coq Require Import Spec Spec1 Rv64i Harness Harness1 Refine.
From Hex0Coq Require Image1.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Engine: fetch at a code offset + per-instruction step lemmas
    (Image1 versions; mirror of lean/Hex1/RefineBase.lean). *)

Definition nthb1 (i : Z) : Z := nth (Z.to_nat i) Image1.coreBytes 0.

Definition wordAt1 (off : Z) : Z :=
  nthb1 off + nthb1 (off + 1) * 256 + nthb1 (off + 2) * 65536 + nthb1 (off + 3) * 16777216.

Definition CodeLoaded1 (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length Image1.coreBytes) ->
    s.(mem) (Image1.coreAddr + i) = nthb1 i.

Lemma coreBytes1_len : Z.of_nat (length Image1.coreBytes) = 724.
Proof. reflexivity. Qed.
Lemma coreAddr1_pos k : 0 <= k -> Image1.coreAddr + k <> 0.
Proof. unfold Image1.coreAddr; lia. Qed.
Lemma CodeLoaded1_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded1 s -> CodeLoaded1 t.
Proof. intros He H i Hi. rewrite He. exact (H i Hi). Qed.

Lemma fetch_code1 : forall s off,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> fetch32 s = wordAt1 off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt1. rewrite hpc.
  replace (Image1.coreAddr + off + 1) with (Image1.coreAddr + (off + 1)) by lia.
  replace (Image1.coreAddr + off + 2) with (Image1.coreAddr + (off + 2)) by lia.
  replace (Image1.coreAddr + off + 3) with (Image1.coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

(* the 16 per-instruction step lemmas, all the same one-line proof *)
Lemma step1_addi : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_add : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sub : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isub rd rs1 rs2 ->
  step s = setPc (rset s rd (wsub (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_or : forall s off rd rs1 rs2,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_slli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_srli : forall s off rd rs1 sh,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isrli rd rs1 sh ->
  step s = setPc (rset s rd (wshr (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_lbu : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_ld : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ild rd rs1 imm ->
  step s = setPc (rset s rd (loadWord s (wadd (rget s rs1) imm))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sb : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_sd : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Isd rs1 rs2 imm ->
  step s = setPc (storeWord s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_beq : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_blt : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bge : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jal : forall s off rd imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step1_jalr : forall s off rd rs1 imm,
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off -> decode (wordAt1 off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code1 s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(** ** storeWord / loadWord state lemmas (mirror of RefineBase.lean's
    storeWord_pc/rget/frame/get0..7 + assemble_bytes; addresses are [Z],
    so distinctness is just [lia]). *)

Lemma storeWord_pc s a v : (storeWord s a v).(pc) = s.(pc).
Proof. reflexivity. Qed.
Lemma storeWord_reg s a v : (storeWord s a v).(reg) = s.(reg).
Proof. reflexivity. Qed.
Lemma storeWord_rget s a v i : rget (storeWord s a v) i = rget s i.
Proof. reflexivity. Qed.

(* the full byte map of an 8-byte store (outermost test = last store, a+7) *)
Lemma storeWord_mem_at : forall s a v x,
  (storeWord s a v).(mem) x =
  (if x =? a + 7 then (v / 2 ^ 56) mod 256
   else if x =? a + 6 then (v / 2 ^ 48) mod 256
   else if x =? a + 5 then (v / 2 ^ 40) mod 256
   else if x =? a + 4 then (v / 2 ^ 32) mod 256
   else if x =? a + 3 then (v / 2 ^ 24) mod 256
   else if x =? a + 2 then (v / 2 ^ 16) mod 256
   else if x =? a + 1 then (v / 2 ^ 8) mod 256
   else if x =? a then v mod 256
   else s.(mem) x).
Proof. reflexivity. Qed.

(* reading outside the 8 stored bytes is unchanged *)
Lemma storeWord_frame : forall s a v x,
  (forall k, 0 <= k < 8 -> x <> a + k) ->
  (storeWord s a v).(mem) x = s.(mem) x.
Proof.
  intros s a v x h. rewrite storeWord_mem_at.
  pose proof (h 0 ltac:(lia)). pose proof (h 1 ltac:(lia)).
  pose proof (h 2 ltac:(lia)). pose proof (h 3 ltac:(lia)).
  pose proof (h 4 ltac:(lia)). pose proof (h 5 ltac:(lia)).
  pose proof (h 6 ltac:(lia)). pose proof (h 7 ltac:(lia)).
  repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia). reflexivity.
Qed.

(* per-byte reads of the stored word: byte k of [storeWord s a v] at a+k *)
Lemma storeWord_get : forall s a v k, 0 <= k < 8 ->
  (storeWord s a v).(mem) (a + k) = (v / 2 ^ (8 * k)) mod 256.
Proof.
  intros s a v k hk.
  assert (hk8 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct hk8 as [->| [->| [->| [->| [->| [->| [->| ->]]]]]]];
    [ replace (a + 0) with a by lia | | | | | | | ];
    rewrite storeWord_mem_at;
    repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia);
    rewrite Z.eqb_refl;
    try reflexivity.
  (* k = 0: 8*0 = 0; v / 2^0 = v *)
  now rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
Qed.

(* the base-256 digit reassembly: loadWord after storeWord at the same
   address returns the stored (in-range) value (Lean's assemble_bytes). *)
Lemma digits8 : forall v, 0 <= v < 2 ^ 64 ->
  v mod 256
  + (v / 2 ^ 8) mod 256 * 2 ^ 8
  + (v / 2 ^ 16) mod 256 * 2 ^ 16
  + (v / 2 ^ 24) mod 256 * 2 ^ 24
  + (v / 2 ^ 32) mod 256 * 2 ^ 32
  + (v / 2 ^ 40) mod 256 * 2 ^ 40
  + (v / 2 ^ 48) mod 256 * 2 ^ 48
  + (v / 2 ^ 56) mod 256 * 2 ^ 56 = v.
Proof.
  intros v hv.
  replace (v / 2 ^ 16) with (v / 2 ^ 8 / 2 ^ 8) by (rewrite Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 24) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 32) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 40) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 48) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (v / 2 ^ 56) with (v / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8 / 2 ^ 8)
    by (rewrite !Z.div_div by lia; reflexivity).
  set (x1 := v / 2 ^ 8). set (x2 := x1 / 2 ^ 8). set (x3 := x2 / 2 ^ 8).
  set (x4 := x3 / 2 ^ 8). set (x5 := x4 / 2 ^ 8). set (x6 := x5 / 2 ^ 8).
  set (x7 := x6 / 2 ^ 8).
  pose proof (Z.div_mod v (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.div_mod x6 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x1 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x2 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x3 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x4 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x5 (2 ^ 8) ltac:(lia)).
  pose proof (Z.mod_pos_bound x6 (2 ^ 8) ltac:(lia)).
  assert (hx7 : x7 = v / 2 ^ 56).
  { unfold x7, x6, x5, x4, x3, x2, x1. rewrite !Z.div_div by lia. reflexivity. }
  assert (hx7b : 0 <= x7 < 2 ^ 8).
  { rewrite hx7. split.
    - apply Z.div_pos; lia.
    - apply Z.div_lt_upper_bound; lia. }
  assert (hx7m : x7 mod 256 = x7) by (apply Z.mod_small; lia).
  rewrite hx7m.
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216. change (2 ^ 32) with 4294967296.
  change (2 ^ 40) with 1099511627776. change (2 ^ 48) with 281474976710656.
  change (2 ^ 56) with 72057594037927936.
  lia.
Qed.

Lemma loadWord_storeWord : forall s a v, 0 <= v < 2 ^ 64 ->
  loadWord (storeWord s a v) a = v.
Proof.
  intros s a v hv. unfold loadWord.
  pose proof (storeWord_get s a v 0 ltac:(lia)) as G0.
  replace (a + 0) with a in G0 by lia.
  pose proof (storeWord_get s a v 1 ltac:(lia)) as G1.
  pose proof (storeWord_get s a v 2 ltac:(lia)) as G2.
  pose proof (storeWord_get s a v 3 ltac:(lia)) as G3.
  pose proof (storeWord_get s a v 4 ltac:(lia)) as G4.
  pose proof (storeWord_get s a v 5 ltac:(lia)) as G5.
  pose proof (storeWord_get s a v 6 ltac:(lia)) as G6.
  pose proof (storeWord_get s a v 7 ltac:(lia)) as G7.
  rewrite G0, G1, G2, G3, G4, G5, G6, G7.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16.
  change (8 * 3) with 24. change (8 * 4) with 32. change (8 * 5) with 40.
  change (8 * 6) with 48. change (8 * 7) with 56.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply digits8. exact hv.
Qed.

(** ** Arithmetic bridges for the new instructions. *)

(* sub with no underflow: the Z value *)
Lemma wsub_id a b : 0 <= a - b < 2 ^ 64 -> wsub a b = a - b.
Proof. unfold wsub. apply wrap_small. Qed.

(* logical shift right = division by 2^n *)
Lemma wshr_div a n : 0 <= n -> wshr a n = a / 2 ^ n.
Proof. intros hn. unfold wshr. apply Z.shiftr_div_pow2. exact hn. Qed.

(** ** Reusable [li t3,K; branch t2,t3] blocks (ports of the hex0 Coq ones,
    under [CodeLoaded1]). Each runs 2 steps, resolving the branch; clobbers
    only t3 (x28) and pc. *)

Lemma li1_beq_ne s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c <> K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbeq hK hne.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with false by (symmetry; apply Z.eqb_neq; exact hne).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_beq_eq s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c = K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbeq hK heq htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with true by (symmetry; apply Z.eqb_eq; exact heq).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_blt_nt s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  ~ c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hblt hK hc63 hge.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hblt), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_blt_t s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  c < K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hblt hK hc63 hlt htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hblt), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_bge_nt s off K c imm :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (Image1.coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbge hK hc63 hlt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 (Image1.coreAddr + (off + 8))).
  { rewrite (step1_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbge), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite hpc1, (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

Lemma li1_bge_t s off K c imm target :
  CodeLoaded1 s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt1 off) = Iaddi 28 0 K ->
  decode (wordAt1 (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 ->
  ~ c < K ->
  wadd (Image1.coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbge hK hc63 hge htgt.
  rewrite coreBytes1_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length Image1.coreBytes)) by (rewrite coreBytes1_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 7 ltac:(lia) ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget;
    rewrite (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)); reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step1_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hbge), h7s1, h28s1.
    rewrite (sltb_small c K ltac:(lia) ltac:(lia)).
    replace (c <? K) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(** ** Well-formedness: the four regions, in address order
    code [coreAddr,+724) < input [inputAddr,+len) <= out [outAddr,+cap)
    <= lbl [lblAddr,+2048), with everything below 2^63 (signed compares on
    table addresses; label positions sign-tested in slots). *)

Record WellFormed1 (inp : list Z) (cap : Z) : Prop := {
  cap_nonneg : 0 <= cap;
  in_fits1   : Image1.inputAddr + Z.of_nat (length inp) <= Image1.outAddr;
  out_fits1  : Image1.outAddr + cap <= Image1.lblAddr;
  lbl_fits1  : Image1.lblAddr + 2048 < 2 ^ 63;
  bytes_ok1  : forall b, In b inp -> 0 <= b < 256
}.

(* cap sits below 2^63 (the out region is below the lbl region) *)
Lemma WellFormed1_cap63 inp cap : WellFormed1 inp cap -> cap < 2 ^ 63.
Proof.
  intros [Hc H1 H2 H3 H4]. unfold Image1.outAddr, Image1.lblAddr in *. lia.
Qed.

(** ** The label table encoding: undefined slot = all-ones (-1 as i64),
    defined slot = the position (< 2^63, so the sign distinguishes them). *)

Definition encodeSlot (o : option nat) : Z :=
  match o with
  | None => 2 ^ 64 - 1
  | Some p => Z.of_nat p
  end.

(* the table region holds [lab]: slot c at lblAddr + 8c, little-endian *)
Definition TableLoaded (s : State) (lab : Labels) : Prop :=
  forall c, (c < 256)%nat -> forall k, 0 <= k < 8 ->
    s.(mem) (Image1.lblAddr + 8 * Z.of_nat c + k)
      = (encodeSlot (lab c) / 2 ^ (8 * k)) mod 256.

Lemma encodeSlot_range : forall o,
  (forall p, o = Some p -> Z.of_nat p < 2 ^ 63) ->
  0 <= encodeSlot o < 2 ^ 64.
Proof.
  intros o hb. destruct o as [p|]; cbn.
  - pose proof (hb p eq_refl). lia.
  - lia.
Qed.

(* the sign test [bge slot,x0]: an undefined slot is negative ... *)
Lemma encodeSlot_none_neg : sltb (encodeSlot None) 0 = true.
Proof. reflexivity. Qed.

(* ... and a defined slot (position < 2^63) is non-negative. *)
Lemma encodeSlot_some_nonneg p : Z.of_nat p < 2 ^ 63 ->
  sltb (encodeSlot (Some p)) 0 = false.
Proof.
  intros hp. cbn.
  rewrite (sltb_small (Z.of_nat p) 0 ltac:(lia) ltac:(lia)).
  apply Z.ltb_ge. lia.
Qed.

(** ** Slot addressing and table access. *)

(* slli t3,t2,3 on a byte value: the slot offset 8c *)
Lemma wshl3 c : 0 <= c < 256 -> wshl c 3 = 8 * c.
Proof.
  intros hc. unfold wshl. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite wrap_small; change (2 ^ 3) with 8; lia.
Qed.

(* ld t4,0(t3) at slot c reads the encoded slot *)
Lemma loadWord_slot s lab c :
  TableLoaded s lab -> (c < 256)%nat ->
  0 <= encodeSlot (lab c) < 2 ^ 64 ->
  loadWord s (Image1.lblAddr + 8 * Z.of_nat c) = encodeSlot (lab c).
Proof.
  intros ht hc hv. unfold loadWord.
  pose proof (ht c hc 0 ltac:(lia)) as T0.
  pose proof (ht c hc 1 ltac:(lia)) as T1.
  pose proof (ht c hc 2 ltac:(lia)) as T2.
  pose proof (ht c hc 3 ltac:(lia)) as T3.
  pose proof (ht c hc 4 ltac:(lia)) as T4.
  pose proof (ht c hc 5 ltac:(lia)) as T5.
  pose proof (ht c hc 6 ltac:(lia)) as T6.
  pose proof (ht c hc 7 ltac:(lia)) as T7.
  replace (Image1.lblAddr + 8 * Z.of_nat c + 0)
    with (Image1.lblAddr + 8 * Z.of_nat c) in T0 by lia.
  rewrite T0, T1, T2, T3, T4, T5, T6, T7.
  change (8 * 0) with 0. change (8 * 1) with 8. change (8 * 2) with 16.
  change (8 * 3) with 24. change (8 * 4) with 32. change (8 * 5) with 40.
  change (8 * 6) with 48. change (8 * 7) with 56.
  rewrite Z.pow_0_r, Z.div_1_r.
  apply digits8. exact hv.
Qed.

(* sd t1,0(t3) at slot c installs [setLabel lab c pos] *)
Lemma storeWord_slot s lab c pos :
  TableLoaded s lab -> (c < 256)%nat ->
  TableLoaded (storeWord s (Image1.lblAddr + 8 * Z.of_nat c) (Z.of_nat pos))
              (setLabel lab c pos).
Proof.
  intros ht hc c' hc' k hk.
  unfold setLabel.
  destruct (Nat.eqb_spec c' c) as [->|hne].
  - (* the written slot: read back the stored bytes *)
    replace (Image1.lblAddr + 8 * Z.of_nat c + k)
      with ((Image1.lblAddr + 8 * Z.of_nat c) + k) by lia.
    rewrite (storeWord_get _ _ _ k hk). reflexivity.
  - (* another slot: untouched (the 8 written bytes are in slot c) *)
    rewrite storeWord_frame.
    + exact (ht c' hc' k hk).
    + intros k' hk' heq.
      assert (Z.of_nat c' <> Z.of_nat c) by lia.
      lia.
Qed.

(* a byte store OUTSIDE the table region preserves TableLoaded *)
Lemma tableLoaded_storeByte s lab a b :
  TableLoaded s lab ->
  (a < Image1.lblAddr \/ Image1.lblAddr + 2048 <= a) ->
  TableLoaded (storeByte s a b) lab.
Proof.
  intros ht hout c hc k hk.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.lblAddr + 8 * Z.of_nat c + k =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  exact (ht c hc k hk).
Qed.

(* memory-equality transport (setPc/rset chains) *)
Lemma tableLoaded_eqmem s t lab :
  t.(mem) = s.(mem) -> TableLoaded s lab -> TableLoaded t lab.
Proof. intros He H c hc k hk. rewrite He. exact (H c hc k hk). Qed.

(** ** Region predicates and their preservation lemmas. *)

Definition InputLoaded (s : State) (inp : list Z) : Prop :=
  forall j, 0 <= j < Z.of_nat (length inp) ->
    s.(mem) (Image1.inputAddr + j) = nth (Z.to_nat j) inp 0.

Lemma inputLoaded_eqmem s t inp :
  t.(mem) = s.(mem) -> InputLoaded s inp -> InputLoaded t inp.
Proof. intros He H j Hj. rewrite He. exact (H j Hj). Qed.

(* byte stores outside the code / input regions preserve them *)
Lemma codeLoaded1_storeByte s a b :
  CodeLoaded1 s ->
  (a < Image1.coreAddr \/ Image1.coreAddr + 724 <= a) ->
  CodeLoaded1 (storeByte s a b).
Proof.
  intros hc hout i hi. rewrite coreBytes1_len in hi.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.coreAddr + i =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  apply hc. rewrite coreBytes1_len. exact hi.
Qed.

Lemma inputLoaded_storeByte s a b inp :
  InputLoaded s inp ->
  (a < Image1.inputAddr \/ Image1.inputAddr + Z.of_nat (length inp) <= a) ->
  InputLoaded (storeByte s a b) inp.
Proof.
  intros hin hout j hj.
  rewrite storeByte_mem. cbv beta.
  replace (Image1.inputAddr + j =? a) with false
    by (symmetry; apply Z.eqb_neq; lia).
  exact (hin j hj).
Qed.

(* word stores outside the code / input regions preserve them *)
Lemma codeLoaded1_storeWord s a v :
  CodeLoaded1 s ->
  (a + 8 <= Image1.coreAddr \/ Image1.coreAddr + 724 <= a) ->
  CodeLoaded1 (storeWord s a v).
Proof.
  intros hc hout i hi. rewrite coreBytes1_len in hi.
  rewrite storeWord_frame by (intros k hk; lia).
  apply hc. rewrite coreBytes1_len. exact hi.
Qed.

Lemma inputLoaded_storeWord s a v inp :
  InputLoaded s inp ->
  (a + 8 <= Image1.inputAddr \/ Image1.inputAddr + Z.of_nat (length inp) <= a) ->
  InputLoaded (storeWord s a v) inp.
Proof.
  intros hin hout j hj.
  rewrite storeWord_frame by (intros k hk; lia).
  exact (hin j hj).
Qed.

(* a word store inside the table region also preserves code/input (the
   regions are in address order; geometry from WellFormed1) *)

(** ** The init loop: 256 iterations of [sd; addi; blt] filling the table
    with -1. Offsets: entry 0..12, loop body 16/20/24, exit -> 28.
    Decodes: 0: addi t3,a4,0 | 4: addi t4,a4,2047 | 8: addi t4,t4,1 |
    12: addi t5,x0,-1 | 16: sd t5,0(t3) | 20: addi t3,t3,8 |
    24: blt t3,t4,-8 | 28/32: li t0,0; li t1,0 | 36: bgeu t0,a1,+324. *)

Record InitInv (inp : list Z) (cap : Z) (s : State) (j : Z) : Prop := {
  ii_pc   : s.(pc) = Image1.coreAddr + 16;
  ii_code : CodeLoaded1 s;
  ii_a0   : rget s 10 = Image1.inputAddr;
  ii_a1   : rget s 11 = Z.of_nat (length inp);
  ii_a2   : rget s 12 = Image1.outAddr;
  ii_a3   : rget s 13 = cap;
  ii_a4   : rget s 14 = Image1.lblAddr;
  ii_ra   : rget s 1 = 0;
  ii_t3   : rget s 28 = Image1.lblAddr + 8 * j;
  ii_t4   : rget s 29 = Image1.lblAddr + 2048;
  ii_t5   : rget s 30 = 2 ^ 64 - 1;
  ii_in   : InputLoaded s inp;
  ii_tbl  : forall b, 0 <= b < 8 * j -> s.(mem) (Image1.lblAddr + b) = 255
}.

(* state shape on arrival at pass 1 (offset 28): table fully initialized *)
Record Pass1Entry (inp : list Z) (cap : Z) (s : State) : Prop := {
  pe_pc   : s.(pc) = Image1.coreAddr + 28;
  pe_code : CodeLoaded1 s;
  pe_a0   : rget s 10 = Image1.inputAddr;
  pe_a1   : rget s 11 = Z.of_nat (length inp);
  pe_a2   : rget s 12 = Image1.outAddr;
  pe_a3   : rget s 13 = cap;
  pe_a4   : rget s 14 = Image1.lblAddr;
  pe_ra   : rget s 1 = 0;
  pe_in   : InputLoaded s inp;
  pe_tbl  : TableLoaded s noLabels
}.

(* One init iteration (offsets 16,20,24): writes slot j, bumps the pointer,
   loops back while j+1 < 256 (else falls through to 28). *)
Lemma init_iter : forall inp cap s j,
  InitInv inp cap s j -> 0 <= j < 256 -> WellFormed1 inp cap ->
  exists s', runUntil 0 3 s = s' /\
    (if j + 1 <? 256 then InitInv inp cap s' (j + 1) else Pass1Entry inp cap s').
Proof.
  intros inp cap s j inv hj hwf.
  destruct inv as [hpc hcode ha0 ha1 ha2 ha3 ha4 hra ht3 ht4 ht5 hinm htbl].
  pose proof (in_fits1 _ _ hwf) as hin. pose proof (out_fits1 _ _ hwf) as hout.
  pose proof (lbl_fits1 _ _ hwf) as hlbl. pose proof (cap_nonneg _ _ hwf) as hcap.
  unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
  (* step 1 (off 16): sd t5,0(t3) *)
  assert (hu1 : step s = setPc (storeWord s (2147489280 + 8 * j) (2 ^ 64 - 1))
                               (2147483792 + 20)).
  { rewrite (step1_sd s 16 28 30 0 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
              hpc ltac:(vm_compute; reflexivity)).
    rewrite ht3, ht5, (wadd_id (2147489280 + 8 * j) 0 ltac:(lia)), Z.add_0_r, hpc,
            (wadd_id (2147483792 + 16) 4 ltac:(lia)).
    f_equal; lia. }
  set (s1 := setPc (storeWord s (2147489280 + 8 * j) (2 ^ 64 - 1)) (2147483792 + 20)) in *.
  assert (hpc1 : s1.(pc) = 2147483792 + 20) by reflexivity.
  assert (hmem1 : s1.(mem) = (storeWord s (2147489280 + 8 * j) (2 ^ 64 - 1)).(mem))
    by reflexivity.
  assert (hr1 : forall i, rget s1 i = rget s i)
    by (intro i; unfold s1; rewrite setPc_rget, storeWord_rget; reflexivity).
  (* table prefix extended to 8(j+1) *)
  assert (htbl1 : forall b, 0 <= b < 8 * (j + 1) -> s1.(mem) (2147489280 + b) = 255).
  { intros b hb. rewrite hmem1.
    destruct (Z.lt_ge_cases b (8 * j)) as [hbj|hbj].
    - rewrite storeWord_frame by (intros k hk; lia).
      exact (htbl b ltac:(lia)).
    - replace (2147489280 + b) with ((2147489280 + 8 * j) + (b - 8 * j)) by lia.
      rewrite (storeWord_get _ _ _ (b - 8 * j) ltac:(lia)).
      assert (h8 : b - 8 * j = 0 \/ b - 8 * j = 1 \/ b - 8 * j = 2 \/ b - 8 * j = 3
                \/ b - 8 * j = 4 \/ b - 8 * j = 5 \/ b - 8 * j = 6 \/ b - 8 * j = 7) by lia.
      destruct h8 as [->| [->| [->| [->| [->| [->| [->| ->]]]]]]]; vm_compute; reflexivity. }
  assert (hcode1 : CodeLoaded1 s1).
  { apply (CodeLoaded1_eqmem (storeWord s (2147489280 + 8 * j) (2 ^ 64 - 1))).
    - exact hmem1.
    - apply codeLoaded1_storeWord; [exact hcode|].
      unfold Image1.coreAddr; lia. }
  assert (hin1 : InputLoaded s1 inp).
  { apply (inputLoaded_eqmem (storeWord s (2147489280 + 8 * j) (2 ^ 64 - 1))).
    - exact hmem1.
    - apply inputLoaded_storeWord; [exact hinm|].
      unfold Image1.inputAddr; lia. }
  (* step 2 (off 20): addi t3,t3,8 *)
  assert (hu2 : step s1 = setPc (rset s1 28 (2147489280 + 8 * (j + 1))) (2147483792 + 24)).
  { rewrite (step1_addi s1 20 28 28 8 hcode1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 ltac:(vm_compute; reflexivity)).
    rewrite (hr1 28), ht3, (wadd_id (2147489280 + 8 * j) 8 ltac:(lia)), hpc1,
            (wadd_id (2147483792 + 20) 4 ltac:(lia)).
    f_equal; try f_equal; lia. }
  set (s2 := setPc (rset s1 28 (2147489280 + 8 * (j + 1))) (2147483792 + 24)) in *.
  assert (hpc2 : s2.(pc) = 2147483792 + 24) by reflexivity.
  assert (hmem2 : s2.(mem) = s1.(mem))
    by (unfold s2; rewrite setPc_mem, rset_mem; reflexivity).
  assert (hcode2 : CodeLoaded1 s2) by (apply (CodeLoaded1_eqmem s1); assumption).
  assert (hr2 : forall i, i <> 28 -> rget s2 i = rget s1 i)
    by (intros i hi; unfold s2; apply li_block_frame; exact hi).
  assert (hr2_28 : rget s2 28 = 2147489280 + 8 * (j + 1)).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)).
    rewrite Z.eqb_refl. reflexivity. }
  (* step 3 (off 24): blt t3,t4,-8 *)
  assert (hr29 : rget s2 29 = 2147489280 + 2048)
    by (rewrite (hr2 29 ltac:(lia)), (hr1 29); exact ht4).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hstep3 : step s2 = setPc s2
            (if sltb (2147489280 + 8 * (j + 1)) (2147489280 + 2048)
             then wadd s2.(pc) (-8) else wadd s2.(pc) 4)).
  { rewrite (step1_blt s2 24 28 29 (-8) hcode2 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc2 ltac:(vm_compute; reflexivity)).
    rewrite hr2_28, hr29. reflexivity. }
  rewrite (sltb_small (2147489280 + 8 * (j + 1)) (2147489280 + 2048)
            ltac:(lia) ltac:(lia)) in hstep3.
  destruct (Z.ltb_spec (j + 1) 256) as [hlt|hge].
  - (* branch TAKEN: back to offset 16, invariant advances *)
    replace (2147489280 + 8 * (j + 1) <? 2147489280 + 2048) with true in hstep3
      by (symmetry; apply Z.ltb_lt; lia).
    assert (hu3 : step s2 = setPc s2 (2147483792 + 16)).
    { rewrite hstep3, hpc2, (wadd_id (2147483792 + 24) (-8) ltac:(lia)). f_equal; lia. }
    exists (setPc s2 (2147483792 + 16)). split.
    { rewrite (runUntil_S 2 s hp0), hu1,
              (runUntil_S 1 s1 hp1), hu2,
              (runUntil_S 0 s2 hp2), hu3. reflexivity. }
    assert (hrS : forall i, i <> 28 -> rget (setPc s2 (2147483792 + 16)) i = rget s i)
      by (intros i hi; rewrite setPc_rget, (hr2 i hi), (hr1 i); reflexivity).
    refine {| ii_pc := _; ii_code := _; ii_a0 := _; ii_a1 := _; ii_a2 := _;
              ii_a3 := _; ii_a4 := _; ii_ra := _; ii_t3 := _; ii_t4 := _;
              ii_t5 := _; ii_in := _; ii_tbl := _ |}.
    + reflexivity.
    + apply (CodeLoaded1_eqmem s2); [reflexivity| exact hcode2].
    + rewrite (hrS 10 ltac:(lia)); exact ha0.
    + rewrite (hrS 11 ltac:(lia)); exact ha1.
    + rewrite (hrS 12 ltac:(lia)); exact ha2.
    + rewrite (hrS 13 ltac:(lia)); exact ha3.
    + rewrite (hrS 14 ltac:(lia)); exact ha4.
    + rewrite (hrS 1 ltac:(lia)); exact hra.
    + rewrite setPc_rget; exact hr2_28.
    + rewrite setPc_rget; exact hr29.
    + rewrite (hrS 30 ltac:(lia)); exact ht5.
    + apply (inputLoaded_eqmem s1); [| exact hin1].
      rewrite <- hmem2; reflexivity.
    + intros b hb. change ((setPc s2 (2147483792+16)).(mem)) with s2.(mem).
      rewrite hmem2. exact (htbl1 b hb).
  - (* branch NOT taken: fall through to offset 28 (pass 1 entry) *)
    replace (2147489280 + 8 * (j + 1) <? 2147489280 + 2048) with false in hstep3
      by (symmetry; apply Z.ltb_ge; lia).
    assert (hu3 : step s2 = setPc s2 (2147483792 + 28)).
    { rewrite hstep3, hpc2, (wadd_id (2147483792 + 24) 4 ltac:(lia)). f_equal; lia. }
    exists (setPc s2 (2147483792 + 28)). split.
    { rewrite (runUntil_S 2 s hp0), hu1,
              (runUntil_S 1 s1 hp1), hu2,
              (runUntil_S 0 s2 hp2), hu3. reflexivity. }
    assert (hj1 : j + 1 = 256) by lia.
    assert (hrS : forall i, i <> 28 -> rget (setPc s2 (2147483792 + 28)) i = rget s i)
      by (intros i hi; rewrite setPc_rget, (hr2 i hi), (hr1 i); reflexivity).
    refine {| pe_pc := _; pe_code := _; pe_a0 := _; pe_a1 := _; pe_a2 := _;
              pe_a3 := _; pe_a4 := _; pe_ra := _; pe_in := _; pe_tbl := _ |}.
    + reflexivity.
    + apply (CodeLoaded1_eqmem s2); [reflexivity| exact hcode2].
    + rewrite (hrS 10 ltac:(lia)); exact ha0.
    + rewrite (hrS 11 ltac:(lia)); exact ha1.
    + rewrite (hrS 12 ltac:(lia)); exact ha2.
    + rewrite (hrS 13 ltac:(lia)); exact ha3.
    + rewrite (hrS 14 ltac:(lia)); exact ha4.
    + rewrite (hrS 1 ltac:(lia)); exact hra.
    + apply (inputLoaded_eqmem s1); [| exact hin1].
      rewrite <- hmem2; reflexivity.
    + (* table fully cleared = TableLoaded noLabels (every byte 255) *)
      intros c hc k hk.
      change ((setPc s2 (2147483792+28)).(mem)) with s2.(mem).
      rewrite hmem2.
      unfold Image1.lblAddr.
      replace (2147489280 + 8 * Z.of_nat c + k) with (2147489280 + (8 * Z.of_nat c + k))
        by lia.
      rewrite (htbl1 (8 * Z.of_nat c + k) ltac:(lia)).
      (* encodeSlot None = 2^64-1: every byte is 255 *)
      unfold noLabels. cbn [encodeSlot].
      assert (h8 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)
        by lia.
      destruct h8 as [->| [->| [->| [->| [->| [->| [->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* the init loop runs to completion: 3*(256-j) steps to pass-1 entry *)
Lemma init_loop : forall inp cap n (s : State) (j : Z),
  Z.of_nat n = 256 - j -> 0 <= j < 256 ->
  InitInv inp cap s j -> WellFormed1 inp cap ->
  exists s', runUntil 0 (3 * n) s = s' /\ Pass1Entry inp cap s'.
Proof.
  intros inp cap n. induction n as [|n ih]; intros s j hn hj inv hwf.
  - exfalso. rewrite Nat2Z.inj_0 in hn. lia.
  - destruct (init_iter inp cap s j inv hj hwf) as (s' & hrun & hpost).
    destruct (Z.ltb_spec (j + 1) 256) as [hlt|hge].
    + (* more iterations *)
      destruct (ih s' (j + 1) ltac:(lia) ltac:(lia) hpost hwf) as (s'' & hrun2 & hp2).
      exists s''. split; [| exact hp2].
      replace (3 * S n)%nat with (3 + 3 * n)%nat by lia.
      rewrite (runUntil_add 3 (3 * n) s), hrun, hrun2. reflexivity.
    + (* last iteration: n = 0 *)
      assert (hn0 : n = 0%nat) by lia.
      subst n. exists s'. split; [| exact hpost].
      replace (3 * 1)%nat with 3%nat by lia.
      exact hrun.
Qed.

(** ** Prologue: from the initial state through the entry block (offsets
    0/4/8/12) into the init loop, and the whole init phase (772 steps). *)

Lemma code_initOn1 : forall inp cap,
  CodeLoaded1 (mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr)).
Proof.
  intros inp cap i Hi. rewrite coreBytes1_len in Hi.
  cbn [mkInit1 Rv64i.mem]. unfold memWith1.
  replace ((Image1.coreAddr <=? Image1.coreAddr + i)
           && (Image1.coreAddr + i <? Image1.coreAddr + Z.of_nat (length Image1.coreBytes)))
    with true
    by (symmetry; apply andb_true_iff; split;
        [apply Z.leb_le; lia | apply Z.ltb_lt; rewrite coreBytes1_len; lia]).
  cbv iota. replace (Image1.coreAddr + i - Image1.coreAddr) with i by lia.
  unfold nthb1. reflexivity.
Qed.

Lemma in_initOn1 : forall inp cap, WellFormed1 inp cap ->
  InputLoaded (mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr)) inp.
Proof.
  intros inp cap hwf j Hj.
  pose proof (in_fits1 _ _ hwf) as hin.
  cbn [mkInit1 Rv64i.mem]. unfold memWith1.
  replace ((Image1.coreAddr <=? Image1.inputAddr + j)
           && (Image1.inputAddr + j <? Image1.coreAddr + Z.of_nat (length Image1.coreBytes)))
    with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge;
        rewrite coreBytes1_len; unfold Image1.coreAddr, Image1.inputAddr; lia).
  cbv iota.
  replace ((Image1.inputAddr <=? Image1.inputAddr + j)
           && (Image1.inputAddr + j <? Image1.inputAddr + Z.of_nat (length inp)))
    with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
  cbv iota. replace (Image1.inputAddr + j - Image1.inputAddr) with j by lia. reflexivity.
Qed.

(* the entry block: 4 steps (addi t3,a4,0; addi t4,a4,2047; addi t4,t4,1;
   addi t5,x0,-1) from the initial state reach the init-loop head with
   InitInv 0. *)
Lemma entry_block : forall inp cap, WellFormed1 inp cap ->
  exists s', runUntil 0 4 (mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr)) = s'
          /\ InitInv inp cap s' 0.
Proof.
  intros inp cap hwf.
  pose proof (lbl_fits1 _ _ hwf) as hlbl.
  set (s0 := mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr)).
  assert (hpc0 : s0.(pc) = Image1.coreAddr + 0) by (cbn; lia).
  assert (hcode0 : CodeLoaded1 s0) by (apply code_initOn1).
  assert (h14 : rget s0 14 = Image1.lblAddr) by reflexivity.
  unfold Image1.coreAddr, Image1.lblAddr in *.
  (* step 1 (off 0): addi t3,a4,0 *)
  assert (hu1 : step s0 = setPc (rset s0 28 2147489280) (2147483792 + 4)).
  { rewrite (step1_addi s0 0 28 14 0 hcode0 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc0 ltac:(vm_compute; reflexivity)).
    rewrite h14, (wadd_id 2147489280 0 ltac:(lia)), Z.add_0_r, hpc0,
            (wadd_id (2147483792 + 0) 4 ltac:(lia)).
    f_equal; lia. }
  set (s1 := setPc (rset s0 28 2147489280) (2147483792 + 4)) in *.
  assert (hpc1 : s1.(pc) = 2147483792 + 4) by reflexivity.
  assert (hcode1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s0); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode0]).
  assert (hr1 : forall i, i <> 28 -> rget s1 i = rget s0 i)
    by (intros i hi; unfold s1; apply li_block_frame; exact hi).
  (* step 2 (off 4): addi t4,a4,2047 *)
  assert (hu2 : step s1 = setPc (rset s1 29 (2147489280 + 2047)) (2147483792 + 8)).
  { rewrite (step1_addi s1 4 29 14 2047 hcode1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 ltac:(vm_compute; reflexivity)).
    rewrite (hr1 14 ltac:(lia)), h14, (wadd_id 2147489280 2047 ltac:(lia)), hpc1,
            (wadd_id (2147483792 + 4) 4 ltac:(lia)).
    f_equal; lia. }
  set (s2 := setPc (rset s1 29 (2147489280 + 2047)) (2147483792 + 8)) in *.
  assert (hpc2 : s2.(pc) = 2147483792 + 8) by reflexivity.
  assert (hcode2 : CodeLoaded1 s2)
    by (apply (CodeLoaded1_eqmem s1); [unfold s2; rewrite setPc_mem, rset_mem; reflexivity| exact hcode1]).
  assert (hr2 : forall i, i <> 29 -> rget s2 i = rget s1 i).
  { intros i hi. unfold s2. rewrite setPc_rget.
    destruct (Z.eqb_spec i 0) as [->|h0]; [reflexivity|].
    rewrite (rset_rget s1 29 _ i ltac:(lia) h0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi). reflexivity. }
  assert (hr2_29 : rget s2 29 = 2147489280 + 2047).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 29 _ 29 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity. }
  (* step 3 (off 8): addi t4,t4,1 *)
  assert (hu3 : step s2 = setPc (rset s2 29 (2147489280 + 2048)) (2147483792 + 12)).
  { rewrite (step1_addi s2 8 29 29 1 hcode2 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc2 ltac:(vm_compute; reflexivity)).
    rewrite hr2_29, (wadd_id (2147489280 + 2047) 1 ltac:(lia)), hpc2,
            (wadd_id (2147483792 + 8) 4 ltac:(lia)).
    f_equal; try f_equal; lia. }
  set (s3 := setPc (rset s2 29 (2147489280 + 2048)) (2147483792 + 12)) in *.
  assert (hpc3 : s3.(pc) = 2147483792 + 12) by reflexivity.
  assert (hcode3 : CodeLoaded1 s3)
    by (apply (CodeLoaded1_eqmem s2); [unfold s3; rewrite setPc_mem, rset_mem; reflexivity| exact hcode2]).
  assert (hr3 : forall i, i <> 29 -> rget s3 i = rget s2 i).
  { intros i hi. unfold s3. rewrite setPc_rget.
    destruct (Z.eqb_spec i 0) as [->|h0]; [reflexivity|].
    rewrite (rset_rget s2 29 _ i ltac:(lia) h0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi). reflexivity. }
  assert (hr3_29 : rget s3 29 = 2147489280 + 2048).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 29 _ 29 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity. }
  (* step 4 (off 12): addi t5,x0,-1 *)
  assert (hu4 : step s3 = setPc (rset s3 30 (2 ^ 64 - 1)) (2147483792 + 16)).
  { rewrite (step1_addi s3 12 30 0 (-1) hcode3 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc3 ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, hpc3, (wadd_id (2147483792 + 12) 4 ltac:(lia)).
    replace (wadd 0 (-1)) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
    f_equal; lia. }
  set (s4 := setPc (rset s3 30 (2 ^ 64 - 1)) (2147483792 + 16)) in *.
  assert (hr4 : forall i, i <> 30 -> rget s4 i = rget s3 i).
  { intros i hi. unfold s4. rewrite setPc_rget.
    destruct (Z.eqb_spec i 0) as [->|h0]; [reflexivity|].
    rewrite (rset_rget s3 30 _ i ltac:(lia) h0).
    replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact hi). reflexivity. }
  assert (hr4_30 : rget s4 30 = 2 ^ 64 - 1).
  { unfold s4. rewrite setPc_rget, (rset_rget s3 30 _ 30 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity. }
  (* assemble *)
  assert (hp0 : s0.(pc) <> 0) by (rewrite hpc0; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; lia).
  exists s4. split.
  { rewrite (runUntil_S 3 s0 hp0), hu1, (runUntil_S 2 s1 hp1), hu2,
            (runUntil_S 1 s2 hp2), hu3, (runUntil_S 0 s3 hp3), hu4. reflexivity. }
  assert (hmem4 : s4.(mem) = s0.(mem))
    by (unfold s4, s3, s2, s1; rewrite !setPc_mem, !rset_mem; reflexivity).
  assert (hrS : forall i, i <> 28 -> i <> 29 -> i <> 30 -> rget s4 i = rget s0 i)
    by (intros i h1 h2 h3;
        rewrite (hr4 i h3), (hr3 i h2), (hr2 i h2), (hr1 i h1); reflexivity).
  refine {| ii_pc := _; ii_code := _; ii_a0 := _; ii_a1 := _; ii_a2 := _;
            ii_a3 := _; ii_a4 := _; ii_ra := _; ii_t3 := _; ii_t4 := _;
            ii_t5 := _; ii_in := _; ii_tbl := _ |}.
  - reflexivity.
  - apply (CodeLoaded1_eqmem s3); [unfold s4; rewrite setPc_mem, rset_mem; reflexivity| exact hcode3].
  - rewrite (hrS 10 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - rewrite (hrS 11 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - rewrite (hrS 12 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - rewrite (hrS 13 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - rewrite (hrS 14 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - rewrite (hrS 1 ltac:(lia) ltac:(lia) ltac:(lia)); reflexivity.
  - (* t3 = lblAddr + 8*0 *)
    rewrite (hr4 28 ltac:(lia)), (hr3 28 ltac:(lia)), (hr2 28 ltac:(lia)).
    unfold s1. rewrite setPc_rget, (rset_rget s0 28 _ 28 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. unfold Image1.lblAddr. lia.
  - rewrite (hr4 29 ltac:(lia)). unfold Image1.lblAddr. exact hr3_29.
  - exact hr4_30.
  - apply (inputLoaded_eqmem s0); [exact hmem4 | apply in_initOn1; exact hwf].
  - intros b hb. lia.
Qed.

(* the whole init phase: 772 = 4 + 3*256 steps from the initial state to
   pass-1 entry with the table cleared *)
Lemma init_phase : forall inp cap, WellFormed1 inp cap ->
  exists s', runUntil 0 772 (mkInit1 (Z.of_nat (length inp)) cap (memWith1 inp Image1.inputAddr)) = s'
          /\ Pass1Entry inp cap s'.
Proof.
  intros inp cap hwf.
  destruct (entry_block inp cap hwf) as (s4 & hrun4 & hinv).
  destruct (init_loop inp cap 256 s4 0 ltac:(lia) ltac:(lia) hinv hwf)
    as (s' & hrunL & hpe).
  exists s'. split; [| exact hpe].
  replace 772%nat with (4 + 3 * 256)%nat by lia.
  rewrite (runUntil_add 4 (3 * 256) _), hrun4, hrunL. reflexivity.
Qed.

(** ** The result relation and the exit epilogues. *)

(* writes to x0 are dropped *)
Lemma rset_zero s v : rset s 0 v = s.
Proof. reflexivity. Qed.

(* the halted observation matches coreSpec1 *)
Definition Result1 (f : State) (inp : list Z) (cap : Z) : Prop :=
  let '(st, bs, ln) := coreSpec1 (zin inp) (Z.to_nat cap) in
  f.(pc) = 0 /\ rget f 10 = Z.of_nat st /\ rget f 11 = Z.of_nat ln /\
  readMem f.(mem) Image1.outAddr ln = bs.

Lemma Result1_pc f inp cap : Result1 f inp cap -> f.(pc) = 0.
Proof.
  unfold Result1. destruct (coreSpec1 (zin inp) (Z.to_nat cap)) as [[st bs] ln]. tauto.
Qed.

(* generic exit epilogue, a1 = 0 shape: li a0,K; li a1,0; ret.
   3 steps to a halted state with a0=K, a1=0, memory untouched. *)
Lemma exit_zero : forall s off K,
  CodeLoaded1 s -> 0 <= off -> off + 8 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 1 = 0 ->
  decode (wordAt1 off) = Iaddi 10 0 K ->
  decode (wordAt1 (off + 4)) = Iaddi 11 0 0 ->
  decode (wordAt1 (off + 8)) = Ijalr 0 1 0 ->
  0 <= K < 2 ^ 64 ->
  exists f, runUntil 0 3 s = f /\ f.(pc) = 0 /\ rget f 10 = K /\
            rget f 11 = 0 /\ f.(mem) = s.(mem).
Proof.
  intros s off K hcode ho hb hpc hra hd1 hd2 hd3 hK.
  rewrite coreBytes1_len in hb.
  assert (hu1 : step s = setPc (rset s 10 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 10 0 K hcode ho ltac:(rewrite coreBytes1_len; lia) hpc hd1),
            rget_zero, (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
            (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; lia. }
  set (s1 := setPc (rset s 10 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (hcode1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hu2 : step s1 = setPc (rset s1 11 0) (Image1.coreAddr + (off + 8))).
  { rewrite (step1_addi s1 (off + 4) 11 0 0 hcode1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hd2),
            rget_zero, (wadd_id 0 0 ltac:(lia)), Z.add_0_l, hpc1,
            (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; lia. }
  set (s2 := setPc (rset s1 11 0) (Image1.coreAddr + (off + 8))) in *.
  assert (hpc2 : s2.(pc) = Image1.coreAddr + (off + 8)) by reflexivity.
  assert (hcode2 : CodeLoaded1 s2)
    by (apply (CodeLoaded1_eqmem s1); [unfold s2; rewrite setPc_mem, rset_mem; reflexivity| exact hcode1]).
  assert (hra2 : rget s2 1 = 0).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 11 0 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 11) with false by reflexivity.
    unfold s1. rewrite setPc_rget, (rset_rget s 10 K 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 10) with false by reflexivity. exact hra. }
  assert (hb3 : (off + 8) + 3 < Z.of_nat (length Image1.coreBytes))
    by (rewrite coreBytes1_len; lia).
  assert (hu3 : step s2 = setPc s2 0).
  { rewrite (step1_jalr s2 (off + 8) 0 1 0 hcode2 ltac:(lia) hb3 hpc2 hd3).
    rewrite rset_zero, hra2.
    f_equal; vm_compute; reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; unfold Image1.coreAddr; lia).
  exists (setPc s2 0). repeat apply conj.
  - rewrite (runUntil_S 2 s hp0), hu1, (runUntil_S 1 s1 hp1), hu2,
            (runUntil_S 0 s2 hp2), hu3. reflexivity.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 0 10 ltac:(lia) ltac:(lia)).
    replace (10 =? 11) with false by reflexivity.
    unfold s1. rewrite setPc_rget, (rset_rget s 10 K 10 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 0 11 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - rewrite setPc_mem. unfold s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(* generic exit epilogue, a1 = t1 shape: li a0,K; mv a1,t1; ret. *)
Lemma exit_t1 : forall s off K,
  CodeLoaded1 s -> 0 <= off -> off + 8 + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s 1 = 0 ->
  decode (wordAt1 off) = Iaddi 10 0 K ->
  decode (wordAt1 (off + 4)) = Iaddi 11 6 0 ->
  decode (wordAt1 (off + 8)) = Ijalr 0 1 0 ->
  0 <= K < 2 ^ 64 -> 0 <= rget s 6 < 2 ^ 64 ->
  exists f, runUntil 0 3 s = f /\ f.(pc) = 0 /\ rget f 10 = K /\
            rget f 11 = rget s 6 /\ f.(mem) = s.(mem).
Proof.
  intros s off K hcode ho hb hpc hra hd1 hd2 hd3 hK h6.
  rewrite coreBytes1_len in hb.
  assert (hu1 : step s = setPc (rset s 10 K) (Image1.coreAddr + (off + 4))).
  { rewrite (step1_addi s off 10 0 K hcode ho ltac:(rewrite coreBytes1_len; lia) hpc hd1),
            rget_zero, (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
            (wadd_id (Image1.coreAddr + off) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; lia. }
  set (s1 := setPc (rset s 10 K) (Image1.coreAddr + (off + 4))) in *.
  assert (hpc1 : s1.(pc) = Image1.coreAddr + (off + 4)) by reflexivity.
  assert (hcode1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hr6_1 : rget s1 6 = rget s 6).
  { unfold s1. rewrite setPc_rget, (rset_rget s 10 K 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 10) with false by reflexivity. reflexivity. }
  assert (hu2 : step s1 = setPc (rset s1 11 (rget s 6)) (Image1.coreAddr + (off + 8))).
  { rewrite (step1_addi s1 (off + 4) 11 6 0 hcode1 ltac:(lia)
              ltac:(rewrite coreBytes1_len; lia) hpc1 hd2),
            hr6_1, (wadd_id (rget s 6) 0 ltac:(lia)), Z.add_0_r, hpc1,
            (wadd_id (Image1.coreAddr + (off + 4)) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; lia. }
  set (s2 := setPc (rset s1 11 (rget s 6)) (Image1.coreAddr + (off + 8))) in *.
  assert (hpc2 : s2.(pc) = Image1.coreAddr + (off + 8)) by reflexivity.
  assert (hcode2 : CodeLoaded1 s2)
    by (apply (CodeLoaded1_eqmem s1); [unfold s2; rewrite setPc_mem, rset_mem; reflexivity| exact hcode1]).
  assert (hra2 : rget s2 1 = 0).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 11 _ 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 11) with false by reflexivity.
    unfold s1. rewrite setPc_rget, (rset_rget s 10 K 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 10) with false by reflexivity. exact hra. }
  assert (hb3 : (off + 8) + 3 < Z.of_nat (length Image1.coreBytes))
    by (rewrite coreBytes1_len; lia).
  assert (hu3 : step s2 = setPc s2 0).
  { rewrite (step1_jalr s2 (off + 8) 0 1 0 hcode2 ltac:(lia) hb3 hpc2 hd3).
    rewrite rset_zero, hra2.
    f_equal; vm_compute; reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; unfold Image1.coreAddr; lia).
  exists (setPc s2 0). repeat apply conj.
  - rewrite (runUntil_S 2 s hp0), hu1, (runUntil_S 1 s1 hp1), hu2,
            (runUntil_S 0 s2 hp2), hu3. reflexivity.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 _ 10 ltac:(lia) ltac:(lia)).
    replace (10 =? 11) with false by reflexivity.
    unfold s1. rewrite setPc_rget, (rset_rget s 10 K 10 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 _ 11 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - rewrite setPc_mem. unfold s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(** ** Pass 1: the loop invariant and the loop-head prefix. *)

(* Invariant at the pass-1 loop head (offset 36). [lab]/[pos] are the scan
   state; [rest] the unconsumed input suffix. The telescope [p1_spec] pins
   the whole-input scan to the residual scan. *)
Record P1Inv (inp : list Z) (cap : Z) (s : State)
    (lab : Labels) (pos : nat) (rest : list Z) : Prop := {
  p1_wf      : WellFormed1 inp cap;
  p1_at_loop : s.(pc) = Image1.coreAddr + 36;
  p1_code    : CodeLoaded1 s;
  p1_a0      : rget s 10 = Image1.inputAddr;
  p1_a1      : rget s 11 = Z.of_nat (length inp);
  p1_a2      : rget s 12 = Image1.outAddr;
  p1_a3      : rget s 13 = cap;
  p1_a4      : rget s 14 = Image1.lblAddr;
  p1_ra      : rget s 1 = 0;
  p1_in_mem  : InputLoaded s inp;
  p1_idx     : rget s 5 = Z.of_nat (length inp) - Z.of_nat (length rest);
  p1_suffix  : skipn (length inp - length rest) inp = rest;
  p1_outidx  : rget s 6 = Z.of_nat pos;
  p1_pos_le  : Z.of_nat pos <= cap;
  p1_tbl     : TableLoaded s lab;
  p1_lab_le  : forall c p, lab c = Some p -> (p <= pos)%nat;
  p1_spec    : scan1 High1 lab pos (zin rest) = scan1 High1 noLabels 0 (zin inp)
}.

(* The shared head of every non-EOF pass-1 iteration (offsets 36..48):
   bgeu (not taken) -> add -> lbu (read char c) -> addi (bump index).
   Lands at offset 52 with t2 = c. *)
Lemma p1_prefix : forall inp cap c rest' lab pos s,
  P1Inv inp cap s lab pos (c :: rest') ->
  exists s4, runUntil 0 4 s = s4 /\
    s4.(pc) = Image1.coreAddr + 52 /\
    rget s4 7 = c /\ 0 <= c < 256 /\
    rget s4 5 = Z.of_nat (length inp) - Z.of_nat (length rest') /\
    s4.(mem) = s.(mem) /\ CodeLoaded1 s4 /\
    (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget s4 i = rget s i).
Proof.
  intros inp cap c rest' lab pos s inv.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf.
  set (k := (length inp - length (c :: rest'))%nat) in *.
  set (jZ := Z.of_nat (length inp) - Z.of_nat (length (c :: rest'))) in *.
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    fold k in Hl. lia. }
  assert (htonat : Z.to_nat jZ = k).
  { unfold jZ, k. rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id. reflexivity. }
  assert (hjpos : 0 <= jZ) by (unfold jZ; lia).
  assert (hjlt : jZ < Z.of_nat (length inp)) by (unfold jZ; simpl length; lia).
  assert (Hc : nth k inp 0 = c).
  { transitivity (nth 0 (skipn k inp) 0).
    - rewrite nth_skipn. f_equal. lia.
    - rewrite hsuf. reflexivity. }
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn k inp). apply in_or_app. right.
    fold k in hsuf. rewrite hsuf. left; reflexivity. }
  assert (Hcr : 0 <= c < 256) by (apply (bytes_ok1 _ _ hwf); exact Hin).
  unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
  (* step 1: bgeu t0,a1,+324 NOT taken (idx < len) -> off 40 *)
  assert (hult : ultb (rget s 5) (rget s 11) = true).
  { rewrite hidx, ha1. unfold ultb. apply Z.ltb_lt. exact hjlt. }
  assert (hu1 : step s = setPc s (2147483792 + 40)).
  { rewrite (step1_bgeu s 36 5 11 324 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
              hpc0 ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc0, (wadd_id (2147483792 + 36) 4 ltac:(lia)). f_equal; lia. }
  set (s1 := setPc s (2147483792 + 40)) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = 2147483792 + 40) by reflexivity.
  (* step 2: add t3,a0,t0 -> off 44 *)
  assert (haddr : wadd (rget s1 10) (rget s1 5) = 2147484516 + jZ).
  { unfold s1. rewrite !setPc_rget, ha0, hidx. apply wadd_id. lia. }
  assert (hu2 : step s1 = setPc (rset s1 28 (2147484516 + jZ)) (2147483792 + 44)).
  { rewrite (step1_add s1 40 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc1
              ltac:(vm_compute; reflexivity)), haddr, hpc1,
            (wadd_id (2147483792 + 40) 4 ltac:(lia)). f_equal; lia. }
  set (s2 := setPc (rset s1 28 (2147484516 + jZ)) (2147483792 + 44)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded1 s2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = 2147483792 + 44) by reflexivity.
  (* step 3: lbu t2,0(t3) -> off 48 *)
  assert (hr28_2 : rget s2 28 = 2147484516 + jZ).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity. }
  assert (hbyteIn : s.(mem) (2147484516 + jZ) = nth (Z.to_nat jZ) inp 0).
  { pose proof (hinm jZ ltac:(lia)) as h. unfold Image1.inputAddr in h. exact h. }
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = c).
  { rewrite hr28_2, (wadd_id (2147484516 + jZ) 0 ltac:(lia)), Z.add_0_r,
            hmem2, hbyteIn, htonat, Hc.
    apply Z.mod_small. exact Hcr. }
  assert (hu3 : step s2 = setPc (rset s2 7 c) (2147483792 + 48)).
  { rewrite (step1_lbu s2 44 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc2
              ltac:(vm_compute; reflexivity)), hbyte, hpc2,
            (wadd_id (2147483792 + 44) 4 ltac:(lia)). f_equal; lia. }
  set (s3 := setPc (rset s2 7 c) (2147483792 + 48)) in *.
  assert (hmem3 : s3.(mem) = s.(mem))
    by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded1 s3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = 2147483792 + 48) by reflexivity.
  (* step 4: addi t0,t0,1 -> off 52 *)
  assert (hr5_3 : rget s3 5 = jZ).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact hidx. }
  assert (hu4 : step s3 = setPc (rset s3 5 (jZ + 1)) (2147483792 + 52)).
  { rewrite (step1_addi s3 48 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc3
              ltac:(vm_compute; reflexivity)), hr5_3,
            (wadd_id jZ 1 ltac:(lia)), hpc3,
            (wadd_id (2147483792 + 48) 4 ltac:(lia)). f_equal; lia. }
  set (s4 := setPc (rset s3 5 (jZ + 1)) (2147483792 + 52)) in *.
  assert (hmem4 : s4.(mem) = s.(mem))
    by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc0; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; lia).
  exists s4. repeat apply conj.
  - rewrite (runUntil_S 3 s hp0), hu1, (runUntil_S 2 s1 hp1), hu2,
            (runUntil_S 1 s2 hp2), hu3, (runUntil_S 0 s3 hp3), hu4. reflexivity.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - lia.
  - lia.
  - assert (H54 : rget s4 5 = jZ + 1)
      by (unfold s4; rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 5 ltac:(lia) ltac:(lia)),
            Z.eqb_refl; reflexivity).
    rewrite H54. unfold jZ. simpl length. lia.
  - exact hmem4.
  - apply (CodeLoaded1_eqmem s); [exact hmem4| exact hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* suffix step: consuming the head advances the drop index *)
Lemma suffix_step1 : forall (inp : list Z) c rest',
  skipn (length inp - length (c :: rest')) inp = c :: rest' ->
  skipn (length inp - length rest') inp = rest'.
Proof.
  intros inp c rest' hsuf.
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in *. lia. }
  replace (length inp - length rest')%nat
    with (1 + (length inp - length (c :: rest')))%nat by (simpl length in *; lia).
  rewrite <- skipn_skipn, hsuf. reflexivity.
Qed.

(** ** Pass-1 iteration: spacing tokens. *)

(* spec side: a spacing char is skipped by the scan *)
Lemma scan1_spacing c rest lab pos : isComment c = false -> isSpace c = true ->
  scan1 High1 lab pos (c :: rest) = scan1 High1 lab pos rest.
Proof. intros hc hs. simp scan1. rewrite hc, hs. reflexivity. Qed.

(* The pass-1 spacing dispatch (from offset 52, t2 = c in {10,32,95}): the
   li;beq chain falls through '#'(52)/';'(60) and branches back to the loop
   head (36) at the matching spacing char (68/76/84). Touches only t3/pc. *)
Lemma p1_spacing_tail s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 52 -> rget s4 7 = c ->
  0 <= c -> isSpace (Z.to_nat c) = true ->
  exists k, (k <= 10)%nat /\ (runUntil 0 k s4).(pc) = Image1.coreAddr + 36 /\
            (runUntil 0 k s4).(mem) = s4.(mem) /\
            (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc ht2 h0 hss.
  destruct (isSpace_cases c h0 hss) as [hc|[hc|hc]].
  all: assert (hne35 : c <> 35) by lia.
  all: assert (hne59 : c <> 59) by lia.
  (* block at off 52 (K=35), not taken *)
  all: pose proof (li1_beq_ne s4 52 35 c 276 hcode ltac:(lia)
         ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne35) as hb1.
  all: set (s_b := setPc (rset s4 28 35) (Image1.coreAddr + (52 + 8))) in *.
  all: assert (hcb : CodeLoaded1 s_b) by
         (apply (CodeLoaded1_eqmem s4); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcb : s_b.(pc) = Image1.coreAddr + 60) by (unfold s_b; cbn; lia).
  all: assert (h7b : rget s_b 7 = c) by
         (unfold s_b; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  (* block at off 60 (K=59), not taken *)
  all: pose proof (li1_beq_ne s_b 60 59 c 268 hcb ltac:(lia)
         ltac:(rewrite coreBytes1_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne59) as hb2.
  all: set (s_c := setPc (rset s_b 28 59) (Image1.coreAddr + (60 + 8))) in *.
  all: assert (hcc : CodeLoaded1 s_c) by
         (apply (CodeLoaded1_eqmem s4); [unfold s_c; rewrite setPc_mem, rset_mem;
            unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcc : s_c.(pc) = Image1.coreAddr + 68) by (unfold s_c; cbn; lia).
  all: assert (h7c : rget s_c 7 = c) by
         (unfold s_c; rewrite (li_block_frame s_b 59 _ 7 ltac:(lia)); exact h7b).
  - (* c = 10: taken at off 68 *)
    pose proof (li1_beq_eq s_c 68 10 c (-36) (Image1.coreAddr + 36) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (68 + 4)) (-36)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb3.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s4 = setPc (rset s_c 28 10) (Image1.coreAddr + 36))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, hb3; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
  - (* c = 32: not taken at 68, taken at 76 *)
    pose proof (li1_beq_ne s_c 68 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (Image1.coreAddr + (68 + 8))) in *.
    assert (hcd : CodeLoaded1 s_d) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = Image1.coreAddr + 76) by (unfold s_d; cbn; lia).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 _ 7 ltac:(lia)); exact h7c).
    pose proof (li1_beq_eq s_d 76 32 c (-44) (Image1.coreAddr + 36) hcd ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (76 + 4)) (-44)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb4.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s4
                   = setPc (rset s_d 28 32) (Image1.coreAddr + 36))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem.
      unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hi. rewrite (li_block_frame s_d 32 _ i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
  - (* c = 95: not taken at 68/76, taken at 84 *)
    pose proof (li1_beq_ne s_c 68 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (Image1.coreAddr + (68 + 8))) in *.
    assert (hcd : CodeLoaded1 s_d) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = Image1.coreAddr + 76) by (unfold s_d; cbn; lia).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 _ 7 ltac:(lia)); exact h7c).
    pose proof (li1_beq_ne s_d 76 32 c (-44) hcd ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (s_e := setPc (rset s_d 28 32) (Image1.coreAddr + (76 + 8))) in *.
    assert (hce : CodeLoaded1 s_e) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_e; rewrite setPc_mem, rset_mem;
         unfold s_d; rewrite setPc_mem, rset_mem; unfold s_c; rewrite setPc_mem, rset_mem;
         unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpce : s_e.(pc) = Image1.coreAddr + 84) by (unfold s_e; cbn; lia).
    assert (h7e : rget s_e 7 = c) by
      (unfold s_e; rewrite (li_block_frame s_d 32 _ 7 ltac:(lia)); exact h7d).
    pose proof (li1_beq_eq s_e 84 95 c (-52) (Image1.coreAddr + 36) hce ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpce h7e ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (84 + 4)) (-52)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb5.
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 2)))) s4
                   = setPc (rset s_e 28 95) (Image1.coreAddr + 36))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
                  runUntil_add, hb4, hb5; reflexivity).
    exists (2 + (2 + (2 + (2 + 2))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_e. rewrite setPc_mem, rset_mem.
      unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_e 95 _ i hi).
      unfold s_e. rewrite (li_block_frame s_d 32 _ i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* A COMPLETE pass-1 iteration for a spacing token: prefix + dispatch back to
   the loop head, invariant rebuilt with the suffix shortened by one. *)
Lemma p1_spacing : forall inp cap c rest' lab pos s,
  isSpace (Z.to_nat c) = true ->
  P1Inv inp cap s lab pos (c :: rest') ->
  exists k, (0 < k <= 50)%nat /\ P1Inv inp cap (runUntil 0 k s) lab pos rest'.
Proof.
  intros inp cap c rest' lab pos s hss inv.
  destruct (p1_prefix inp cap c rest' lab pos s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  assert (hsc : isComment (Z.to_nat c) = false)
    by (destruct (isSpace_cases c ltac:(lia) hss) as [H|[H|H]]; rewrite H; reflexivity).
  destruct (p1_spacing_tail s4 c hcode4 hpc4 ht2 ltac:(lia) hss)
    as (k & hk & htpc & htmem & htother).
  exists (4 + k)%nat. split; [lia|].
  rewrite runUntil_add, hrun4.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  refine {| p1_wf := hwf; p1_at_loop := htpc; p1_code := _; p1_a0 := _; p1_a1 := _;
            p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
            p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := hposle;
            p1_tbl := _; p1_lab_le := hlable; p1_spec := _ |}.
  - apply (CodeLoaded1_eqmem s); [rewrite htmem; exact hmem4| exact hcode].
  - rewrite (htother 10 ltac:(lia)),
      (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
  - rewrite (htother 11 ltac:(lia)),
      (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
  - rewrite (htother 12 ltac:(lia)),
      (hother4 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
  - rewrite (htother 13 ltac:(lia)),
      (hother4 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
  - rewrite (htother 14 ltac:(lia)),
      (hother4 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
  - rewrite (htother 1 ltac:(lia)),
      (hother4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
  - apply (inputLoaded_eqmem s); [rewrite htmem; exact hmem4| exact hinm].
  - rewrite (htother 5 ltac:(lia)), ht0. simpl length. reflexivity.
  - apply (suffix_step1 inp c rest'). exact hsuf.
  - rewrite (htother 6 ltac:(lia)),
      (hother4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx.
  - apply (tableLoaded_eqmem s); [rewrite htmem; exact hmem4| exact htbl].
  - rewrite <- hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    rewrite (scan1_spacing (Z.to_nat c) (zin rest') lab pos hsc hss). reflexivity.
Qed.

(** ** Pass-1 iteration: comment tokens -- the inner scan loop (332..356). *)

(* spec side: a comment char skips to past the newline *)
Lemma scan1_comment c rest lab pos : isComment c = true ->
  scan1 High1 lab pos (c :: rest) = scan1 High1 lab pos (skipComment rest).
Proof. intros hc. simp scan1. rewrite hc. reflexivity. Qed.

Lemma scan1_nil lab pos : scan1 High1 lab pos [] = (lab, pos, Ok1).
Proof. now simp scan1. Qed.

(* bgeu with equal operands: TAKEN *)
Lemma bgeu1_eq_taken s off rs1 rs2 A immB target :
  CodeLoaded1 s -> 0 <= off -> off + 3 < Z.of_nat (length Image1.coreBytes) ->
  s.(pc) = Image1.coreAddr + off ->
  rget s rs1 = A -> rget s rs2 = A ->
  decode (wordAt1 off) = Ibgeu rs1 rs2 immB ->
  wadd (Image1.coreAddr + off) immB = target ->
  step s = setPc s target.
Proof.
  intros hc ho hb hpc h1 h2 hd htgt.
  rewrite (step1_bgeu s off rs1 rs2 immB hc ho hb hpc hd), h1, h2.
  unfold ultb. rewrite Z.ltb_irrefl. rewrite hpc, htgt. reflexivity.
Qed.

(* The 4-instruction head of the comment inner loop (332..344):
   bgeu(not taken) -> add -> lbu (read inp[idx]) -> li t3,10.
   Reaches offset 348 with t2 = inp[idx], t3 = 10, t0 unchanged. *)
Lemma comment_read1 s inp idx ch :
  CodeLoaded1 s -> s.(pc) = Image1.coreAddr + 332 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = Image1.inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  (idx < length inp)%nat ->
  Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  InputLoaded s inp ->
  nth idx inp 0 = ch -> 0 <= ch < 256 ->
  (runUntil 0 4 s).(pc) = Image1.coreAddr + 348 /\ rget (runUntil 0 4 s) 7 = ch /\
  rget (runUntil 0 4 s) 28 = 10 /\ rget (runUntil 0 4 s) 5 = Z.of_nat idx /\
  (runUntil 0 4 s).(mem) = s.(mem) /\ CodeLoaded1 (runUntil 0 4 s) /\
  (forall i, i <> 7 -> i <> 28 -> rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros hcode hpc Hidx Ha0 Ha1 hlt hin_fit Hinmem Hch Hcr.
  assert (HinmemX : forall j, 0 <= j < Z.of_nat (length inp) ->
            s.(mem) (2147484516 + j) = nth (Z.to_nat j) inp 0).
  { intros j hj. pose proof (Hinmem j hj) as h. unfold Image1.inputAddr in h. exact h. }
  unfold Image1.inputAddr, Image1.coreAddr in *.
  assert (hult : ultb (rget s 5) (rget s 11) = true)
    by (rewrite Hidx, Ha1; unfold ultb; apply Z.ltb_lt; apply Nat2Z.inj_lt; exact hlt).
  assert (hs1 : step s = setPc s (2147483792 + 336)).
  { rewrite (step1_bgeu s 332 5 11 28 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc
      ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc, (wadd_id (2147483792 + 332) 4 ltac:(lia)). f_equal; lia. }
  set (s1 := setPc s (2147483792 + 336)) in *.
  assert (hc1 : CodeLoaded1 s1) by
    (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = 2147483792 + 336) by reflexivity.
  assert (haddr : wadd (rget s1 10) (rget s1 5) = 2147484516 + Z.of_nat idx).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (2147484516 + Z.of_nat idx)) (2147483792 + 340)).
  { rewrite (step1_add s1 336 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc1
      ltac:(vm_compute; reflexivity)), haddr, hpc1,
      (wadd_id (2147483792 + 336) 4 ltac:(lia)). f_equal; lia. }
  set (s2 := setPc (rset s1 28 (2147484516 + Z.of_nat idx)) (2147483792 + 340)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded1 s2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = 2147483792 + 340) by reflexivity.
  assert (hr28 : rget s2 28 = 2147484516 + Z.of_nat idx) by
    (unfold s2; rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl;
     reflexivity).
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = ch).
  { rewrite hr28, (wadd_id (2147484516 + Z.of_nat idx) 0 ltac:(lia)), Z.add_0_r,
      hmem2, (HinmemX (Z.of_nat idx) ltac:(split; [lia| apply Nat2Z.inj_lt; exact hlt])),
      Nat2Z.id, Hch.
    apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 ch) (2147483792 + 344)).
  { rewrite (step1_lbu s2 340 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc2
      ltac:(vm_compute; reflexivity)), hbyte, hpc2,
      (wadd_id (2147483792 + 340) 4 ltac:(lia)). f_equal; lia. }
  set (s3 := setPc (rset s2 7 ch) (2147483792 + 344)) in *.
  assert (hmem3 : s3.(mem) = s.(mem)) by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded1 s3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = 2147483792 + 344) by reflexivity.
  assert (hs4 : step s3 = setPc (rset s3 28 10) (2147483792 + 348)).
  { rewrite (step1_addi s3 344 28 0 10 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc3
      ltac:(vm_compute; reflexivity)), rget_zero, (wadd_id 0 10 ltac:(lia)), Z.add_0_l, hpc3,
      (wadd_id (2147483792 + 344) 4 ltac:(lia)). f_equal; lia. }
  set (s4 := setPc (rset s3 28 10) (2147483792 + 348)) in *.
  assert (hmem4 : s4.(mem) = s.(mem)) by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4; apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 28 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact Hidx.
  - exact hmem4.
  - apply (CodeLoaded1_eqmem s); [exact hmem4| exact hcode].
  - intros i h7 h28. unfold s4.
    destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
    apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget s3 28 10 i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch i ltac:(lia) E0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* The comment inner loop: scan [inp] from [idx] one char/turn to the first
   newline or EOF. Either it reaches the pass-1 loop head (36) ON the newline
   at position q, or pass-2 entry (360) at EOF. Induction on the span. *)
Lemma comment_loop1 inp : forall n s idx,
  CodeLoaded1 s -> s.(pc) = Image1.coreAddr + 332 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = Image1.inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  InputLoaded s inp ->
  Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  (forall b, In b inp -> 0 <= b < 256) ->
  (idx <= length inp)%nat -> (length inp - idx <= n)%nat ->
  exists k,
    (exists q, (idx <= q < length inp)%nat /\ (k <= 7 * (q - idx) + 5)%nat /\
        nth q inp 0 = 10 /\
        skipComment (zin (skipn idx inp)) = zin (skipn (S q) inp) /\
        (runUntil 0 k s).(pc) = Image1.coreAddr + 36 /\
        rget (runUntil 0 k s) 5 = Z.of_nat q /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i))
    \/ ((k <= 7 * (length inp - idx) + 1)%nat /\
        skipComment (zin (skipn idx inp)) = nil /\
        (runUntil 0 k s).(pc) = Image1.coreAddr + 360 /\
        rget (runUntil 0 k s) 5 = Z.of_nat (length inp) /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i)).
Proof.
  induction n; intros s idx hcode hpc Hidx Ha0 Ha1 Hinmem hin_fit Hbytes Hle Hn.
  - (* idx = length inp *)
    assert (hidxeq : idx = length inp) by lia. subst idx.
    assert (hbt : step s = setPc s (Image1.coreAddr + 360)).
    { apply (bgeu1_eq_taken s 332 5 11 (Z.of_nat (length inp)) 28 _ hcode ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpc Hidx Ha1 ltac:(vm_compute; reflexivity)).
      rewrite (wadd_id (Image1.coreAddr + 332) 28 ltac:(unfold Image1.coreAddr; lia)).
      unfold Image1.coreAddr. lia. }
    assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
    exists 1%nat. right. rewrite (runUntil_one s hp0), hbt. repeat apply conj.
    + lia.
    + rewrite skipn_all. reflexivity.
    + apply setPc_pc.
    + rewrite setPc_rget. exact Hidx.
    + apply setPc_mem.
    + intros i _ _ _. apply setPc_rget.
  - destruct (lt_dec idx (length inp)) as [Hlt|Hge].
    + (* read inp[idx] *)
      assert (Hin : In (nth idx inp 0) inp) by (apply nth_In; exact Hlt).
      assert (Hch256 : 0 <= nth idx inp 0 < 256) by (apply Hbytes; exact Hin).
      assert (hcons : skipn idx inp = nth idx inp 0 :: skipn (S idx) inp)
        by (apply skipn_cons_nth; exact Hlt).
      destruct (comment_read1 s inp idx (nth idx inp 0) hcode hpc Hidx Ha0 Ha1 Hlt hin_fit
        Hinmem eq_refl Hch256) as [hpc4 [h7_4 [h28_4 [h5_4 [hmem4 [hcode4 hoth4]]]]]].
      set (s4 := runUntil 0 4 s) in *.
      destruct (Z.eq_dec (nth idx inp 0) 10) as [Hnl|Hnnl].
      * (* newline at idx -> pass-1 loop head 36 *)
        assert (hbeq : step s4 = setPc s4 (Image1.coreAddr + 36)).
        { rewrite (step1_beq s4 348 7 28 (-312) hcode4 ltac:(lia)
            ltac:(rewrite coreBytes1_len; lia) hpc4 ltac:(vm_compute; reflexivity)),
            h7_4, h28_4, Hnl, Z.eqb_refl, hpc4,
            (wadd_id (Image1.coreAddr + 348) (-312) ltac:(unfold Image1.coreAddr; lia)).
          f_equal; unfold Image1.coreAddr; lia. }
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; unfold Image1.coreAddr; lia).
        exists (4 + 1)%nat. left. exists idx.
        rewrite (runUntil_add 4 1). fold s4. rewrite (runUntil_one s4 hp4), hbeq.
        repeat apply conj.
        -- lia.
        -- lia.
        -- lia.
        -- exact Hnl.
        -- assert (Heqb : Nat.eqb (Z.to_nat (nth idx inp 0)) c_nl = true)
             by (apply Nat.eqb_eq; unfold c_nl; rewrite Hnl; reflexivity).
           rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_eq _ _ Heqb). reflexivity.
        -- apply setPc_pc.
        -- rewrite setPc_rget. exact h5_4.
        -- rewrite setPc_mem. exact hmem4.
        -- intros i _ h7 h28. rewrite setPc_rget. exact (hoth4 i h7 h28).
      * (* not newline -> advance to idx+1, recurse *)
        assert (Hnl_ne : Nat.eqb (Z.to_nat (nth idx inp 0)) c_nl = false)
          by (apply Nat.eqb_neq; unfold c_nl; intro Hc; apply Hnnl; lia).
        assert (hbeq : step s4 = setPc s4 (Image1.coreAddr + 352)).
        { rewrite (step1_beq s4 348 7 28 (-312) hcode4 ltac:(lia)
            ltac:(rewrite coreBytes1_len; lia) hpc4 ltac:(vm_compute; reflexivity)),
            h7_4, h28_4.
          replace (nth idx inp 0 =? 10) with false by (symmetry; apply Z.eqb_neq; exact Hnnl).
          rewrite hpc4, (wadd_id (Image1.coreAddr + 348) 4 ltac:(unfold Image1.coreAddr; lia)).
          f_equal; lia. }
        set (v5 := setPc s4 (Image1.coreAddr + 352)) in *.
        assert (hc5 : CodeLoaded1 v5) by
          (apply (CodeLoaded1_eqmem s4); [unfold v5; rewrite setPc_mem; reflexivity| exact hcode4]).
        assert (hpc5 : v5.(pc) = Image1.coreAddr + 352) by reflexivity.
        assert (h5v5 : rget v5 5 = Z.of_nat idx) by (unfold v5; rewrite setPc_rget; exact h5_4).
        assert (haddi : step v5 = setPc (rset v5 5 (Z.of_nat (S idx))) (Image1.coreAddr + 356)).
        { rewrite (step1_addi v5 352 5 5 1 hc5 ltac:(unfold Image1.coreAddr; lia)
            ltac:(rewrite coreBytes1_len; lia) hpc5
            ltac:(vm_compute; reflexivity)), h5v5,
            (wadd_id (Z.of_nat idx) 1 ltac:(unfold Image1.inputAddr in *; lia)), hpc5,
            (wadd_id (Image1.coreAddr + 352) 4 ltac:(unfold Image1.coreAddr; lia)).
          rewrite Nat2Z.inj_succ. f_equal; lia. }
        set (v6 := setPc (rset v5 5 (Z.of_nat (S idx))) (Image1.coreAddr + 356)) in *.
        assert (hc6 : CodeLoaded1 v6) by
          (apply (CodeLoaded1_eqmem s4); [unfold v6, v5; rewrite !setPc_mem, rset_mem;
            reflexivity| exact hcode4]).
        assert (hpc6 : v6.(pc) = Image1.coreAddr + 356) by reflexivity.
        assert (hjal : step v6 = setPc v6 (Image1.coreAddr + 332)).
        { rewrite (step1_jal v6 356 0 (-24) hc6 ltac:(unfold Image1.coreAddr; lia)
            ltac:(rewrite coreBytes1_len; lia) hpc6
            ltac:(vm_compute; reflexivity)).
          rewrite rset_zero, hpc6,
            (wadd_id (Image1.coreAddr + 356) (-24) ltac:(unfold Image1.coreAddr; lia)).
          f_equal; lia. }
        set (s' := setPc v6 (Image1.coreAddr + 332)) in *.
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; unfold Image1.coreAddr; lia).
        assert (hp5 : v5.(pc) <> 0) by (rewrite hpc5; unfold Image1.coreAddr; lia).
        assert (hp6 : v6.(pc) <> 0) by (rewrite hpc6; unfold Image1.coreAddr; lia).
        assert (hrun3 : runUntil 0 3 s4 = s').
        { rewrite (runUntil_S 2 s4 hp4), hbeq, (runUntil_S 1 v5 hp5), haddi,
                  (runUntil_S 0 v6 hp6), hjal. reflexivity. }
        assert (hmems' : s'.(mem) = s.(mem))
          by (unfold s', v6, v5; rewrite !setPc_mem, rset_mem, setPc_mem; exact hmem4).
        assert (hcs' : CodeLoaded1 s') by (apply (CodeLoaded1_eqmem s); [exact hmems'| exact hcode]).
        assert (hpcs' : s'.(pc) = Image1.coreAddr + 332) by reflexivity.
        assert (h5s' : rget s' 5 = Z.of_nat (S idx)) by
          (unfold s'; rewrite setPc_rget; unfold v6;
           rewrite setPc_rget, (rset_rget v5 5 _ 5 ltac:(lia) ltac:(lia)), Z.eqb_refl;
           reflexivity).
        assert (hother' : forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget s' i = rget s i).
        { intros i h5 h7 h28. unfold s'. rewrite setPc_rget. unfold v6.
          destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
          apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget v5 5 _ i ltac:(lia) E0).
          replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
          unfold v5. rewrite setPc_rget. exact (hoth4 i h7 h28). }
        assert (h10s' : rget s' 10 = Image1.inputAddr) by
          (rewrite (hother' 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha0).
        assert (h11s' : rget s' 11 = Z.of_nat (length inp)) by
          (rewrite (hother' 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha1).
        destruct (IHn s' (S idx) hcs' hpcs' h5s' h10s' h11s'
          ltac:(intros j hj; rewrite hmems'; exact (Hinmem j hj)) hin_fit Hbytes
          ltac:(lia) ltac:(lia)) as [k [[q [Hq1 [Hkb [Hq2 [Hqskip [Hppc [H5q [Hmemq Hothq]]]]]]]]|
                                          [Hkb [Hskip0 [Hppc [H5q [Hmemq Hothq]]]]]]].
        -- exists (4 + (3 + k))%nat. left. exists q.
           rewrite (runUntil_add 4 (3 + k)). fold s4. rewrite (runUntil_add 3 k), hrun3.
           repeat apply conj.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ exact Hq2.
           ++ rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_ne _ _ Hnl_ne). exact Hqskip.
           ++ exact Hppc.
           ++ exact H5q.
           ++ rewrite Hmemq, hmems'. reflexivity.
           ++ intros i h5 h7 h28. rewrite (Hothq i h5 h7 h28), (hother' i h5 h7 h28). reflexivity.
        -- exists (4 + (3 + k))%nat. right.
           rewrite (runUntil_add 4 (3 + k)). fold s4. rewrite (runUntil_add 3 k), hrun3.
           repeat apply conj.
           ++ lia.
           ++ rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_ne _ _ Hnl_ne). exact Hskip0.
           ++ exact Hppc.
           ++ exact H5q.
           ++ rewrite Hmemq, hmems'. reflexivity.
           ++ intros i h5 h7 h28. rewrite (Hothq i h5 h7 h28), (hother' i h5 h7 h28). reflexivity.
    + (* idx = length inp *)
      assert (hidxeq : idx = length inp) by lia. subst idx.
      assert (hbt : step s = setPc s (Image1.coreAddr + 360)).
      { apply (bgeu1_eq_taken s 332 5 11 (Z.of_nat (length inp)) 28 _ hcode ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc Hidx Ha1 ltac:(vm_compute; reflexivity)).
        rewrite (wadd_id (Image1.coreAddr + 332) 28 ltac:(unfold Image1.coreAddr; lia)).
        unfold Image1.coreAddr. lia. }
      assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
      exists 1%nat. right. rewrite (runUntil_one s hp0), hbt. repeat apply conj.
      * lia.
      * rewrite skipn_all. reflexivity.
      * apply setPc_pc.
      * rewrite setPc_rget. exact Hidx.
      * apply setPc_mem.
      * intros i _ _ _. apply setPc_rget.
Qed.

(** ** Pass-1 iteration: comment tokens, assembled. *)

(* State shape on arrival at pass 2 (offset 360): the scan is complete and
   Ok with final labels [labF] and total output size [m]. *)
Record P2Start (inp : list Z) (cap : Z) (s : State)
    (labF : Labels) (m : nat) : Prop := {
  p2s_wf      : WellFormed1 inp cap;
  p2s_pc      : s.(pc) = Image1.coreAddr + 360;
  p2s_code    : CodeLoaded1 s;
  p2s_a0      : rget s 10 = Image1.inputAddr;
  p2s_a1      : rget s 11 = Z.of_nat (length inp);
  p2s_a2      : rget s 12 = Image1.outAddr;
  p2s_a3      : rget s 13 = cap;
  p2s_a4      : rget s 14 = Image1.lblAddr;
  p2s_ra      : rget s 1 = 0;
  p2s_in_mem  : InputLoaded s inp;
  p2s_tbl     : TableLoaded s labF;
  p2s_m_le    : Z.of_nat m <= cap;
  p2s_lab_le  : forall c p, labF c = Some p -> (p <= m)%nat;
  p2s_scan_ok : scan1 High1 noLabels 0 (zin inp) = (labF, m, Ok1)
}.

(* A COMPLETE pass-1 iteration for a comment token (#/;): prefix + dispatch
   to 332 + the inner loop. Lands back at the loop head sitting ON the
   newline (strictly shorter suffix), or at pass-2 entry on EOF. *)
Lemma p1_comment : forall inp cap c rest' lab pos s,
  isComment (Z.to_nat c) = true ->
  P1Inv inp cap s lab pos (c :: rest') ->
  exists k,
    (exists rest2, (length rest2 < length (c :: rest'))%nat /\
        (k <= 50 * (length (c :: rest') - length rest2))%nat /\
        P1Inv inp cap (runUntil 0 k s) lab pos rest2)
    \/ ((k <= 50 * length (c :: rest'))%nat /\
        P2Start inp cap (runUntil 0 k s) lab pos).
Proof.
  intros inp cap c rest' lab pos s hcm inv. pose proof inv as inv0.
  destruct (p1_prefix inp cap c rest' lab pos s inv)
    as (s4' & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  assert (hs4 : runUntil 0 4 s = s4') by exact hrun4.
  (* dispatch 52 -> 332 (2 steps for '#', 4 for ';') *)
  assert (Hreach : exists kb, (kb <= 4)%nat /\
      (runUntil 0 kb s4').(pc) = Image1.coreAddr + 332 /\
      (runUntil 0 kb s4').(mem) = s4'.(mem) /\
      rget (runUntil 0 kb s4') 5 = rget s4' 5 /\
      (forall i, i <> 28 -> rget (runUntil 0 kb s4') i = rget s4' i)).
  { destruct (isComment_cases c ltac:(lia) hcm) as [Hc35|Hc59].
    - exists 2%nat. split; [lia|].
      rewrite (li1_beq_eq s4' 52 35 c 276 (Image1.coreAddr + 332) hcode4 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpc4 ht2 ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(lia) Hc35
        ltac:(rewrite (wadd_id (Image1.coreAddr + (52 + 4)) 276
                ltac:(unfold Image1.coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem. reflexivity.
      + exact (li_block_frame s4' 35 _ 5 ltac:(lia)).
      + intros i hi. exact (li_block_frame s4' 35 _ i hi).
    - exists 4%nat. split; [lia|].
      rewrite (runUntil_add 2 2),
        (li1_beq_ne s4' 52 35 c 276 hcode4 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc4 ht2 ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
      set (sb := setPc (rset s4' 28 35) (Image1.coreAddr + (52 + 8))) in *.
      assert (hcb : CodeLoaded1 sb) by
        (apply (CodeLoaded1_eqmem s4'); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity|
         exact hcode4]).
      assert (hpcb : sb.(pc) = Image1.coreAddr + 60) by (unfold sb; cbn; lia).
      assert (h7b : rget sb 7 = c) by
        (unfold sb; rewrite (li_block_frame s4' 35 _ 7 ltac:(lia)); exact ht2).
      rewrite (li1_beq_eq sb 60 59 c 268 (Image1.coreAddr + 332) hcb ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(lia) Hc59
        ltac:(rewrite (wadd_id (Image1.coreAddr + (60 + 4)) 268
                ltac:(unfold Image1.coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. reflexivity.
      + rewrite (li_block_frame sb 59 _ 5 ltac:(lia)).
        exact (li_block_frame s4' 35 _ 5 ltac:(lia)).
      + intros i hi. rewrite (li_block_frame sb 59 _ i hi).
        exact (li_block_frame s4' 35 _ i hi). }
  destruct Hreach as (kb & hkb & hbpc & hbmem & hb5 & hbother).
  set (sB := runUntil 0 kb s4') in *.
  (* facts for the inner loop at index idx1 = len - |rest'| *)
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hin_fit : Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64).
  { pose proof (in_fits1 _ _ hwf). pose proof (lbl_fits1 _ _ hwf).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr in *. lia. }
  assert (h5B : rget sB 5 = Z.of_nat idx1).
  { rewrite hb5, ht0. unfold idx1. lia. }
  assert (h10B : rget sB 10 = Image1.inputAddr).
  { rewrite (hbother 10 ltac:(lia)),
      (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha0. }
  assert (h11B : rget sB 11 = Z.of_nat (length inp)).
  { rewrite (hbother 11 ltac:(lia)),
      (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha1. }
  assert (hmemB : sB.(mem) = s.(mem)) by (rewrite hbmem; exact hmem4).
  assert (hcodeB : CodeLoaded1 sB)
    by (apply (CodeLoaded1_eqmem s); [exact hmemB| exact hcode]).
  assert (hinmB : InputLoaded sB inp)
    by (apply (inputLoaded_eqmem s); [exact hmemB| exact hinm]).
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp c rest'); exact hsuf).
  destruct (comment_loop1 inp (length inp - idx1)%nat sB idx1 hcodeB hbpc h5B h10B h11B
              hinmB hin_fit (bytes_ok1 _ _ hwf) ltac:(unfold idx1; lia) ltac:(lia))
    as [k [[q [Hq1 [Hkb2 [Hq2 [Hqskip [Hppc [H5q [Hmemq Hothq]]]]]]]]|
            [Hkb2 [Hskip0 [Hppc [H5q [Hmemq Hothq]]]]]]].
  - (* newline at q -> back to the loop head sitting on the newline *)
    exists (4 + (kb + k))%nat. left. exists (skipn q inp).
    rewrite (runUntil_add 4 (kb + k)), hs4, (runUntil_add kb k). fold sB.
    set (sF := runUntil 0 k sB) in *.
    assert (hlq : length (skipn q inp) = (length inp - q)%nat) by (apply length_skipn).
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget sF i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (Hothq i h5 h7 h28), (hbother i h28),
              (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemF : sF.(mem) = s.(mem)) by (rewrite Hmemq; exact hmemB).
    split; [unfold idx1 in *; simpl length in *; lia|
            split; [unfold idx1 in *; simpl length in *; lia|]].
    refine {| p1_wf := hwf; p1_at_loop := Hppc; p1_code := _; p1_a0 := _; p1_a1 := _;
              p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
              p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := hposle;
              p1_tbl := _; p1_lab_le := hlable; p1_spec := _ |}.
    + apply (CodeLoaded1_eqmem s); [exact hmemF| exact hcode].
    + rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
    + rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
    + rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
    + rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
    + rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
    + rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
    + apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
    + rewrite H5q, hlq. lia.
    + rewrite hlq. replace (length inp - (length inp - q))%nat with q by lia. reflexivity.
    + rewrite (hothF 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx.
    + apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
    + (* spec telescope through the comment skip and the newline *)
      assert (hconsq : skipn q inp = nth q inp 0 :: skipn (S q) inp)
        by (apply skipn_cons_nth; lia).
      rewrite hconsq, Hq2.
      change (zin (10 :: skipn (S q) inp)) with (10%nat :: zin (skipn (S q) inp)).
      rewrite (scan1_spacing 10%nat (zin (skipn (S q) inp)) lab pos
                 ltac:(reflexivity) ltac:(reflexivity)).
      rewrite <- Hqskip, hsufx.
      rewrite <- (scan1_comment (Z.to_nat c) (zin rest') lab pos hcm).
      change (Z.to_nat c :: zin rest') with (zin (c :: rest')).
      exact hspec.
  - (* EOF -> pass-2 entry; the scan is complete and Ok *)
    exists (4 + (kb + k))%nat. right.
    rewrite (runUntil_add 4 (kb + k)), hs4, (runUntil_add kb k). fold sB.
    set (sF := runUntil 0 k sB) in *.
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget sF i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (Hothq i h5 h7 h28), (hbother i h28),
              (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemF : sF.(mem) = s.(mem)) by (rewrite Hmemq; exact hmemB).
    split; [unfold idx1 in *; simpl length in *; lia|].
    assert (hscan : scan1 High1 noLabels 0 (zin inp) = (lab, pos, Ok1)).
    { rewrite <- hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      rewrite (scan1_comment (Z.to_nat c) (zin rest') lab pos hcm).
      rewrite hsufx in Hskip0. rewrite Hskip0. apply scan1_nil. }
    refine {| p2s_wf := hwf; p2s_pc := Hppc; p2s_code := _; p2s_a0 := _; p2s_a1 := _;
              p2s_a2 := _; p2s_a3 := _; p2s_a4 := _; p2s_ra := _; p2s_in_mem := _;
              p2s_tbl := _; p2s_m_le := hposle; p2s_lab_le := hlable;
              p2s_scan_ok := hscan |}.
    + apply (CodeLoaded1_eqmem s); [exact hmemF| exact hcode].
    + rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
    + rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
    + rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
    + rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
    + rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
    + rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
    + apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
    + apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
Qed.

(** ** Pass-1 iteration: label definitions (`:l`), plus the Result1 builder
    for the empty-output error exits. *)

(* package a Result1 from a halted error-exit state (output empty) *)
Lemma error_result1 : forall f inp cap labf m st,
  scan1 High1 noLabels 0 (zin inp) = (labf, m, st) ->
  st <> Ok1 ->
  Z.of_nat m <= cap ->
  f.(pc) = 0 -> rget f 10 = Z.of_nat (statusCode1 st) -> rget f 11 = 0 ->
  Result1 f inp cap.
Proof.
  intros f inp cap labf m st hscan hne hm hpc h10 h11.
  assert (hcapm : (Z.to_nat cap <? m)%nat = false)
    by (apply Nat.ltb_ge; lia).
  assert (hcs : coreSpec1 (zin inp) (Z.to_nat cap) = (statusCode1 st, [], 0%nat)).
  { unfold coreSpec1, decode1. rewrite hscan.
    destruct st; try congruence; rewrite hcapm; reflexivity. }
  unfold Result1. rewrite hcs.
  repeat apply conj; [exact hpc| exact h10| exact h11| reflexivity].
Qed.

(* spec-side colon unfolds *)
Lemma scan1_colon lab pos rest :
  scan1 High1 lab pos (58%nat :: rest) = scan1 Col1 lab pos rest.
Proof. simp scan1. reflexivity. Qed.

Lemma scan1_col_nil lab pos : scan1 Col1 lab pos [] = (lab, pos, TrailTok1).
Proof. now simp scan1. Qed.

Lemma scan1_col_cons lab pos lc rest :
  scan1 Col1 lab pos (lc :: rest)
  = match lab lc with
    | Some _ => (lab, pos, Dup1)
    | None => scan1 High1 (setLabel lab lc pos) pos rest
    end.
Proof. now simp scan1. Qed.

(* dispatch 52 -> 264 for ':' (5 not-taken blocks + 1 taken): 12 steps *)
Lemma p1_colon_tail s4 :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 52 -> rget s4 7 = 58 ->
  exists s', runUntil 0 12 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 264 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc ht2.
  pose proof (li1_beq_ne s4 52 35 58 276 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (52 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 60) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = 58) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  pose proof (li1_beq_ne sB 60 59 58 268 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (60 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 68) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = 58) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 68 10 58 (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (68 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 76) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = 58) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 76 32 58 (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (76 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 84) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = 58) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 84 95 58 (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (84 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 92) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = 58) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_eq sF 92 58 58 168 (Image1.coreAddr + 264) hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl
    ltac:(rewrite (wadd_id (Image1.coreAddr + (92 + 4)) 168
            ltac:(unfold Image1.coreAddr; lia)); lia)) as hb6.
  exists (setPc (rset sF 28 58) (Image1.coreAddr + 264)).
  split.
  { replace 12%nat with (2 + (2 + (2 + (2 + (2 + 2)))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
            runUntil_add, hb4, runUntil_add, hb5, hb6. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold sF. rewrite setPc_mem, rset_mem.
    unfold sE. rewrite setPc_mem, rset_mem. unfold sD. rewrite setPc_mem, rset_mem.
    unfold sC. rewrite setPc_mem, rset_mem. unfold sB. rewrite setPc_mem, rset_mem.
    reflexivity.
  - apply (CodeLoaded1_eqmem sF);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcF].
  - intros i hi. rewrite (li_block_frame sF 58 _ i hi).
    unfold sF. rewrite (li_block_frame sE 95 _ i hi).
    unfold sE. rewrite (li_block_frame sD 32 _ i hi).
    unfold sD. rewrite (li_block_frame sC 10 _ i hi).
    unfold sC. rewrite (li_block_frame sB 59 _ i hi).
    unfold sB. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* A COMPLETE pass-1 iteration for a label definition (':l'): prefix +
   dispatch to 264 + the slot test. Outcomes: fresh label installed (back to
   the loop head, 2 chars consumed), duplicate (exit 688), EOF (exit 712). *)
Lemma p1_labelDef : forall inp cap rest' lab pos s,
  P1Inv inp cap s lab pos (58 :: rest') ->
  exists k,
    (exists rest2 lab2, (length rest2 < length ((58:Z) :: rest'))%nat /\
        (k <= 50 * (length ((58:Z) :: rest') - length rest2))%nat /\
        P1Inv inp cap (runUntil 0 k s) lab2 pos rest2)
    \/ ((k <= 50 * length ((58:Z) :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap rest' lab pos s inv. pose proof inv as inv0.
  destruct (p1_prefix inp cap 58 rest' lab pos s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct (p1_colon_tail s4 hcode4 hpc4 ht2)
    as (sL & hrunT & hpcL & hmemL & hcodeL & hothL).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf. pose proof (cap_nonneg _ _ hwf) as hcap0.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp 58 rest'); exact hsuf).
  assert (h5L : rget sL 5 = Z.of_nat idx1).
  { rewrite (hothL 5 ltac:(lia)), ht0. unfold idx1. lia. }
  assert (hothLS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
            rget sL i = rget s i).
  { intros i h0 h5 h7 h28.
    rewrite (hothL i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
  assert (hmemLS : sL.(mem) = s.(mem)) by (rewrite hmemL; exact hmem4).
  assert (ha1L : rget sL 11 = Z.of_nat (length inp))
    by (rewrite (hothLS 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1).
  assert (hraL : rget sL 1 = 0)
    by (rewrite (hothLS 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
  assert (hrun16 : runUntil 0 16 s = sL).
  { replace 16%nat with (4 + 12)%nat by lia.
    rewrite runUntil_add, hrun4, hrunT. reflexivity. }
  destruct rest' as [|l rest''].
  - (* EOF after ':' -> TrailTok exit (712) *)
    assert (hidx1 : idx1 = length inp) by (unfold idx1; simpl; lia).
    assert (hbt : step sL = setPc sL (Image1.coreAddr + 712)).
    { apply (bgeu1_eq_taken sL 264 5 11 (Z.of_nat (length inp)) 448 _ hcodeL ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcL
        ltac:(rewrite h5L, hidx1; reflexivity) ha1L ltac:(vm_compute; reflexivity)).
      rewrite (wadd_id (Image1.coreAddr + 264) 448 ltac:(unfold Image1.coreAddr; lia)).
      lia. }
    set (sX := setPc sL (Image1.coreAddr + 712)) in *.
    assert (hcodeX : CodeLoaded1 sX)
      by (apply (CodeLoaded1_eqmem sL); [reflexivity| exact hcodeL]).
    assert (hpcX : sX.(pc) = Image1.coreAddr + 712) by reflexivity.
    assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraL).
    destruct (exit_zero sX 712 8 hcodeX ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                hpcX hraX ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(lia))
      as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
    exists (16 + (1 + 3))%nat. right. split; [simpl length; lia|].
    rewrite (runUntil_add 16 (1+3)), hrun16.
    assert (hpL0 : sL.(pc) <> 0) by (rewrite hpcL; unfold Image1.coreAddr; lia).
    rewrite (runUntil_add 1 3), (runUntil_one sL hpL0), hbt. fold sX. rewrite hrunE.
    apply (error_result1 f inp cap lab pos TrailTok1).
    + rewrite <- hspec. change (zin (58 :: nil)) with (58%nat :: @nil nat).
      rewrite scan1_colon. apply scan1_col_nil.
    + discriminate.
    + exact hposle.
    + exact hfpc.
    + exact hf10.
    + exact hf11.
  - (* read the label byte l *)
    assert (hidxlt : (idx1 < length inp)%nat) by (unfold idx1; simpl length in *; lia).
    assert (Hl : nth idx1 inp 0 = l).
    { transitivity (nth 0 (skipn idx1 inp) 0).
      - rewrite nth_skipn. f_equal. lia.
      - rewrite hsufx. reflexivity. }
    assert (HinL : In l inp).
    { rewrite <- (firstn_skipn idx1 inp). apply in_or_app. right.
      rewrite hsufx. left; reflexivity. }
    assert (Hlr : 0 <= l < 256) by (apply (bytes_ok1 _ _ hwf); exact HinL).
    assert (hl' : Z.of_nat (Z.to_nat l) = l) by (apply Z2Nat.id; lia).
    set (l' := Z.to_nat l) in *.
    assert (hl256 : (l' < 256)%nat) by (unfold l'; lia).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
    (* step: bgeu NOT taken at 264 *)
    assert (hult : ultb (rget sL 5) (rget sL 11) = true).
    { rewrite h5L, ha1L. unfold ultb. apply Z.ltb_lt. lia. }
    assert (hu1 : step sL = setPc sL (2147483792 + 268)).
    { rewrite (step1_bgeu sL 264 5 11 448 hcodeL ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcL ltac:(vm_compute; reflexivity)), hult.
      cbn match. rewrite hpcL, (wadd_id (2147483792 + 264) 4 ltac:(lia)).
      f_equal; lia. }
    set (sM1 := setPc sL (2147483792 + 268)) in *.
    assert (hc1 : CodeLoaded1 sM1)
      by (apply (CodeLoaded1_eqmem sL); [reflexivity| exact hcodeL]).
    assert (hpc1 : sM1.(pc) = 2147483792 + 268) by reflexivity.
    (* step: add t3,a0,t0 *)
    assert (ha0L : rget sM1 10 = 2147484516).
    { unfold sM1. rewrite setPc_rget.
      rewrite (hothLS 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha0. }
    assert (haddr : wadd (rget sM1 10) (rget sM1 5) = 2147484516 + Z.of_nat idx1).
    { rewrite ha0L. unfold sM1. rewrite setPc_rget, h5L. apply wadd_id. lia. }
    assert (hu2 : step sM1 = setPc (rset sM1 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 272)).
    { rewrite (step1_add sM1 268 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc1 ltac:(vm_compute; reflexivity)), haddr, hpc1,
        (wadd_id (2147483792 + 268) 4 ltac:(lia)). f_equal; lia. }
    set (sM2 := setPc (rset sM1 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 272)) in *.
    assert (hmem2 : sM2.(mem) = s.(mem))
      by (unfold sM2, sM1; rewrite setPc_mem, rset_mem, setPc_mem; exact hmemLS).
    assert (hc2 : CodeLoaded1 sM2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
    assert (hpc2 : sM2.(pc) = 2147483792 + 272) by reflexivity.
    (* step: lbu t2,0(t3) *)
    assert (hr28_2 : rget sM2 28 = 2147484516 + Z.of_nat idx1).
    { unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hbyteIn : s.(mem) (2147484516 + Z.of_nat idx1) = nth idx1 inp 0).
    { pose proof (hinm (Z.of_nat idx1) ltac:(lia)) as h.
      unfold Image1.inputAddr in h. rewrite Nat2Z.id in h. exact h. }
    assert (hbyte : sM2.(mem) (wadd (rget sM2 28) 0) mod 256 = l).
    { rewrite hr28_2, (wadd_id (2147484516 + Z.of_nat idx1) 0 ltac:(lia)), Z.add_0_r,
        hmem2, hbyteIn, Hl. apply Z.mod_small. exact Hlr. }
    assert (hu3 : step sM2 = setPc (rset sM2 7 l) (2147483792 + 276)).
    { rewrite (step1_lbu sM2 272 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc2 ltac:(vm_compute; reflexivity)), hbyte, hpc2,
        (wadd_id (2147483792 + 272) 4 ltac:(lia)). f_equal; lia. }
    set (sM3 := setPc (rset sM2 7 l) (2147483792 + 276)) in *.
    assert (hmem3 : sM3.(mem) = s.(mem))
      by (unfold sM3; rewrite setPc_mem, rset_mem; exact hmem2).
    assert (hc3 : CodeLoaded1 sM3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
    assert (hpc3 : sM3.(pc) = 2147483792 + 276) by reflexivity.
    (* step: addi t0,t0,1 *)
    assert (hr5_3 : rget sM3 5 = Z.of_nat idx1).
    { unfold sM3. rewrite setPc_rget, (rset_rget sM2 7 l 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 7) with false by reflexivity.
      unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 28) with false by reflexivity.
      unfold sM1. rewrite setPc_rget. exact h5L. }
    assert (hu4 : step sM3 = setPc (rset sM3 5 (Z.of_nat idx1 + 1)) (2147483792 + 280)).
    { rewrite (step1_addi sM3 276 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc3 ltac:(vm_compute; reflexivity)), hr5_3,
        (wadd_id (Z.of_nat idx1) 1 ltac:(lia)), hpc3,
        (wadd_id (2147483792 + 276) 4 ltac:(lia)). f_equal; lia. }
    set (sM4 := setPc (rset sM3 5 (Z.of_nat idx1 + 1)) (2147483792 + 280)) in *.
    assert (hmem4' : sM4.(mem) = s.(mem))
      by (unfold sM4; rewrite setPc_mem, rset_mem; exact hmem3).
    assert (hc4 : CodeLoaded1 sM4) by (apply (CodeLoaded1_eqmem s); [exact hmem4'| exact hcode]).
    assert (hpc4' : sM4.(pc) = 2147483792 + 280) by reflexivity.
    (* step: slli t3,t2,3 *)
    assert (hr7_4 : rget sM4 7 = l).
    { unfold sM4. rewrite setPc_rget, (rset_rget sM3 5 _ 7 ltac:(lia) ltac:(lia)).
      replace (7 =? 5) with false by reflexivity.
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 7 l 7 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hu5 : step sM4 = setPc (rset sM4 28 (8 * l)) (2147483792 + 284)).
    { rewrite (step1_slli sM4 280 28 7 3 hc4 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc4' ltac:(vm_compute; reflexivity)), hr7_4, (wshl3 l Hlr), hpc4',
        (wadd_id (2147483792 + 280) 4 ltac:(lia)). f_equal; lia. }
    set (sM5 := setPc (rset sM4 28 (8 * l)) (2147483792 + 284)) in *.
    assert (hmem5 : sM5.(mem) = s.(mem))
      by (unfold sM5; rewrite setPc_mem, rset_mem; exact hmem4').
    assert (hc5 : CodeLoaded1 sM5) by (apply (CodeLoaded1_eqmem s); [exact hmem5| exact hcode]).
    assert (hpc5 : sM5.(pc) = 2147483792 + 284) by reflexivity.
    (* step: add t3,t3,a4 *)
    assert (hr28_5 : rget sM5 28 = 8 * l).
    { unfold sM5. rewrite setPc_rget, (rset_rget sM4 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (ha4_5 : rget sM5 14 = 2147489280).
    { unfold sM5. rewrite setPc_rget, (rset_rget sM4 28 _ 14 ltac:(lia) ltac:(lia)).
      replace (14 =? 28) with false by reflexivity.
      unfold sM4. rewrite setPc_rget, (rset_rget sM3 5 _ 14 ltac:(lia) ltac:(lia)).
      replace (14 =? 5) with false by reflexivity.
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 7 l 14 ltac:(lia) ltac:(lia)).
      replace (14 =? 7) with false by reflexivity.
      unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ 14 ltac:(lia) ltac:(lia)).
      replace (14 =? 28) with false by reflexivity.
      unfold sM1. rewrite setPc_rget.
      rewrite (hothLS 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha4. }
    assert (hslot : wadd (rget sM5 28) (rget sM5 14) = 2147489280 + 8 * Z.of_nat l').
    { rewrite hr28_5, ha4_5, (wadd_id (8 * l) 2147489280 ltac:(lia)).
      rewrite hl'. lia. }
    assert (hu6 : step sM5 = setPc (rset sM5 28 (2147489280 + 8 * Z.of_nat l'))
                                   (2147483792 + 288)).
    { rewrite (step1_add sM5 284 28 28 14 hc5 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc5 ltac:(vm_compute; reflexivity)), hslot, hpc5,
        (wadd_id (2147483792 + 284) 4 ltac:(lia)). f_equal; lia. }
    set (sM6 := setPc (rset sM5 28 (2147489280 + 8 * Z.of_nat l')) (2147483792 + 288)) in *.
    assert (hmem6 : sM6.(mem) = s.(mem))
      by (unfold sM6; rewrite setPc_mem, rset_mem; exact hmem5).
    assert (hc6 : CodeLoaded1 sM6) by (apply (CodeLoaded1_eqmem s); [exact hmem6| exact hcode]).
    assert (hpc6 : sM6.(pc) = 2147483792 + 288) by reflexivity.
    (* step: ld t4,0(t3) reads the slot *)
    assert (hr28_6 : rget sM6 28 = 2147489280 + 8 * Z.of_nat l').
    { unfold sM6. rewrite setPc_rget, (rset_rget sM5 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hslotrange : 0 <= encodeSlot (lab l') < 2 ^ 64).
    { destruct (lab l') as [p|] eqn:Elab; cbn.
      - pose proof (hlable l' p Elab). lia.
      - lia. }
    assert (htblS : TableLoaded sM6 lab)
      by (apply (tableLoaded_eqmem s); [exact hmem6| exact htbl]).
    assert (hldval : loadWord sM6 (wadd (rget sM6 28) 0) = encodeSlot (lab l')).
    { rewrite hr28_6, (wadd_id (2147489280 + 8 * Z.of_nat l') 0 ltac:(lia)), Z.add_0_r.
      pose proof (loadWord_slot sM6 lab l' htblS hl256 hslotrange) as h.
      unfold Image1.lblAddr in h. exact h. }
    assert (hu7 : step sM6 = setPc (rset sM6 29 (encodeSlot (lab l'))) (2147483792 + 292)).
    { rewrite (step1_ld sM6 288 29 28 0 hc6 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc6 ltac:(vm_compute; reflexivity)), hldval, hpc6,
        (wadd_id (2147483792 + 288) 4 ltac:(lia)). f_equal; lia. }
    set (sM7 := setPc (rset sM6 29 (encodeSlot (lab l'))) (2147483792 + 292)) in *.
    assert (hmem7 : sM7.(mem) = s.(mem))
      by (unfold sM7; rewrite setPc_mem, rset_mem; exact hmem6).
    assert (hc7 : CodeLoaded1 sM7) by (apply (CodeLoaded1_eqmem s); [exact hmem7| exact hcode]).
    assert (hpc7 : sM7.(pc) = 2147483792 + 292) by reflexivity.
    assert (hr29_7 : rget sM7 29 = encodeSlot (lab l')).
    { unfold sM7. rewrite setPc_rget, (rset_rget sM6 29 _ 29 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    (* assemble the 7 steps 264..288 *)
    assert (hpL : sL.(pc) <> 0) by (rewrite hpcL; lia).
    assert (hp1 : sM1.(pc) <> 0) by (rewrite hpc1; lia).
    assert (hp2 : sM2.(pc) <> 0) by (rewrite hpc2; lia).
    assert (hp3 : sM3.(pc) <> 0) by (rewrite hpc3; lia).
    assert (hp4 : sM4.(pc) <> 0) by (rewrite hpc4'; lia).
    assert (hp5 : sM5.(pc) <> 0) by (rewrite hpc5; lia).
    assert (hp6 : sM6.(pc) <> 0) by (rewrite hpc6; lia).
    assert (hrun7 : runUntil 0 7 sL = sM7).
    { rewrite (runUntil_S 6 sL hpL), hu1, (runUntil_S 5 sM1 hp1), hu2,
              (runUntil_S 4 sM2 hp2), hu3, (runUntil_S 3 sM3 hp3), hu4,
              (runUntil_S 2 sM4 hp4), hu5, (runUntil_S 1 sM5 hp5), hu6,
              (runUntil_S 0 sM6 hp6), hu7. reflexivity. }
    (* the register frame from s to sM7 (clobbers 5,7,28,29) *)
    assert (hoth7 : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> i <> 29 ->
              rget sM7 i = rget s i).
    { intros i h0 h5 h7 h28 h29.
      unfold sM7. rewrite setPc_rget, (rset_rget sM6 29 _ i ltac:(lia) h0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sM6. rewrite setPc_rget, (rset_rget sM5 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sM5. rewrite setPc_rget, (rset_rget sM4 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sM4. rewrite setPc_rget, (rset_rget sM3 5 _ i ltac:(lia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 7 l i ltac:(lia) h0).
      replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
      unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sM1. rewrite setPc_rget.
      exact (hothLS i h0 h5 h7 h28). }
    assert (hr5_7 : rget sM7 5 = Z.of_nat idx1 + 1).
    { unfold sM7. rewrite setPc_rget, (rset_rget sM6 29 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 29) with false by reflexivity.
      unfold sM6. rewrite setPc_rget, (rset_rget sM5 28 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 28) with false by reflexivity.
      unfold sM5. rewrite setPc_rget, (rset_rget sM4 28 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 28) with false by reflexivity.
      unfold sM4. rewrite setPc_rget, (rset_rget sM3 5 _ 5 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hraM : rget sM7 1 = 0)
      by (rewrite (hoth7 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
    (* spec unfolding through ':' and the label byte *)
    assert (hspec2 : scan1 Col1 lab pos (l' :: zin rest'') = scan1 High1 noLabels 0 (zin inp)).
    { rewrite <- hspec.
      change (zin (58 :: l :: rest'')) with (58%nat :: zin (l :: rest'')).
      rewrite scan1_colon.
      change (zin (l :: rest'')) with (Z.to_nat l :: zin rest''). reflexivity. }
    destruct (lab l') as [p|] eqn:Elab.
    + (* duplicate -> exit 688 *)
      assert (hp63 : Z.of_nat p < 2 ^ 63).
      { pose proof (hlable l' p Elab). lia. }
      assert (hslt : sltb (rget sM7 29) (rget sM7 0) = false).
      { rewrite hr29_7, rget_zero. exact (encodeSlot_some_nonneg p hp63). }
      assert (hu8 : step sM7 = setPc sM7 (2147483792 + 688)).
      { rewrite (step1_bge sM7 292 29 0 396 hc7 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc7 ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpc7, (wadd_id (2147483792 + 292) 396 ltac:(lia)).
        f_equal; lia. }
      set (sX := setPc sM7 (2147483792 + 688)) in *.
      assert (hcodeX : CodeLoaded1 sX)
        by (apply (CodeLoaded1_eqmem sM7); [reflexivity| exact hc7]).
      assert (hpcX : sX.(pc) = Image1.coreAddr + 688) by (unfold Image1.coreAddr; reflexivity).
      assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraM).
      destruct (exit_zero sX 688 6 hcodeX ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                  hpcX hraX ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(lia))
        as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
      exists (16 + (7 + (1 + 3)))%nat. right. split; [simpl length; lia|].
      rewrite (runUntil_add 16 (7 + (1 + 3))), hrun16,
              (runUntil_add 7 (1 + 3)), hrun7.
      assert (hp7 : sM7.(pc) <> 0) by (rewrite hpc7; lia).
      rewrite (runUntil_add 1 3), (runUntil_one sM7 hp7), hu8. fold sX. rewrite hrunE.
      apply (error_result1 f inp cap lab pos Dup1).
      * rewrite <- hspec2, scan1_col_cons, Elab. reflexivity.
      * discriminate.
      * exact hposle.
      * exact hfpc.
      * exact hf10.
      * exact hf11.
    + (* fresh label -> sd; j 36; invariant with setLabel *)
      assert (hslt : sltb (rget sM7 29) (rget sM7 0) = true).
      { rewrite hr29_7, rget_zero. exact encodeSlot_none_neg. }
      assert (hu8 : step sM7 = setPc sM7 (2147483792 + 296)).
      { rewrite (step1_bge sM7 292 29 0 396 hc7 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc7 ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpc7, (wadd_id (2147483792 + 292) 4 ltac:(lia)).
        f_equal; lia. }
      set (sM8 := setPc sM7 (2147483792 + 296)) in *.
      assert (hc8 : CodeLoaded1 sM8)
        by (apply (CodeLoaded1_eqmem sM7); [reflexivity| exact hc7]).
      assert (hpc8 : sM8.(pc) = 2147483792 + 296) by reflexivity.
      assert (hr28_8 : rget sM8 28 = 2147489280 + 8 * Z.of_nat l').
      { unfold sM8. rewrite setPc_rget.
        unfold sM7. rewrite setPc_rget, (rset_rget sM6 29 _ 28 ltac:(lia) ltac:(lia)).
        replace (28 =? 29) with false by reflexivity. exact hr28_6. }
      assert (hr6_8 : rget sM8 6 = Z.of_nat pos).
      { unfold sM8. rewrite setPc_rget.
        rewrite (hoth7 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        exact houtidx. }
      (* sd t1,0(t3): install the slot *)
      assert (hu9 : step sM8 = setPc (storeWord sM8 (2147489280 + 8 * Z.of_nat l')
                                        (Z.of_nat pos)) (2147483792 + 300)).
      { rewrite (step1_sd sM8 296 28 6 0 hc8 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc8 ltac:(vm_compute; reflexivity)),
          hr28_8, hr6_8,
          (wadd_id (2147489280 + 8 * Z.of_nat l') 0 ltac:(lia)), Z.add_0_r, hpc8,
          (wadd_id (2147483792 + 296) 4 ltac:(lia)). f_equal; lia. }
      set (sM9 := setPc (storeWord sM8 (2147489280 + 8 * Z.of_nat l') (Z.of_nat pos))
                        (2147483792 + 300)) in *.
      assert (hpc9 : sM9.(pc) = 2147483792 + 300) by reflexivity.
      assert (hmem8 : sM8.(mem) = s.(mem)) by (unfold sM8; rewrite setPc_mem; exact hmem7).
      assert (hc9 : CodeLoaded1 sM9).
      { apply (CodeLoaded1_eqmem (storeWord sM8 (2147489280 + 8 * Z.of_nat l')
                  (Z.of_nat pos))); [reflexivity|].
        apply codeLoaded1_storeWord;
          [apply (CodeLoaded1_eqmem s); [exact hmem8| exact hcode]|].
        unfold Image1.coreAddr. lia. }
      (* jal back to the loop head *)
      assert (hu10 : step sM9 = setPc sM9 (2147483792 + 36)).
      { rewrite (step1_jal sM9 300 0 (-264) hc9 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc9 ltac:(vm_compute; reflexivity)),
          rset_zero, hpc9, (wadd_id (2147483792 + 300) (-264) ltac:(lia)).
        f_equal; lia. }
      set (sF := setPc sM9 (2147483792 + 36)) in *.
      assert (hp7 : sM7.(pc) <> 0) by (rewrite hpc7; lia).
      assert (hp8 : sM8.(pc) <> 0) by (rewrite hpc8; lia).
      assert (hp9 : sM9.(pc) <> 0) by (rewrite hpc9; lia).
      assert (hrunF : runUntil 0 (16 + (7 + 3)) s = sF).
      { rewrite (runUntil_add 16 (7 + 3)), hrun16, (runUntil_add 7 3), hrun7,
                (runUntil_S 2 sM7 hp7), hu8, (runUntil_S 1 sM8 hp8), hu9,
                (runUntil_S 0 sM9 hp9), hu10. reflexivity. }
      exists (16 + (7 + 3))%nat. left. exists rest''. exists (setLabel lab l' pos).
      rewrite hrunF.
      assert (hmemF : sF.(mem) = (storeWord sM8 (2147489280 + 8 * Z.of_nat l')
                                    (Z.of_nat pos)).(mem))
        by reflexivity.
      assert (hrF : forall i, i <> 0 -> rget sF i = rget sM7 i).
      { intros i h0. unfold sF. rewrite setPc_rget. unfold sM9.
        rewrite setPc_rget, storeWord_rget. unfold sM8. rewrite setPc_rget. reflexivity. }
      assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> i <> 29 ->
                rget sF i = rget s i).
      { intros i h0 h5 h7 h28 h29. rewrite (hrF i h0).
        exact (hoth7 i h0 h5 h7 h28 h29). }
      split; [simpl length; lia| split; [simpl length; lia|]].
      assert (hsufx2 : skipn (S idx1) inp = rest'').
      { replace (S idx1) with (1 + idx1)%nat by lia.
        rewrite <- skipn_skipn, hsufx. reflexivity. }
      refine {| p1_wf := hwf; p1_at_loop := _; p1_code := _; p1_a0 := _; p1_a1 := _;
                p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
                p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := hposle;
                p1_tbl := _; p1_lab_le := _; p1_spec := _ |}.
      * apply setPc_pc.
      * apply (CodeLoaded1_eqmem sM9); [reflexivity| exact hc9].
      * rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
      * rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
      * rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
      * rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
      * rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
      * rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
      * (* input intact through the slot store *)
        apply (inputLoaded_eqmem (storeWord sM8 (2147489280 + 8 * Z.of_nat l')
                 (Z.of_nat pos))); [exact hmemF|].
        apply inputLoaded_storeWord;
          [apply (inputLoaded_eqmem s); [exact hmem8| exact hinm]|].
        unfold Image1.inputAddr. lia.
      * rewrite (hrF 5 ltac:(lia)), hr5_7. simpl length.
        unfold idx1. simpl length in *. lia.
      * replace (length inp - length rest'')%nat with (S idx1)
          by (unfold idx1; simpl length in *; lia).
        exact hsufx2.
      * rewrite (hrF 6 ltac:(lia)).
        rewrite (hoth7 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        exact houtidx.
      * (* table now holds setLabel lab l' pos *)
        apply (tableLoaded_eqmem (storeWord sM8 (2147489280 + 8 * Z.of_nat l')
                 (Z.of_nat pos))); [exact hmemF|].
        pose proof (storeWord_slot sM8 lab l' pos
          ltac:(apply (tableLoaded_eqmem s); [exact hmem8| exact htbl]) hl256) as h.
        unfold Image1.lblAddr in h. exact h.
      * (* lab_le for the extended map *)
        intros c0 p0 hc0. unfold setLabel in hc0.
        destruct (Nat.eqb_spec c0 l') as [->|hne].
        -- inversion hc0; subst p0; lia.
        -- exact (hlable c0 p0 hc0).
      * (* the scan telescope through the fresh definition *)
        rewrite <- hspec2, scan1_col_cons, Elab. reflexivity.
Qed.

(** ** Pass-1 iteration: label references (`%l`), plus the scan-position
    monotonicity that justifies the Short exit. *)

(* spec-side pct unfolds *)
Lemma scan1_pct lab pos rest :
  scan1 High1 lab pos (37%nat :: rest) = scan1 Pct1 lab pos rest.
Proof. simp scan1. reflexivity. Qed.

Lemma scan1_pct_nil lab pos : scan1 Pct1 lab pos [] = (lab, pos, TrailTok1).
Proof. now simp scan1. Qed.

Lemma scan1_pct_cons lab pos lc rest :
  scan1 Pct1 lab pos (lc :: rest) = scan1 High1 lab (pos + 4) rest.
Proof. now simp scan1. Qed.

(* the scan position never decreases (CAP-FREE spec; the machine shorts
   iff the position would cross cap) *)
Lemma scan1_pos_le_n : forall n (l : list nat) st lab pos labf m stat,
  (length l <= n)%nat ->
  scan1 st lab pos l = (labf, m, stat) -> (pos <= m)%nat.
Proof.
  induction n; intros l st lab pos labf m stat hlen heq.
  - destruct l; [| simpl in hlen; lia].
    destruct st; autorewrite with scan1 in heq; inversion heq; subst; lia.
  - destruct l as [|c rest].
    + destruct st; autorewrite with scan1 in heq; inversion heq; subst; lia.
    + destruct st.
      * autorewrite with scan1 in heq.
        destruct (isComment c) eqn:E1.
        -- pose proof (skipComment_len rest) as hsk. simpl in hlen.
           exact (IHn (skipComment rest) High1 lab pos labf m stat ltac:(lia) heq).
        -- destruct (isSpace c) eqn:E2.
           ++ simpl in hlen.
              exact (IHn rest High1 lab pos labf m stat ltac:(lia) heq).
           ++ destruct (c =? c_colon)%nat eqn:E3.
              ** simpl in hlen.
                 exact (IHn rest Col1 lab pos labf m stat ltac:(lia) heq).
              ** destruct (c =? c_pct)%nat eqn:E4.
                 --- simpl in hlen.
                     exact (IHn rest Pct1 lab pos labf m stat ltac:(lia) heq).
                 --- destruct (nibble c) eqn:E5.
                     +++ simpl in hlen.
                         exact (IHn rest (Low1 n0) lab pos labf m stat ltac:(lia) heq).
                     +++ inversion heq; subst; lia.
      * autorewrite with scan1 in heq.
        destruct (isLowStop1 c) eqn:E1; [inversion heq; subst; lia|].
        destruct (nibble c) eqn:E2.
        -- simpl in hlen.
           pose proof (IHn rest High1 lab (pos + 1)%nat labf m stat ltac:(lia) heq). lia.
        -- inversion heq; subst; lia.
      * autorewrite with scan1 in heq.
        destruct (lab c) eqn:E1; [inversion heq; subst; lia|].
        simpl in hlen.
        exact (IHn rest High1 (setLabel lab c pos) pos labf m stat ltac:(lia) heq).
      * autorewrite with scan1 in heq. simpl in hlen.
        pose proof (IHn rest High1 lab (pos + 4)%nat labf m stat ltac:(lia) heq). lia.
Qed.

Lemma scan1_pos_le : forall (l : list nat) st lab pos labf m stat,
  scan1 st lab pos l = (labf, m, stat) -> (pos <= m)%nat.
Proof. intros l st lab pos labf m stat. apply (scan1_pos_le_n (length l)). lia. Qed.

(* package a Result1 for the Short exit: the spec shorts iff cap < m *)
Lemma short_result1 : forall f inp cap labf m st,
  scan1 High1 noLabels 0 (zin inp) = (labf, m, st) ->
  cap < Z.of_nat m -> 0 <= cap ->
  f.(pc) = 0 -> rget f 10 = 2 -> rget f 11 = 0 ->
  Result1 f inp cap.
Proof.
  intros f inp cap labf m st hscan hm hcap hpc h10 h11.
  assert (hcapm : (Z.to_nat cap <? m)%nat = true)
    by (apply Nat.ltb_lt; lia).
  assert (hcs : coreSpec1 (zin inp) (Z.to_nat cap) = (2%nat, [], 0%nat)).
  { unfold coreSpec1, decode1. rewrite hscan.
    destruct st; try (rewrite hcapm; reflexivity).
    destruct (emit1 High1 labf 0 (zin inp)) as [out st'].
    rewrite hcapm. reflexivity. }
  unfold Result1. rewrite hcs.
  repeat apply conj; [exact hpc| exact h10| exact h11| reflexivity].
Qed.

(* dispatch 52 -> 304 for '%' (6 not-taken blocks + 1 taken): 14 steps *)
Lemma p1_pct_tail s4 :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 52 -> rget s4 7 = 37 ->
  exists s', runUntil 0 14 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 304 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc ht2.
  pose proof (li1_beq_ne s4 52 35 37 276 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (52 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 60) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = 37) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  pose proof (li1_beq_ne sB 60 59 37 268 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (60 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 68) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = 37) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 68 10 37 (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (68 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 76) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = 37) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 76 32 37 (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (76 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 84) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = 37) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 84 95 37 (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (84 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 92) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = 37) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_ne sF 92 58 37 168 hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
  set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (92 + 8))) in *.
  assert (hcG : CodeLoaded1 sG) by
    (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
  assert (hpcG : sG.(pc) = Image1.coreAddr + 100) by (unfold sG; cbn; lia).
  assert (h7G : rget sG 7 = 37) by
    (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
  pose proof (li1_beq_eq sG 100 37 37 200 (Image1.coreAddr + 304) hcG ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl
    ltac:(rewrite (wadd_id (Image1.coreAddr + (100 + 4)) 200
            ltac:(unfold Image1.coreAddr; lia)); lia)) as hb7.
  exists (setPc (rset sG 28 37) (Image1.coreAddr + 304)).
  split.
  { replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + 2))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
            runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold sG. rewrite setPc_mem, rset_mem.
    unfold sF. rewrite setPc_mem, rset_mem. unfold sE. rewrite setPc_mem, rset_mem.
    unfold sD. rewrite setPc_mem, rset_mem. unfold sC. rewrite setPc_mem, rset_mem.
    unfold sB. rewrite setPc_mem, rset_mem. reflexivity.
  - apply (CodeLoaded1_eqmem sG);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcG].
  - intros i hi. rewrite (li_block_frame sG 37 _ i hi).
    unfold sG. rewrite (li_block_frame sF 58 _ i hi).
    unfold sF. rewrite (li_block_frame sE 95 _ i hi).
    unfold sE. rewrite (li_block_frame sD 32 _ i hi).
    unfold sD. rewrite (li_block_frame sC 10 _ i hi).
    unfold sC. rewrite (li_block_frame sB 59 _ i hi).
    unfold sB. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* A COMPLETE pass-1 iteration for a label reference ('%l'): prefix +
   dispatch to 304 + skip the label byte + the capacity test. Outcomes:
   room for the 4 offset bytes (back to the loop head, 2 chars consumed,
   pos+4), short (exit 640), EOF (exit 712). *)
Lemma p1_ref : forall inp cap rest' lab pos s,
  P1Inv inp cap s lab pos (37 :: rest') ->
  exists k,
    (exists rest2 pos2, (length rest2 < length ((37:Z) :: rest'))%nat /\
        (k <= 50 * (length ((37:Z) :: rest') - length rest2))%nat /\
        P1Inv inp cap (runUntil 0 k s) lab pos2 rest2)
    \/ ((k <= 50 * length ((37:Z) :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap rest' lab pos s inv. pose proof inv as inv0.
  destruct (p1_prefix inp cap 37 rest' lab pos s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct (p1_pct_tail s4 hcode4 hpc4 ht2)
    as (sL & hrunT & hpcL & hmemL & hcodeL & hothL).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf. pose proof (cap_nonneg _ _ hwf) as hcap0.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp 37 rest'); exact hsuf).
  assert (h5L : rget sL 5 = Z.of_nat idx1).
  { rewrite (hothL 5 ltac:(lia)), ht0. unfold idx1. lia. }
  assert (hothLS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
            rget sL i = rget s i).
  { intros i h0 h5 h7 h28.
    rewrite (hothL i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
  assert (hmemLS : sL.(mem) = s.(mem)) by (rewrite hmemL; exact hmem4).
  assert (ha1L : rget sL 11 = Z.of_nat (length inp))
    by (rewrite (hothLS 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1).
  assert (hraL : rget sL 1 = 0)
    by (rewrite (hothLS 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
  assert (hrun18 : runUntil 0 18 s = sL).
  { replace 18%nat with (4 + 14)%nat by lia.
    rewrite runUntil_add, hrun4, hrunT. reflexivity. }
  destruct rest' as [|l rest''].
  - (* EOF after '%' -> TrailTok exit (712) *)
    assert (hidx1 : idx1 = length inp) by (unfold idx1; simpl; lia).
    assert (hbt : step sL = setPc sL (Image1.coreAddr + 712)).
    { apply (bgeu1_eq_taken sL 304 5 11 (Z.of_nat (length inp)) 408 _ hcodeL ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcL
        ltac:(rewrite h5L, hidx1; reflexivity) ha1L ltac:(vm_compute; reflexivity)).
      rewrite (wadd_id (Image1.coreAddr + 304) 408 ltac:(unfold Image1.coreAddr; lia)).
      lia. }
    set (sX := setPc sL (Image1.coreAddr + 712)) in *.
    assert (hcodeX : CodeLoaded1 sX)
      by (apply (CodeLoaded1_eqmem sL); [reflexivity| exact hcodeL]).
    assert (hpcX : sX.(pc) = Image1.coreAddr + 712) by reflexivity.
    assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraL).
    destruct (exit_zero sX 712 8 hcodeX ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                hpcX hraX ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(lia))
      as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
    exists (18 + (1 + 3))%nat. right. split; [simpl length; lia|].
    rewrite (runUntil_add 18 (1 + 3)), hrun18.
    assert (hpL0 : sL.(pc) <> 0) by (rewrite hpcL; unfold Image1.coreAddr; lia).
    rewrite (runUntil_add 1 3), (runUntil_one sL hpL0), hbt. fold sX. rewrite hrunE.
    apply (error_result1 f inp cap lab pos TrailTok1).
    + rewrite <- hspec. change (zin (37 :: nil)) with (37%nat :: @nil nat).
      rewrite scan1_pct. apply scan1_pct_nil.
    + discriminate.
    + exact hposle.
    + exact hfpc.
    + exact hf10.
    + exact hf11.
  - (* the label byte is skipped; only the capacity matters *)
    assert (hidxlt : (idx1 < length inp)%nat) by (unfold idx1; simpl length in *; lia).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
    (* spec side: '%' consumes the label byte and advances pos by 4 *)
    assert (hspec2 : scan1 High1 lab ((pos + 4)%nat) (zin rest'')
                     = scan1 High1 noLabels 0 (zin inp)).
    { rewrite <- hspec.
      change (zin (37 :: l :: rest'')) with (37%nat :: zin (l :: rest'')).
      rewrite scan1_pct.
      change (zin (l :: rest'')) with (Z.to_nat l :: zin rest'').
      rewrite scan1_pct_cons. reflexivity. }
    (* step 1 (304): bgeu t0,a1 -- NOT taken *)
    assert (hult : ultb (rget sL 5) (rget sL 11) = true).
    { rewrite h5L, ha1L. unfold ultb. apply Z.ltb_lt. lia. }
    assert (hu1 : step sL = setPc sL (2147483792 + 308)).
    { rewrite (step1_bgeu sL 304 5 11 408 hcodeL ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcL ltac:(vm_compute; reflexivity)), hult.
      cbn match. rewrite hpcL, (wadd_id (2147483792 + 304) 4 ltac:(lia)).
      f_equal; lia. }
    set (sM1 := setPc sL (2147483792 + 308)) in *.
    assert (hmem1 : sM1.(mem) = s.(mem)) by (unfold sM1; rewrite setPc_mem; exact hmemLS).
    assert (hc1 : CodeLoaded1 sM1) by (apply (CodeLoaded1_eqmem s); [exact hmem1| exact hcode]).
    assert (hpc1 : sM1.(pc) = 2147483792 + 308) by reflexivity.
    (* step 2 (308): addi t0,t0,1 -- skip the label byte *)
    assert (hr5_1 : rget sM1 5 = Z.of_nat idx1) by (unfold sM1; rewrite setPc_rget; exact h5L).
    assert (hu2 : step sM1 = setPc (rset sM1 5 (Z.of_nat idx1 + 1)) (2147483792 + 312)).
    { rewrite (step1_addi sM1 308 5 5 1 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc1 ltac:(vm_compute; reflexivity)), hr5_1,
        (wadd_id (Z.of_nat idx1) 1 ltac:(lia)), hpc1,
        (wadd_id (2147483792 + 308) 4 ltac:(lia)). f_equal; lia. }
    set (sM2 := setPc (rset sM1 5 (Z.of_nat idx1 + 1)) (2147483792 + 312)) in *.
    assert (hmem2 : sM2.(mem) = s.(mem))
      by (unfold sM2; rewrite setPc_mem, rset_mem; exact hmem1).
    assert (hc2 : CodeLoaded1 sM2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
    assert (hpc2 : sM2.(pc) = 2147483792 + 312) by reflexivity.
    (* step 3 (312): sub t3,a3,t1 -- remaining capacity *)
    assert (hr13_2 : rget sM2 13 = cap).
    { unfold sM2. rewrite setPc_rget, (rset_rget sM1 5 _ 13 ltac:(lia) ltac:(lia)).
      replace (13 =? 5) with false by reflexivity.
      unfold sM1. rewrite setPc_rget.
      rewrite (hothLS 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha3. }
    assert (hr6_2 : rget sM2 6 = Z.of_nat pos).
    { unfold sM2. rewrite setPc_rget, (rset_rget sM1 5 _ 6 ltac:(lia) ltac:(lia)).
      replace (6 =? 5) with false by reflexivity.
      unfold sM1. rewrite setPc_rget.
      rewrite (hothLS 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact houtidx. }
    assert (hu3 : step sM2 = setPc (rset sM2 28 (cap - Z.of_nat pos)) (2147483792 + 316)).
    { rewrite (step1_sub sM2 312 28 13 6 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc2 ltac:(vm_compute; reflexivity)), hr13_2, hr6_2,
        (wsub_id cap (Z.of_nat pos) ltac:(lia)), hpc2,
        (wadd_id (2147483792 + 312) 4 ltac:(lia)). f_equal; lia. }
    set (sM3 := setPc (rset sM2 28 (cap - Z.of_nat pos)) (2147483792 + 316)) in *.
    assert (hmem3 : sM3.(mem) = s.(mem))
      by (unfold sM3; rewrite setPc_mem, rset_mem; exact hmem2).
    assert (hc3 : CodeLoaded1 sM3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
    assert (hpc3 : sM3.(pc) = 2147483792 + 316) by reflexivity.
    (* step 4 (316): li t4,4 *)
    assert (hu4 : step sM3 = setPc (rset sM3 29 4) (2147483792 + 320)).
    { rewrite (step1_addi sM3 316 29 0 4 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpc3 ltac:(vm_compute; reflexivity)),
        rget_zero, (wadd_id 0 4 ltac:(lia)), Z.add_0_l, hpc3,
        (wadd_id (2147483792 + 316) 4 ltac:(lia)). f_equal; lia. }
    set (sM4 := setPc (rset sM3 29 4) (2147483792 + 320)) in *.
    assert (hmem4' : sM4.(mem) = s.(mem))
      by (unfold sM4; rewrite setPc_mem, rset_mem; exact hmem3).
    assert (hc4 : CodeLoaded1 sM4) by (apply (CodeLoaded1_eqmem s); [exact hmem4'| exact hcode]).
    assert (hpc4' : sM4.(pc) = 2147483792 + 320) by reflexivity.
    assert (hr28_4 : rget sM4 28 = cap - Z.of_nat pos).
    { unfold sM4. rewrite setPc_rget, (rset_rget sM3 29 4 28 ltac:(lia) ltac:(lia)).
      replace (28 =? 29) with false by reflexivity.
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hr29_4 : rget sM4 29 = 4).
    { unfold sM4. rewrite setPc_rget, (rset_rget sM3 29 4 29 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    (* the register frame from sL to sM4 (clobbers 5,28,29) *)
    assert (hoth4M : forall i, i <> 0 -> i <> 5 -> i <> 28 -> i <> 29 ->
              rget sM4 i = rget sL i).
    { intros i h0 h5 h28 h29.
      unfold sM4. rewrite setPc_rget, (rset_rget sM3 29 4 i ltac:(lia) h0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sM2. rewrite setPc_rget, (rset_rget sM1 5 _ i ltac:(lia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      unfold sM1. rewrite setPc_rget. reflexivity. }
    (* assemble the 4 steps 304..316 *)
    assert (hpL : sL.(pc) <> 0) by (rewrite hpcL; lia).
    assert (hp1 : sM1.(pc) <> 0) by (rewrite hpc1; lia).
    assert (hp2 : sM2.(pc) <> 0) by (rewrite hpc2; lia).
    assert (hp3 : sM3.(pc) <> 0) by (rewrite hpc3; lia).
    assert (hp4 : sM4.(pc) <> 0) by (rewrite hpc4'; lia).
    assert (hrun4M : runUntil 0 4 sL = sM4).
    { rewrite (runUntil_S 3 sL hpL), hu1, (runUntil_S 2 sM1 hp1), hu2,
              (runUntil_S 1 sM2 hp2), hu3, (runUntil_S 0 sM3 hp3), hu4. reflexivity. }
    (* step 5 (320): blt t3,t4 -- the capacity test *)
    destruct (Z_lt_le_dec cap (Z.of_nat pos + 4)) as [hshort|hroom].
    + (* SHORT: cap - pos < 4, branch to 640 *)
      assert (hslt : sltb (rget sM4 28) (rget sM4 29) = true).
      { rewrite hr28_4, hr29_4,
          (sltb_small (cap - Z.of_nat pos) 4 ltac:(lia) ltac:(lia)).
        apply Z.ltb_lt. lia. }
      assert (hu5 : step sM4 = setPc sM4 (2147483792 + 640)).
      { rewrite (step1_blt sM4 320 28 29 320 hc4 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc4' ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpc4', (wadd_id (2147483792 + 320) 320 ltac:(lia)).
        f_equal; lia. }
      set (sX := setPc sM4 (2147483792 + 640)) in *.
      assert (hcodeX : CodeLoaded1 sX)
        by (apply (CodeLoaded1_eqmem sM4); [reflexivity| exact hc4]).
      assert (hpcX : sX.(pc) = Image1.coreAddr + 640) by (unfold Image1.coreAddr; reflexivity).
      assert (hraM : rget sM4 1 = 0).
      { rewrite (hoth4M 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact hraL. }
      assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraM).
      destruct (exit_zero sX 640 2 hcodeX ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                  hpcX hraX ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(lia))
        as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
      destruct (scan1 High1 lab ((pos + 4)%nat) (zin rest'')) as [[labf m] stf] eqn:Hres.
      pose proof (scan1_pos_le (zin rest'') High1 lab ((pos + 4)%nat) labf m stf Hres)
        as hmono.
      assert (hscan_inp : scan1 High1 noLabels 0 (zin inp) = (labf, m, stf))
        by (rewrite <- hspec2; reflexivity).
      exists (18 + (4 + (1 + 3)))%nat. right. split; [simpl length; lia|].
      rewrite (runUntil_add 18 (4 + (1 + 3))), hrun18, (runUntil_add 4 (1 + 3)), hrun4M,
              (runUntil_add 1 3), (runUntil_one sM4 hp4), hu5. fold sX. rewrite hrunE.
      exact (short_result1 f inp cap labf m stf hscan_inp ltac:(lia) hcap0
               hfpc hf10 hf11).
    + (* room for the 4 offset bytes: fall through, bump pos, loop back *)
      assert (hslt : sltb (rget sM4 28) (rget sM4 29) = false).
      { rewrite hr28_4, hr29_4,
          (sltb_small (cap - Z.of_nat pos) 4 ltac:(lia) ltac:(lia)).
        apply Z.ltb_ge. lia. }
      assert (hu5 : step sM4 = setPc sM4 (2147483792 + 324)).
      { rewrite (step1_blt sM4 320 28 29 320 hc4 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc4' ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpc4', (wadd_id (2147483792 + 320) 4 ltac:(lia)).
        f_equal; lia. }
      set (sM5 := setPc sM4 (2147483792 + 324)) in *.
      assert (hmem5 : sM5.(mem) = s.(mem)) by (unfold sM5; rewrite setPc_mem; exact hmem4').
      assert (hc5 : CodeLoaded1 sM5) by (apply (CodeLoaded1_eqmem s); [exact hmem5| exact hcode]).
      assert (hpc5 : sM5.(pc) = 2147483792 + 324) by reflexivity.
      (* step 6 (324): addi t1,t1,4 *)
      assert (hr6_5 : rget sM5 6 = Z.of_nat pos).
      { unfold sM5. rewrite setPc_rget.
        rewrite (hoth4M 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        rewrite (hothLS 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact houtidx. }
      assert (hu6 : step sM5 = setPc (rset sM5 6 (Z.of_nat pos + 4)) (2147483792 + 328)).
      { rewrite (step1_addi sM5 324 6 6 4 hc5 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
          hpc5 ltac:(vm_compute; reflexivity)), hr6_5,
          (wadd_id (Z.of_nat pos) 4 ltac:(lia)), hpc5,
          (wadd_id (2147483792 + 324) 4 ltac:(lia)). f_equal; lia. }
      set (sM6 := setPc (rset sM5 6 (Z.of_nat pos + 4)) (2147483792 + 328)) in *.
      assert (hmem6 : sM6.(mem) = s.(mem))
        by (unfold sM6; rewrite setPc_mem, rset_mem; exact hmem5).
      assert (hc6 : CodeLoaded1 sM6) by (apply (CodeLoaded1_eqmem s); [exact hmem6| exact hcode]).
      assert (hpc6 : sM6.(pc) = 2147483792 + 328) by reflexivity.
      (* step 7 (328): jal back to the loop head *)
      assert (hu7 : step sM6 = setPc sM6 (2147483792 + 36)).
      { rewrite (step1_jal sM6 328 0 (-292) hc6 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc6 ltac:(vm_compute; reflexivity)),
          rset_zero, hpc6, (wadd_id (2147483792 + 328) (-292) ltac:(lia)).
        f_equal; lia. }
      set (sF := setPc sM6 (2147483792 + 36)) in *.
      assert (hp5 : sM5.(pc) <> 0) by (rewrite hpc5; lia).
      assert (hp6 : sM6.(pc) <> 0) by (rewrite hpc6; lia).
      assert (hrunF : runUntil 0 (18 + (4 + 3)) s = sF).
      { rewrite (runUntil_add 18 (4 + 3)), hrun18, (runUntil_add 4 3), hrun4M,
                (runUntil_S 2 sM4 hp4), hu5, (runUntil_S 1 sM5 hp5), hu6,
                (runUntil_S 0 sM6 hp6), hu7. reflexivity. }
      exists (18 + (4 + 3))%nat. left. exists rest''. exists ((pos + 4)%nat).
      rewrite hrunF.
      assert (hmemF : sF.(mem) = s.(mem)) by (unfold sF; rewrite setPc_mem; exact hmem6).
      assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 6 -> i <> 7 -> i <> 28 -> i <> 29 ->
                rget sF i = rget s i).
      { intros i h0 h5 h6 h7 h28 h29.
        unfold sF. rewrite setPc_rget.
        unfold sM6. rewrite setPc_rget, (rset_rget sM5 6 _ i ltac:(lia) h0).
        replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
        unfold sM5. rewrite setPc_rget.
        rewrite (hoth4M i h0 h5 h28 h29).
        exact (hothLS i h0 h5 h7 h28). }
      split; [simpl length; lia| split; [simpl length; lia|]].
      assert (hsufx2 : skipn (S idx1) inp = rest'').
      { replace (S idx1) with (1 + idx1)%nat by lia.
        rewrite <- skipn_skipn, hsufx. reflexivity. }
      refine {| p1_wf := hwf; p1_at_loop := _; p1_code := _; p1_a0 := _; p1_a1 := _;
                p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
                p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := _;
                p1_tbl := _; p1_lab_le := _; p1_spec := hspec2 |}.
      * apply setPc_pc.
      * apply (CodeLoaded1_eqmem sM6); [reflexivity| exact hc6].
      * rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
      * rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
      * rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
      * rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
      * rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
      * rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
      * apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
      * (* t0 = consumed count *)
        assert (hr5F : rget sF 5 = Z.of_nat idx1 + 1).
        { unfold sF. rewrite setPc_rget.
          unfold sM6. rewrite setPc_rget, (rset_rget sM5 6 _ 5 ltac:(lia) ltac:(lia)).
          replace (5 =? 6) with false by reflexivity.
          unfold sM5. rewrite setPc_rget.
          unfold sM4. rewrite setPc_rget, (rset_rget sM3 29 4 5 ltac:(lia) ltac:(lia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sM3. rewrite setPc_rget, (rset_rget sM2 28 _ 5 ltac:(lia) ltac:(lia)).
          replace (5 =? 28) with false by reflexivity.
          unfold sM2. rewrite setPc_rget, (rset_rget sM1 5 _ 5 ltac:(lia) ltac:(lia)),
            Z.eqb_refl. reflexivity. }
        rewrite hr5F. unfold idx1. simpl length in *. lia.
      * replace (length inp - length rest'')%nat with (S idx1)
          by (unfold idx1; simpl length in *; lia).
        exact hsufx2.
      * (* t1 = pos + 4 *)
        assert (hr6F : rget sF 6 = Z.of_nat pos + 4).
        { unfold sF. rewrite setPc_rget.
          unfold sM6. rewrite setPc_rget, (rset_rget sM5 6 _ 6 ltac:(lia) ltac:(lia)),
            Z.eqb_refl. reflexivity. }
        rewrite hr6F. lia.
      * lia.
      * apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
      * intros c0 p0 h. pose proof (hlable c0 p0 h). lia.
Qed.

(** ** Pass-1 byte path (hex-digit token): range checks, the stop check,
    and (next chunk) the assembled iteration. *)

(* spec-side unfolds for the High1 nibble case and the Low1 state *)
Lemma scan1_high_nibble c hi lab pos rest :
  isComment c = false -> isSpace c = false ->
  (c =? c_colon)%nat = false -> (c =? c_pct)%nat = false ->
  nibble c = Some hi ->
  scan1 High1 lab pos (c :: rest) = scan1 (Low1 hi) lab pos rest.
Proof. intros h1 h2 h3 h4 h5. simp scan1. rewrite h1, h2, h3, h4, h5. reflexivity. Qed.

Lemma scan1_low_nil hi lab pos : scan1 (Low1 hi) lab pos [] = (lab, pos, Trailing1).
Proof. now simp scan1. Qed.

Lemma scan1_low_stop hi lab pos lc rest : isLowStop1 lc = true ->
  scan1 (Low1 hi) lab pos (lc :: rest) = (lab, pos, Split1).
Proof. intros h. simp scan1. rewrite h. reflexivity. Qed.

Lemma scan1_low_unk hi lab pos lc rest : isLowStop1 lc = false -> nibble lc = None ->
  scan1 (Low1 hi) lab pos (lc :: rest) = (lab, pos, Unknown1).
Proof. intros h1 h2. simp scan1. rewrite h1, h2. reflexivity. Qed.

Lemma scan1_low_ok hi lo lab pos lc rest : isLowStop1 lc = false -> nibble lc = Some lo ->
  scan1 (Low1 hi) lab pos (lc :: rest) = scan1 High1 lab (pos + 1) rest.
Proof. intros h1 h2. simp scan1. rewrite h1, h2. reflexivity. Qed.

(* the hex1 stop set, by cases (order matches the machine's beq chain) *)
Lemma isLowStop1_cases c : 0 <= c -> isLowStop1 (Z.to_nat c) = true ->
  c = 10 \/ c = 32 \/ c = 95 \/ c = 35 \/ c = 59 \/ c = 58 \/ c = 37.
Proof.
  intros h0 hs. unfold isLowStop1 in hs.
  apply orb_true_iff in hs. destruct hs as [hs|hs].
  - apply orb_true_iff in hs. destruct hs as [hs|hs].
    + destruct (isLowStop_cases c h0 hs) as [H|[H|[H|[H|H]]]]; tauto.
    + apply Nat.eqb_eq in hs. unfold c_colon in hs.
      do 5 right. left. lia.
  - apply Nat.eqb_eq in hs. unfold c_pct in hs. do 6 right. lia.
Qed.

Lemma isLowStop1_false_ne c : 0 <= c < 256 -> isLowStop1 (Z.to_nat c) = false ->
  c <> 10 /\ c <> 32 /\ c <> 95 /\ c <> 35 /\ c <> 59 /\ c <> 58 /\ c <> 37.
Proof.
  intros hr hs. repeat apply conj; intros He; rewrite He in hs;
    vm_compute in hs; discriminate.
Qed.

(* a nibble char is none of the token/stop characters *)
Lemma nibble_high_bools c hi : 0 <= c -> nibble (Z.to_nat c) = Some hi ->
  isComment (Z.to_nat c) = false /\ isSpace (Z.to_nat c) = false /\
  (Z.to_nat c =? c_colon)%nat = false /\ (Z.to_nat c =? c_pct)%nat = false.
Proof.
  intros h0 hn.
  destruct (nibble_cases c hi h0 hn) as [[Hr _]|[Hr _]];
    unfold isComment, isSpace, c_hash, c_semi, c_nl, c_sp, c_us, c_colon, c_pct;
    repeat apply conj;
    repeat (replace (Z.to_nat c =? _)%nat with false by
      (symmetry; apply Nat.eqb_neq; lia));
    reflexivity.
Qed.

Lemma nibble_ne_stops c hi : 0 <= c -> nibble (Z.to_nat c) = Some hi ->
  c <> 35 /\ c <> 59 /\ c <> 10 /\ c <> 32 /\ c <> 95 /\ c <> 58 /\ c <> 37.
Proof.
  intros h0 hn.
  destruct (nibble_cases c hi h0 hn) as [[Hr _]|[Hr _]]; repeat apply conj; lia.
Qed.

(* === BEGIN generated by tools/gen_refine1_chains.py === *)
(* dispatch 52 -> 108 for a hex-digit first char (7 not-taken blocks): 14 steps *)
Lemma p1_fall_tail s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 52 -> rget s4 7 = c ->
  0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 -> c <> 58 -> c <> 37 ->
  exists s', runUntil 0 14 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 108 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hne1 hne2 hne3 hne4 hne5 hne6 hne7.
  pose proof (li1_beq_ne s4 52 35 c 276 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (52 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 60) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = c) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact h7).
  pose proof (li1_beq_ne sB 60 59 c 268 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (60 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 68) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = c) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 68 10 c (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (68 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 76) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = c) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 76 32 c (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (76 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 84) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = c) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 84 95 c (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (84 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 92) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = c) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_ne sF 92 58 c 168 hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
  set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (92 + 8))) in *.
  assert (hcG : CodeLoaded1 sG) by
    (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
  assert (hpcG : sG.(pc) = Image1.coreAddr + 100) by (unfold sG; cbn; lia).
  assert (h7G : rget sG 7 = c) by
    (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
  pose proof (li1_beq_ne sG 100 37 c 200 hcG ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb7.
  exists (setPc (rset sG 28 37) (Image1.coreAddr + (100 + 8))).
  split.
  { replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + (2)))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem.
    unfold sG. rewrite setPc_mem, rset_mem.
    unfold sF. rewrite setPc_mem, rset_mem.
    unfold sE. rewrite setPc_mem, rset_mem.
    unfold sD. rewrite setPc_mem, rset_mem.
    unfold sC. rewrite setPc_mem, rset_mem.
    unfold sB. rewrite setPc_mem, rset_mem.
    reflexivity.
  - apply (CodeLoaded1_eqmem sG);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcG].
  - intros i hir.
    rewrite (li_block_frame sG 37 _ i hir).
    unfold sG. rewrite (li_block_frame sF 58 _ i hir).
    unfold sF. rewrite (li_block_frame sE 95 _ i hir).
    unfold sE. rewrite (li_block_frame sD 32 _ i hir).
    unfold sD. rewrite (li_block_frame sC 10 _ i hir).
    unfold sC. rewrite (li_block_frame sB 59 _ i hir).
    unfold sB. rewrite (li_block_frame s4 35 _ i hir).
    reflexivity.
Qed.

(* high-nibble range check (108..140), valid: fall to the low read at 144 *)
Lemma p1_high_ok s4 c hi :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 108 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = Some hi ->
  exists k, (0 < k <= 8)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 144 /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr _]|[Hr _]].
  - (* digit: blt48 nt, bge58 nt, jal *)
    pose proof (li1_blt_nt s4 108 48 c 564 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (108 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 116) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_nt sB 116 58 c 8 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + (116 + 8))) in *.
    assert (hcJ : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcJ : sC.(pc) = Image1.coreAddr + 124) by (unfold sC; cbn; lia).
    assert (huJ : step sC = setPc sC (Image1.coreAddr + 144)).
    { rewrite (step1_jal sC 124 0 20 hcJ ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcJ ltac:(vm_compute; reflexivity)),
        rset_zero, hpcJ, (wadd_id (Image1.coreAddr + 124) 20
          ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpJ : sC.(pc) <> 0) by (rewrite hpcJ; unfold Image1.coreAddr; lia).
    exists 5%nat. split; [lia|].
    replace 5%nat with (2 + (2 + (1)))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, (runUntil_one sC hpJ), huJ.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite setPc_rget.
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* letter: blt48 nt, bge58 taken, blt65 nt, bge71 nt *)
    pose proof (li1_blt_nt s4 108 48 c 564 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (108 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 116) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 116 58 c 8 (Image1.coreAddr + 128) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (116 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 128)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 128) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_nt sC 128 65 c 544 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 65) (Image1.coreAddr + (128 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 136) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 65 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_bge_nt sD 136 71 c 536 hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb4.
    exists 8%nat. split; [lia|].
    replace 8%nat with (2 + (2 + (2 + (2))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sD 71 _ i hir).
      unfold sD. rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
Qed.

(* high-nibble range check (108..140), invalid: Unknown exit 676 *)
Lemma p1_high_unk s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 108 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = None ->
  exists k, (0 < k <= 8)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 676 /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_none_cases c ltac:(lia) hn) as [Hr|[Hr|Hr]].
  - (* c < 48: blt48 taken *)
    pose proof (li1_blt_t s4 108 48 c 564 (Image1.coreAddr + 676) hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (108 + 4)) 564
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb1.
    exists 2%nat. split; [lia|].
    rewrite hb1.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* 57 < c < 65: blt48 nt, bge58 taken, blt65 taken *)
    pose proof (li1_blt_nt s4 108 48 c 564 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (108 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 116) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 116 58 c 8 (Image1.coreAddr + 128) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (116 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 128)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 128) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_t sC 128 65 c 544 (Image1.coreAddr + 676) hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (128 + 4)) 544
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb3.
    exists 6%nat. split; [lia|].
    replace 6%nat with (2 + (2 + (2)))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, hb3.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* 70 < c: blt48 nt, bge58 taken, blt65 nt, bge71 taken *)
    pose proof (li1_blt_nt s4 108 48 c 564 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (108 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 116) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 116 58 c 8 (Image1.coreAddr + 128) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (116 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 128)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 128) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_nt sC 128 65 c 544 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 65) (Image1.coreAddr + (128 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 136) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 65 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_bge_t sD 136 71 c 536 (Image1.coreAddr + 676) hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (136 + 4)) 536
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb4.
    exists 8%nat. split; [lia|].
    replace 8%nat with (2 + (2 + (2 + (2))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sD 71 _ i hir).
      unfold sD. rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
Qed.

(* low-char stop check (160..212), stop case: the matching beq fires
   -> split exit 652. *)
Lemma p1_stop_split s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 160 -> rget s4 7 = c ->
  0 <= c < 256 -> isLowStop1 (Z.to_nat c) = true ->
  exists k, (0 < k <= 14)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 652 /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hstop.
  destruct (isLowStop1_cases c ltac:(lia) hstop)
    as [He|[He|[He|[He|[He|[He|He]]]]]].
  - (* c = 10 *)
    pose proof (li1_beq_eq s4 160 10 c 488 (Image1.coreAddr + 652) hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (160 + 4)) 488
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb1.
    exists 2%nat. split; [lia|].
    rewrite hb1.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 32 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_eq sB 168 32 c 480 (Image1.coreAddr + 652) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (168 + 4)) 480
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    exists 4%nat. split; [lia|].
    replace 4%nat with (2 + (2))%nat by lia.
    rewrite runUntil_add, hb1, hb2.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 95 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_beq_eq sC 176 95 c 472 (Image1.coreAddr + 652) hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (176 + 4)) 472
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb3.
    exists 6%nat. split; [lia|].
    replace 6%nat with (2 + (2 + (2)))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, hb3.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sC 95 _ i hir).
      unfold sC. rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 35 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_beq_ne sC 176 95 c 472 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 95) (Image1.coreAddr + (176 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 184) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 95 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_beq_eq sD 184 35 c 464 (Image1.coreAddr + 652) hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (184 + 4)) 464
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb4.
    exists 8%nat. split; [lia|].
    replace 8%nat with (2 + (2 + (2 + (2))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sD 35 _ i hir).
      unfold sD. rewrite (li_block_frame sC 95 _ i hir).
      unfold sC. rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 59 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_beq_ne sC 176 95 c 472 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 95) (Image1.coreAddr + (176 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 184) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 95 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_beq_ne sD 184 35 c 464 hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (sE := setPc (rset sD 28 35) (Image1.coreAddr + (184 + 8))) in *.
    assert (hcE : CodeLoaded1 sE) by
      (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
    assert (hpcE : sE.(pc) = Image1.coreAddr + 192) by (unfold sE; cbn; lia).
    assert (h7E : rget sE 7 = c) by
      (unfold sE; rewrite (li_block_frame sD 35 _ 7 ltac:(lia)); exact h7D).
    pose proof (li1_beq_eq sE 192 59 c 456 (Image1.coreAddr + 652) hcE ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (192 + 4)) 456
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb5.
    exists 10%nat. split; [lia|].
    replace 10%nat with (2 + (2 + (2 + (2 + (2)))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, hb5.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sE. rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sE 59 _ i hir).
      unfold sE. rewrite (li_block_frame sD 35 _ i hir).
      unfold sD. rewrite (li_block_frame sC 95 _ i hir).
      unfold sC. rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 58 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_beq_ne sC 176 95 c 472 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 95) (Image1.coreAddr + (176 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 184) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 95 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_beq_ne sD 184 35 c 464 hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (sE := setPc (rset sD 28 35) (Image1.coreAddr + (184 + 8))) in *.
    assert (hcE : CodeLoaded1 sE) by
      (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
    assert (hpcE : sE.(pc) = Image1.coreAddr + 192) by (unfold sE; cbn; lia).
    assert (h7E : rget sE 7 = c) by
      (unfold sE; rewrite (li_block_frame sD 35 _ 7 ltac:(lia)); exact h7D).
    pose proof (li1_beq_ne sE 192 59 c 456 hcE ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
    set (sF := setPc (rset sE 28 59) (Image1.coreAddr + (192 + 8))) in *.
    assert (hcF : CodeLoaded1 sF) by
      (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
    assert (hpcF : sF.(pc) = Image1.coreAddr + 200) by (unfold sF; cbn; lia).
    assert (h7F : rget sF 7 = c) by
      (unfold sF; rewrite (li_block_frame sE 59 _ 7 ltac:(lia)); exact h7E).
    pose proof (li1_beq_eq sF 200 58 c 448 (Image1.coreAddr + 652) hcF ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (200 + 4)) 448
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb6.
    exists 12%nat. split; [lia|].
    replace 12%nat with (2 + (2 + (2 + (2 + (2 + (2))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, runUntil_add, hb5, hb6.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sF. rewrite setPc_mem, rset_mem.
      unfold sE. rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sF 58 _ i hir).
      unfold sF. rewrite (li_block_frame sE 59 _ i hir).
      unfold sE. rewrite (li_block_frame sD 35 _ i hir).
      unfold sD. rewrite (li_block_frame sC 95 _ i hir).
      unfold sC. rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
  - (* c = 37 *)
    pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_beq_ne sC 176 95 c 472 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 95) (Image1.coreAddr + (176 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 184) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 95 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_beq_ne sD 184 35 c 464 hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (sE := setPc (rset sD 28 35) (Image1.coreAddr + (184 + 8))) in *.
    assert (hcE : CodeLoaded1 sE) by
      (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
    assert (hpcE : sE.(pc) = Image1.coreAddr + 192) by (unfold sE; cbn; lia).
    assert (h7E : rget sE 7 = c) by
      (unfold sE; rewrite (li_block_frame sD 35 _ 7 ltac:(lia)); exact h7D).
    pose proof (li1_beq_ne sE 192 59 c 456 hcE ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
    set (sF := setPc (rset sE 28 59) (Image1.coreAddr + (192 + 8))) in *.
    assert (hcF : CodeLoaded1 sF) by
      (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
    assert (hpcF : sF.(pc) = Image1.coreAddr + 200) by (unfold sF; cbn; lia).
    assert (h7F : rget sF 7 = c) by
      (unfold sF; rewrite (li_block_frame sE 59 _ 7 ltac:(lia)); exact h7E).
    pose proof (li1_beq_ne sF 200 58 c 448 hcF ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
    set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (200 + 8))) in *.
    assert (hcG : CodeLoaded1 sG) by
      (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
    assert (hpcG : sG.(pc) = Image1.coreAddr + 208) by (unfold sG; cbn; lia).
    assert (h7G : rget sG 7 = c) by
      (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
    pose proof (li1_beq_eq sG 208 37 c 440 (Image1.coreAddr + 652) hcG ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) He
      ltac:(rewrite (wadd_id (Image1.coreAddr + (208 + 4)) 440
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb7.
    exists 14%nat. split; [lia|].
    replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + (2)))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sG. rewrite setPc_mem, rset_mem.
      unfold sF. rewrite setPc_mem, rset_mem.
      unfold sE. rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sG 37 _ i hir).
      unfold sG. rewrite (li_block_frame sF 58 _ i hir).
      unfold sF. rewrite (li_block_frame sE 59 _ i hir).
      unfold sE. rewrite (li_block_frame sD 35 _ i hir).
      unfold sD. rewrite (li_block_frame sC 95 _ i hir).
      unfold sC. rewrite (li_block_frame sB 32 _ i hir).
      unfold sB. rewrite (li_block_frame s4 10 _ i hir).
      reflexivity.
Qed.

(* low-char stop check (160..212), no stop matches (7 not-taken blocks): 14 steps *)
Lemma p1_stop_fall s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 160 -> rget s4 7 = c ->
  0 <= c < 256 ->
  c <> 10 -> c <> 32 -> c <> 95 -> c <> 35 -> c <> 59 -> c <> 58 -> c <> 37 ->
  exists s', runUntil 0 14 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 216 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hne1 hne2 hne3 hne4 hne5 hne6 hne7.
  pose proof (li1_beq_ne s4 160 10 c 488 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 10) (Image1.coreAddr + (160 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 168) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = c) by
    (unfold sB; rewrite (li_block_frame s4 10 _ 7 ltac:(lia)); exact h7).
  pose proof (li1_beq_ne sB 168 32 c 480 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 32) (Image1.coreAddr + (168 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 176) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = c) by
    (unfold sC; rewrite (li_block_frame sB 32 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 176 95 c 472 hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 95) (Image1.coreAddr + (176 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 184) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = c) by
    (unfold sD; rewrite (li_block_frame sC 95 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 184 35 c 464 hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 35) (Image1.coreAddr + (184 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 192) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = c) by
    (unfold sE; rewrite (li_block_frame sD 35 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 192 59 c 456 hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 59) (Image1.coreAddr + (192 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 200) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = c) by
    (unfold sF; rewrite (li_block_frame sE 59 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_ne sF 200 58 c 448 hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
  set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (200 + 8))) in *.
  assert (hcG : CodeLoaded1 sG) by
    (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
  assert (hpcG : sG.(pc) = Image1.coreAddr + 208) by (unfold sG; cbn; lia).
  assert (h7G : rget sG 7 = c) by
    (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
  pose proof (li1_beq_ne sG 208 37 c 440 hcG ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb7.
  exists (setPc (rset sG 28 37) (Image1.coreAddr + (208 + 8))).
  split.
  { replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + (2)))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem.
    unfold sG. rewrite setPc_mem, rset_mem.
    unfold sF. rewrite setPc_mem, rset_mem.
    unfold sE. rewrite setPc_mem, rset_mem.
    unfold sD. rewrite setPc_mem, rset_mem.
    unfold sC. rewrite setPc_mem, rset_mem.
    unfold sB. rewrite setPc_mem, rset_mem.
    reflexivity.
  - apply (CodeLoaded1_eqmem sG);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcG].
  - intros i hir.
    rewrite (li_block_frame sG 37 _ i hir).
    unfold sG. rewrite (li_block_frame sF 58 _ i hir).
    unfold sF. rewrite (li_block_frame sE 59 _ i hir).
    unfold sE. rewrite (li_block_frame sD 35 _ i hir).
    unfold sD. rewrite (li_block_frame sC 95 _ i hir).
    unfold sC. rewrite (li_block_frame sB 32 _ i hir).
    unfold sB. rewrite (li_block_frame s4 10 _ i hir).
    reflexivity.
Qed.

(* low-nibble range check (216..248), valid: fall to the count at 252 *)
Lemma p1_low_ok s4 c hi :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 216 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = Some hi ->
  exists k, (0 < k <= 8)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 252 /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr _]|[Hr _]].
  - (* digit: blt48 nt, bge58 nt, jal *)
    pose proof (li1_blt_nt s4 216 48 c 456 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (216 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 224) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_nt sB 224 58 c 8 hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + (224 + 8))) in *.
    assert (hcJ : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcJ : sC.(pc) = Image1.coreAddr + 232) by (unfold sC; cbn; lia).
    assert (huJ : step sC = setPc sC (Image1.coreAddr + 252)).
    { rewrite (step1_jal sC 232 0 20 hcJ ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcJ ltac:(vm_compute; reflexivity)),
        rset_zero, hpcJ, (wadd_id (Image1.coreAddr + 232) 20
          ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpJ : sC.(pc) <> 0) by (rewrite hpcJ; unfold Image1.coreAddr; lia).
    exists 5%nat. split; [lia|].
    replace 5%nat with (2 + (2 + (1)))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, (runUntil_one sC hpJ), huJ.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite setPc_rget.
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* letter: blt48 nt, bge58 taken, blt65 nt, bge71 nt *)
    pose proof (li1_blt_nt s4 216 48 c 456 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (216 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 224) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 224 58 c 8 (Image1.coreAddr + 236) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (224 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 236)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 236) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_nt sC 236 65 c 436 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 65) (Image1.coreAddr + (236 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 244) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 65 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_bge_nt sD 244 71 c 428 hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb4.
    exists 8%nat. split; [lia|].
    replace 8%nat with (2 + (2 + (2 + (2))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sD 71 _ i hir).
      unfold sD. rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
Qed.

(* low-nibble range check (216..248), invalid: Unknown exit 676 *)
Lemma p1_low_unk s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 216 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = None ->
  exists k, (0 < k <= 8)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 676 /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_none_cases c ltac:(lia) hn) as [Hr|[Hr|Hr]].
  - (* c < 48: blt48 taken *)
    pose proof (li1_blt_t s4 216 48 c 456 (Image1.coreAddr + 676) hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (216 + 4)) 456
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb1.
    exists 2%nat. split; [lia|].
    rewrite hb1.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* 57 < c < 65: blt48 nt, bge58 taken, blt65 taken *)
    pose proof (li1_blt_nt s4 216 48 c 456 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (216 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 224) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 224 58 c 8 (Image1.coreAddr + 236) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (224 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 236)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 236) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_t sC 236 65 c 436 (Image1.coreAddr + 676) hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (236 + 4)) 436
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb3.
    exists 6%nat. split; [lia|].
    replace 6%nat with (2 + (2 + (2)))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, hb3.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
  - (* 70 < c: blt48 nt, bge58 taken, blt65 nt, bge71 taken *)
    pose proof (li1_blt_nt s4 216 48 c 456 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sB := setPc (rset s4 28 48) (Image1.coreAddr + (216 + 8))) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 224) by (unfold sB; cbn; lia).
    assert (h7B : rget sB 7 = c) by
      (unfold sB; rewrite (li_block_frame s4 48 _ 7 ltac:(lia)); exact h7).
    pose proof (li1_bge_t sB 224 58 c 8 (Image1.coreAddr + 236) hcB ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (224 + 4)) 8
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb2.
    set (sC := setPc (rset sB 28 58) (Image1.coreAddr + 236)) in *.
    assert (hcC : CodeLoaded1 sC) by
      (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
    assert (hpcC : sC.(pc) = Image1.coreAddr + 236) by (unfold sC; cbn; lia).
    assert (h7C : rget sC 7 = c) by
      (unfold sC; rewrite (li_block_frame sB 58 _ 7 ltac:(lia)); exact h7B).
    pose proof (li1_blt_nt sC 236 65 c 436 hcC ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb3.
    set (sD := setPc (rset sC 28 65) (Image1.coreAddr + (236 + 8))) in *.
    assert (hcD : CodeLoaded1 sD) by
      (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
    assert (hpcD : sD.(pc) = Image1.coreAddr + 244) by (unfold sD; cbn; lia).
    assert (h7D : rget sD 7 = c) by
      (unfold sD; rewrite (li_block_frame sC 65 _ 7 ltac:(lia)); exact h7C).
    pose proof (li1_bge_t sD 244 71 c 428 (Image1.coreAddr + 676) hcD ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (244 + 4)) 428
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb4.
    exists 8%nat. split; [lia|].
    replace 8%nat with (2 + (2 + (2 + (2))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem.
      unfold sD. rewrite setPc_mem, rset_mem.
      unfold sC. rewrite setPc_mem, rset_mem.
      unfold sB. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hir.
      rewrite (li_block_frame sD 71 _ i hir).
      unfold sD. rewrite (li_block_frame sC 65 _ i hir).
      unfold sC. rewrite (li_block_frame sB 58 _ i hir).
      unfold sB. rewrite (li_block_frame s4 48 _ i hir).
      reflexivity.
Qed.

(* === END generated === *)

(* A COMPLETE pass-1 iteration for a hex byte token: prefix + fall-through
   dispatch to 108 + high-nibble check + low-char read + stop check +
   low-nibble check + the capacity count. Outcomes: byte accepted (back to
   the loop head, 2 chars consumed, pos+1), Trailing (EOF after the high
   char, exit 664), Split (stop char in low position, exit 652), Unknown
   (bad low char, exit 676), Short (pos = cap, exit 640). *)
Lemma p1_byte : forall inp cap c hi rest' lab pos s,
  nibble (Z.to_nat c) = Some hi ->
  P1Inv inp cap s lab pos (c :: rest') ->
  exists k,
    (exists rest2 pos2, (length rest2 < length (c :: rest'))%nat /\
        (k <= 50 * (length (c :: rest') - length rest2))%nat /\
        P1Inv inp cap (runUntil 0 k s) lab pos2 rest2)
    \/ ((k <= 50 * length (c :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap c hi rest' lab pos s hn inv. pose proof inv as inv0.
  destruct (p1_prefix inp cap c rest' lab pos s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf. pose proof (cap_nonneg _ _ hwf) as hcap0.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp c rest'); exact hsuf).
  (* dispatch 52 -> 108 (the 7 token tests all fail for a nibble char) *)
  destruct (nibble_ne_stops c hi ltac:(lia) hn)
    as (hne35 & hne59 & hne10 & hne32 & hne95 & hne58 & hne37).
  destruct (p1_fall_tail s4 c hcode4 hpc4 ht2 hcr
              hne35 hne59 hne10 hne32 hne95 hne58 hne37)
    as (sH & hrunH & hpcH & hmemH & hcodeH & hothH).
  (* high-nibble range check 108 -> 144 *)
  destruct (p1_high_ok sH c hi hcodeH hpcH
              ltac:(rewrite (hothH 7 ltac:(lia)); exact ht2) hcr hn)
    as (k1 & hk1 & hpcN & hmemN & hframeN).
  set (sN := runUntil 0 k1 sH) in *.
  assert (hmemNS : sN.(mem) = s.(mem)).
  { rewrite hmemN, hmemH. exact hmem4. }
  assert (hcodeN : CodeLoaded1 sN)
    by (apply (CodeLoaded1_eqmem s); [exact hmemNS| exact hcode]).
  assert (hothNS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
            rget sN i = rget s i).
  { intros i h0 h5 h7 h28.
    rewrite (hframeN i h28), (hothH i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
  assert (h5N : rget sN 5 = Z.of_nat idx1).
  { rewrite (hframeN 5 ltac:(lia)), (hothH 5 ltac:(lia)), ht0. unfold idx1. lia. }
  assert (ha1N : rget sN 11 = Z.of_nat (length inp))
    by (rewrite (hothNS 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1).
  assert (hraN : rget sN 1 = 0)
    by (rewrite (hothNS 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
  assert (hrunN : runUntil 0 (4 + (14 + k1)) s = sN).
  { rewrite (runUntil_add 4 (14 + k1)), hrun4, (runUntil_add 14 k1), hrunH.
    reflexivity. }
  assert (hpN0 : sN.(pc) <> 0) by (rewrite hpcN; unfold Image1.coreAddr; lia).
  (* spec side: the high nibble sends High1 to Low1 hi *)
  destruct (nibble_high_bools c hi ltac:(lia) hn) as (hbc & hbs & hbcol & hbpct).
  assert (hspec2 : scan1 (Low1 hi) lab pos (zin rest')
                   = scan1 High1 noLabels 0 (zin inp)).
  { rewrite <- hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    rewrite (scan1_high_nibble (Z.to_nat c) hi lab pos (zin rest')
               hbc hbs hbcol hbpct hn). reflexivity. }
  destruct rest' as [|l rest''].
  - (* EOF after the high char -> Trailing exit (664) *)
    assert (h5N' : rget sN 5 = Z.of_nat (length inp))
      by (rewrite h5N; unfold idx1; simpl length; lia).
    assert (hbt : step sN = setPc sN (Image1.coreAddr + 664)).
    { apply (bgeu1_eq_taken sN 144 5 11 (Z.of_nat (length inp)) 520 _ hcodeN ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcN h5N' ha1N ltac:(vm_compute; reflexivity)).
      rewrite (wadd_id (Image1.coreAddr + 144) 520 ltac:(unfold Image1.coreAddr; lia)).
      lia. }
    set (sX := setPc sN (Image1.coreAddr + 664)) in *.
    assert (hcodeX : CodeLoaded1 sX)
      by (apply (CodeLoaded1_eqmem sN); [reflexivity| exact hcodeN]).
    assert (hpcX : sX.(pc) = Image1.coreAddr + 664) by reflexivity.
    assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraN).
    destruct (exit_zero sX 664 4 hcodeX ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                hpcX hraX ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(lia))
      as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
    exists ((4 + (14 + k1)) + (1 + 3))%nat. right. split; [simpl length; lia|].
    rewrite (runUntil_add (4 + (14 + k1)) (1 + 3)), hrunN,
            (runUntil_add 1 3), (runUntil_one sN hpN0), hbt. fold sX. rewrite hrunE.
    apply (error_result1 f inp cap lab pos Trailing1).
    + rewrite <- hspec2. change (zin (@nil Z)) with (@nil nat).
      apply scan1_low_nil.
    + discriminate.
    + exact hposle.
    + exact hfpc.
    + exact hf10.
    + exact hf11.
  - (* read the low char l (144..156) *)
    assert (hidxlt : (idx1 < length inp)%nat) by (unfold idx1; simpl length in *; lia).
    assert (Hl : nth idx1 inp 0 = l).
    { transitivity (nth 0 (skipn idx1 inp) 0).
      - rewrite nth_skipn. f_equal. lia.
      - rewrite hsufx. reflexivity. }
    assert (HinL : In l inp).
    { rewrite <- (firstn_skipn idx1 inp). apply in_or_app. right.
      rewrite hsufx. left; reflexivity. }
    assert (Hlr : 0 <= l < 256) by (apply (bytes_ok1 _ _ hwf); exact HinL).
    set (l' := Z.to_nat l) in *.
    assert (hl' : Z.of_nat l' = l) by (unfold l'; apply Z2Nat.id; lia).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
    (* step (144): bgeu t0,a1 -- NOT taken *)
    assert (hult : ultb (rget sN 5) (rget sN 11) = true).
    { rewrite h5N, ha1N. unfold ultb. apply Z.ltb_lt. lia. }
    assert (hu1 : step sN = setPc sN (2147483792 + 148)).
    { rewrite (step1_bgeu sN 144 5 11 520 hcodeN ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcN ltac:(vm_compute; reflexivity)), hult.
      cbn match. rewrite hpcN, (wadd_id (2147483792 + 144) 4 ltac:(lia)).
      f_equal; lia. }
    set (sR1 := setPc sN (2147483792 + 148)) in *.
    assert (hmemR1 : sR1.(mem) = s.(mem)) by (unfold sR1; rewrite setPc_mem; exact hmemNS).
    assert (hcR1 : CodeLoaded1 sR1) by (apply (CodeLoaded1_eqmem s); [exact hmemR1| exact hcode]).
    assert (hpcR1 : sR1.(pc) = 2147483792 + 148) by reflexivity.
    (* step (148): add t3,a0,t0 *)
    assert (ha0R1 : rget sR1 10 = 2147484516).
    { unfold sR1. rewrite setPc_rget.
      rewrite (hothNS 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha0. }
    assert (haddr : wadd (rget sR1 10) (rget sR1 5) = 2147484516 + Z.of_nat idx1).
    { rewrite ha0R1. unfold sR1. rewrite setPc_rget, h5N. apply wadd_id. lia. }
    assert (hu2 : step sR1 = setPc (rset sR1 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 152)).
    { rewrite (step1_add sR1 148 28 10 5 hcR1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcR1 ltac:(vm_compute; reflexivity)), haddr, hpcR1,
        (wadd_id (2147483792 + 148) 4 ltac:(lia)). f_equal; lia. }
    set (sR2 := setPc (rset sR1 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 152)) in *.
    assert (hmemR2 : sR2.(mem) = s.(mem))
      by (unfold sR2; rewrite setPc_mem, rset_mem; exact hmemR1).
    assert (hcR2 : CodeLoaded1 sR2) by (apply (CodeLoaded1_eqmem s); [exact hmemR2| exact hcode]).
    assert (hpcR2 : sR2.(pc) = 2147483792 + 152) by reflexivity.
    (* step (152): lbu t2,0(t3) *)
    assert (hr28R2 : rget sR2 28 = 2147484516 + Z.of_nat idx1).
    { unfold sR2. rewrite setPc_rget, (rset_rget sR1 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hbyteIn : s.(mem) (2147484516 + Z.of_nat idx1) = nth idx1 inp 0).
    { pose proof (hinm (Z.of_nat idx1) ltac:(lia)) as h.
      unfold Image1.inputAddr in h. rewrite Nat2Z.id in h. exact h. }
    assert (hbyte : sR2.(mem) (wadd (rget sR2 28) 0) mod 256 = l).
    { rewrite hr28R2, (wadd_id (2147484516 + Z.of_nat idx1) 0 ltac:(lia)), Z.add_0_r,
        hmemR2, hbyteIn, Hl. apply Z.mod_small. exact Hlr. }
    assert (hu3 : step sR2 = setPc (rset sR2 7 l) (2147483792 + 156)).
    { rewrite (step1_lbu sR2 152 7 28 0 hcR2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcR2 ltac:(vm_compute; reflexivity)), hbyte, hpcR2,
        (wadd_id (2147483792 + 152) 4 ltac:(lia)). f_equal; lia. }
    set (sR3 := setPc (rset sR2 7 l) (2147483792 + 156)) in *.
    assert (hmemR3 : sR3.(mem) = s.(mem))
      by (unfold sR3; rewrite setPc_mem, rset_mem; exact hmemR2).
    assert (hcR3 : CodeLoaded1 sR3) by (apply (CodeLoaded1_eqmem s); [exact hmemR3| exact hcode]).
    assert (hpcR3 : sR3.(pc) = 2147483792 + 156) by reflexivity.
    (* step (156): addi t0,t0,1 *)
    assert (hr5R3 : rget sR3 5 = Z.of_nat idx1).
    { unfold sR3. rewrite setPc_rget, (rset_rget sR2 7 l 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 7) with false by reflexivity.
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 28 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 28) with false by reflexivity.
      unfold sR1. rewrite setPc_rget. exact h5N. }
    assert (hu4 : step sR3 = setPc (rset sR3 5 (Z.of_nat idx1 + 1)) (2147483792 + 160)).
    { rewrite (step1_addi sR3 156 5 5 1 hcR3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcR3 ltac:(vm_compute; reflexivity)), hr5R3,
        (wadd_id (Z.of_nat idx1) 1 ltac:(lia)), hpcR3,
        (wadd_id (2147483792 + 156) 4 ltac:(lia)). f_equal; lia. }
    set (sR4 := setPc (rset sR3 5 (Z.of_nat idx1 + 1)) (2147483792 + 160)) in *.
    assert (hmemR4 : sR4.(mem) = s.(mem))
      by (unfold sR4; rewrite setPc_mem, rset_mem; exact hmemR3).
    assert (hcR4 : CodeLoaded1 sR4) by (apply (CodeLoaded1_eqmem s); [exact hmemR4| exact hcode]).
    assert (hpcR4 : sR4.(pc) = 2147483792 + 160) by reflexivity.
    assert (h7R4 : rget sR4 7 = l).
    { unfold sR4. rewrite setPc_rget, (rset_rget sR3 5 _ 7 ltac:(lia) ltac:(lia)).
      replace (7 =? 5) with false by reflexivity.
      unfold sR3. rewrite setPc_rget, (rset_rget sR2 7 l 7 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (h5R4 : rget sR4 5 = Z.of_nat idx1 + 1).
    { unfold sR4. rewrite setPc_rget, (rset_rget sR3 5 _ 5 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hothR : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sR4 i = rget sN i).
    { intros i h0 h5 h7 h28.
      unfold sR4. rewrite setPc_rget, (rset_rget sR3 5 _ i ltac:(lia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      unfold sR3. rewrite setPc_rget, (rset_rget sR2 7 l i ltac:(lia) h0).
      replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sR1. rewrite setPc_rget. reflexivity. }
    assert (hothRS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sR4 i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (hothR i h0 h5 h7 h28). exact (hothNS i h0 h5 h7 h28). }
    assert (hpN0' : sN.(pc) <> 0) by (rewrite hpcN; lia).
    assert (hpR1 : sR1.(pc) <> 0) by (rewrite hpcR1; lia).
    assert (hpR2 : sR2.(pc) <> 0) by (rewrite hpcR2; lia).
    assert (hpR3 : sR3.(pc) <> 0) by (rewrite hpcR3; lia).
    assert (hrunR : runUntil 0 4 sN = sR4).
    { rewrite (runUntil_S 3 sN hpN0'), hu1, (runUntil_S 2 sR1 hpR1), hu2,
              (runUntil_S 1 sR2 hpR2), hu3, (runUntil_S 0 sR3 hpR3), hu4. reflexivity. }
    assert (hraR4 : rget sR4 1 = 0)
      by (rewrite (hothRS 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
    (* the stop check at 160 *)
    destruct (isLowStop1 l') eqn:Estop.
    + (* stop char in low position -> Split exit (652) *)
      destruct (p1_stop_split sR4 l hcR4 ltac:(rewrite hpcR4; unfold Image1.coreAddr; lia)
                  h7R4 Hlr Estop)
        as (k2 & hk2 & hpcE & hmemE & hframeE).
      set (sE := runUntil 0 k2 sR4) in *.
      assert (hcodeE : CodeLoaded1 sE).
      { apply (CodeLoaded1_eqmem s); [rewrite hmemE; exact hmemR4| exact hcode]. }
      assert (hraE : rget sE 1 = 0) by (rewrite (hframeE 1 ltac:(lia)); exact hraR4).
      destruct (exit_zero sE 652 3 hcodeE ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                  hpcE hraE ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) ltac:(lia))
        as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
      exists ((4 + (14 + k1)) + (4 + (k2 + 3)))%nat. right.
      split; [simpl length; lia|].
      rewrite (runUntil_add (4 + (14 + k1)) (4 + (k2 + 3))), hrunN,
              (runUntil_add 4 (k2 + 3)), hrunR, (runUntil_add k2 3).
      fold sE. rewrite hrunE.
      apply (error_result1 f inp cap lab pos Split1).
      * rewrite <- hspec2. change (zin (l :: rest'')) with (l' :: zin rest'').
        apply (scan1_low_stop hi lab pos l' (zin rest'') Estop).
      * discriminate.
      * exact hposle.
      * exact hfpc.
      * exact hf10.
      * exact hf11.
    + (* not a stop: fall to the low-nibble check (216) *)
      destruct (isLowStop1_false_ne l Hlr Estop)
        as (hl10 & hl32 & hl95 & hl35 & hl59 & hl58 & hl37).
      destruct (p1_stop_fall sR4 l hcR4
                  ltac:(rewrite hpcR4; unfold Image1.coreAddr; lia)
                  h7R4 Hlr hl10 hl32 hl95 hl35 hl59 hl58 hl37)
        as (sT & hrunT & hpcT & hmemT & hcodeT & hothT).
      assert (h7T : rget sT 7 = l) by (rewrite (hothT 7 ltac:(lia)); exact h7R4).
      destruct (nibble l') as [lo|] eqn:Enib.
      * (* valid low nibble: fall to the count at 252 *)
        destruct (p1_low_ok sT l lo hcodeT hpcT h7T Hlr Enib)
          as (k2 & hk2 & hpcU & hmemU & hframeU).
        set (sU := runUntil 0 k2 sT) in *.
        assert (hmemUS : sU.(mem) = s.(mem)).
        { rewrite hmemU, hmemT. exact hmemR4. }
        assert (hcodeU : CodeLoaded1 sU)
          by (apply (CodeLoaded1_eqmem s); [exact hmemUS| exact hcode]).
        assert (hothUS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
                  rget sU i = rget s i).
        { intros i h0 h5 h7 h28.
          rewrite (hframeU i h28), (hothT i h28). exact (hothRS i h0 h5 h7 h28). }
        assert (h6U : rget sU 6 = Z.of_nat pos)
          by (rewrite (hothUS 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx).
        assert (h13U : rget sU 13 = cap)
          by (rewrite (hothUS 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3).
        assert (h5U : rget sU 5 = Z.of_nat idx1 + 1).
        { rewrite (hframeU 5 ltac:(lia)), (hothT 5 ltac:(lia)). exact h5R4. }
        assert (hraU : rget sU 1 = 0)
          by (rewrite (hothUS 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
        assert (hpU0 : sU.(pc) <> 0) by (rewrite hpcU; unfold Image1.coreAddr; lia).
        (* spec: the byte is accepted, pos+1 *)
        assert (hspec3 : scan1 High1 lab ((pos + 1)%nat) (zin rest'')
                         = scan1 High1 noLabels 0 (zin inp)).
        { rewrite <- hspec2. change (zin (l :: rest'')) with (l' :: zin rest'').
          rewrite (scan1_low_ok hi lo lab pos l' (zin rest'') Estop Enib). reflexivity. }
        destruct (Z_lt_le_dec (Z.of_nat pos) cap) as [hroom|hshort].
        -- (* room: bgeu nt (252), t1++ (256), j36 (260) *)
           assert (hult2 : ultb (rget sU 6) (rget sU 13) = true).
           { rewrite h6U, h13U. unfold ultb. apply Z.ltb_lt. lia. }
           assert (hu5 : step sU = setPc sU (2147483792 + 256)).
           { rewrite (step1_bgeu sU 252 6 13 388 hcodeU ltac:(lia)
               ltac:(rewrite coreBytes1_len; lia) hpcU ltac:(vm_compute; reflexivity)),
               hult2.
             cbn match. rewrite hpcU.
             unfold Image1.coreAddr.
             rewrite (wadd_id (2147483792 + 252) 4 ltac:(lia)).
             f_equal; lia. }
           set (sV1 := setPc sU (2147483792 + 256)) in *.
           assert (hmemV1 : sV1.(mem) = s.(mem)) by (unfold sV1; rewrite setPc_mem; exact hmemUS).
           assert (hcV1 : CodeLoaded1 sV1)
             by (apply (CodeLoaded1_eqmem s); [exact hmemV1| exact hcode]).
           assert (hpcV1 : sV1.(pc) = 2147483792 + 256) by reflexivity.
           assert (h6V1 : rget sV1 6 = Z.of_nat pos) by (unfold sV1; rewrite setPc_rget; exact h6U).
           assert (hu6 : step sV1 = setPc (rset sV1 6 (Z.of_nat pos + 1)) (2147483792 + 260)).
           { rewrite (step1_addi sV1 256 6 6 1 hcV1 ltac:(lia)
               ltac:(rewrite coreBytes1_len; lia) hpcV1 ltac:(vm_compute; reflexivity)),
               h6V1, (wadd_id (Z.of_nat pos) 1 ltac:(lia)), hpcV1,
               (wadd_id (2147483792 + 256) 4 ltac:(lia)). f_equal; lia. }
           set (sV2 := setPc (rset sV1 6 (Z.of_nat pos + 1)) (2147483792 + 260)) in *.
           assert (hmemV2 : sV2.(mem) = s.(mem))
             by (unfold sV2; rewrite setPc_mem, rset_mem; exact hmemV1).
           assert (hcV2 : CodeLoaded1 sV2)
             by (apply (CodeLoaded1_eqmem s); [exact hmemV2| exact hcode]).
           assert (hpcV2 : sV2.(pc) = 2147483792 + 260) by reflexivity.
           assert (hu7 : step sV2 = setPc sV2 (2147483792 + 36)).
           { rewrite (step1_jal sV2 260 0 (-224) hcV2 ltac:(lia)
               ltac:(rewrite coreBytes1_len; lia) hpcV2 ltac:(vm_compute; reflexivity)),
               rset_zero, hpcV2, (wadd_id (2147483792 + 260) (-224) ltac:(lia)).
             f_equal; lia. }
           set (sF := setPc sV2 (2147483792 + 36)) in *.
           assert (hpV1 : sV1.(pc) <> 0) by (rewrite hpcV1; lia).
           assert (hpV2 : sV2.(pc) <> 0) by (rewrite hpcV2; lia).
           assert (hrunF : runUntil 0 ((4 + (14 + k1)) + (4 + (14 + (k2 + 3)))) s = sF).
           { rewrite (runUntil_add (4 + (14 + k1)) (4 + (14 + (k2 + 3)))), hrunN,
                     (runUntil_add 4 (14 + (k2 + 3))), hrunR,
                     (runUntil_add 14 (k2 + 3)), hrunT,
                     (runUntil_add k2 3).
             fold sU.
             rewrite (runUntil_S 2 sU hpU0), hu5, (runUntil_S 1 sV1 hpV1), hu6,
                     (runUntil_S 0 sV2 hpV2), hu7. reflexivity. }
           exists ((4 + (14 + k1)) + (4 + (14 + (k2 + 3))))%nat. left.
           exists rest''. exists ((pos + 1)%nat).
           rewrite hrunF.
           assert (hmemF : sF.(mem) = s.(mem)) by (unfold sF; rewrite setPc_mem; exact hmemV2).
           assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 6 -> i <> 7 -> i <> 28 ->
                     rget sF i = rget s i).
           { intros i h0 h5 h6 h7 h28.
             unfold sF. rewrite setPc_rget.
             unfold sV2. rewrite setPc_rget, (rset_rget sV1 6 _ i ltac:(lia) h0).
             replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
             unfold sV1. rewrite setPc_rget.
             exact (hothUS i h0 h5 h7 h28). }
           split; [simpl length; lia| split; [simpl length; lia|]].
           assert (hsufx2 : skipn (S idx1) inp = rest'').
           { replace (S idx1) with (1 + idx1)%nat by lia.
             rewrite <- skipn_skipn, hsufx. reflexivity. }
           refine {| p1_wf := hwf; p1_at_loop := _; p1_code := _; p1_a0 := _; p1_a1 := _;
                     p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
                     p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := _;
                     p1_tbl := _; p1_lab_le := _; p1_spec := hspec3 |}.
           ++ apply setPc_pc.
           ++ apply (CodeLoaded1_eqmem sV2); [reflexivity| exact hcV2].
           ++ rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
           ++ rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
           ++ rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
           ++ rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
           ++ rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
           ++ rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
           ++ apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
           ++ (* t0 = consumed count *)
              assert (hr5F : rget sF 5 = Z.of_nat idx1 + 1).
              { unfold sF. rewrite setPc_rget.
                unfold sV2. rewrite setPc_rget, (rset_rget sV1 6 _ 5 ltac:(lia) ltac:(lia)).
                replace (5 =? 6) with false by reflexivity.
                unfold sV1. rewrite setPc_rget. exact h5U. }
              rewrite hr5F. unfold idx1. simpl length in *. lia.
           ++ replace (length inp - length rest'')%nat with (S idx1)
                by (unfold idx1; simpl length in *; lia).
              exact hsufx2.
           ++ (* t1 = pos + 1 *)
              assert (hr6F : rget sF 6 = Z.of_nat pos + 1).
              { unfold sF. rewrite setPc_rget.
                unfold sV2. rewrite setPc_rget, (rset_rget sV1 6 _ 6 ltac:(lia) ltac:(lia)),
                  Z.eqb_refl. reflexivity. }
              rewrite hr6F. lia.
           ++ lia.
           ++ apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
           ++ intros c0 p0 h. pose proof (hlable c0 p0 h). lia.
        -- (* short: bgeu taken at 252 -> exit 640 *)
           assert (hult2 : ultb (rget sU 6) (rget sU 13) = false).
           { rewrite h6U, h13U. unfold ultb. apply Z.ltb_ge. lia. }
           assert (hu5 : step sU = setPc sU (2147483792 + 640)).
           { rewrite (step1_bgeu sU 252 6 13 388 hcodeU ltac:(lia)
               ltac:(rewrite coreBytes1_len; lia) hpcU ltac:(vm_compute; reflexivity)),
               hult2.
             cbn match. rewrite hpcU.
             unfold Image1.coreAddr.
             rewrite (wadd_id (2147483792 + 252) 388 ltac:(lia)).
             f_equal; lia. }
           set (sX := setPc sU (2147483792 + 640)) in *.
           assert (hcodeX : CodeLoaded1 sX)
             by (apply (CodeLoaded1_eqmem sU); [reflexivity| exact hcodeU]).
           assert (hpcX : sX.(pc) = Image1.coreAddr + 640)
             by (unfold Image1.coreAddr; reflexivity).
           assert (hraX : rget sX 1 = 0) by (unfold sX; rewrite setPc_rget; exact hraU).
           destruct (exit_zero sX 640 2 hcodeX ltac:(lia)
                       ltac:(rewrite coreBytes1_len; lia)
                       hpcX hraX ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(lia))
             as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
           destruct (scan1 High1 lab ((pos + 1)%nat) (zin rest'')) as [[labf m] stf] eqn:Hres.
           pose proof (scan1_pos_le (zin rest'') High1 lab ((pos + 1)%nat) labf m stf Hres)
             as hmono.
           assert (hscan_inp : scan1 High1 noLabels 0 (zin inp) = (labf, m, stf))
             by (rewrite <- hspec3; reflexivity).
           exists ((4 + (14 + k1)) + (4 + (14 + (k2 + (1 + 3)))))%nat. right.
           split; [simpl length; lia|].
           rewrite (runUntil_add (4 + (14 + k1)) (4 + (14 + (k2 + (1 + 3))))), hrunN,
                   (runUntil_add 4 (14 + (k2 + (1 + 3)))), hrunR,
                   (runUntil_add 14 (k2 + (1 + 3))), hrunT,
                   (runUntil_add k2 (1 + 3)).
           fold sU.
           rewrite (runUntil_add 1 3), (runUntil_one sU hpU0), hu5. fold sX.
           rewrite hrunE.
           exact (short_result1 f inp cap labf m stf hscan_inp ltac:(lia) hcap0
                    hfpc hf10 hf11).
      * (* invalid low char -> Unknown exit (676) *)
        destruct (p1_low_unk sT l hcodeT hpcT h7T Hlr Enib)
          as (k2 & hk2 & hpcU & hmemU & hframeU).
        set (sU := runUntil 0 k2 sT) in *.
        assert (hmemUS : sU.(mem) = s.(mem)).
        { rewrite hmemU, hmemT. exact hmemR4. }
        assert (hcodeU : CodeLoaded1 sU)
          by (apply (CodeLoaded1_eqmem s); [exact hmemUS| exact hcode]).
        assert (hraU : rget sU 1 = 0).
        { rewrite (hframeU 1 ltac:(lia)), (hothT 1 ltac:(lia)). exact hraR4. }
        destruct (exit_zero sU 676 5 hcodeU ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
                    hpcU hraU ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                    ltac:(vm_compute; reflexivity) ltac:(lia))
          as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
        exists ((4 + (14 + k1)) + (4 + (14 + (k2 + 3))))%nat. right.
        split; [simpl length; lia|].
        rewrite (runUntil_add (4 + (14 + k1)) (4 + (14 + (k2 + 3)))), hrunN,
                (runUntil_add 4 (14 + (k2 + 3))), hrunR,
                (runUntil_add 14 (k2 + 3)), hrunT,
                (runUntil_add k2 3).
        fold sU. rewrite hrunE.
        apply (error_result1 f inp cap lab pos Unknown1).
        -- rewrite <- hspec2. change (zin (l :: rest'')) with (l' :: zin rest'').
           apply (scan1_low_unk hi lab pos l' (zin rest'') Estop Enib).
        -- discriminate.
        -- exact hposle.
        -- exact hfpc.
        -- exact hf10.
        -- exact hf11.
Qed.

(** ** Pass-1 completion: the invalid-char iteration, EOF, the per-token
    dispatch, and the loop induction. *)

(* spec-side unfold for an invalid char in high position *)
Lemma scan1_high_unk c lab pos rest :
  isComment c = false -> isSpace c = false ->
  (c =? c_colon)%nat = false -> (c =? c_pct)%nat = false ->
  nibble c = None ->
  scan1 High1 lab pos (c :: rest) = (lab, pos, Unknown1).
Proof. intros h1 h2 h3 h4 h5. simp scan1. rewrite h1, h2, h3, h4, h5. reflexivity. Qed.

(* a non-token char (by the four bool tests) is none of the 7 dispatch chars *)
Lemma high_bools_ne c : 0 <= c < 256 ->
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false ->
  (Z.to_nat c =? c_colon)%nat = false -> (Z.to_nat c =? c_pct)%nat = false ->
  c <> 35 /\ c <> 59 /\ c <> 10 /\ c <> 32 /\ c <> 95 /\ c <> 58 /\ c <> 37.
Proof.
  intros hr h1 h2 h3 h4.
  repeat apply conj; intros He; rewrite He in h1, h2, h3, h4;
    vm_compute in h1, h2, h3, h4; congruence.
Qed.

(* A COMPLETE pass-1 iteration for an invalid first char: prefix + fall
   dispatch + high-nibble check fails -> Unknown exit (676). *)
Lemma p1_unk : forall inp cap c rest' lab pos s,
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false ->
  (Z.to_nat c =? c_colon)%nat = false -> (Z.to_nat c =? c_pct)%nat = false ->
  nibble (Z.to_nat c) = None ->
  P1Inv inp cap s lab pos (c :: rest') ->
  exists k, (k <= 50 * length ((c:Z) :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap.
Proof.
  intros inp cap c rest' lab pos s hbc hbs hbcol hbpct hn inv.
  destruct (p1_prefix inp cap c rest' lab pos s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  destruct (high_bools_ne c hcr hbc hbs hbcol hbpct)
    as (hne35 & hne59 & hne10 & hne32 & hne95 & hne58 & hne37).
  destruct (p1_fall_tail s4 c hcode4 hpc4 ht2 hcr
              hne35 hne59 hne10 hne32 hne95 hne58 hne37)
    as (sH & hrunH & hpcH & hmemH & hcodeH & hothH).
  destruct (p1_high_unk sH c hcodeH hpcH
              ltac:(rewrite (hothH 7 ltac:(lia)); exact ht2) hcr hn)
    as (k1 & hk1 & hpcU & hmemU & hframeU).
  set (sU := runUntil 0 k1 sH) in *.
  assert (hmemUS : sU.(mem) = s.(mem)).
  { rewrite hmemU, hmemH. exact hmem4. }
  assert (hcodeU : CodeLoaded1 sU)
    by (apply (CodeLoaded1_eqmem s); [exact hmemUS| exact hcode]).
  assert (hraU : rget sU 1 = 0).
  { rewrite (hframeU 1 ltac:(lia)), (hothH 1 ltac:(lia)),
      (hother4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact hra. }
  destruct (exit_zero sU 676 5 hcodeU ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
              hpcU hraU ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia))
    as (f & hrunE & hfpc & hf10 & hf11 & hfmem).
  exists ((4 + (14 + (k1 + 3))))%nat. split; [simpl length; lia|].
  rewrite (runUntil_add 4 (14 + (k1 + 3))), hrun4,
          (runUntil_add 14 (k1 + 3)), hrunH, (runUntil_add k1 3).
  fold sU. rewrite hrunE.
  apply (error_result1 f inp cap lab pos Unknown1).
  - rewrite <- hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    apply (scan1_high_unk (Z.to_nat c) lab pos (zin rest') hbc hbs hbcol hbpct hn).
  - discriminate.
  - exact hposle.
  - exact hfpc.
  - exact hf10.
  - exact hf11.
Qed.

(* EOF at the loop head: bgeu taken at 36 -> pass-2 entry (360). *)
Lemma p1_eof : forall inp cap lab pos s,
  P1Inv inp cap s lab pos [] ->
  exists s', runUntil 0 1 s = s' /\ P2Start inp cap s' lab pos.
Proof.
  intros inp cap lab pos s inv.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   hposle htbl hlable hspec].
  assert (h5' : rget s 5 = Z.of_nat (length inp))
    by (rewrite hidx; simpl length; lia).
  assert (hbt : step s = setPc s (Image1.coreAddr + 360)).
  { apply (bgeu1_eq_taken s 36 5 11 (Z.of_nat (length inp)) 324 _ hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc0 h5' ha1 ltac:(vm_compute; reflexivity)).
    rewrite (wadd_id (Image1.coreAddr + 36) 324 ltac:(unfold Image1.coreAddr; lia)).
    lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc0; unfold Image1.coreAddr; lia).
  exists (setPc s (Image1.coreAddr + 360)).
  split; [rewrite (runUntil_one s hp0), hbt; reflexivity|].
  refine {| p2s_wf := hwf; p2s_pc := _; p2s_code := _; p2s_a0 := _; p2s_a1 := _;
            p2s_a2 := _; p2s_a3 := _; p2s_a4 := _; p2s_ra := _; p2s_in_mem := _;
            p2s_tbl := _; p2s_m_le := hposle; p2s_lab_le := hlable;
            p2s_scan_ok := _ |}.
  - apply setPc_pc.
  - apply (CodeLoaded1_eqmem s); [reflexivity| exact hcode].
  - rewrite setPc_rget; exact ha0.
  - rewrite setPc_rget; exact ha1.
  - rewrite setPc_rget; exact ha2.
  - rewrite setPc_rget; exact ha3.
  - rewrite setPc_rget; exact ha4.
  - rewrite setPc_rget; exact hra.
  - apply (inputLoaded_eqmem s); [reflexivity| exact hinm].
  - apply (tableLoaded_eqmem s); [reflexivity| exact htbl].
  - rewrite <- hspec. change (zin (@nil Z)) with (@nil nat). apply scan1_nil.
Qed.

(* One pass-1 iteration: consume >= 1 char in <= 50 steps/char preserving
   P1Inv, or halt in a Result1 / reach pass-2 entry. Per-token dispatch. *)
Theorem p1_iteration : forall inp cap rest lab pos s,
  rest <> [] -> P1Inv inp cap s lab pos rest ->
  exists k,
    (exists rest2 lab2 pos2, (length rest2 < length rest)%nat /\
        (k <= 50 * (length rest - length rest2))%nat /\
        P1Inv inp cap (runUntil 0 k s) lab2 pos2 rest2)
    \/ ((k <= 50 * length rest)%nat /\
        (Result1 (runUntil 0 k s) inp cap \/
         exists labF m, P2Start inp cap (runUntil 0 k s) labF m)).
Proof.
  intros inp cap rest lab pos s hne inv.
  destruct rest as [|c rest']; [exfalso; apply hne; reflexivity|].
  pose proof inv as inv0.
  destruct inv0 as [hwf _ _ _ _ _ _ _ _ _ _ hsuf _ _ _ _].
  assert (HinC : In c inp).
  { rewrite <- (firstn_skipn (length inp - length (c :: rest')) inp).
    apply in_or_app. right. rewrite hsuf. left; reflexivity. }
  assert (hcr : 0 <= c < 256) by (apply (bytes_ok1 _ _ hwf); exact HinC).
  destruct (isComment (Z.to_nat c)) eqn:Ecm.
  - (* comment *)
    destruct (p1_comment inp cap c rest' lab pos s Ecm inv)
      as (k & [ (rest2 & hlt & hk & inv2) | (hk & hp2) ]).
    + exists k. left. exists rest2. exists lab. exists pos. tauto.
    + exists k. right. split; [exact hk|]. right. exists lab. exists pos. exact hp2.
  - destruct (isSpace (Z.to_nat c)) eqn:Esp.
    + (* spacing *)
      destruct (p1_spacing inp cap c rest' lab pos s Esp inv) as (k & hk & inv2).
      exists k. left. exists rest'. exists lab. exists pos.
      split; [simpl length; lia| split; [simpl length; lia| exact inv2]].
    + destruct (Z.eq_dec c 58) as [-> |hcol].
      * (* label definition *)
        destruct (p1_labelDef inp cap rest' lab pos s inv)
          as (k & [ (rest2 & lab2 & hlt & hk & inv2) | (hk & hres) ]).
        -- exists k. left. exists rest2. exists lab2. exists pos. tauto.
        -- exists k. right. split; [exact hk| left; exact hres].
      * destruct (Z.eq_dec c 37) as [-> |hpct].
        -- (* label reference *)
           destruct (p1_ref inp cap rest' lab pos s inv)
             as (k & [ (rest2 & pos2 & hlt & hk & inv2) | (hk & hres) ]).
           ++ exists k. left. exists rest2. exists lab. exists pos2. tauto.
           ++ exists k. right. split; [exact hk| left; exact hres].
        -- (* byte or invalid *)
           assert (hncol : (Z.to_nat c =? c_colon)%nat = false)
             by (apply Nat.eqb_neq; unfold c_colon; lia).
           assert (hnpct : (Z.to_nat c =? c_pct)%nat = false)
             by (apply Nat.eqb_neq; unfold c_pct; lia).
           destruct (nibble (Z.to_nat c)) as [hi|] eqn:En.
           ++ (* hex byte *)
              destruct (p1_byte inp cap c hi rest' lab pos s En inv)
                as (k & [ (rest2 & pos2 & hlt & hk & inv2) | (hk & hres) ]).
              ** exists k. left. exists rest2. exists lab. exists pos2. tauto.
              ** exists k. right. split; [exact hk| left; exact hres].
           ++ (* invalid char *)
              destruct (p1_unk inp cap c rest' lab pos s Ecm Esp hncol hnpct En inv)
                as (k & hk & hres).
              exists k. right. split; [exact hk| left; exact hres].
Qed.

(* Pass 1 runs to completion within 50*|rest|+1 steps: a halted Result1
   (pass-1 error) or pass-2 entry. Strong induction on the suffix bound. *)
Theorem pass1_correct : forall n inp cap rest lab pos s,
  (length rest <= n)%nat ->
  P1Inv inp cap s lab pos rest ->
  exists k, (k <= 50 * length rest + 1)%nat /\
    (Result1 (runUntil 0 k s) inp cap \/
     exists labF m, P2Start inp cap (runUntil 0 k s) labF m).
Proof.
  intros n. induction n as [|n IH]; intros inp cap rest lab pos s hn inv.
  - assert (hr : rest = []) by (destruct rest; [reflexivity| simpl in hn; lia]).
    subst rest.
    destruct (p1_eof inp cap lab pos s inv) as (s' & hrun & hp2).
    exists 1%nat. split; [simpl; lia|]. right. exists lab. exists pos.
    rewrite hrun. exact hp2.
  - destruct rest as [|c rest'].
    + destruct (p1_eof inp cap lab pos s inv) as (s' & hrun & hp2).
      exists 1%nat. split; [simpl; lia|]. right. exists lab. exists pos.
      rewrite hrun. exact hp2.
    + destruct (p1_iteration inp cap (c :: rest') lab pos s ltac:(discriminate) inv)
        as (k1 & [ (rest2 & lab2 & pos2 & hlt & hk1 & inv2) | (hk1 & hres) ]).
      * destruct (IH inp cap rest2 lab2 pos2 (runUntil 0 k1 s)
                    ltac:(simpl length in *; lia) inv2)
          as (k2 & hk2 & hres2).
        exists (k1 + k2)%nat. split; [simpl length in *; lia|].
        rewrite runUntil_add. exact hres2.
      * exists k1. split; [simpl length in *; lia| exact hres].
Qed.

(** ** Pass 2: the emit loop invariant, entry, and exits. *)

(* readMem extension: one more byte at the end *)
Lemma readMem_snoc : forall len m base,
  readMem m base (S len) = readMem m base len ++ [Z.to_nat (m (base + Z.of_nat len))].
Proof.
  induction len; intros m base.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - replace (base + Z.of_nat (S len)) with ((base + 1) + Z.of_nat len) by lia.
    change (readMem m base (S (S len)))
      with (Z.to_nat (m base) :: readMem m (base + 1) (S len)).
    rewrite IHlen. reflexivity.
Qed.

(* readMem only depends on the window it reads *)
Lemma readMem_frame : forall len m m' base,
  (forall a, base <= a < base + Z.of_nat len -> m' a = m a) ->
  readMem m' base len = readMem m base len.
Proof.
  induction len; intros m m' base h; simpl; [reflexivity|].
  f_equal.
  - f_equal. apply h. lia.
  - apply IHlen. intros a ha. apply h. lia.
Qed.

(* Pass-1 entry (offsets 28, 32): zero t0/t1, establishing P1Inv on the
   whole input with the empty label map. *)
Lemma p1_entry : forall inp cap s,
  WellFormed1 inp cap -> Pass1Entry inp cap s ->
  exists s', runUntil 0 2 s = s' /\ P1Inv inp cap s' noLabels 0 inp.
Proof.
  intros inp cap s hwf pe.
  destruct pe as [hpc hcode ha0 ha1 ha2 ha3 ha4 hra hinm htbl].
  pose proof (cap_nonneg _ _ hwf) as hcap0.
  assert (hu1 : step s = setPc (rset s 5 0) (Image1.coreAddr + 32)).
  { rewrite (step1_addi s 28 5 0 0 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
      hpc ltac:(vm_compute; reflexivity)),
      rget_zero, (wadd_id 0 0 ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + 28) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; unfold Image1.coreAddr; lia. }
  set (s1 := setPc (rset s 5 0) (Image1.coreAddr + 32)) in *.
  assert (hc1 : CodeLoaded1 s1) by
    (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + 32) by reflexivity.
  assert (hu2 : step s1 = setPc (rset s1 6 0) (Image1.coreAddr + 36)).
  { rewrite (step1_addi s1 32 6 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
      hpc1 ltac:(vm_compute; reflexivity)),
      rget_zero, (wadd_id 0 0 ltac:(lia)), Z.add_0_l, hpc1,
      (wadd_id (Image1.coreAddr + 32) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; unfold Image1.coreAddr; lia. }
  set (s2 := setPc (rset s1 6 0) (Image1.coreAddr + 36)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem, rset_mem; reflexivity).
  assert (hreg2 : forall i, i <> 0 -> i <> 5 -> i <> 6 -> rget s2 i = rget s i).
  { intros i h0 h5 h6.
    unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 i ltac:(lia) h0).
    replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
    unfold s1. rewrite setPc_rget, (rset_rget s 5 0 i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hq1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  exists s2. split.
  { rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hq1), hu2. reflexivity. }
  refine {| p1_wf := hwf; p1_at_loop := _; p1_code := _; p1_a0 := _; p1_a1 := _;
            p1_a2 := _; p1_a3 := _; p1_a4 := _; p1_ra := _; p1_in_mem := _;
            p1_idx := _; p1_suffix := _; p1_outidx := _; p1_pos_le := _;
            p1_tbl := _; p1_lab_le := _; p1_spec := _ |}.
  - apply setPc_pc.
  - apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode].
  - rewrite (hreg2 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
  - rewrite (hreg2 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
  - rewrite (hreg2 12 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
  - rewrite (hreg2 13 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
  - rewrite (hreg2 14 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
  - rewrite (hreg2 1 ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
  - apply (inputLoaded_eqmem s); [exact hmem2| exact hinm].
  - assert (h5 : rget s2 5 = 0).
    { unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 6) with false by reflexivity.
      unfold s1. rewrite setPc_rget, (rset_rget s 5 0 5 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    rewrite h5. lia.
  - rewrite Nat.sub_diag. reflexivity.
  - unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 6 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity.
  - simpl. exact hcap0.
  - apply (tableLoaded_eqmem s); [exact hmem2| exact htbl].
  - intros c p h. discriminate h.
  - reflexivity.
Qed.

(* Invariant at the pass-2 loop head (offset 368). [labF] is the final label
   map (the table is never written in pass 2); [emitted] the bytes written so
   far; [rest] the unconsumed suffix. [labNow]/[m] pin the residual scan,
   which is Ok ([p2_scan_ok]) -- control-flow totality + write bounds.
   [p2_spec] is the emit telescope. *)
Record P2Inv (inp : list Z) (cap : Z) (s : State) (labF labNow : Labels)
    (m : nat) (emitted : list nat) (rest : list Z) : Prop := {
  p2_wf      : WellFormed1 inp cap;
  p2_at_loop : s.(pc) = Image1.coreAddr + 368;
  p2_code    : CodeLoaded1 s;
  p2_a0      : rget s 10 = Image1.inputAddr;
  p2_a1      : rget s 11 = Z.of_nat (length inp);
  p2_a2      : rget s 12 = Image1.outAddr;
  p2_a3      : rget s 13 = cap;
  p2_a4      : rget s 14 = Image1.lblAddr;
  p2_ra      : rget s 1 = 0;
  p2_in_mem  : InputLoaded s inp;
  p2_idx     : rget s 5 = Z.of_nat (length inp) - Z.of_nat (length rest);
  p2_suffix  : skipn (length inp - length rest) inp = rest;
  p2_outidx  : rget s 6 = Z.of_nat (length emitted);
  p2_out_mem : readMem s.(mem) Image1.outAddr (length emitted) = emitted;
  p2_tbl     : TableLoaded s labF;
  p2_m_le    : Z.of_nat m <= cap;
  p2_lab_le  : forall c p, labF c = Some p -> (p <= m)%nat;
  p2_scan_inp : scan1 High1 noLabels 0 (zin inp) = (labF, m, Ok1);
  p2_scan_ok : scan1 High1 labNow (length emitted) (zin rest) = (labF, m, Ok1);
  p2_spec    : emit1 High1 labF 0 (zin inp)
               = (emitted ++ fst (emit1 High1 labF (length emitted) (zin rest)),
                  snd (emit1 High1 labF (length emitted) (zin rest)))
}.

(* Pass-2 entry (offsets 360, 364): zero t0/t1, establishing the loop
   invariant on the whole input with nothing emitted. *)
Lemma p2_entry : forall inp cap labF m s,
  P2Start inp cap s labF m ->
  exists s', runUntil 0 2 s = s' /\ P2Inv inp cap s' labF noLabels m [] inp.
Proof.
  intros inp cap labF m s hp2.
  destruct hp2 as [hwf hpc hcode ha0 ha1 ha2 ha3 ha4 hra hinm htbl hmle hlable hscan].
  assert (hu1 : step s = setPc (rset s 5 0) (Image1.coreAddr + 364)).
  { rewrite (step1_addi s 360 5 0 0 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
      hpc ltac:(vm_compute; reflexivity)),
      rget_zero, (wadd_id 0 0 ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (Image1.coreAddr + 360) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; unfold Image1.coreAddr; lia. }
  set (s1 := setPc (rset s 5 0) (Image1.coreAddr + 364)) in *.
  assert (hc1 : CodeLoaded1 s1) by
    (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + 364) by reflexivity.
  assert (hu2 : step s1 = setPc (rset s1 6 0) (Image1.coreAddr + 368)).
  { rewrite (step1_addi s1 364 6 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
      hpc1 ltac:(vm_compute; reflexivity)),
      rget_zero, (wadd_id 0 0 ltac:(lia)), Z.add_0_l, hpc1,
      (wadd_id (Image1.coreAddr + 364) 4 ltac:(unfold Image1.coreAddr; lia)).
    f_equal; unfold Image1.coreAddr; lia. }
  set (s2 := setPc (rset s1 6 0) (Image1.coreAddr + 368)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem, rset_mem; reflexivity).
  assert (hreg2 : forall i, i <> 0 -> i <> 5 -> i <> 6 -> rget s2 i = rget s i).
  { intros i h0 h5 h6.
    unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 i ltac:(lia) h0).
    replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
    unfold s1. rewrite setPc_rget, (rset_rget s 5 0 i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
  assert (hq1 : s1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
  exists s2. split.
  { rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hq1), hu2. reflexivity. }
  refine {| p2_wf := hwf; p2_at_loop := _; p2_code := _; p2_a0 := _; p2_a1 := _;
            p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
            p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
            p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
            p2_scan_inp := hscan; p2_scan_ok := _; p2_spec := _ |}.
  - apply setPc_pc.
  - apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode].
  - rewrite (hreg2 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
  - rewrite (hreg2 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
  - rewrite (hreg2 12 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
  - rewrite (hreg2 13 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
  - rewrite (hreg2 14 ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
  - rewrite (hreg2 1 ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
  - apply (inputLoaded_eqmem s); [exact hmem2| exact hinm].
  - assert (h5 : rget s2 5 = 0).
    { unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 6) with false by reflexivity.
      unfold s1. rewrite setPc_rget, (rset_rget s 5 0 5 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    rewrite h5. lia.
  - rewrite Nat.sub_diag. reflexivity.
  - unfold s2. rewrite setPc_rget, (rset_rget s1 6 0 6 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity.
  - reflexivity.
  - apply (tableLoaded_eqmem s); [exact hmem2| exact htbl].
  - exact hscan.
  - cbn [length]. destruct (emit1 High1 labF 0 (zin inp)) as [out st]. reflexivity.
Qed.

(* Build a Result1 for a pass-2 exit (Ok or Undef): the machine halted with
   a0 = statusCode, a1 = |emitted|, the out region holding [emitted], while
   scan and emit agree. *)
Lemma emit_result1 : forall f inp cap labF m emitted st',
  st' = Ok1 \/ st' = Undef1 ->
  f.(pc) = 0 ->
  rget f 10 = Z.of_nat (statusCode1 st') ->
  rget f 11 = Z.of_nat (length emitted) ->
  readMem f.(mem) Image1.outAddr (length emitted) = emitted ->
  scan1 High1 noLabels 0 (zin inp) = (labF, m, Ok1) ->
  Z.of_nat m <= cap ->
  emit1 High1 labF 0 (zin inp) = (emitted, st') ->
  Result1 f inp cap.
Proof.
  intros f inp cap labF m emitted st' hst hp h10 h11 hout hscan hm hemit.
  assert (hcapm : (Z.to_nat cap <? m)%nat = false) by (apply Nat.ltb_ge; lia).
  assert (hcs : coreSpec1 (zin inp) (Z.to_nat cap)
                = (statusCode1 st', emitted, length emitted)).
  { unfold coreSpec1, decode1. rewrite hscan, hemit, hcapm.
    destruct hst as [-> | ->]; reflexivity. }
  unfold Result1. rewrite hcs.
  repeat apply conj.
  - exact hp.
  - exact h10.
  - exact h11.
  - exact hout.
Qed.

(* The Ok exit (628): li a0,0; mv a1,t1; ret. *)
Lemma p2_ok_exit : forall inp cap labF m emitted s,
  s.(pc) = Image1.coreAddr + 628 -> CodeLoaded1 s -> rget s 1 = 0 ->
  rget s 6 = Z.of_nat (length emitted) ->
  Z.of_nat (length emitted) < 2 ^ 63 ->
  readMem s.(mem) Image1.outAddr (length emitted) = emitted ->
  scan1 High1 noLabels 0 (zin inp) = (labF, m, Ok1) ->
  Z.of_nat m <= cap ->
  emit1 High1 labF 0 (zin inp) = (emitted, Ok1) ->
  exists f, runUntil 0 3 s = f /\ Result1 f inp cap.
Proof.
  intros inp cap labF m emitted s hpc hcode hra h6 hlen hout hscan hm hemit.
  destruct (exit_t1 s 628 0 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc hra
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite h6; lia))
    as (f & hrun & hfpc & hf10 & hf11 & hfmem).
  exists f. split; [exact hrun|].
  apply (emit_result1 f inp cap labF m emitted Ok1).
  - left; reflexivity.
  - exact hfpc.
  - exact hf10.
  - rewrite hf11. exact h6.
  - rewrite hfmem. exact hout.
  - exact hscan.
  - exact hm.
  - exact hemit.
Qed.

(* The Undef exit (700): li a0,7; mv a1,t1; ret. *)
Lemma p2_undef_exit : forall inp cap labF m emitted s,
  s.(pc) = Image1.coreAddr + 700 -> CodeLoaded1 s -> rget s 1 = 0 ->
  rget s 6 = Z.of_nat (length emitted) ->
  Z.of_nat (length emitted) < 2 ^ 63 ->
  readMem s.(mem) Image1.outAddr (length emitted) = emitted ->
  scan1 High1 noLabels 0 (zin inp) = (labF, m, Ok1) ->
  Z.of_nat m <= cap ->
  emit1 High1 labF 0 (zin inp) = (emitted, Undef1) ->
  exists f, runUntil 0 3 s = f /\ Result1 f inp cap.
Proof.
  intros inp cap labF m emitted s hpc hcode hra h6 hlen hout hscan hm hemit.
  destruct (exit_t1 s 700 7 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc hra
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite h6; lia))
    as (f & hrun & hfpc & hf10 & hf11 & hfmem).
  exists f. split; [exact hrun|].
  apply (emit_result1 f inp cap labF m emitted Undef1).
  - right; reflexivity.
  - exact hfpc.
  - exact hf10.
  - rewrite hf11. exact h6.
  - rewrite hfmem. exact hout.
  - exact hscan.
  - exact hm.
  - exact hemit.
Qed.

(* The shared head of every non-EOF pass-2 iteration (offsets 368..380):
   bgeu (not taken) -> add -> lbu (read char c) -> addi (bump index).
   Lands at offset 384 with t2 = c. *)
Lemma p2_prefix : forall inp cap c rest' labF labNow m emitted s,
  P2Inv inp cap s labF labNow m emitted (c :: rest') ->
  exists s4, runUntil 0 4 s = s4 /\
    s4.(pc) = Image1.coreAddr + 384 /\
    rget s4 7 = c /\ 0 <= c < 256 /\
    rget s4 5 = Z.of_nat (length inp) - Z.of_nat (length rest') /\
    s4.(mem) = s.(mem) /\ CodeLoaded1 s4 /\
    (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget s4 i = rget s i).
Proof.
  intros inp cap c rest' labF labNow m emitted s inv.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf.
  set (k := (length inp - length (c :: rest'))%nat) in *.
  set (jZ := Z.of_nat (length inp) - Z.of_nat (length (c :: rest'))) in *.
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    fold k in Hl. lia. }
  assert (htonat : Z.to_nat jZ = k).
  { unfold jZ, k. rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id. reflexivity. }
  assert (hjpos : 0 <= jZ) by (unfold jZ; lia).
  assert (hjlt : jZ < Z.of_nat (length inp)) by (unfold jZ; simpl length; lia).
  assert (Hc : nth k inp 0 = c).
  { transitivity (nth 0 (skipn k inp) 0).
    - rewrite nth_skipn. f_equal. lia.
    - rewrite hsuf. reflexivity. }
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn k inp). apply in_or_app. right.
    fold k in hsuf. rewrite hsuf. left; reflexivity. }
  assert (Hcr : 0 <= c < 256) by (apply (bytes_ok1 _ _ hwf); exact Hin).
  unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
  (* step 1: bgeu t0,a1,+260 NOT taken (idx < len) -> off 372 *)
  assert (hult : ultb (rget s 5) (rget s 11) = true).
  { rewrite hidx, ha1. unfold ultb. apply Z.ltb_lt. exact hjlt. }
  assert (hu1 : step s = setPc s (2147483792 + 372)).
  { rewrite (step1_bgeu s 368 5 11 260 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
              hpc0 ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc0, (wadd_id (2147483792 + 368) 4 ltac:(lia)). f_equal; lia. }
  set (s1 := setPc s (2147483792 + 372)) in *.
  assert (hc1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = 2147483792 + 372) by reflexivity.
  (* step 2: add t3,a0,t0 -> off 376 *)
  assert (haddr : wadd (rget s1 10) (rget s1 5) = 2147484516 + jZ).
  { unfold s1. rewrite !setPc_rget, ha0, hidx. apply wadd_id. lia. }
  assert (hu2 : step s1 = setPc (rset s1 28 (2147484516 + jZ)) (2147483792 + 376)).
  { rewrite (step1_add s1 372 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc1
              ltac:(vm_compute; reflexivity)), haddr, hpc1,
            (wadd_id (2147483792 + 372) 4 ltac:(lia)). f_equal; lia. }
  set (s2 := setPc (rset s1 28 (2147484516 + jZ)) (2147483792 + 376)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded1 s2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = 2147483792 + 376) by reflexivity.
  (* step 3: lbu t2,0(t3) -> off 380 *)
  assert (hr28_2 : rget s2 28 = 2147484516 + jZ).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)),
      Z.eqb_refl. reflexivity. }
  assert (hbyteIn : s.(mem) (2147484516 + jZ) = nth (Z.to_nat jZ) inp 0).
  { pose proof (hinm jZ ltac:(lia)) as h. unfold Image1.inputAddr in h. exact h. }
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = c).
  { rewrite hr28_2, (wadd_id (2147484516 + jZ) 0 ltac:(lia)), Z.add_0_r,
            hmem2, hbyteIn, htonat, Hc.
    apply Z.mod_small. exact Hcr. }
  assert (hu3 : step s2 = setPc (rset s2 7 c) (2147483792 + 380)).
  { rewrite (step1_lbu s2 376 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc2
              ltac:(vm_compute; reflexivity)), hbyte, hpc2,
            (wadd_id (2147483792 + 376) 4 ltac:(lia)). f_equal; lia. }
  set (s3 := setPc (rset s2 7 c) (2147483792 + 380)) in *.
  assert (hmem3 : s3.(mem) = s.(mem))
    by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded1 s3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = 2147483792 + 380) by reflexivity.
  (* step 4: addi t0,t0,1 -> off 384 *)
  assert (hr5_3 : rget s3 5 = jZ).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact hidx. }
  assert (hu4 : step s3 = setPc (rset s3 5 (jZ + 1)) (2147483792 + 384)).
  { rewrite (step1_addi s3 380 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc3
              ltac:(vm_compute; reflexivity)), hr5_3,
            (wadd_id jZ 1 ltac:(lia)), hpc3,
            (wadd_id (2147483792 + 380) 4 ltac:(lia)). f_equal; lia. }
  set (s4 := setPc (rset s3 5 (jZ + 1)) (2147483792 + 384)) in *.
  assert (hmem4 : s4.(mem) = s.(mem))
    by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc0; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; lia).
  exists s4. repeat apply conj.
  - rewrite (runUntil_S 3 s hp0), hu1, (runUntil_S 2 s1 hp1), hu2,
            (runUntil_S 1 s2 hp2), hu3, (runUntil_S 0 s3 hp3), hu4. reflexivity.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - lia.
  - lia.
  - assert (H54 : rget s4 5 = jZ + 1)
      by (unfold s4; rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 5 ltac:(lia) ltac:(lia)),
            Z.eqb_refl; reflexivity).
    rewrite H54. unfold jZ. simpl length. lia.
  - exact hmem4.
  - apply (CodeLoaded1_eqmem s); [exact hmem4| exact hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(** ** Pass-2 iteration: spacing and comment tokens (textual ports of the
    pass-1 versions; offsets 384..420 dispatch, 600..624 comment loop). *)

(* spec-side emit1 unfolds (mirror the scan1 set) *)
Lemma emit1_nil lab pos : emit1 High1 lab pos [] = ([], Ok1).
Proof. now simp emit1. Qed.

Lemma emit1_comment c rest lab pos : isComment c = true ->
  emit1 High1 lab pos (c :: rest) = emit1 High1 lab pos (skipComment rest).
Proof. intros h. simp emit1. rewrite h. reflexivity. Qed.

Lemma emit1_spacing c rest lab pos : isComment c = false -> isSpace c = true ->
  emit1 High1 lab pos (c :: rest) = emit1 High1 lab pos rest.
Proof. intros h1 h2. simp emit1. rewrite h1, h2. reflexivity. Qed.

Lemma emit1_colon lab pos rest :
  emit1 High1 lab pos (58%nat :: rest) = emit1 Col1 lab pos rest.
Proof. simp emit1. reflexivity. Qed.

Lemma emit1_col_cons lab pos lc rest :
  emit1 Col1 lab pos (lc :: rest) = emit1 High1 lab pos rest.
Proof. now simp emit1. Qed.

Lemma emit1_pct lab pos rest :
  emit1 High1 lab pos (37%nat :: rest) = emit1 Pct1 lab pos rest.
Proof. simp emit1. reflexivity. Qed.

Lemma emit1_pct_cons lab pos lc rest :
  emit1 Pct1 lab pos (lc :: rest)
  = match lab lc with
    | None => ([], Undef1)
    | Some p => appOut (offBytes p pos) (emit1 High1 lab (pos + 4) rest)
    end.
Proof. now simp emit1. Qed.

Lemma emit1_high_nibble c hi lab pos rest :
  isComment c = false -> isSpace c = false ->
  (c =? c_colon)%nat = false -> (c =? c_pct)%nat = false ->
  nibble c = Some hi ->
  emit1 High1 lab pos (c :: rest) = emit1 (Low1 hi) lab pos rest.
Proof. intros h1 h2 h3 h4 h5. simp emit1. rewrite h1, h2, h3, h4, h5. reflexivity. Qed.

Lemma emit1_low_ok hi lo lab pos lc rest :
  isLowStop1 lc = false -> nibble lc = Some lo ->
  emit1 (Low1 hi) lab pos (lc :: rest)
  = consOut (hi * 16 + lo) (emit1 High1 lab (pos + 1) rest).
Proof. intros h1 h2. simp emit1. rewrite h1, h2. reflexivity. Qed.

(* dispatch 384..420 back to the loop head for a spacing char (port of
   p1_spacing_tail; the #/; blocks are not taken). *)
(* The pass-1 spacing dispatch (from offset 384, t2 = c in {10,32,95}): the
   li;beq chain falls through '#'(384)/';'(392) and branches back to the loop
   head (368) at the matching spacing char (400/408/416). Touches only t3/pc. *)
Lemma p2_spacing_tail s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 384 -> rget s4 7 = c ->
  0 <= c -> isSpace (Z.to_nat c) = true ->
  exists k, (k <= 10)%nat /\ (runUntil 0 k s4).(pc) = Image1.coreAddr + 368 /\
            (runUntil 0 k s4).(mem) = s4.(mem) /\
            (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc ht2 h0 hss.
  destruct (isSpace_cases c h0 hss) as [hc|[hc|hc]].
  all: assert (hne35 : c <> 35) by lia.
  all: assert (hne59 : c <> 59) by lia.
  (* block at off 384 (K=35), not taken *)
  all: pose proof (li1_beq_ne s4 384 35 c 212 hcode ltac:(lia)
         ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne35) as hb1.
  all: set (s_b := setPc (rset s4 28 35) (Image1.coreAddr + (384 + 8))) in *.
  all: assert (hcb : CodeLoaded1 s_b) by
         (apply (CodeLoaded1_eqmem s4); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcb : s_b.(pc) = Image1.coreAddr + 392) by (unfold s_b; cbn; lia).
  all: assert (h7b : rget s_b 7 = c) by
         (unfold s_b; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  (* block at off 392 (K=59), not taken *)
  all: pose proof (li1_beq_ne s_b 392 59 c 204 hcb ltac:(lia)
         ltac:(rewrite coreBytes1_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne59) as hb2.
  all: set (s_c := setPc (rset s_b 28 59) (Image1.coreAddr + (392 + 8))) in *.
  all: assert (hcc : CodeLoaded1 s_c) by
         (apply (CodeLoaded1_eqmem s4); [unfold s_c; rewrite setPc_mem, rset_mem;
            unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcc : s_c.(pc) = Image1.coreAddr + 400) by (unfold s_c; cbn; lia).
  all: assert (h7c : rget s_c 7 = c) by
         (unfold s_c; rewrite (li_block_frame s_b 59 _ 7 ltac:(lia)); exact h7b).
  - (* c = 10: taken at off 400 *)
    pose proof (li1_beq_eq s_c 400 10 c (-36) (Image1.coreAddr + 368) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (400 + 4)) (-36)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb3.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s4 = setPc (rset s_c 28 10) (Image1.coreAddr + 368))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, hb3; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
  - (* c = 32: not taken at 400, taken at 408 *)
    pose proof (li1_beq_ne s_c 400 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (Image1.coreAddr + (400 + 8))) in *.
    assert (hcd : CodeLoaded1 s_d) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = Image1.coreAddr + 408) by (unfold s_d; cbn; lia).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 _ 7 ltac:(lia)); exact h7c).
    pose proof (li1_beq_eq s_d 408 32 c (-44) (Image1.coreAddr + 368) hcd ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (408 + 4)) (-44)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb4.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s4
                   = setPc (rset s_d 28 32) (Image1.coreAddr + 368))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem.
      unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem.
      reflexivity.
    + intros i hi. rewrite (li_block_frame s_d 32 _ i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
  - (* c = 95: not taken at 400/408, taken at 416 *)
    pose proof (li1_beq_ne s_c 400 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (Image1.coreAddr + (400 + 8))) in *.
    assert (hcd : CodeLoaded1 s_d) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = Image1.coreAddr + 408) by (unfold s_d; cbn; lia).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 _ 7 ltac:(lia)); exact h7c).
    pose proof (li1_beq_ne s_d 408 32 c (-44) hcd ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (s_e := setPc (rset s_d 28 32) (Image1.coreAddr + (408 + 8))) in *.
    assert (hce : CodeLoaded1 s_e) by
      (apply (CodeLoaded1_eqmem s4); [unfold s_e; rewrite setPc_mem, rset_mem;
         unfold s_d; rewrite setPc_mem, rset_mem; unfold s_c; rewrite setPc_mem, rset_mem;
         unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpce : s_e.(pc) = Image1.coreAddr + 416) by (unfold s_e; cbn; lia).
    assert (h7e : rget s_e 7 = c) by
      (unfold s_e; rewrite (li_block_frame s_d 32 _ 7 ltac:(lia)); exact h7d).
    pose proof (li1_beq_eq s_e 416 95 c (-52) (Image1.coreAddr + 368) hce ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpce h7e ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (Image1.coreAddr + (416 + 4)) (-52)
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb5.
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 2)))) s4
                   = setPc (rset s_e 28 95) (Image1.coreAddr + 368))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
                  runUntil_add, hb4, hb5; reflexivity).
    exists (2 + (2 + (2 + (2 + 2))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_e. rewrite setPc_mem, rset_mem.
      unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_e 95 _ i hi).
      unfold s_e. rewrite (li_block_frame s_d 32 _ i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 _ i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 _ i hi).
      unfold s_b. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* The 4-instruction head of the comment inner loop (600..612):
   bgeu(not taken) -> add -> lbu (read inp[idx]) -> li t3,10.
   Reaches offset 616 with t2 = inp[idx], t3 = 10, t0 unchanged. *)
Lemma comment_read2 s inp idx ch :
  CodeLoaded1 s -> s.(pc) = Image1.coreAddr + 600 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = Image1.inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  (idx < length inp)%nat ->
  Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  InputLoaded s inp ->
  nth idx inp 0 = ch -> 0 <= ch < 256 ->
  (runUntil 0 4 s).(pc) = Image1.coreAddr + 616 /\ rget (runUntil 0 4 s) 7 = ch /\
  rget (runUntil 0 4 s) 28 = 10 /\ rget (runUntil 0 4 s) 5 = Z.of_nat idx /\
  (runUntil 0 4 s).(mem) = s.(mem) /\ CodeLoaded1 (runUntil 0 4 s) /\
  (forall i, i <> 7 -> i <> 28 -> rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros hcode hpc Hidx Ha0 Ha1 hlt hin_fit Hinmem Hch Hcr.
  assert (HinmemX : forall j, 0 <= j < Z.of_nat (length inp) ->
            s.(mem) (2147484516 + j) = nth (Z.to_nat j) inp 0).
  { intros j hj. pose proof (Hinmem j hj) as h. unfold Image1.inputAddr in h. exact h. }
  unfold Image1.inputAddr, Image1.coreAddr in *.
  assert (hult : ultb (rget s 5) (rget s 11) = true)
    by (rewrite Hidx, Ha1; unfold ultb; apply Z.ltb_lt; apply Nat2Z.inj_lt; exact hlt).
  assert (hs1 : step s = setPc s (2147483792 + 604)).
  { rewrite (step1_bgeu s 600 5 11 28 hcode ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc
      ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc, (wadd_id (2147483792 + 600) 4 ltac:(lia)). f_equal; lia. }
  set (s1 := setPc s (2147483792 + 604)) in *.
  assert (hc1 : CodeLoaded1 s1) by
    (apply (CodeLoaded1_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = 2147483792 + 604) by reflexivity.
  assert (haddr : wadd (rget s1 10) (rget s1 5) = 2147484516 + Z.of_nat idx).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (2147484516 + Z.of_nat idx)) (2147483792 + 608)).
  { rewrite (step1_add s1 604 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc1
      ltac:(vm_compute; reflexivity)), haddr, hpc1,
      (wadd_id (2147483792 + 604) 4 ltac:(lia)). f_equal; lia. }
  set (s2 := setPc (rset s1 28 (2147484516 + Z.of_nat idx)) (2147483792 + 608)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded1 s2) by (apply (CodeLoaded1_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = 2147483792 + 608) by reflexivity.
  assert (hr28 : rget s2 28 = 2147484516 + Z.of_nat idx) by
    (unfold s2; rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl;
     reflexivity).
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = ch).
  { rewrite hr28, (wadd_id (2147484516 + Z.of_nat idx) 0 ltac:(lia)), Z.add_0_r,
      hmem2, (HinmemX (Z.of_nat idx) ltac:(split; [lia| apply Nat2Z.inj_lt; exact hlt])),
      Nat2Z.id, Hch.
    apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 ch) (2147483792 + 612)).
  { rewrite (step1_lbu s2 608 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc2
      ltac:(vm_compute; reflexivity)), hbyte, hpc2,
      (wadd_id (2147483792 + 608) 4 ltac:(lia)). f_equal; lia. }
  set (s3 := setPc (rset s2 7 ch) (2147483792 + 612)) in *.
  assert (hmem3 : s3.(mem) = s.(mem)) by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded1 s3) by (apply (CodeLoaded1_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = 2147483792 + 612) by reflexivity.
  assert (hs4 : step s3 = setPc (rset s3 28 10) (2147483792 + 616)).
  { rewrite (step1_addi s3 612 28 0 10 hc3 ltac:(lia) ltac:(rewrite coreBytes1_len; lia) hpc3
      ltac:(vm_compute; reflexivity)), rget_zero, (wadd_id 0 10 ltac:(lia)), Z.add_0_l, hpc3,
      (wadd_id (2147483792 + 612) 4 ltac:(lia)). f_equal; lia. }
  set (s4 := setPc (rset s3 28 10) (2147483792 + 616)) in *.
  assert (hmem4 : s4.(mem) = s.(mem)) by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4; apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 28 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact Hidx.
  - exact hmem4.
  - apply (CodeLoaded1_eqmem s); [exact hmem4| exact hcode].
  - intros i h7 h28. unfold s4.
    destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
    apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget s3 28 10 i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch i ltac:(lia) E0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* The comment inner loop: scan [inp] from [idx] one char/turn to the first
   newline or EOF. Either it reaches the pass-2 loop head (368) ON the newline
   at position q, or the Ok exit (628) at EOF. Induction on the span. *)
Lemma comment_loop2 inp : forall n s idx,
  CodeLoaded1 s -> s.(pc) = Image1.coreAddr + 600 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = Image1.inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  InputLoaded s inp ->
  Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  (forall b, In b inp -> 0 <= b < 256) ->
  (idx <= length inp)%nat -> (length inp - idx <= n)%nat ->
  exists k,
    (exists q, (idx <= q < length inp)%nat /\ (k <= 7 * (q - idx) + 5)%nat /\
        nth q inp 0 = 10 /\
        skipComment (zin (skipn idx inp)) = zin (skipn (S q) inp) /\
        (runUntil 0 k s).(pc) = Image1.coreAddr + 368 /\
        rget (runUntil 0 k s) 5 = Z.of_nat q /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i))
    \/ ((k <= 7 * (length inp - idx) + 1)%nat /\
        skipComment (zin (skipn idx inp)) = nil /\
        (runUntil 0 k s).(pc) = Image1.coreAddr + 628 /\
        rget (runUntil 0 k s) 5 = Z.of_nat (length inp) /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i)).
Proof.
  induction n; intros s idx hcode hpc Hidx Ha0 Ha1 Hinmem hin_fit Hbytes Hle Hn.
  - (* idx = length inp *)
    assert (hidxeq : idx = length inp) by lia. subst idx.
    assert (hbt : step s = setPc s (Image1.coreAddr + 628)).
    { apply (bgeu1_eq_taken s 600 5 11 (Z.of_nat (length inp)) 28 _ hcode ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpc Hidx Ha1 ltac:(vm_compute; reflexivity)).
      rewrite (wadd_id (Image1.coreAddr + 600) 28 ltac:(unfold Image1.coreAddr; lia)).
      unfold Image1.coreAddr. lia. }
    assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
    exists 1%nat. right. rewrite (runUntil_one s hp0), hbt. repeat apply conj.
    + lia.
    + rewrite skipn_all. reflexivity.
    + apply setPc_pc.
    + rewrite setPc_rget. exact Hidx.
    + apply setPc_mem.
    + intros i _ _ _. apply setPc_rget.
  - destruct (lt_dec idx (length inp)) as [Hlt|Hge].
    + (* read inp[idx] *)
      assert (Hin : In (nth idx inp 0) inp) by (apply nth_In; exact Hlt).
      assert (Hch256 : 0 <= nth idx inp 0 < 256) by (apply Hbytes; exact Hin).
      assert (hcons : skipn idx inp = nth idx inp 0 :: skipn (S idx) inp)
        by (apply skipn_cons_nth; exact Hlt).
      destruct (comment_read2 s inp idx (nth idx inp 0) hcode hpc Hidx Ha0 Ha1 Hlt hin_fit
        Hinmem eq_refl Hch256) as [hpc4 [h7_4 [h28_4 [h5_4 [hmem4 [hcode4 hoth4]]]]]].
      set (s4 := runUntil 0 4 s) in *.
      destruct (Z.eq_dec (nth idx inp 0) 10) as [Hnl|Hnnl].
      * (* newline at idx -> pass-2 loop head 368 *)
        assert (hbeq : step s4 = setPc s4 (Image1.coreAddr + 368)).
        { rewrite (step1_beq s4 616 7 28 (-248) hcode4 ltac:(lia)
            ltac:(rewrite coreBytes1_len; lia) hpc4 ltac:(vm_compute; reflexivity)),
            h7_4, h28_4, Hnl, Z.eqb_refl, hpc4,
            (wadd_id (Image1.coreAddr + 616) (-248) ltac:(unfold Image1.coreAddr; lia)).
          f_equal; unfold Image1.coreAddr; lia. }
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; unfold Image1.coreAddr; lia).
        exists (4 + 1)%nat. left. exists idx.
        rewrite (runUntil_add 4 1). fold s4. rewrite (runUntil_one s4 hp4), hbeq.
        repeat apply conj.
        -- lia.
        -- lia.
        -- lia.
        -- exact Hnl.
        -- assert (Heqb : Nat.eqb (Z.to_nat (nth idx inp 0)) c_nl = true)
             by (apply Nat.eqb_eq; unfold c_nl; rewrite Hnl; reflexivity).
           rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_eq _ _ Heqb). reflexivity.
        -- apply setPc_pc.
        -- rewrite setPc_rget. exact h5_4.
        -- rewrite setPc_mem. exact hmem4.
        -- intros i _ h7 h28. rewrite setPc_rget. exact (hoth4 i h7 h28).
      * (* not newline -> advance to idx+1, recurse *)
        assert (Hnl_ne : Nat.eqb (Z.to_nat (nth idx inp 0)) c_nl = false)
          by (apply Nat.eqb_neq; unfold c_nl; intro Hc; apply Hnnl; lia).
        assert (hbeq : step s4 = setPc s4 (Image1.coreAddr + 620)).
        { rewrite (step1_beq s4 616 7 28 (-248) hcode4 ltac:(lia)
            ltac:(rewrite coreBytes1_len; lia) hpc4 ltac:(vm_compute; reflexivity)),
            h7_4, h28_4.
          replace (nth idx inp 0 =? 10) with false by (symmetry; apply Z.eqb_neq; exact Hnnl).
          rewrite hpc4, (wadd_id (Image1.coreAddr + 616) 4 ltac:(unfold Image1.coreAddr; lia)).
          f_equal; lia. }
        set (v5 := setPc s4 (Image1.coreAddr + 620)) in *.
        assert (hc5 : CodeLoaded1 v5) by
          (apply (CodeLoaded1_eqmem s4); [unfold v5; rewrite setPc_mem; reflexivity| exact hcode4]).
        assert (hpc5 : v5.(pc) = Image1.coreAddr + 620) by reflexivity.
        assert (h5v5 : rget v5 5 = Z.of_nat idx) by (unfold v5; rewrite setPc_rget; exact h5_4).
        assert (haddi : step v5 = setPc (rset v5 5 (Z.of_nat (S idx))) (Image1.coreAddr + 624)).
        { rewrite (step1_addi v5 620 5 5 1 hc5 ltac:(unfold Image1.coreAddr; lia)
            ltac:(rewrite coreBytes1_len; lia) hpc5
            ltac:(vm_compute; reflexivity)), h5v5,
            (wadd_id (Z.of_nat idx) 1 ltac:(unfold Image1.inputAddr in *; lia)), hpc5,
            (wadd_id (Image1.coreAddr + 620) 4 ltac:(unfold Image1.coreAddr; lia)).
          rewrite Nat2Z.inj_succ. f_equal; lia. }
        set (v6 := setPc (rset v5 5 (Z.of_nat (S idx))) (Image1.coreAddr + 624)) in *.
        assert (hc6 : CodeLoaded1 v6) by
          (apply (CodeLoaded1_eqmem s4); [unfold v6, v5; rewrite !setPc_mem, rset_mem;
            reflexivity| exact hcode4]).
        assert (hpc6 : v6.(pc) = Image1.coreAddr + 624) by reflexivity.
        assert (hjal : step v6 = setPc v6 (Image1.coreAddr + 600)).
        { rewrite (step1_jal v6 624 0 (-24) hc6 ltac:(unfold Image1.coreAddr; lia)
            ltac:(rewrite coreBytes1_len; lia) hpc6
            ltac:(vm_compute; reflexivity)).
          rewrite rset_zero, hpc6,
            (wadd_id (Image1.coreAddr + 624) (-24) ltac:(unfold Image1.coreAddr; lia)).
          f_equal; lia. }
        set (s' := setPc v6 (Image1.coreAddr + 600)) in *.
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; unfold Image1.coreAddr; lia).
        assert (hp5 : v5.(pc) <> 0) by (rewrite hpc5; unfold Image1.coreAddr; lia).
        assert (hp6 : v6.(pc) <> 0) by (rewrite hpc6; unfold Image1.coreAddr; lia).
        assert (hrun3 : runUntil 0 3 s4 = s').
        { rewrite (runUntil_S 2 s4 hp4), hbeq, (runUntil_S 1 v5 hp5), haddi,
                  (runUntil_S 0 v6 hp6), hjal. reflexivity. }
        assert (hmems' : s'.(mem) = s.(mem))
          by (unfold s', v6, v5; rewrite !setPc_mem, rset_mem, setPc_mem; exact hmem4).
        assert (hcs' : CodeLoaded1 s') by (apply (CodeLoaded1_eqmem s); [exact hmems'| exact hcode]).
        assert (hpcs' : s'.(pc) = Image1.coreAddr + 600) by reflexivity.
        assert (h5s' : rget s' 5 = Z.of_nat (S idx)) by
          (unfold s'; rewrite setPc_rget; unfold v6;
           rewrite setPc_rget, (rset_rget v5 5 _ 5 ltac:(lia) ltac:(lia)), Z.eqb_refl;
           reflexivity).
        assert (hother' : forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget s' i = rget s i).
        { intros i h5 h7 h28. unfold s'. rewrite setPc_rget. unfold v6.
          destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
          apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget v5 5 _ i ltac:(lia) E0).
          replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
          unfold v5. rewrite setPc_rget. exact (hoth4 i h7 h28). }
        assert (h10s' : rget s' 10 = Image1.inputAddr) by
          (rewrite (hother' 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha0).
        assert (h11s' : rget s' 11 = Z.of_nat (length inp)) by
          (rewrite (hother' 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha1).
        destruct (IHn s' (S idx) hcs' hpcs' h5s' h10s' h11s'
          ltac:(intros j hj; rewrite hmems'; exact (Hinmem j hj)) hin_fit Hbytes
          ltac:(lia) ltac:(lia)) as [k [[q [Hq1 [Hkb [Hq2 [Hqskip [Hppc [H5q [Hmemq Hothq]]]]]]]]|
                                          [Hkb [Hskip0 [Hppc [H5q [Hmemq Hothq]]]]]]].
        -- exists (4 + (3 + k))%nat. left. exists q.
           rewrite (runUntil_add 4 (3 + k)). fold s4. rewrite (runUntil_add 3 k), hrun3.
           repeat apply conj.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ exact Hq2.
           ++ rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_ne _ _ Hnl_ne). exact Hqskip.
           ++ exact Hppc.
           ++ exact H5q.
           ++ rewrite Hmemq, hmems'. reflexivity.
           ++ intros i h5 h7 h28. rewrite (Hothq i h5 h7 h28), (hother' i h5 h7 h28). reflexivity.
        -- exists (4 + (3 + k))%nat. right.
           rewrite (runUntil_add 4 (3 + k)). fold s4. rewrite (runUntil_add 3 k), hrun3.
           repeat apply conj.
           ++ lia.
           ++ rewrite hcons. cbn [zin map]. rewrite (skipComment_cons_ne _ _ Hnl_ne). exact Hskip0.
           ++ exact Hppc.
           ++ exact H5q.
           ++ rewrite Hmemq, hmems'. reflexivity.
           ++ intros i h5 h7 h28. rewrite (Hothq i h5 h7 h28), (hother' i h5 h7 h28). reflexivity.
    + (* idx = length inp *)
      assert (hidxeq : idx = length inp) by lia. subst idx.
      assert (hbt : step s = setPc s (Image1.coreAddr + 628)).
      { apply (bgeu1_eq_taken s 600 5 11 (Z.of_nat (length inp)) 28 _ hcode ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc Hidx Ha1 ltac:(vm_compute; reflexivity)).
        rewrite (wadd_id (Image1.coreAddr + 600) 28 ltac:(unfold Image1.coreAddr; lia)).
        unfold Image1.coreAddr. lia. }
      assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold Image1.coreAddr; lia).
      exists 1%nat. right. rewrite (runUntil_one s hp0), hbt. repeat apply conj.
      * lia.
      * rewrite skipn_all. reflexivity.
      * apply setPc_pc.
      * rewrite setPc_rget. exact Hidx.
      * apply setPc_mem.
      * intros i _ _ _. apply setPc_rget.
Qed.

(* A COMPLETE pass-2 iteration for a spacing token. *)
Lemma p2_spacing : forall inp cap c rest' labF labNow m emitted s,
  isSpace (Z.to_nat c) = true ->
  P2Inv inp cap s labF labNow m emitted (c :: rest') ->
  exists k, (0 < k <= 50)%nat /\
    P2Inv inp cap (runUntil 0 k s) labF labNow m emitted rest'.
Proof.
  intros inp cap c rest' labF labNow m emitted s hss inv.
  destruct (p2_prefix inp cap c rest' labF labNow m emitted s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  assert (hsc : isComment (Z.to_nat c) = false)
    by (destruct (isSpace_cases c ltac:(lia) hss) as [H|[H|H]]; rewrite H; reflexivity).
  destruct (p2_spacing_tail s4 c hcode4 hpc4 ht2 ltac:(lia) hss)
    as (k & hk & htpc & htmem & htother).
  exists (4 + k)%nat. split; [lia|].
  rewrite runUntil_add, hrun4.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  refine {| p2_wf := hwf; p2_at_loop := htpc; p2_code := _; p2_a0 := _; p2_a1 := _;
            p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
            p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
            p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
            p2_scan_inp := hscaninp; p2_scan_ok := _; p2_spec := _ |}.
  - apply (CodeLoaded1_eqmem s); [rewrite htmem; exact hmem4| exact hcode].
  - rewrite (htother 10 ltac:(lia)),
      (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
  - rewrite (htother 11 ltac:(lia)),
      (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
  - rewrite (htother 12 ltac:(lia)),
      (hother4 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
  - rewrite (htother 13 ltac:(lia)),
      (hother4 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
  - rewrite (htother 14 ltac:(lia)),
      (hother4 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
  - rewrite (htother 1 ltac:(lia)),
      (hother4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
  - apply (inputLoaded_eqmem s); [rewrite htmem; exact hmem4| exact hinm].
  - rewrite (htother 5 ltac:(lia)), ht0. simpl length. reflexivity.
  - apply (suffix_step1 inp c rest'). exact hsuf.
  - rewrite (htother 6 ltac:(lia)),
      (hother4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx.
  - rewrite htmem, hmem4. exact houtmem.
  - apply (tableLoaded_eqmem s); [rewrite htmem; exact hmem4| exact htbl].
  - assert (hE : scan1 High1 labNow (length emitted) (zin (c :: rest'))
                 = scan1 High1 labNow (length emitted) (zin rest')).
    { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      apply scan1_spacing; assumption. }
    rewrite <- hE. exact hscanok.
  - assert (hE : emit1 High1 labF (length emitted) (zin (c :: rest'))
                 = emit1 High1 labF (length emitted) (zin rest')).
    { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      apply emit1_spacing; assumption. }
    rewrite <- hE. exact hspec.
Qed.

(* A COMPLETE pass-2 iteration for a comment token (#/;): prefix + dispatch
   to 600 + the inner loop. Lands back at the loop head sitting ON the
   newline (strictly shorter suffix), or halts via the Ok exit on EOF. *)
Lemma p2_comment : forall inp cap c rest' labF labNow m emitted s,
  isComment (Z.to_nat c) = true ->
  P2Inv inp cap s labF labNow m emitted (c :: rest') ->
  exists k,
    (exists rest2, (length rest2 < length (c :: rest'))%nat /\
        (k <= 50 * (length (c :: rest') - length rest2))%nat /\
        P2Inv inp cap (runUntil 0 k s) labF labNow m emitted rest2)
    \/ ((k <= 50 * length (c :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap c rest' labF labNow m emitted s hcm inv. pose proof inv as inv0.
  destruct (p2_prefix inp cap c rest' labF labNow m emitted s inv)
    as (s4' & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  assert (hs4 : runUntil 0 4 s = s4') by exact hrun4.
  (* dispatch 384 -> 600 (2 steps for '#', 4 for ';') *)
  assert (Hreach : exists kb, (kb <= 4)%nat /\
      (runUntil 0 kb s4').(pc) = Image1.coreAddr + 600 /\
      (runUntil 0 kb s4').(mem) = s4'.(mem) /\
      rget (runUntil 0 kb s4') 5 = rget s4' 5 /\
      (forall i, i <> 28 -> rget (runUntil 0 kb s4') i = rget s4' i)).
  { destruct (isComment_cases c ltac:(lia) hcm) as [Hc35|Hc59].
    - exists 2%nat. split; [lia|].
      rewrite (li1_beq_eq s4' 384 35 c 212 (Image1.coreAddr + 600) hcode4 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpc4 ht2 ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(lia) Hc35
        ltac:(rewrite (wadd_id (Image1.coreAddr + (384 + 4)) 212
                ltac:(unfold Image1.coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem. reflexivity.
      + exact (li_block_frame s4' 35 _ 5 ltac:(lia)).
      + intros i hi. exact (li_block_frame s4' 35 _ i hi).
    - exists 4%nat. split; [lia|].
      rewrite (runUntil_add 2 2),
        (li1_beq_ne s4' 384 35 c 212 hcode4 ltac:(lia)
          ltac:(rewrite coreBytes1_len; lia) hpc4 ht2 ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
      set (sb := setPc (rset s4' 28 35) (Image1.coreAddr + (384 + 8))) in *.
      assert (hcb : CodeLoaded1 sb) by
        (apply (CodeLoaded1_eqmem s4'); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity|
         exact hcode4]).
      assert (hpcb : sb.(pc) = Image1.coreAddr + 392) by (unfold sb; cbn; lia).
      assert (h7b : rget sb 7 = c) by
        (unfold sb; rewrite (li_block_frame s4' 35 _ 7 ltac:(lia)); exact ht2).
      rewrite (li1_beq_eq sb 392 59 c 204 (Image1.coreAddr + 600) hcb ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(lia) Hc59
        ltac:(rewrite (wadd_id (Image1.coreAddr + (392 + 4)) 204
                ltac:(unfold Image1.coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. reflexivity.
      + rewrite (li_block_frame sb 59 _ 5 ltac:(lia)).
        exact (li_block_frame s4' 35 _ 5 ltac:(lia)).
      + intros i hi. rewrite (li_block_frame sb 59 _ i hi).
        exact (li_block_frame s4' 35 _ i hi). }
  destruct Hreach as (kb & hkb & hbpc & hbmem & hb5 & hbother).
  set (sB := runUntil 0 kb s4') in *.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hin_fit : Image1.inputAddr + Z.of_nat (length inp) < 2 ^ 64).
  { pose proof (in_fits1 _ _ hwf). pose proof (lbl_fits1 _ _ hwf).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr in *. lia. }
  assert (h5B : rget sB 5 = Z.of_nat idx1).
  { rewrite hb5, ht0. unfold idx1. lia. }
  assert (h10B : rget sB 10 = Image1.inputAddr).
  { rewrite (hbother 10 ltac:(lia)),
      (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha0. }
  assert (h11B : rget sB 11 = Z.of_nat (length inp)).
  { rewrite (hbother 11 ltac:(lia)),
      (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact ha1. }
  assert (hmemB : sB.(mem) = s.(mem)) by (rewrite hbmem; exact hmem4).
  assert (hcodeB : CodeLoaded1 sB)
    by (apply (CodeLoaded1_eqmem s); [exact hmemB| exact hcode]).
  assert (hinmB : InputLoaded sB inp)
    by (apply (inputLoaded_eqmem s); [exact hmemB| exact hinm]).
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp c rest'); exact hsuf).
  destruct (comment_loop2 inp (length inp - idx1)%nat sB idx1 hcodeB hbpc h5B h10B h11B
              hinmB hin_fit (bytes_ok1 _ _ hwf) ltac:(unfold idx1; lia) ltac:(lia))
    as [k [[q [Hq1 [Hkb2 [Hq2 [Hqskip [Hppc [H5q [Hmemq Hothq]]]]]]]]|
            [Hkb2 [Hskip0 [Hppc [H5q [Hmemq Hothq]]]]]]].
  - (* newline at q -> back to the loop head sitting on the newline *)
    exists (4 + (kb + k))%nat. left. exists (skipn q inp).
    rewrite (runUntil_add 4 (kb + k)), hs4, (runUntil_add kb k). fold sB.
    set (sF := runUntil 0 k sB) in *.
    assert (hlq : length (skipn q inp) = (length inp - q)%nat) by (apply length_skipn).
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget sF i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (Hothq i h5 h7 h28), (hbother i h28),
              (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemF : sF.(mem) = s.(mem)) by (rewrite Hmemq; exact hmemB).
    split; [unfold idx1 in *; simpl length in *; lia|
            split; [unfold idx1 in *; simpl length in *; lia|]].
    assert (hconsq : skipn q inp = nth q inp 0 :: skipn (S q) inp)
      by (apply skipn_cons_nth; lia).
    refine {| p2_wf := hwf; p2_at_loop := Hppc; p2_code := _; p2_a0 := _; p2_a1 := _;
              p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
              p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
              p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
              p2_scan_inp := hscaninp; p2_scan_ok := _; p2_spec := _ |}.
    + apply (CodeLoaded1_eqmem s); [exact hmemF| exact hcode].
    + rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
    + rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
    + rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
    + rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
    + rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
    + rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
    + apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
    + rewrite H5q, hlq. lia.
    + rewrite hlq. replace (length inp - (length inp - q))%nat with q by lia. reflexivity.
    + rewrite (hothF 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx.
    + rewrite hmemF. exact houtmem.
    + apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
    + (* scan telescope through the comment skip and the newline *)
      rewrite hconsq, Hq2.
      change (zin (10 :: skipn (S q) inp)) with (10%nat :: zin (skipn (S q) inp)).
      rewrite (scan1_spacing 10%nat (zin (skipn (S q) inp)) labNow (length emitted)
                 ltac:(reflexivity) ltac:(reflexivity)).
      rewrite <- Hqskip, hsufx.
      rewrite <- (scan1_comment (Z.to_nat c) (zin rest') labNow (length emitted) hcm).
      change (Z.to_nat c :: zin rest') with (zin (c :: rest')).
      exact hscanok.
    + (* emit telescope through the comment skip and the newline *)
      rewrite hconsq, Hq2.
      assert (hE : emit1 High1 labF (length emitted) (zin (c :: rest'))
                   = emit1 High1 labF (length emitted) (zin (10 :: skipn (S q) inp))).
      { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
        rewrite (emit1_comment (Z.to_nat c) (zin rest') labF (length emitted) hcm).
        rewrite hsufx in Hqskip. rewrite Hqskip.
        change (zin (10 :: skipn (S q) inp)) with (10%nat :: zin (skipn (S q) inp)).
        rewrite (emit1_spacing 10%nat (zin (skipn (S q) inp)) labF (length emitted)
                   ltac:(reflexivity) ltac:(reflexivity)).
        reflexivity. }
      rewrite <- hE. exact hspec.
  - (* EOF -> the Ok exit (628): the residual emit collapses *)
    set (sF := runUntil 0 k sB) in *.
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget sF i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (Hothq i h5 h7 h28), (hbother i h28),
              (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemF : sF.(mem) = s.(mem)) by (rewrite Hmemq; exact hmemB).
    assert (hcodeF : CodeLoaded1 sF)
      by (apply (CodeLoaded1_eqmem s); [exact hmemF| exact hcode]).
    assert (hraF : rget sF 1 = 0)
      by (rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra).
    assert (h6F : rget sF 6 = Z.of_nat (length emitted))
      by (rewrite (hothF 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx).
    assert (hposle : (length emitted <= m)%nat)
      by (exact (scan1_pos_le (zin (c :: rest')) High1 labNow (length emitted)
                   labF m Ok1 hscanok)).
    assert (hskipnil : skipComment (zin rest') = nil)
      by (rewrite <- hsufx; exact Hskip0).
    assert (hemitres : emit1 High1 labF (length emitted) (zin (c :: rest')) = ([], Ok1)).
    { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      rewrite (emit1_comment (Z.to_nat c) (zin rest') labF (length emitted) hcm).
      rewrite hskipnil. apply emit1_nil. }
    assert (hemit : emit1 High1 labF 0 (zin inp) = (emitted, Ok1)).
    { rewrite hspec, hemitres. cbn [fst snd]. rewrite app_nil_r. reflexivity. }
    destruct (p2_ok_exit inp cap labF m emitted sF Hppc hcodeF hraF h6F
                ltac:(lia) ltac:(rewrite hmemF; exact houtmem) hscaninp hmle hemit)
      as (f & hrunE & hres).
    exists (4 + (kb + (k + 3)))%nat. right.
    split; [unfold idx1 in *; simpl length in *; lia|].
    rewrite (runUntil_add 4 (kb + (k + 3))), hs4, (runUntil_add kb (k + 3)).
    fold sB. rewrite (runUntil_add k 3). fold sF. rewrite hrunE. exact hres.
Qed.
(* dispatch 384 -> 516 for ':' (5 not-taken blocks + 1 taken): 12 steps *)
Lemma p2_colon_tail s4 :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 384 -> rget s4 7 = 58 ->
  exists s', runUntil 0 12 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 516 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc ht2.
  pose proof (li1_beq_ne s4 384 35 58 212 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (384 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 392) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = 58) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  pose proof (li1_beq_ne sB 392 59 58 204 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (392 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 400) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = 58) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 400 10 58 (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (400 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 408) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = 58) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 408 32 58 (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (408 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 416) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = 58) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 416 95 58 (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (416 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 424) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = 58) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_eq sF 424 58 58 88 (Image1.coreAddr + 516) hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl
    ltac:(rewrite (wadd_id (Image1.coreAddr + (424 + 4)) 88
            ltac:(unfold Image1.coreAddr; lia)); lia)) as hb6.
  exists (setPc (rset sF 28 58) (Image1.coreAddr + 516)).
  split.
  { replace 12%nat with (2 + (2 + (2 + (2 + (2 + 2)))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
            runUntil_add, hb4, runUntil_add, hb5, hb6. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold sF. rewrite setPc_mem, rset_mem.
    unfold sE. rewrite setPc_mem, rset_mem. unfold sD. rewrite setPc_mem, rset_mem.
    unfold sC. rewrite setPc_mem, rset_mem. unfold sB. rewrite setPc_mem, rset_mem.
    reflexivity.
  - apply (CodeLoaded1_eqmem sF);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcF].
  - intros i hi. rewrite (li_block_frame sF 58 _ i hi).
    unfold sF. rewrite (li_block_frame sE 95 _ i hi).
    unfold sE. rewrite (li_block_frame sD 32 _ i hi).
    unfold sD. rewrite (li_block_frame sC 10 _ i hi).
    unfold sC. rewrite (li_block_frame sB 59 _ i hi).
    unfold sB. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* dispatch 384 -> 524 for '%' (6 not-taken blocks + 1 taken): 14 steps *)
Lemma p2_pct_tail s4 :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 384 -> rget s4 7 = 37 ->
  exists s', runUntil 0 14 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 524 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc ht2.
  pose proof (li1_beq_ne s4 384 35 37 212 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (384 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 392) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = 37) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact ht2).
  pose proof (li1_beq_ne sB 392 59 37 204 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (392 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 400) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = 37) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 400 10 37 (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (400 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 408) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = 37) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 408 32 37 (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (408 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 416) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = 37) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 416 95 37 (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (416 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 424) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = 37) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_ne sF 424 58 37 88 hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
  set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (424 + 8))) in *.
  assert (hcG : CodeLoaded1 sG) by
    (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
  assert (hpcG : sG.(pc) = Image1.coreAddr + 432) by (unfold sG; cbn; lia).
  assert (h7G : rget sG 7 = 37) by
    (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
  pose proof (li1_beq_eq sG 432 37 37 88 (Image1.coreAddr + 524) hcG ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) eq_refl
    ltac:(rewrite (wadd_id (Image1.coreAddr + (432 + 4)) 88
            ltac:(unfold Image1.coreAddr; lia)); lia)) as hb7.
  exists (setPc (rset sG 28 37) (Image1.coreAddr + 524)).
  split.
  { replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + 2))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3,
            runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold sG. rewrite setPc_mem, rset_mem.
    unfold sF. rewrite setPc_mem, rset_mem. unfold sE. rewrite setPc_mem, rset_mem.
    unfold sD. rewrite setPc_mem, rset_mem. unfold sC. rewrite setPc_mem, rset_mem.
    unfold sB. rewrite setPc_mem, rset_mem. reflexivity.
  - apply (CodeLoaded1_eqmem sG);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcG].
  - intros i hi. rewrite (li_block_frame sG 37 _ i hi).
    unfold sG. rewrite (li_block_frame sF 58 _ i hi).
    unfold sF. rewrite (li_block_frame sE 95 _ i hi).
    unfold sE. rewrite (li_block_frame sD 32 _ i hi).
    unfold sD. rewrite (li_block_frame sC 10 _ i hi).
    unfold sC. rewrite (li_block_frame sB 59 _ i hi).
    unfold sB. rewrite (li_block_frame s4 35 _ i hi). reflexivity.
Qed.

(* A COMPLETE pass-2 iteration for a label definition (':l'): the machine
   just skips the label byte (516: t0++; 520: j 368); the residual scan
   installs the label into [labNow]. The scan validity excludes EOF and
   duplicates. *)
Lemma p2_labelDef : forall inp cap rest' labF labNow m emitted s,
  P2Inv inp cap s labF labNow m emitted (58 :: rest') ->
  exists k,
    (exists rest2 labNow2, (length rest2 < length ((58:Z) :: rest'))%nat /\
        (k <= 50 * (length ((58:Z) :: rest') - length rest2))%nat /\
        P2Inv inp cap (runUntil 0 k s) labF labNow2 m emitted rest2)
    \/ ((k <= 50 * length ((58:Z) :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap rest' labF labNow m emitted s inv. pose proof inv as inv0.
  destruct (p2_prefix inp cap 58 rest' labF labNow m emitted s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct (p2_colon_tail s4 hcode4 hpc4 ht2)
    as (sL & hrunT & hpcL & hmemL & hcodeL & hothL).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp 58 rest'); exact hsuf).
  destruct rest' as [|l rest''].
  - (* impossible: the residual scan would end TrailTok *)
    exfalso.
    change (zin (58 :: nil)) with (58%nat :: @nil nat) in hscanok.
    rewrite scan1_colon, scan1_col_nil in hscanok.
    inversion hscanok.
  - (* the residual scan forces a fresh label *)
    set (l' := Z.to_nat l) in *.
    assert (hscan2 : scan1 Col1 labNow (length emitted) (l' :: zin rest'')
                     = (labF, m, Ok1)).
    { rewrite <- hscanok.
      change (zin (58 :: l :: rest'')) with (58%nat :: zin (l :: rest'')).
      rewrite scan1_colon.
      change (zin (l :: rest'')) with (l' :: zin rest''). reflexivity. }
    rewrite scan1_col_cons in hscan2.
    destruct (labNow l') as [p|] eqn:Elab; [inversion hscan2|].
    (* machine: t0++ (516), j 368 (520) *)
    assert (h5L : rget sL 5 = Z.of_nat idx1).
    { rewrite (hothL 5 ltac:(lia)), ht0. unfold idx1. lia. }
    assert (hothLS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sL i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (hothL i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemLS : sL.(mem) = s.(mem)) by (rewrite hmemL; exact hmem4).
    assert (hu1 : step sL = setPc (rset sL 5 (Z.of_nat idx1 + 1)) (Image1.coreAddr + 520)).
    { rewrite (step1_addi sL 516 5 5 1 hcodeL ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcL ltac:(vm_compute; reflexivity)), h5L,
        (wadd_id (Z.of_nat idx1) 1 ltac:(pose proof (in_fits1 _ _ hwf);
          pose proof (lbl_fits1 _ _ hwf);
          unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr in *; lia)), hpcL,
        (wadd_id (Image1.coreAddr + 516) 4 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    set (sM1 := setPc (rset sL 5 (Z.of_nat idx1 + 1)) (Image1.coreAddr + 520)) in *.
    assert (hmem1 : sM1.(mem) = s.(mem))
      by (unfold sM1; rewrite setPc_mem, rset_mem; exact hmemLS).
    assert (hc1 : CodeLoaded1 sM1) by (apply (CodeLoaded1_eqmem s); [exact hmem1| exact hcode]).
    assert (hpc1 : sM1.(pc) = Image1.coreAddr + 520) by reflexivity.
    assert (hu2 : step sM1 = setPc sM1 (Image1.coreAddr + 368)).
    { rewrite (step1_jal sM1 520 0 (-152) hc1 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpc1 ltac:(vm_compute; reflexivity)),
        rset_zero, hpc1,
        (wadd_id (Image1.coreAddr + 520) (-152) ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    set (sF := setPc sM1 (Image1.coreAddr + 368)) in *.
    assert (hpL : sL.(pc) <> 0) by (rewrite hpcL; unfold Image1.coreAddr; lia).
    assert (hp1 : sM1.(pc) <> 0) by (rewrite hpc1; unfold Image1.coreAddr; lia).
    assert (hrunF : runUntil 0 (4 + (12 + 2)) s = sF).
    { rewrite (runUntil_add 4 (12 + 2)), hrun4, (runUntil_add 12 2), hrunT,
              (runUntil_S 1 sL hpL), hu1, (runUntil_S 0 sM1 hp1), hu2. reflexivity. }
    exists (4 + (12 + 2))%nat. left.
    exists rest''. exists (setLabel labNow l' (length emitted)).
    rewrite hrunF.
    assert (hmemF : sF.(mem) = s.(mem)) by (unfold sF; rewrite setPc_mem; exact hmem1).
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sF i = rget s i).
    { intros i h0 h5 h7 h28.
      unfold sF. rewrite setPc_rget.
      unfold sM1. rewrite setPc_rget, (rset_rget sL 5 _ i ltac:(lia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      exact (hothLS i h0 h5 h7 h28). }
    split; [simpl length; lia| split; [simpl length; lia|]].
    assert (hsufx2 : skipn (S idx1) inp = rest'').
    { replace (S idx1) with (1 + idx1)%nat by lia.
      rewrite <- skipn_skipn, hsufx. reflexivity. }
    refine {| p2_wf := hwf; p2_at_loop := _; p2_code := _; p2_a0 := _; p2_a1 := _;
              p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
              p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
              p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
              p2_scan_inp := hscaninp; p2_scan_ok := _; p2_spec := _ |}.
    + apply setPc_pc.
    + apply (CodeLoaded1_eqmem s); [exact hmemF| exact hcode].
    + rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
    + rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
    + rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
    + rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
    + rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
    + rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
    + apply (inputLoaded_eqmem s); [exact hmemF| exact hinm].
    + assert (hr5F : rget sF 5 = Z.of_nat idx1 + 1).
      { unfold sF. rewrite setPc_rget.
        unfold sM1. rewrite setPc_rget, (rset_rget sL 5 _ 5 ltac:(lia) ltac:(lia)),
          Z.eqb_refl. reflexivity. }
      rewrite hr5F. unfold idx1. simpl length in *. lia.
    + replace (length inp - length rest'')%nat with (S idx1)
        by (unfold idx1; simpl length in *; lia).
      exact hsufx2.
    + rewrite (hothF 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact houtidx.
    + rewrite hmemF. exact houtmem.
    + apply (tableLoaded_eqmem s); [exact hmemF| exact htbl].
    + exact hscan2.
    + assert (hE : emit1 High1 labF (length emitted) (zin (58 :: l :: rest''))
                   = emit1 High1 labF (length emitted) (zin rest'')).
      { change (zin (58 :: l :: rest'')) with (58%nat :: zin (l :: rest'')).
        rewrite emit1_colon.
        change (zin (l :: rest'')) with (l' :: zin rest'').
        apply emit1_col_cons. }
      rewrite <- hE. exact hspec.
Qed.
(* dispatch 384 -> 440 for a hex-digit first char in pass 2 (7 not-taken
   blocks): 14 steps *)
Lemma p2_fall_tail s4 c :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 384 -> rget s4 7 = c ->
  0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 -> c <> 58 -> c <> 37 ->
  exists s', runUntil 0 14 s4 = s' /\
    s'.(pc) = Image1.coreAddr + 440 /\ s'.(mem) = s4.(mem) /\ CodeLoaded1 s' /\
    (forall i, i <> 28 -> rget s' i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hne1 hne2 hne3 hne4 hne5 hne6 hne7.
  pose proof (li1_beq_ne s4 384 35 c 212 hcode ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb1.
  set (sB := setPc (rset s4 28 35) (Image1.coreAddr + (384 + 8))) in *.
  assert (hcB : CodeLoaded1 sB) by
    (apply (CodeLoaded1_eqmem s4); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcB : sB.(pc) = Image1.coreAddr + 392) by (unfold sB; cbn; lia).
  assert (h7B : rget sB 7 = c) by
    (unfold sB; rewrite (li_block_frame s4 35 _ 7 ltac:(lia)); exact h7).
  pose proof (li1_beq_ne sB 392 59 c 204 hcB ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcB h7B ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb2.
  set (sC := setPc (rset sB 28 59) (Image1.coreAddr + (392 + 8))) in *.
  assert (hcC : CodeLoaded1 sC) by
    (apply (CodeLoaded1_eqmem sB); [unfold sC; rewrite setPc_mem, rset_mem; reflexivity| exact hcB]).
  assert (hpcC : sC.(pc) = Image1.coreAddr + 400) by (unfold sC; cbn; lia).
  assert (h7C : rget sC 7 = c) by
    (unfold sC; rewrite (li_block_frame sB 59 _ 7 ltac:(lia)); exact h7B).
  pose proof (li1_beq_ne sC 400 10 c (-36) hcC ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcC h7C ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
  set (sD := setPc (rset sC 28 10) (Image1.coreAddr + (400 + 8))) in *.
  assert (hcD : CodeLoaded1 sD) by
    (apply (CodeLoaded1_eqmem sC); [unfold sD; rewrite setPc_mem, rset_mem; reflexivity| exact hcC]).
  assert (hpcD : sD.(pc) = Image1.coreAddr + 408) by (unfold sD; cbn; lia).
  assert (h7D : rget sD 7 = c) by
    (unfold sD; rewrite (li_block_frame sC 10 _ 7 ltac:(lia)); exact h7C).
  pose proof (li1_beq_ne sD 408 32 c (-44) hcD ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcD h7D ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
  set (sE := setPc (rset sD 28 32) (Image1.coreAddr + (408 + 8))) in *.
  assert (hcE : CodeLoaded1 sE) by
    (apply (CodeLoaded1_eqmem sD); [unfold sE; rewrite setPc_mem, rset_mem; reflexivity| exact hcD]).
  assert (hpcE : sE.(pc) = Image1.coreAddr + 416) by (unfold sE; cbn; lia).
  assert (h7E : rget sE 7 = c) by
    (unfold sE; rewrite (li_block_frame sD 32 _ 7 ltac:(lia)); exact h7D).
  pose proof (li1_beq_ne sE 416 95 c (-52) hcE ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcE h7E ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb5.
  set (sF := setPc (rset sE 28 95) (Image1.coreAddr + (416 + 8))) in *.
  assert (hcF : CodeLoaded1 sF) by
    (apply (CodeLoaded1_eqmem sE); [unfold sF; rewrite setPc_mem, rset_mem; reflexivity| exact hcE]).
  assert (hpcF : sF.(pc) = Image1.coreAddr + 424) by (unfold sF; cbn; lia).
  assert (h7F : rget sF 7 = c) by
    (unfold sF; rewrite (li_block_frame sE 95 _ 7 ltac:(lia)); exact h7E).
  pose proof (li1_beq_ne sF 424 58 c 88 hcF ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcF h7F ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb6.
  set (sG := setPc (rset sF 28 58) (Image1.coreAddr + (424 + 8))) in *.
  assert (hcG : CodeLoaded1 sG) by
    (apply (CodeLoaded1_eqmem sF); [unfold sG; rewrite setPc_mem, rset_mem; reflexivity| exact hcF]).
  assert (hpcG : sG.(pc) = Image1.coreAddr + 432) by (unfold sG; cbn; lia).
  assert (h7G : rget sG 7 = c) by
    (unfold sG; rewrite (li_block_frame sF 58 _ 7 ltac:(lia)); exact h7F).
  pose proof (li1_beq_ne sG 432 37 c 88 hcG ltac:(lia)
    ltac:(rewrite coreBytes1_len; lia) hpcG h7G ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb7.
  exists (setPc (rset sG 28 37) (Image1.coreAddr + (432 + 8))).
  split.
  { replace 14%nat with (2 + (2 + (2 + (2 + (2 + (2 + (2)))))))%nat by lia.
    rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, runUntil_add, hb5, runUntil_add, hb6, hb7. reflexivity. }
  repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem.
    unfold sG. rewrite setPc_mem, rset_mem.
    unfold sF. rewrite setPc_mem, rset_mem.
    unfold sE. rewrite setPc_mem, rset_mem.
    unfold sD. rewrite setPc_mem, rset_mem.
    unfold sC. rewrite setPc_mem, rset_mem.
    unfold sB. rewrite setPc_mem, rset_mem.
    reflexivity.
  - apply (CodeLoaded1_eqmem sG);
      [rewrite setPc_mem, rset_mem; reflexivity| exact hcG].
  - intros i hir.
    rewrite (li_block_frame sG 37 _ i hir).
    unfold sG. rewrite (li_block_frame sF 58 _ i hir).
    unfold sF. rewrite (li_block_frame sE 95 _ i hir).
    unfold sE. rewrite (li_block_frame sD 32 _ i hir).
    unfold sD. rewrite (li_block_frame sC 10 _ i hir).
    unfold sC. rewrite (li_block_frame sB 59 _ i hir).
    unfold sB. rewrite (li_block_frame s4 35 _ i hir).
    reflexivity.
Qed.

(* hi-nibble VALUE (440..456): t4 (x29) = c-48 / c-55 = hi; lands at 460.
   Touches only t3/t4/pc. *)
Lemma p2_hi_value s4 c hi :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 440 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = Some hi ->
  exists k, (0 < k <= 4)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 460 /\
    rget (runUntil 0 k s4) 29 = Z.of_nat hi /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> i <> 29 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit: blt taken to 456; addi t4,t2,-48 *)
    pose proof (li1_blt_t s4 440 58 c 12 (Image1.coreAddr + 456) hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (440 + 4)) 12
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb1.
    set (sA := setPc (rset s4 28 58) (Image1.coreAddr + 456)) in *.
    assert (hcA : CodeLoaded1 sA) by
      (apply (CodeLoaded1_eqmem s4); [unfold sA; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcA : sA.(pc) = Image1.coreAddr + 456) by reflexivity.
    assert (h7A : rget sA 7 = c) by
      (unfold sA; rewrite (li_block_frame s4 58 _ 7 ltac:(lia)); exact h7).
    assert (hu2 : step sA = setPc (rset sA 29 (c - 48)) (Image1.coreAddr + 460)).
    { rewrite (step1_addi sA 456 29 7 (-48) hcA ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcA ltac:(vm_compute; reflexivity)), h7A,
        (wadd_id c (-48) ltac:(lia)), hpcA,
        (wadd_id (Image1.coreAddr + 456) 4 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpA : sA.(pc) <> 0) by (rewrite hpcA; unfold Image1.coreAddr; lia).
    exists 3%nat. split; [lia|].
    replace 3%nat with (2 + 1)%nat by lia.
    rewrite runUntil_add, hb1. fold sA. rewrite (runUntil_one sA hpA), hu2.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_rget, (rset_rget sA 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + rewrite setPc_mem, rset_mem. unfold sA. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i h28 h29.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0.
      rewrite setPc_rget, (rset_rget sA 29 _ i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sA. rewrite (li_block_frame s4 58 _ i h28). reflexivity.
  - (* letter: blt not taken; addi t4,t2,-55 at 448; j 460 *)
    pose proof (li1_blt_nt s4 440 58 c 12 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sA := setPc (rset s4 28 58) (Image1.coreAddr + (440 + 8))) in *.
    assert (hcA : CodeLoaded1 sA) by
      (apply (CodeLoaded1_eqmem s4); [unfold sA; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcA : sA.(pc) = Image1.coreAddr + 448) by (unfold sA; cbn; lia).
    assert (h7A : rget sA 7 = c) by
      (unfold sA; rewrite (li_block_frame s4 58 _ 7 ltac:(lia)); exact h7).
    assert (hu2 : step sA = setPc (rset sA 29 (c - 55)) (Image1.coreAddr + 452)).
    { rewrite (step1_addi sA 448 29 7 (-55) hcA ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcA ltac:(vm_compute; reflexivity)), h7A,
        (wadd_id c (-55) ltac:(lia)), hpcA,
        (wadd_id (Image1.coreAddr + 448) 4 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    set (sB := setPc (rset sA 29 (c - 55)) (Image1.coreAddr + 452)) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem sA); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcA]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 452) by reflexivity.
    assert (hu3 : step sB = setPc sB (Image1.coreAddr + 460)).
    { rewrite (step1_jal sB 452 0 8 hcB ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcB ltac:(vm_compute; reflexivity)),
        rset_zero, hpcB,
        (wadd_id (Image1.coreAddr + 452) 8 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpA : sA.(pc) <> 0) by (rewrite hpcA; unfold Image1.coreAddr; lia).
    assert (hpB : sB.(pc) <> 0) by (rewrite hpcB; unfold Image1.coreAddr; lia).
    exists 4%nat. split; [lia|].
    replace 4%nat with (2 + (1 + 1))%nat by lia.
    rewrite runUntil_add, hb1. fold sA.
    rewrite (runUntil_add 1 1), (runUntil_one sA hpA), hu2.
    fold sB. rewrite (runUntil_one sB hpB), hu3.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_rget. unfold sB.
      rewrite setPc_rget, (rset_rget sA 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + rewrite setPc_mem. unfold sB. rewrite setPc_mem, rset_mem.
      unfold sA. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i h28 h29.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0.
      rewrite setPc_rget. unfold sB.
      rewrite setPc_rget, (rset_rget sA 29 _ i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sA. rewrite (li_block_frame s4 58 _ i h28). reflexivity.
Qed.

(* lo-nibble VALUE (472..488): t5 (x30) = l-48 / l-55 = lo; lands at 492. *)
Lemma p2_lo_value s4 c lo :
  CodeLoaded1 s4 -> s4.(pc) = Image1.coreAddr + 472 -> rget s4 7 = c ->
  0 <= c < 256 -> nibble (Z.to_nat c) = Some lo ->
  exists k, (0 < k <= 4)%nat /\
    (runUntil 0 k s4).(pc) = Image1.coreAddr + 492 /\
    rget (runUntil 0 k s4) 30 = Z.of_nat lo /\
    (runUntil 0 k s4).(mem) = s4.(mem) /\
    (forall i, i <> 28 -> i <> 30 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc h7 hcr hn.
  destruct (nibble_cases c lo ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit: blt taken to 488; addi t5,t2,-48 *)
    pose proof (li1_blt_t s4 472 58 c 12 (Image1.coreAddr + 488) hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (Image1.coreAddr + (472 + 4)) 12
              ltac:(unfold Image1.coreAddr; lia)); lia)) as hb1.
    set (sA := setPc (rset s4 28 58) (Image1.coreAddr + 488)) in *.
    assert (hcA : CodeLoaded1 sA) by
      (apply (CodeLoaded1_eqmem s4); [unfold sA; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcA : sA.(pc) = Image1.coreAddr + 488) by reflexivity.
    assert (h7A : rget sA 7 = c) by
      (unfold sA; rewrite (li_block_frame s4 58 _ 7 ltac:(lia)); exact h7).
    assert (hu2 : step sA = setPc (rset sA 30 (c - 48)) (Image1.coreAddr + 492)).
    { rewrite (step1_addi sA 488 30 7 (-48) hcA ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcA ltac:(vm_compute; reflexivity)), h7A,
        (wadd_id c (-48) ltac:(lia)), hpcA,
        (wadd_id (Image1.coreAddr + 488) 4 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpA : sA.(pc) <> 0) by (rewrite hpcA; unfold Image1.coreAddr; lia).
    exists 3%nat. split; [lia|].
    replace 3%nat with (2 + 1)%nat by lia.
    rewrite runUntil_add, hb1. fold sA. rewrite (runUntil_one sA hpA), hu2.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_rget, (rset_rget sA 30 _ 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + rewrite setPc_mem, rset_mem. unfold sA. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i h28 h30.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0.
      rewrite setPc_rget, (rset_rget sA 30 _ i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact h30).
      unfold sA. rewrite (li_block_frame s4 58 _ i h28). reflexivity.
  - (* letter: blt not taken; addi t5,t2,-55 at 480; j 492 *)
    pose proof (li1_blt_nt s4 472 58 c 12 hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as hb1.
    set (sA := setPc (rset s4 28 58) (Image1.coreAddr + (472 + 8))) in *.
    assert (hcA : CodeLoaded1 sA) by
      (apply (CodeLoaded1_eqmem s4); [unfold sA; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpcA : sA.(pc) = Image1.coreAddr + 480) by (unfold sA; cbn; lia).
    assert (h7A : rget sA 7 = c) by
      (unfold sA; rewrite (li_block_frame s4 58 _ 7 ltac:(lia)); exact h7).
    assert (hu2 : step sA = setPc (rset sA 30 (c - 55)) (Image1.coreAddr + 484)).
    { rewrite (step1_addi sA 480 30 7 (-55) hcA ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcA ltac:(vm_compute; reflexivity)), h7A,
        (wadd_id c (-55) ltac:(lia)), hpcA,
        (wadd_id (Image1.coreAddr + 480) 4 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    set (sB := setPc (rset sA 30 (c - 55)) (Image1.coreAddr + 484)) in *.
    assert (hcB : CodeLoaded1 sB) by
      (apply (CodeLoaded1_eqmem sA); [unfold sB; rewrite setPc_mem, rset_mem; reflexivity| exact hcA]).
    assert (hpcB : sB.(pc) = Image1.coreAddr + 484) by reflexivity.
    assert (hu3 : step sB = setPc sB (Image1.coreAddr + 492)).
    { rewrite (step1_jal sB 484 0 8 hcB ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcB ltac:(vm_compute; reflexivity)),
        rset_zero, hpcB,
        (wadd_id (Image1.coreAddr + 484) 8 ltac:(unfold Image1.coreAddr; lia)).
      f_equal; lia. }
    assert (hpA : sA.(pc) <> 0) by (rewrite hpcA; unfold Image1.coreAddr; lia).
    assert (hpB : sB.(pc) <> 0) by (rewrite hpcB; unfold Image1.coreAddr; lia).
    exists 4%nat. split; [lia|].
    replace 4%nat with (2 + (1 + 1))%nat by lia.
    rewrite runUntil_add, hb1. fold sA.
    rewrite (runUntil_add 1 1), (runUntil_one sA hpA), hu2.
    fold sB. rewrite (runUntil_one sB hpB), hu3.
    repeat apply conj.
    + apply setPc_pc.
    + rewrite setPc_rget. unfold sB.
      rewrite setPc_rget, (rset_rget sA 30 _ 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + rewrite setPc_mem. unfold sB. rewrite setPc_mem, rset_mem.
      unfold sA. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i h28 h30.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0.
      rewrite setPc_rget. unfold sB.
      rewrite setPc_rget, (rset_rget sA 30 _ i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact h30).
      unfold sA. rewrite (li_block_frame s4 58 _ i h28). reflexivity.
Qed.

(* A COMPLETE pass-2 iteration for a hex byte token: prefix + fall dispatch
   to 440 + hi value + low read (460..468, no EOF check: scan validity) +
   lo value + combine/store/count (492..512). The byte hi*16+lo is appended
   to the out region. *)
Lemma p2_byte : forall inp cap c hi rest' labF labNow m emitted s,
  nibble (Z.to_nat c) = Some hi ->
  P2Inv inp cap s labF labNow m emitted (c :: rest') ->
  exists k,
    (exists rest2 emitted2, (length rest2 < length (c :: rest'))%nat /\
        (k <= 50 * (length (c :: rest') - length rest2))%nat /\
        P2Inv inp cap (runUntil 0 k s) labF labNow m emitted2 rest2)
    \/ ((k <= 50 * length (c :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap c hi rest' labF labNow m emitted s hn inv. pose proof inv as inv0.
  destruct (p2_prefix inp cap c rest' labF labNow m emitted s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf. pose proof (cap_nonneg _ _ hwf) as hcap0.
  pose proof (nibble_lt _ _ hn) as hhi16.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. lia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp c rest'); exact hsuf).
  (* spec side: High1 sends the nibble to Low1 hi *)
  destruct (nibble_high_bools c hi ltac:(lia) hn) as (hbc & hbs & hbcol & hbpct).
  assert (hscanL : scan1 (Low1 hi) labNow (length emitted) (zin rest')
                   = (labF, m, Ok1)).
  { rewrite <- hscanok. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    rewrite (scan1_high_nibble (Z.to_nat c) hi labNow (length emitted) (zin rest')
               hbc hbs hbcol hbpct hn). reflexivity. }
  (* the residual scan forces a valid low char *)
  destruct rest' as [|l rest''].
  - exfalso. rewrite scan1_low_nil in hscanL. inversion hscanL.
  - set (l' := Z.to_nat l) in *.
    assert (hidxlt : (idx1 < length inp)%nat) by (unfold idx1; simpl length in *; lia).
    assert (Hl : nth idx1 inp 0 = l).
    { transitivity (nth 0 (skipn idx1 inp) 0).
      - rewrite nth_skipn. f_equal. lia.
      - rewrite hsufx. reflexivity. }
    assert (HinL : In l inp).
    { rewrite <- (firstn_skipn idx1 inp). apply in_or_app. right.
      rewrite hsufx. left; reflexivity. }
    assert (Hlr : 0 <= l < 256) by (apply (bytes_ok1 _ _ hwf); exact HinL).
    change (zin (l :: rest'')) with (l' :: zin rest'') in hscanL.
    destruct (isLowStop1 l') eqn:Estop;
      [exfalso; rewrite (scan1_low_stop hi labNow (length emitted) l' (zin rest'') Estop)
         in hscanL; inversion hscanL|].
    destruct (nibble l') as [lo|] eqn:Enib;
      [| exfalso; rewrite (scan1_low_unk hi labNow (length emitted) l' (zin rest'')
            Estop Enib) in hscanL; inversion hscanL].
    pose proof (nibble_lt _ _ Enib) as hlo16.
    rewrite (scan1_low_ok hi lo labNow (length emitted) l' (zin rest'') Estop Enib)
      in hscanL.
    assert (hposlt : (length emitted + 1 <= m)%nat)
      by (exact (scan1_pos_le (zin rest'') High1 labNow (length emitted + 1)
                   labF m Ok1 hscanL)).
    (* machine: fall dispatch 384 -> 440 *)
    destruct (nibble_ne_stops c hi ltac:(lia) hn)
      as (hne35 & hne59 & hne10 & hne32 & hne95 & hne58 & hne37).
    destruct (p2_fall_tail s4 c hcode4 hpc4 ht2 hcr
                hne35 hne59 hne10 hne32 hne95 hne58 hne37)
      as (sH & hrunH & hpcH & hmemH & hcodeH & hothH).
    (* hi value 440 -> 460 *)
    destruct (p2_hi_value sH c hi hcodeH hpcH
                ltac:(rewrite (hothH 7 ltac:(lia)); exact ht2) hcr hn)
      as (k1 & hk1 & hpcN & h29N & hmemN & hframeN).
    set (sN := runUntil 0 k1 sH) in *.
    assert (hmemNS : sN.(mem) = s.(mem)) by (rewrite hmemN, hmemH; exact hmem4).
    assert (hcodeN : CodeLoaded1 sN)
      by (apply (CodeLoaded1_eqmem s); [exact hmemNS| exact hcode]).
    assert (hothNS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> i <> 29 ->
              rget sN i = rget s i).
    { intros i h0 h5 h7 h28 h29.
      rewrite (hframeN i h28 h29), (hothH i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (h5N : rget sN 5 = Z.of_nat idx1).
    { rewrite (hframeN 5 ltac:(lia) ltac:(lia)), (hothH 5 ltac:(lia)), ht0.
      unfold idx1. lia. }
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
    (* read l (460..468) *)
    assert (ha0N : rget sN 10 = 2147484516).
    { rewrite (hothNS 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact ha0. }
    assert (haddr : wadd (rget sN 10) (rget sN 5) = 2147484516 + Z.of_nat idx1).
    { rewrite ha0N, h5N. apply wadd_id. lia. }
    assert (hu1 : step sN = setPc (rset sN 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 464)).
    { rewrite (step1_add sN 460 28 10 5 hcodeN ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcN ltac:(vm_compute; reflexivity)), haddr, hpcN.
      unfold Image1.coreAddr.
      rewrite (wadd_id (2147483792 + 460) 4 ltac:(lia)). f_equal; lia. }
    set (sR1 := setPc (rset sN 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 464)) in *.
    assert (hmemR1 : sR1.(mem) = s.(mem))
      by (unfold sR1; rewrite setPc_mem, rset_mem; exact hmemNS).
    assert (hcR1 : CodeLoaded1 sR1) by (apply (CodeLoaded1_eqmem s); [exact hmemR1| exact hcode]).
    assert (hpcR1 : sR1.(pc) = 2147483792 + 464) by reflexivity.
    assert (hr28R1 : rget sR1 28 = 2147484516 + Z.of_nat idx1).
    { unfold sR1. rewrite setPc_rget, (rset_rget sN 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hbyteIn : s.(mem) (2147484516 + Z.of_nat idx1) = nth idx1 inp 0).
    { pose proof (hinm (Z.of_nat idx1) ltac:(lia)) as h.
      unfold Image1.inputAddr in h. rewrite Nat2Z.id in h. exact h. }
    assert (hbyte : sR1.(mem) (wadd (rget sR1 28) 0) mod 256 = l).
    { rewrite hr28R1, (wadd_id (2147484516 + Z.of_nat idx1) 0 ltac:(lia)), Z.add_0_r,
        hmemR1, hbyteIn, Hl. apply Z.mod_small. exact Hlr. }
    assert (hu2 : step sR1 = setPc (rset sR1 7 l) (2147483792 + 468)).
    { rewrite (step1_lbu sR1 464 7 28 0 hcR1 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcR1 ltac:(vm_compute; reflexivity)), hbyte, hpcR1,
        (wadd_id (2147483792 + 464) 4 ltac:(lia)). f_equal; lia. }
    set (sR2 := setPc (rset sR1 7 l) (2147483792 + 468)) in *.
    assert (hmemR2 : sR2.(mem) = s.(mem))
      by (unfold sR2; rewrite setPc_mem, rset_mem; exact hmemR1).
    assert (hcR2 : CodeLoaded1 sR2) by (apply (CodeLoaded1_eqmem s); [exact hmemR2| exact hcode]).
    assert (hpcR2 : sR2.(pc) = 2147483792 + 468) by reflexivity.
    assert (hr5R2 : rget sR2 5 = Z.of_nat idx1).
    { unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 7) with false by reflexivity.
      unfold sR1. rewrite setPc_rget, (rset_rget sN 28 _ 5 ltac:(lia) ltac:(lia)).
      replace (5 =? 28) with false by reflexivity. exact h5N. }
    assert (hu3 : step sR2 = setPc (rset sR2 5 (Z.of_nat idx1 + 1)) (2147483792 + 472)).
    { rewrite (step1_addi sR2 468 5 5 1 hcR2 ltac:(lia) ltac:(rewrite coreBytes1_len; lia)
        hpcR2 ltac:(vm_compute; reflexivity)), hr5R2,
        (wadd_id (Z.of_nat idx1) 1 ltac:(lia)), hpcR2,
        (wadd_id (2147483792 + 468) 4 ltac:(lia)). f_equal; lia. }
    set (sR3 := setPc (rset sR2 5 (Z.of_nat idx1 + 1)) (2147483792 + 472)) in *.
    assert (hmemR3 : sR3.(mem) = s.(mem))
      by (unfold sR3; rewrite setPc_mem, rset_mem; exact hmemR2).
    assert (hcR3 : CodeLoaded1 sR3) by (apply (CodeLoaded1_eqmem s); [exact hmemR3| exact hcode]).
    assert (hpcR3 : sR3.(pc) = Image1.coreAddr + 472)
      by (unfold Image1.coreAddr; reflexivity).
    assert (h7R3 : rget sR3 7 = l).
    { unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ 7 ltac:(lia) ltac:(lia)).
      replace (7 =? 5) with false by reflexivity.
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l 7 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hothR : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sR3 i = rget sN i).
    { intros i h0 h5 h7 h28.
      unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ i ltac:(lia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l i ltac:(lia) h0).
      replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
      unfold sR1. rewrite setPc_rget, (rset_rget sN 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      reflexivity. }
    assert (hpN : sN.(pc) <> 0) by (rewrite hpcN; unfold Image1.coreAddr; lia).
    assert (hpR1 : sR1.(pc) <> 0) by (rewrite hpcR1; lia).
    assert (hpR2 : sR2.(pc) <> 0) by (rewrite hpcR2; lia).
    assert (hrunR : runUntil 0 3 sN = sR3).
    { rewrite (runUntil_S 2 sN hpN), hu1, (runUntil_S 1 sR1 hpR1), hu2,
              (runUntil_S 0 sR2 hpR2), hu3. reflexivity. }
    (* lo value 472 -> 492 *)
    destruct (p2_lo_value sR3 l lo hcR3 hpcR3 h7R3 Hlr Enib)
      as (k2 & hk2 & hpcU & h30U & hmemU & hframeU).
    set (sU := runUntil 0 k2 sR3) in *.
    assert (hmemUS : sU.(mem) = s.(mem)) by (rewrite hmemU; exact hmemR3).
    assert (hcodeU : CodeLoaded1 sU)
      by (apply (CodeLoaded1_eqmem s); [exact hmemUS| exact hcode]).
    assert (h29U : rget sU 29 = Z.of_nat hi).
    { rewrite (hframeU 29 ltac:(lia) ltac:(lia)),
        (hothR 29 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact h29N. }
    assert (hothUS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> i <> 29 -> i <> 30 ->
              rget sU i = rget s i).
    { intros i h0 h5 h7 h28 h29 h30.
      rewrite (hframeU i h28 h30), (hothR i h0 h5 h7 h28).
      exact (hothNS i h0 h5 h7 h28 h29). }
    assert (h6U : rget sU 6 = Z.of_nat (length emitted)).
    { rewrite (hothUS 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact houtidx. }
    assert (h12U : rget sU 12 = 2147485184).
    { rewrite (hothUS 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact ha2. }
    assert (hpU : sU.(pc) <> 0) by (rewrite hpcU; unfold Image1.coreAddr; lia).
    (* store block 492..512 *)
    assert (hu4 : step sU = setPc (rset sU 29 (wshl (Z.of_nat hi) 4)) (2147483792 + 496)).
    { rewrite (step1_slli sU 492 29 29 4 hcodeU ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcU ltac:(vm_compute; reflexivity)), h29U, hpcU.
      unfold Image1.coreAddr.
      rewrite (wadd_id (2147483792 + 492) 4 ltac:(lia)). f_equal; lia. }
    set (sV1 := setPc (rset sU 29 (wshl (Z.of_nat hi) 4)) (2147483792 + 496)) in *.
    assert (hmemV1 : sV1.(mem) = s.(mem))
      by (unfold sV1; rewrite setPc_mem, rset_mem; exact hmemUS).
    assert (hcV1 : CodeLoaded1 sV1) by (apply (CodeLoaded1_eqmem s); [exact hmemV1| exact hcode]).
    assert (hpcV1 : sV1.(pc) = 2147483792 + 496) by reflexivity.
    assert (h29V1 : rget sV1 29 = wshl (Z.of_nat hi) 4).
    { unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ 29 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (h30V1 : rget sV1 30 = Z.of_nat lo).
    { unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ 30 ltac:(lia) ltac:(lia)).
      replace (30 =? 29) with false by reflexivity. exact h30U. }
    assert (hu5 : step sV1 = setPc (rset sV1 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)))
                                   (2147483792 + 500)).
    { rewrite (step1_or sV1 496 29 29 30 hcV1 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcV1 ltac:(vm_compute; reflexivity)),
        h29V1, h30V1, hpcV1, (wadd_id (2147483792 + 496) 4 ltac:(lia)). f_equal; lia. }
    set (sV2 := setPc (rset sV1 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)))
                      (2147483792 + 500)) in *.
    assert (hmemV2 : sV2.(mem) = s.(mem))
      by (unfold sV2; rewrite setPc_mem, rset_mem; exact hmemV1).
    assert (hcV2 : CodeLoaded1 sV2) by (apply (CodeLoaded1_eqmem s); [exact hmemV2| exact hcode]).
    assert (hpcV2 : sV2.(pc) = 2147483792 + 500) by reflexivity.
    assert (h12V2 : rget sV2 12 = 2147485184).
    { unfold sV2. rewrite setPc_rget, (rset_rget sV1 29 _ 12 ltac:(lia) ltac:(lia)).
      replace (12 =? 29) with false by reflexivity.
      unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ 12 ltac:(lia) ltac:(lia)).
      replace (12 =? 29) with false by reflexivity. exact h12U. }
    assert (h6V2 : rget sV2 6 = Z.of_nat (length emitted)).
    { unfold sV2. rewrite setPc_rget, (rset_rget sV1 29 _ 6 ltac:(lia) ltac:(lia)).
      replace (6 =? 29) with false by reflexivity.
      unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ 6 ltac:(lia) ltac:(lia)).
      replace (6 =? 29) with false by reflexivity. exact h6U. }
    assert (houtaddr : wadd (rget sV2 12) (rget sV2 6)
                       = 2147485184 + Z.of_nat (length emitted)).
    { rewrite h12V2, h6V2. apply wadd_id. lia. }
    assert (hu6 : step sV2 = setPc (rset sV2 28 (2147485184 + Z.of_nat (length emitted)))
                                   (2147483792 + 504)).
    { rewrite (step1_add sV2 500 28 12 6 hcV2 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcV2 ltac:(vm_compute; reflexivity)),
        houtaddr, hpcV2, (wadd_id (2147483792 + 500) 4 ltac:(lia)). f_equal; lia. }
    set (sV3 := setPc (rset sV2 28 (2147485184 + Z.of_nat (length emitted)))
                      (2147483792 + 504)) in *.
    assert (hmemV3 : sV3.(mem) = s.(mem))
      by (unfold sV3; rewrite setPc_mem, rset_mem; exact hmemV2).
    assert (hcV3 : CodeLoaded1 sV3) by (apply (CodeLoaded1_eqmem s); [exact hmemV3| exact hcode]).
    assert (hpcV3 : sV3.(pc) = 2147483792 + 504) by reflexivity.
    assert (h28V3 : rget sV3 28 = 2147485184 + Z.of_nat (length emitted)).
    { unfold sV3. rewrite setPc_rget, (rset_rget sV2 28 _ 28 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (h29V3 : rget sV3 29 = wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)).
    { unfold sV3. rewrite setPc_rget, (rset_rget sV2 28 _ 29 ltac:(lia) ltac:(lia)).
      replace (29 =? 28) with false by reflexivity.
      unfold sV2. rewrite setPc_rget, (rset_rget sV1 29 _ 29 ltac:(lia) ltac:(lia)),
        Z.eqb_refl. reflexivity. }
    assert (hu7 : step sV3 = setPc (storeByte sV3 (2147485184 + Z.of_nat (length emitted))
                                      (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)))
                                   (2147483792 + 508)).
    { rewrite (step1_sb sV3 504 28 29 0 hcV3 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcV3 ltac:(vm_compute; reflexivity)),
        h28V3, h29V3,
        (wadd_id (2147485184 + Z.of_nat (length emitted)) 0 ltac:(lia)), Z.add_0_r,
        hpcV3, (wadd_id (2147483792 + 504) 4 ltac:(lia)). f_equal; lia. }
    set (sW := storeByte sV3 (2147485184 + Z.of_nat (length emitted))
                 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) in *.
    set (sV4 := setPc sW (2147483792 + 508)) in *.
    assert (hpcV4 : sV4.(pc) = 2147483792 + 508) by reflexivity.
    assert (hmemV4 : sV4.(mem) = sW.(mem)) by reflexivity.
    assert (hcV4 : CodeLoaded1 sV4).
    { apply (CodeLoaded1_eqmem sW); [reflexivity|].
      apply codeLoaded1_storeByte;
        [apply (CodeLoaded1_eqmem s); [exact hmemV3| exact hcode]|].
      unfold Image1.coreAddr. lia. }
    assert (h6V4 : rget sV4 6 = Z.of_nat (length emitted)).
    { unfold sV4. rewrite setPc_rget. unfold sW. rewrite storeByte_rget.
      unfold sV3. rewrite setPc_rget, (rset_rget sV2 28 _ 6 ltac:(lia) ltac:(lia)).
      replace (6 =? 28) with false by reflexivity. exact h6V2. }
    assert (hu8 : step sV4 = setPc (rset sV4 6 (Z.of_nat (length emitted) + 1))
                                   (2147483792 + 512)).
    { rewrite (step1_addi sV4 508 6 6 1 hcV4 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcV4 ltac:(vm_compute; reflexivity)), h6V4,
        (wadd_id (Z.of_nat (length emitted)) 1 ltac:(lia)), hpcV4,
        (wadd_id (2147483792 + 508) 4 ltac:(lia)). f_equal; lia. }
    set (sV5 := setPc (rset sV4 6 (Z.of_nat (length emitted) + 1)) (2147483792 + 512)) in *.
    assert (hmemV5 : sV5.(mem) = sW.(mem))
      by (unfold sV5; rewrite setPc_mem, rset_mem; reflexivity).
    assert (hcV5 : CodeLoaded1 sV5)
      by (apply (CodeLoaded1_eqmem sV4); [exact hmemV5| exact hcV4]).
    assert (hpcV5 : sV5.(pc) = 2147483792 + 512) by reflexivity.
    assert (hu9 : step sV5 = setPc sV5 (2147483792 + 368)).
    { rewrite (step1_jal sV5 512 0 (-144) hcV5 ltac:(lia)
        ltac:(rewrite coreBytes1_len; lia) hpcV5 ltac:(vm_compute; reflexivity)),
        rset_zero, hpcV5, (wadd_id (2147483792 + 512) (-144) ltac:(lia)).
      f_equal; lia. }
    set (sF := setPc sV5 (2147483792 + 368)) in *.
    assert (hpV1 : sV1.(pc) <> 0) by (rewrite hpcV1; lia).
    assert (hpV2 : sV2.(pc) <> 0) by (rewrite hpcV2; lia).
    assert (hpV3 : sV3.(pc) <> 0) by (rewrite hpcV3; lia).
    assert (hpV4 : sV4.(pc) <> 0) by (rewrite hpcV4; lia).
    assert (hpV5 : sV5.(pc) <> 0) by (rewrite hpcV5; lia).
    assert (hrunF : runUntil 0 ((4 + (14 + k1)) + (3 + (k2 + 6))) s = sF).
    { rewrite (runUntil_add (4 + (14 + k1)) (3 + (k2 + 6))),
              (runUntil_add 4 (14 + k1)), hrun4, (runUntil_add 14 k1), hrunH.
      fold sN.
      rewrite (runUntil_add 3 (k2 + 6)), hrunR, (runUntil_add k2 6).
      fold sU.
      rewrite (runUntil_S 5 sU hpU), hu4, (runUntil_S 4 sV1 hpV1), hu5,
              (runUntil_S 3 sV2 hpV2), hu6, (runUntil_S 2 sV3 hpV3), hu7.
      fold sW. fold sV4.
      rewrite (runUntil_S 1 sV4 hpV4), hu8, (runUntil_S 0 sV5 hpV5), hu9.
      reflexivity. }
    set (b := (hi * 16 + lo)%nat) in *.
    exists ((4 + (14 + k1)) + (3 + (k2 + 6)))%nat. left.
    exists rest''. exists (emitted ++ b :: nil).
    rewrite hrunF.
    assert (hlen2 : length (emitted ++ b :: nil) = S (length emitted))
      by (rewrite length_app; simpl; lia).
    assert (hmemW : forall a, sW.(mem) a
              = if a =? 2147485184 + Z.of_nat (length emitted)
                then (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)) mod 256
                else s.(mem) a).
    { intros a. unfold sW. rewrite storeByte_mem. cbv beta.
      destruct (a =? 2147485184 + Z.of_nat (length emitted)); [reflexivity|].
      rewrite hmemV3. reflexivity. }
    assert (hmemF : sF.(mem) = sW.(mem)) by (unfold sF; rewrite setPc_mem; exact hmemV5).
    assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 6 -> i <> 7 -> i <> 28 ->
              i <> 29 -> i <> 30 -> rget sF i = rget s i).
    { intros i h0 h5 h6 h7 h28 h29 h30.
      unfold sF. rewrite setPc_rget.
      unfold sV5. rewrite setPc_rget, (rset_rget sV4 6 _ i ltac:(lia) h0).
      replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
      unfold sV4. rewrite setPc_rget. unfold sW. rewrite storeByte_rget.
      unfold sV3. rewrite setPc_rget, (rset_rget sV2 28 _ i ltac:(lia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sV2. rewrite setPc_rget, (rset_rget sV1 29 _ i ltac:(lia) h0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ i ltac:(lia) h0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      exact (hothUS i h0 h5 h7 h28 h29 h30). }
    split; [simpl length; lia| split; [simpl length; lia|]].
    assert (hsufx2 : skipn (S idx1) inp = rest'').
    { replace (S idx1) with (1 + idx1)%nat by lia.
      rewrite <- skipn_skipn, hsufx. reflexivity. }
    refine {| p2_wf := hwf; p2_at_loop := _; p2_code := _; p2_a0 := _; p2_a1 := _;
              p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
              p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
              p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
              p2_scan_inp := hscaninp; p2_scan_ok := _; p2_spec := _ |}.
    + apply setPc_pc.
    + apply (CodeLoaded1_eqmem sV5); [reflexivity| exact hcV5].
    + rewrite (hothF 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha0.
    + rewrite (hothF 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha1.
    + rewrite (hothF 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha2.
    + rewrite (hothF 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha3.
    + rewrite (hothF 14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact ha4.
    + rewrite (hothF 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact hra.
    + (* input intact through the byte store *)
      apply (inputLoaded_eqmem sW); [exact hmemF|].
      unfold sW.
      apply inputLoaded_storeByte;
        [apply (inputLoaded_eqmem s); [exact hmemV3| exact hinm]|].
      unfold Image1.inputAddr. right. lia.
    + (* t0 *)
      assert (hr5F : rget sF 5 = Z.of_nat idx1 + 1).
      { unfold sF. rewrite setPc_rget.
        unfold sV5. rewrite setPc_rget, (rset_rget sV4 6 _ 5 ltac:(lia) ltac:(lia)).
        replace (5 =? 6) with false by reflexivity.
        unfold sV4. rewrite setPc_rget. unfold sW. rewrite storeByte_rget.
        unfold sV3. rewrite setPc_rget, (rset_rget sV2 28 _ 5 ltac:(lia) ltac:(lia)).
        replace (5 =? 28) with false by reflexivity.
        unfold sV2. rewrite setPc_rget, (rset_rget sV1 29 _ 5 ltac:(lia) ltac:(lia)).
        replace (5 =? 29) with false by reflexivity.
        unfold sV1. rewrite setPc_rget, (rset_rget sU 29 _ 5 ltac:(lia) ltac:(lia)).
        replace (5 =? 29) with false by reflexivity.
        rewrite (hframeU 5 ltac:(lia) ltac:(lia)).
        unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ 5 ltac:(lia) ltac:(lia)),
          Z.eqb_refl. reflexivity. }
      rewrite hr5F. unfold idx1. simpl length in *. lia.
    + replace (length inp - length rest'')%nat with (S idx1)
        by (unfold idx1; simpl length in *; lia).
      exact hsufx2.
    + (* t1 = |emitted| + 1 *)
      assert (hr6F : rget sF 6 = Z.of_nat (length emitted) + 1).
      { unfold sF. rewrite setPc_rget.
        unfold sV5. rewrite setPc_rget, (rset_rget sV4 6 _ 6 ltac:(lia) ltac:(lia)),
          Z.eqb_refl. reflexivity. }
      rewrite hr6F, hlen2. lia.
    + (* the out region extends by the new byte *)
      unfold Image1.outAddr.
      rewrite hlen2, hmemF.
      rewrite readMem_snoc.
      f_equal.
      * rewrite (readMem_frame (length emitted) s.(mem) sW.(mem) 2147485184
          ltac:(intros a ha; rewrite (hmemW a);
                replace (a =? 2147485184 + Z.of_nat (length emitted)) with false
                  by (symmetry; apply Z.eqb_neq; lia);
                reflexivity)).
        exact houtmem.
      * rewrite (hmemW (2147485184 + Z.of_nat (length emitted))), Z.eqb_refl.
        rewrite (combine_nibbles hi lo hhi16 hlo16).
        unfold b. rewrite Nat2Z.id. reflexivity.
    + (* table intact through the byte store *)
      apply (tableLoaded_eqmem sW); [exact hmemF|].
      unfold sW.
      apply tableLoaded_storeByte;
        [apply (tableLoaded_eqmem s); [exact hmemV3| exact htbl]|].
      unfold Image1.lblAddr. left. lia.
    + (* residual scan *)
      rewrite hlen2. replace (S (length emitted)) with (length emitted + 1)%nat by lia.
      exact hscanL.
    + (* emit telescope through the byte *)
      assert (hE : emit1 High1 labF (length emitted) (zin (c :: l :: rest''))
                   = consOut b (emit1 High1 labF (length emitted + 1) (zin rest''))).
      { change (zin (c :: l :: rest'')) with (Z.to_nat c :: zin (l :: rest'')).
        rewrite (emit1_high_nibble (Z.to_nat c) hi labF (length emitted)
                   (zin (l :: rest'')) hbc hbs hbcol hbpct hn).
        change (zin (l :: rest'')) with (l' :: zin rest'').
        apply (emit1_low_ok hi lo labF (length emitted) l' (zin rest'') Estop Enib). }
      rewrite hspec, hE. unfold consOut. cbn [fst snd].
      rewrite hlen2.
      replace (S (length emitted)) with (length emitted + 1)%nat by lia.
      rewrite <- app_assoc. reflexivity.
Qed.

(* The low 32 bits of the 64-bit wrapped offset agree with the spec's
   32-bit truncation, byte by byte. *)
Lemma off_byte_agree x sh : sh = 0 \/ sh = 8 \/ sh = 16 \/ sh = 24 ->
  ((x mod 2 ^ 64) / 2 ^ sh) mod 256 = ((x mod 2 ^ 32) / 2 ^ sh) mod 256.
Proof.
  intros hsh.
  assert (hb : x mod 2 ^ 32 = (x mod 2 ^ 64) mod 2 ^ 32).
  { apply Znumtheory.Zmod_div_mod; [lia| lia|].
    exists (2 ^ 32). reflexivity. }
  set (a := x mod 2 ^ 64) in *.
  assert (ha : 0 <= a < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite hb.
  rewrite (Z.div_mod a (2 ^ 32)) at 1 by lia.
  destruct hsh as [h|[h|[h|h]]]; subst sh.
  - change (2 ^ 0) with 1. rewrite !Z.div_1_r.
    replace (2 ^ 32 * (a / 2 ^ 32) + a mod 2 ^ 32)
      with (a mod 2 ^ 32 + (2 ^ 24 * (a / 2 ^ 32)) * 256) by ring.
    apply Z_mod_plus_full.
  - replace (2 ^ 32 * (a / 2 ^ 32) + a mod 2 ^ 32)
      with ((2 ^ 24 * (a / 2 ^ 32)) * 2 ^ 8 + a mod 2 ^ 32) by ring.
    rewrite (Z.div_add_l (2 ^ 24 * (a / 2 ^ 32)) (2 ^ 8) (a mod 2 ^ 32) ltac:(lia)).
    replace (2 ^ 24 * (a / 2 ^ 32) + a mod 2 ^ 32 / 2 ^ 8)
      with (a mod 2 ^ 32 / 2 ^ 8 + (2 ^ 16 * (a / 2 ^ 32)) * 256) by ring.
    apply Z_mod_plus_full.
  - replace (2 ^ 32 * (a / 2 ^ 32) + a mod 2 ^ 32)
      with ((2 ^ 16 * (a / 2 ^ 32)) * 2 ^ 16 + a mod 2 ^ 32) by ring.
    rewrite (Z.div_add_l (2 ^ 16 * (a / 2 ^ 32)) (2 ^ 16) (a mod 2 ^ 32) ltac:(lia)).
    replace (2 ^ 16 * (a / 2 ^ 32) + a mod 2 ^ 32 / 2 ^ 16)
      with (a mod 2 ^ 32 / 2 ^ 16 + (2 ^ 8 * (a / 2 ^ 32)) * 256) by ring.
    apply Z_mod_plus_full.
  - replace (2 ^ 32 * (a / 2 ^ 32) + a mod 2 ^ 32)
      with ((2 ^ 8 * (a / 2 ^ 32)) * 2 ^ 24 + a mod 2 ^ 32) by ring.
    rewrite (Z.div_add_l (2 ^ 8 * (a / 2 ^ 32)) (2 ^ 24) (a mod 2 ^ 32) ltac:(lia)).
    replace (2 ^ 8 * (a / 2 ^ 32) + a mod 2 ^ 32 / 2 ^ 24)
      with (a mod 2 ^ 32 / 2 ^ 24 + (a / 2 ^ 32) * 256) by ring.
    apply Z_mod_plus_full.
Qed.

Lemma offBytes_len p pos : length (offBytes p pos) = 4%nat.
Proof. reflexivity. Qed.

(* lia wrapper for proofs carrying a long set-bound State chain: a bare lia
   zify-preprocesses the whole context (OOM at 16 GiB).  Drop every
   State-related hypothesis, then unfold the Image1 address constants so
   symbolic bounds (in_fits1 etc.) connect with literal addresses. *)
Ltac clia :=
  repeat match goal with
  | H : context [step] |- _ => clear H
  | H : context [runUntil] |- _ => clear H
  | H : context [setPc] |- _ => clear H
  | H : context [rset] |- _ => clear H
  | H : context [storeByte] |- _ => clear H
  | H : context [storeWord] |- _ => clear H
  | H : context [rget] |- _ => clear H
  | H : context [CodeLoaded1] |- _ => clear H
  | H : context [TableLoaded] |- _ => clear H
  | H : context [InputLoaded] |- _ => clear H
  | H : context [readMem] |- _ => clear H
  | H : context [mem] |- _ => clear H
  | H : context [pc] |- _ => clear H
  | H : context [scan1] |- _ => clear H
  | H : context [emit1] |- _ => clear H
  | H : context [WellFormed1] |- _ => clear H
  | H : context [nth] |- _ => clear H
  | H : context [skipn] |- _ => clear H
  | H : context [In] |- _ => clear H
  end;
  repeat match goal with x : State |- _ => clear x end;
  unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr
    in *;
  lia.


(* A COMPLETE pass-2 iteration for a label reference ('%l'): read the label
   byte, load the slot, sign-test. Undefined -> Undef exit 700 (Result1);
   defined at p -> 4 little-endian offset bytes via sb/srli (= offBytes),
   t1 += 4, back to the loop head. *)
Lemma p2_ref : forall inp cap rest' labF labNow m emitted s,
  P2Inv inp cap s labF labNow m emitted (37 :: rest') ->
  exists k,
    (exists rest2 emitted2, (length rest2 < length ((37:Z) :: rest'))%nat /\
        (k <= 50 * (length ((37:Z) :: rest') - length rest2))%nat /\
        P2Inv inp cap (runUntil 0 k s) labF labNow m emitted2 rest2)
    \/ ((k <= 50 * length ((37:Z) :: rest'))%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap rest' labF labNow m emitted s inv. pose proof inv as inv0.
  destruct (p2_prefix inp cap 37 rest' labF labNow m emitted s inv)
    as (s4 & hrun4 & hpc4 & ht2 & hcr & ht0 & hmem4 & hcode4 & hother4).
  destruct (p2_pct_tail s4 hcode4 hpc4 ht2)
    as (sL & hrunT & hpcL & hmemL & hcodeL & hothL).
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  pose proof (WellFormed1_cap63 _ _ hwf) as hcap63.
  pose proof (in_fits1 _ _ hwf) as hinf. pose proof (out_fits1 _ _ hwf) as houtf.
  pose proof (lbl_fits1 _ _ hwf) as hlblf. pose proof (cap_nonneg _ _ hwf) as hcap0.
  set (idx1 := (length inp - length rest')%nat) in *.
  assert (hge : (length rest' + 1 <= length inp)%nat).
  { pose proof (f_equal (@length Z) hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl. clia. }
  assert (hsufx : skipn idx1 inp = rest')
    by (apply (suffix_step1 inp 37 rest'); exact hsuf).
  (* the residual scan forces a label byte to exist *)
  assert (hscanP : scan1 Pct1 labNow (length emitted) (zin rest') = (labF, m, Ok1)).
  { rewrite <- hscanok.
    change (zin (37 :: rest')) with (37%nat :: zin rest').
    rewrite scan1_pct. reflexivity. }
  destruct rest' as [|l rest''].
  - exfalso. rewrite scan1_pct_nil in hscanP. inversion hscanP.
  - set (l' := Z.to_nat l) in *.
    assert (hbnd1 : (length rest'' < length ((37:Z) :: l :: rest''))%nat)
      by (simpl length; clia).
    assert (hbnd2 : ((4 + 14) + (6 + 13) <= 50 * (length ((37:Z) :: l :: rest'')
                       - length rest''))%nat)
      by (simpl length; clia).
    change (zin (l :: rest'')) with (l' :: zin rest'') in hscanP.
    rewrite scan1_pct_cons in hscanP.
    assert (hposlt : (length emitted + 4 <= m)%nat)
      by (exact (scan1_pos_le (zin rest'') High1 labNow (length emitted + 4)
                   labF m Ok1 hscanP)).
    assert (hidxlt : (idx1 < length inp)%nat) by (unfold idx1; simpl length in *; clia).
    assert (Hl : nth idx1 inp 0 = l).
    { transitivity (nth 0 (skipn idx1 inp) 0).
      - rewrite nth_skipn. f_equal. clia.
      - rewrite hsufx. reflexivity. }
    assert (HinL : In l inp).
    { rewrite <- (firstn_skipn idx1 inp). apply in_or_app. right.
      rewrite hsufx. left; reflexivity. }
    assert (Hlr : 0 <= l < 256) by (apply (bytes_ok1 _ _ hwf); exact HinL).
    assert (hl' : Z.of_nat l' = l) by (unfold l'; apply Z2Nat.id; clia).
    assert (hl256 : (l' < 256)%nat) by (unfold l'; clia).
    assert (h5L : rget sL 5 = Z.of_nat idx1).
    { rewrite (hothL 5 ltac:(clia)), ht0. unfold idx1. clia. }
    assert (hothLS : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sL i = rget s i).
    { intros i h0 h5 h7 h28.
      rewrite (hothL i h28), (hother4 i h0 h5 h7 h28). reflexivity. }
    assert (hmemLS : sL.(mem) = s.(mem)) by (rewrite hmemL; exact hmem4).
    unfold Image1.inputAddr, Image1.outAddr, Image1.lblAddr, Image1.coreAddr in *.
    (* read the label byte (524..532) *)
    assert (ha0L : rget sL 10 = 2147484516).
    { rewrite (hothLS 10 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)). exact ha0. }
    assert (haddr : wadd (rget sL 10) (rget sL 5) = 2147484516 + Z.of_nat idx1).
    { rewrite ha0L, h5L. apply wadd_id. clia. }
    assert (hu1 : step sL = setPc (rset sL 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 528)).
    { rewrite (step1_add sL 524 28 10 5 hcodeL ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcL ltac:(vm_compute; reflexivity)), haddr, hpcL.
      unfold Image1.coreAddr.
      rewrite (wadd_id (2147483792 + 524) 4 ltac:(clia)). f_equal; clia. }
    set (sR1 := setPc (rset sL 28 (2147484516 + Z.of_nat idx1)) (2147483792 + 528)) in *.
    assert (hmemR1 : sR1.(mem) = s.(mem))
      by (unfold sR1; rewrite setPc_mem, rset_mem; exact hmemLS).
    assert (hcR1 : CodeLoaded1 sR1) by (apply (CodeLoaded1_eqmem s); [exact hmemR1| exact hcode]).
    assert (hpcR1 : sR1.(pc) = 2147483792 + 528) by reflexivity.
    assert (hr28R1 : rget sR1 28 = 2147484516 + Z.of_nat idx1).
    { unfold sR1. rewrite setPc_rget, (rset_rget sL 28 _ 28 ltac:(clia) ltac:(clia)),
        Z.eqb_refl. reflexivity. }
    assert (hbyteIn : s.(mem) (2147484516 + Z.of_nat idx1) = nth idx1 inp 0).
    { pose proof (hinm (Z.of_nat idx1) ltac:(clia)) as h.
      unfold Image1.inputAddr in h. rewrite Nat2Z.id in h. exact h. }
    assert (hbyte : sR1.(mem) (wadd (rget sR1 28) 0) mod 256 = l).
    { rewrite hr28R1, (wadd_id (2147484516 + Z.of_nat idx1) 0 ltac:(clia)), Z.add_0_r,
        hmemR1, hbyteIn, Hl. apply Z.mod_small. exact Hlr. }
    assert (hu2 : step sR1 = setPc (rset sR1 7 l) (2147483792 + 532)).
    { rewrite (step1_lbu sR1 528 7 28 0 hcR1 ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcR1 ltac:(vm_compute; reflexivity)), hbyte, hpcR1,
        (wadd_id (2147483792 + 528) 4 ltac:(clia)). f_equal; clia. }
    set (sR2 := setPc (rset sR1 7 l) (2147483792 + 532)) in *.
    assert (hmemR2 : sR2.(mem) = s.(mem))
      by (unfold sR2; rewrite setPc_mem, rset_mem; exact hmemR1).
    assert (hcR2 : CodeLoaded1 sR2) by (apply (CodeLoaded1_eqmem s); [exact hmemR2| exact hcode]).
    assert (hpcR2 : sR2.(pc) = 2147483792 + 532) by reflexivity.
    assert (hr5R2 : rget sR2 5 = Z.of_nat idx1).
    { unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l 5 ltac:(clia) ltac:(clia)).
      replace (5 =? 7) with false by reflexivity.
      unfold sR1. rewrite setPc_rget, (rset_rget sL 28 _ 5 ltac:(clia) ltac:(clia)).
      replace (5 =? 28) with false by reflexivity. exact h5L. }
    assert (hu3 : step sR2 = setPc (rset sR2 5 (Z.of_nat idx1 + 1)) (2147483792 + 536)).
    { rewrite (step1_addi sR2 532 5 5 1 hcR2 ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcR2 ltac:(vm_compute; reflexivity)), hr5R2,
        (wadd_id (Z.of_nat idx1) 1 ltac:(clia)), hpcR2,
        (wadd_id (2147483792 + 532) 4 ltac:(clia)). f_equal; clia. }
    set (sR3 := setPc (rset sR2 5 (Z.of_nat idx1 + 1)) (2147483792 + 536)) in *.
    assert (hmemR3 : sR3.(mem) = s.(mem))
      by (unfold sR3; rewrite setPc_mem, rset_mem; exact hmemR2).
    assert (hcR3 : CodeLoaded1 sR3) by (apply (CodeLoaded1_eqmem s); [exact hmemR3| exact hcode]).
    assert (hpcR3 : sR3.(pc) = 2147483792 + 536) by reflexivity.
    assert (h7R3 : rget sR3 7 = l).
    { unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ 7 ltac:(clia) ltac:(clia)).
      replace (7 =? 5) with false by reflexivity.
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l 7 ltac:(clia) ltac:(clia)),
        Z.eqb_refl. reflexivity. }
    assert (hothR : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
              rget sR3 i = rget s i).
    { intros i h0 h5 h7 h28.
      unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ i ltac:(clia) h0).
      replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
      unfold sR2. rewrite setPc_rget, (rset_rget sR1 7 l i ltac:(clia) h0).
      replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
      unfold sR1. rewrite setPc_rget, (rset_rget sL 28 _ i ltac:(clia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      exact (hothLS i h0 h5 h7 h28). }
    (* slot address (536..544) *)
    assert (hu4 : step sR3 = setPc (rset sR3 28 (8 * l)) (2147483792 + 540)).
    { rewrite (step1_slli sR3 536 28 7 3 hcR3 ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcR3 ltac:(vm_compute; reflexivity)), h7R3, (wshl3 l Hlr), hpcR3,
        (wadd_id (2147483792 + 536) 4 ltac:(clia)). f_equal; clia. }
    set (sM1 := setPc (rset sR3 28 (8 * l)) (2147483792 + 540)) in *.
    assert (hmemM1 : sM1.(mem) = s.(mem))
      by (unfold sM1; rewrite setPc_mem, rset_mem; exact hmemR3).
    assert (hcM1 : CodeLoaded1 sM1) by (apply (CodeLoaded1_eqmem s); [exact hmemM1| exact hcode]).
    assert (hpcM1 : sM1.(pc) = 2147483792 + 540) by reflexivity.
    assert (hr28M1 : rget sM1 28 = 8 * l).
    { unfold sM1. rewrite setPc_rget, (rset_rget sR3 28 _ 28 ltac:(clia) ltac:(clia)),
        Z.eqb_refl. reflexivity. }
    assert (ha4M1 : rget sM1 14 = 2147489280).
    { unfold sM1. rewrite setPc_rget, (rset_rget sR3 28 _ 14 ltac:(clia) ltac:(clia)).
      replace (14 =? 28) with false by reflexivity.
      rewrite (hothR 14 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)). exact ha4. }
    assert (hslot : wadd (rget sM1 28) (rget sM1 14) = 2147489280 + 8 * Z.of_nat l').
    { rewrite hr28M1, ha4M1, (wadd_id (8 * l) 2147489280 ltac:(clia)).
      rewrite hl'. clia. }
    assert (hu5 : step sM1 = setPc (rset sM1 28 (2147489280 + 8 * Z.of_nat l'))
                                   (2147483792 + 544)).
    { rewrite (step1_add sM1 540 28 28 14 hcM1 ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcM1 ltac:(vm_compute; reflexivity)), hslot, hpcM1,
        (wadd_id (2147483792 + 540) 4 ltac:(clia)). f_equal; clia. }
    set (sM2 := setPc (rset sM1 28 (2147489280 + 8 * Z.of_nat l')) (2147483792 + 544)) in *.
    assert (hmemM2 : sM2.(mem) = s.(mem))
      by (unfold sM2; rewrite setPc_mem, rset_mem; exact hmemM1).
    assert (hcM2 : CodeLoaded1 sM2) by (apply (CodeLoaded1_eqmem s); [exact hmemM2| exact hcode]).
    assert (hpcM2 : sM2.(pc) = 2147483792 + 544) by reflexivity.
    assert (hr28M2 : rget sM2 28 = 2147489280 + 8 * Z.of_nat l').
    { unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ 28 ltac:(clia) ltac:(clia)),
        Z.eqb_refl. reflexivity. }
    assert (hslotrange : 0 <= encodeSlot (labF l') < 2 ^ 64).
    { destruct (labF l') as [p|] eqn:Elab0; cbn.
      - pose proof (hlable l' p Elab0). clia.
      - clia. }
    assert (htblM2 : TableLoaded sM2 labF)
      by (apply (tableLoaded_eqmem s); [exact hmemM2| exact htbl]).
    assert (hldval : loadWord sM2 (wadd (rget sM2 28) 0) = encodeSlot (labF l')).
    { rewrite hr28M2, (wadd_id (2147489280 + 8 * Z.of_nat l') 0 ltac:(clia)), Z.add_0_r.
      pose proof (loadWord_slot sM2 labF l' htblM2 hl256 hslotrange) as h.
      unfold Image1.lblAddr in h. exact h. }
    assert (hu6 : step sM2 = setPc (rset sM2 29 (encodeSlot (labF l'))) (2147483792 + 548)).
    { rewrite (step1_ld sM2 544 29 28 0 hcM2 ltac:(clia) ltac:(rewrite coreBytes1_len; clia)
        hpcM2 ltac:(vm_compute; reflexivity)), hldval, hpcM2,
        (wadd_id (2147483792 + 544) 4 ltac:(clia)). f_equal; clia. }
    set (sM3 := setPc (rset sM2 29 (encodeSlot (labF l'))) (2147483792 + 548)) in *.
    assert (hmemM3 : sM3.(mem) = s.(mem))
      by (unfold sM3; rewrite setPc_mem, rset_mem; exact hmemM2).
    assert (hcM3 : CodeLoaded1 sM3) by (apply (CodeLoaded1_eqmem s); [exact hmemM3| exact hcode]).
    assert (hpcM3 : sM3.(pc) = 2147483792 + 548) by reflexivity.
    assert (hr29M3 : rget sM3 29 = encodeSlot (labF l')).
    { unfold sM3. rewrite setPc_rget, (rset_rget sM2 29 _ 29 ltac:(clia) ltac:(clia)),
        Z.eqb_refl. reflexivity. }
    assert (hothM : forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> i <> 29 ->
              rget sM3 i = rget s i).
    { intros i h0 h5 h7 h28 h29.
      unfold sM3. rewrite setPc_rget, (rset_rget sM2 29 _ i ltac:(clia) h0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
      unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ i ltac:(clia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      unfold sM1. rewrite setPc_rget, (rset_rget sR3 28 _ i ltac:(clia) h0).
      replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
      exact (hothR i h0 h5 h7 h28). }
    assert (hpL0 : sL.(pc) <> 0) by (rewrite hpcL; clia).
    assert (hpR1 : sR1.(pc) <> 0) by (rewrite hpcR1; clia).
    assert (hpR2 : sR2.(pc) <> 0) by (rewrite hpcR2; clia).
    assert (hpR3 : sR3.(pc) <> 0) by (rewrite hpcR3; clia).
    assert (hpM1 : sM1.(pc) <> 0) by (rewrite hpcM1; clia).
    assert (hpM2 : sM2.(pc) <> 0) by (rewrite hpcM2; clia).
    assert (hpM3 : sM3.(pc) <> 0) by (rewrite hpcM3; clia).
    assert (hrun6 : runUntil 0 6 sL = sM3).
    { rewrite (runUntil_S 5 sL hpL0), hu1, (runUntil_S 4 sR1 hpR1), hu2,
              (runUntil_S 3 sR2 hpR2), hu3, (runUntil_S 2 sR3 hpR3), hu4,
              (runUntil_S 1 sM1 hpM1), hu5, (runUntil_S 0 sM2 hpM2), hu6. reflexivity. }
    (* spec side: the emit either resolves or stops Undef *)
    destruct (labF l') as [p|] eqn:Elab.
    + (* defined at p: 4 offset bytes *)
      assert (hp63 : Z.of_nat p < 2 ^ 63).
      { pose proof (hlable l' p Elab). clia. }
      assert (hslt : sltb (rget sM3 29) (rget sM3 0) = false).
      { rewrite hr29M3, rget_zero. exact (encodeSlot_some_nonneg p hp63). }
      assert (hu7 : step sM3 = setPc sM3 (2147483792 + 552)).
      { rewrite (step1_blt sM3 548 29 0 152 hcM3 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcM3 ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpcM3, (wadd_id (2147483792 + 548) 4 ltac:(clia)).
        f_equal; clia. }
      set (sN0 := setPc sM3 (2147483792 + 552)) in *.
      assert (hmemN0 : sN0.(mem) = s.(mem)) by (unfold sN0; rewrite setPc_mem; exact hmemM3).
      assert (hcN0 : CodeLoaded1 sN0) by (apply (CodeLoaded1_eqmem s); [exact hmemN0| exact hcode]).
      assert (hpcN0 : sN0.(pc) = 2147483792 + 552) by reflexivity.
      assert (h6N0 : rget sN0 6 = Z.of_nat (length emitted)).
      { unfold sN0. rewrite setPc_rget.
        rewrite (hothM 6 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)).
        exact houtidx. }
      (* 552: addi t5,t1,4 *)
      assert (hu8 : step sN0 = setPc (rset sN0 30 (Z.of_nat (length emitted) + 4))
                                     (2147483792 + 556)).
      { rewrite (step1_addi sN0 552 30 6 4 hcN0 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcN0 ltac:(vm_compute; reflexivity)), h6N0,
          (wadd_id (Z.of_nat (length emitted)) 4 ltac:(clia)), hpcN0,
          (wadd_id (2147483792 + 552) 4 ltac:(clia)). f_equal; clia. }
      set (sN1 := setPc (rset sN0 30 (Z.of_nat (length emitted) + 4)) (2147483792 + 556)) in *.
      assert (hmemN1 : sN1.(mem) = s.(mem))
        by (unfold sN1; rewrite setPc_mem, rset_mem; exact hmemN0).
      assert (hcN1 : CodeLoaded1 sN1) by (apply (CodeLoaded1_eqmem s); [exact hmemN1| exact hcode]).
      assert (hpcN1 : sN1.(pc) = 2147483792 + 556) by reflexivity.
      set (S4 := Z.of_nat (length emitted) + 4) in *.
      set (V := wsub (Z.of_nat p) S4) in *.
      assert (hr29N1 : rget sN1 29 = Z.of_nat p).
      { unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ 29 ltac:(clia) ltac:(clia)).
        replace (29 =? 30) with false by reflexivity.
        unfold sN0. rewrite setPc_rget. rewrite hr29M3. reflexivity. }
      assert (hr30N1 : rget sN1 30 = S4).
      { unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ 30 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      (* 556: sub t4,t4,t5 *)
      assert (hu9 : step sN1 = setPc (rset sN1 29 V) (2147483792 + 560)).
      { rewrite (step1_sub sN1 556 29 29 30 hcN1 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcN1 ltac:(vm_compute; reflexivity)),
          hr29N1, hr30N1, hpcN1, (wadd_id (2147483792 + 556) 4 ltac:(clia)).
        f_equal; clia. }
      set (sN2 := setPc (rset sN1 29 V) (2147483792 + 560)) in *.
      assert (hmemN2 : sN2.(mem) = s.(mem))
        by (unfold sN2; rewrite setPc_mem, rset_mem; exact hmemN1).
      assert (hcN2 : CodeLoaded1 sN2) by (apply (CodeLoaded1_eqmem s); [exact hmemN2| exact hcode]).
      assert (hpcN2 : sN2.(pc) = 2147483792 + 560) by reflexivity.
      assert (h12N2 : rget sN2 12 = 2147485184).
      { unfold sN2. rewrite setPc_rget, (rset_rget sN1 29 _ 12 ltac:(clia) ltac:(clia)).
        replace (12 =? 29) with false by reflexivity.
        unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ 12 ltac:(clia) ltac:(clia)).
        replace (12 =? 30) with false by reflexivity.
        unfold sN0. rewrite setPc_rget.
        rewrite (hothM 12 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)).
        exact ha2. }
      assert (h6N2 : rget sN2 6 = Z.of_nat (length emitted)).
      { unfold sN2. rewrite setPc_rget, (rset_rget sN1 29 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 29) with false by reflexivity.
        unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 30) with false by reflexivity. exact h6N0. }
      set (A := 2147485184 + Z.of_nat (length emitted)) in *.
      (* 560: add t3,a2,t1 *)
      assert (hu10 : step sN2 = setPc (rset sN2 28 A) (2147483792 + 564)).
      { rewrite (step1_add sN2 560 28 12 6 hcN2 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcN2 ltac:(vm_compute; reflexivity)),
          h12N2, h6N2, (wadd_id 2147485184 (Z.of_nat (length emitted)) ltac:(clia)),
          hpcN2, (wadd_id (2147483792 + 560) 4 ltac:(clia)).
        f_equal; clia. }
      set (sN3 := setPc (rset sN2 28 A) (2147483792 + 564)) in *.
      assert (hmemN3 : sN3.(mem) = s.(mem))
        by (unfold sN3; rewrite setPc_mem, rset_mem; exact hmemN2).
      assert (hcN3 : CodeLoaded1 sN3) by (apply (CodeLoaded1_eqmem s); [exact hmemN3| exact hcode]).
      assert (hpcN3 : sN3.(pc) = 2147483792 + 564) by reflexivity.
      assert (hVr : 0 <= V < 2 ^ 64).
      { unfold V, wsub, wrap, w64. apply Z.mod_pos_bound. clia. }
      (* the 4 sb/srli stores (564..588) *)
      assert (hr28N3 : rget sN3 28 = A).
      { unfold sN3. rewrite setPc_rget, (rset_rget sN2 28 _ 28 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      assert (hr29N3 : rget sN3 29 = V).
      { unfold sN3. rewrite setPc_rget, (rset_rget sN2 28 _ 29 ltac:(clia) ltac:(clia)).
        replace (29 =? 28) with false by reflexivity.
        unfold sN2. rewrite setPc_rget, (rset_rget sN1 29 _ 29 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      assert (hu11 : step sN3 = setPc (storeByte sN3 A V) (2147483792 + 568)).
      { rewrite (step1_sb sN3 564 28 29 0 hcN3 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcN3 ltac:(vm_compute; reflexivity)),
          hr28N3, hr29N3, (wadd_id A 0 ltac:(unfold A; clia)), Z.add_0_r,
          hpcN3, (wadd_id (2147483792 + 564) 4 ltac:(clia)). f_equal; clia. }
      set (sP1 := setPc (storeByte sN3 A V) (2147483792 + 568)) in *.
      assert (hcP1 : CodeLoaded1 sP1).
      { apply (CodeLoaded1_eqmem (storeByte sN3 A V)); [reflexivity|].
        apply codeLoaded1_storeByte;
          [apply (CodeLoaded1_eqmem s); [exact hmemN3| exact hcode]|].
        unfold Image1.coreAddr, A. clia. }
      assert (hpcP1 : sP1.(pc) = 2147483792 + 568) by reflexivity.
      assert (hr29P1 : rget sP1 29 = V).
      { unfold sP1. rewrite setPc_rget, storeByte_rget. exact hr29N3. }
      assert (hu12 : step sP1 = setPc (rset sP1 29 (V / 2 ^ 8)) (2147483792 + 572)).
      { rewrite (step1_srli sP1 568 29 29 8 hcP1 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcP1 ltac:(vm_compute; reflexivity)),
          hr29P1, (wshr_div V 8 ltac:(clia)), hpcP1,
          (wadd_id (2147483792 + 568) 4 ltac:(clia)). f_equal; clia. }
      set (sQ1 := setPc (rset sP1 29 (V / 2 ^ 8)) (2147483792 + 572)) in *.
      assert (hcQ1 : CodeLoaded1 sQ1)
        by (apply (CodeLoaded1_eqmem sP1); [unfold sQ1; rewrite setPc_mem, rset_mem; reflexivity| exact hcP1]).
      assert (hpcQ1 : sQ1.(pc) = 2147483792 + 572) by reflexivity.
      assert (hr28Q1 : rget sQ1 28 = A).
      { unfold sQ1. rewrite setPc_rget, (rset_rget sP1 29 _ 28 ltac:(clia) ltac:(clia)).
        replace (28 =? 29) with false by reflexivity.
        unfold sP1. rewrite setPc_rget, storeByte_rget. exact hr28N3. }
      assert (hr29Q1 : rget sQ1 29 = V / 2 ^ 8).
      { unfold sQ1. rewrite setPc_rget, (rset_rget sP1 29 _ 29 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      assert (hu13 : step sQ1 = setPc (storeByte sQ1 (A + 1) (V / 2 ^ 8)) (2147483792 + 576)).
      { rewrite (step1_sb sQ1 572 28 29 1 hcQ1 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcQ1 ltac:(vm_compute; reflexivity)),
          hr28Q1, hr29Q1, (wadd_id A 1 ltac:(unfold A; clia)),
          hpcQ1, (wadd_id (2147483792 + 572) 4 ltac:(clia)). f_equal; clia. }
      set (sP2 := setPc (storeByte sQ1 (A + 1) (V / 2 ^ 8)) (2147483792 + 576)) in *.
      assert (hcP2 : CodeLoaded1 sP2).
      { apply (CodeLoaded1_eqmem (storeByte sQ1 (A + 1) (V / 2 ^ 8))); [reflexivity|].
        apply codeLoaded1_storeByte; [exact hcQ1|].
        unfold Image1.coreAddr, A. clia. }
      assert (hpcP2 : sP2.(pc) = 2147483792 + 576) by reflexivity.
      assert (hr29P2 : rget sP2 29 = V / 2 ^ 8).
      { unfold sP2. rewrite setPc_rget, storeByte_rget. exact hr29Q1. }
      assert (hu14 : step sP2 = setPc (rset sP2 29 (V / 2 ^ 16)) (2147483792 + 580)).
      { rewrite (step1_srli sP2 576 29 29 8 hcP2 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcP2 ltac:(vm_compute; reflexivity)),
          hr29P2, (wshr_div (V / 2 ^ 8) 8 ltac:(clia)), hpcP2,
          (wadd_id (2147483792 + 576) 4 ltac:(clia)).
        rewrite Z.div_div by clia. f_equal; clia. }
      set (sQ2 := setPc (rset sP2 29 (V / 2 ^ 16)) (2147483792 + 580)) in *.
      assert (hcQ2 : CodeLoaded1 sQ2)
        by (apply (CodeLoaded1_eqmem sP2); [unfold sQ2; rewrite setPc_mem, rset_mem; reflexivity| exact hcP2]).
      assert (hpcQ2 : sQ2.(pc) = 2147483792 + 580) by reflexivity.
      assert (hr28Q2 : rget sQ2 28 = A).
      { unfold sQ2. rewrite setPc_rget, (rset_rget sP2 29 _ 28 ltac:(clia) ltac:(clia)).
        replace (28 =? 29) with false by reflexivity.
        unfold sP2. rewrite setPc_rget, storeByte_rget. exact hr28Q1. }
      assert (hr29Q2 : rget sQ2 29 = V / 2 ^ 16).
      { unfold sQ2. rewrite setPc_rget, (rset_rget sP2 29 _ 29 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      assert (hu15 : step sQ2 = setPc (storeByte sQ2 (A + 2) (V / 2 ^ 16)) (2147483792 + 584)).
      { rewrite (step1_sb sQ2 580 28 29 2 hcQ2 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcQ2 ltac:(vm_compute; reflexivity)),
          hr28Q2, hr29Q2, (wadd_id A 2 ltac:(unfold A; clia)),
          hpcQ2, (wadd_id (2147483792 + 580) 4 ltac:(clia)). f_equal; clia. }
      set (sP3 := setPc (storeByte sQ2 (A + 2) (V / 2 ^ 16)) (2147483792 + 584)) in *.
      assert (hcP3 : CodeLoaded1 sP3).
      { apply (CodeLoaded1_eqmem (storeByte sQ2 (A + 2) (V / 2 ^ 16))); [reflexivity|].
        apply codeLoaded1_storeByte; [exact hcQ2|].
        unfold Image1.coreAddr, A. clia. }
      assert (hpcP3 : sP3.(pc) = 2147483792 + 584) by reflexivity.
      assert (hr29P3 : rget sP3 29 = V / 2 ^ 16).
      { unfold sP3. rewrite setPc_rget, storeByte_rget. exact hr29Q2. }
      assert (hu16 : step sP3 = setPc (rset sP3 29 (V / 2 ^ 24)) (2147483792 + 588)).
      { rewrite (step1_srli sP3 584 29 29 8 hcP3 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcP3 ltac:(vm_compute; reflexivity)),
          hr29P3, (wshr_div (V / 2 ^ 16) 8 ltac:(clia)), hpcP3,
          (wadd_id (2147483792 + 584) 4 ltac:(clia)).
        rewrite Z.div_div by clia. f_equal; clia. }
      set (sQ3 := setPc (rset sP3 29 (V / 2 ^ 24)) (2147483792 + 588)) in *.
      assert (hcQ3 : CodeLoaded1 sQ3)
        by (apply (CodeLoaded1_eqmem sP3); [unfold sQ3; rewrite setPc_mem, rset_mem; reflexivity| exact hcP3]).
      assert (hpcQ3 : sQ3.(pc) = 2147483792 + 588) by reflexivity.
      assert (hr28Q3 : rget sQ3 28 = A).
      { unfold sQ3. rewrite setPc_rget, (rset_rget sP3 29 _ 28 ltac:(clia) ltac:(clia)).
        replace (28 =? 29) with false by reflexivity.
        unfold sP3. rewrite setPc_rget, storeByte_rget. exact hr28Q2. }
      assert (hr29Q3 : rget sQ3 29 = V / 2 ^ 24).
      { unfold sQ3. rewrite setPc_rget, (rset_rget sP3 29 _ 29 ltac:(clia) ltac:(clia)),
          Z.eqb_refl. reflexivity. }
      assert (hu17 : step sQ3 = setPc (storeByte sQ3 (A + 3) (V / 2 ^ 24)) (2147483792 + 592)).
      { rewrite (step1_sb sQ3 588 28 29 3 hcQ3 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcQ3 ltac:(vm_compute; reflexivity)),
          hr28Q3, hr29Q3, (wadd_id A 3 ltac:(unfold A; clia)),
          hpcQ3, (wadd_id (2147483792 + 588) 4 ltac:(clia)). f_equal; clia. }
      set (sP4 := setPc (storeByte sQ3 (A + 3) (V / 2 ^ 24)) (2147483792 + 592)) in *.
      assert (hcP4 : CodeLoaded1 sP4).
      { apply (CodeLoaded1_eqmem (storeByte sQ3 (A + 3) (V / 2 ^ 24))); [reflexivity|].
        apply codeLoaded1_storeByte; [exact hcQ3|].
        unfold Image1.coreAddr, A. clia. }
      assert (hpcP4 : sP4.(pc) = 2147483792 + 592) by reflexivity.
      assert (h6P4 : rget sP4 6 = Z.of_nat (length emitted)).
      { unfold sP4. rewrite setPc_rget, storeByte_rget.
        unfold sQ3. rewrite setPc_rget, (rset_rget sP3 29 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 29) with false by reflexivity.
        unfold sP3. rewrite setPc_rget, storeByte_rget.
        unfold sQ2. rewrite setPc_rget, (rset_rget sP2 29 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 29) with false by reflexivity.
        unfold sP2. rewrite setPc_rget, storeByte_rget.
        unfold sQ1. rewrite setPc_rget, (rset_rget sP1 29 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 29) with false by reflexivity.
        unfold sP1. rewrite setPc_rget, storeByte_rget.
        unfold sN3. rewrite setPc_rget, (rset_rget sN2 28 _ 6 ltac:(clia) ltac:(clia)).
        replace (6 =? 28) with false by reflexivity. exact h6N2. }
      (* 592: addi t1,t1,4; 596: jal back *)
      assert (hu18 : step sP4 = setPc (rset sP4 6 S4) (2147483792 + 596)).
      { rewrite (step1_addi sP4 592 6 6 4 hcP4 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcP4 ltac:(vm_compute; reflexivity)), h6P4,
          (wadd_id (Z.of_nat (length emitted)) 4 ltac:(clia)), hpcP4,
          (wadd_id (2147483792 + 592) 4 ltac:(clia)). f_equal; clia. }
      set (sN4 := setPc (rset sP4 6 S4) (2147483792 + 596)) in *.
      assert (hcN4 : CodeLoaded1 sN4)
        by (apply (CodeLoaded1_eqmem sP4); [unfold sN4; rewrite setPc_mem, rset_mem; reflexivity| exact hcP4]).
      assert (hpcN4 : sN4.(pc) = 2147483792 + 596) by reflexivity.
      assert (hu19 : step sN4 = setPc sN4 (2147483792 + 368)).
      { rewrite (step1_jal sN4 596 0 (-228) hcN4 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcN4 ltac:(vm_compute; reflexivity)),
          rset_zero, hpcN4, (wadd_id (2147483792 + 596) (-228) ltac:(clia)).
        f_equal; clia. }
      set (sF := setPc sN4 (2147483792 + 368)) in *.
      assert (hpN0 : sN0.(pc) <> 0) by (rewrite hpcN0; clia).
      assert (hpN1 : sN1.(pc) <> 0) by (rewrite hpcN1; clia).
      assert (hpN2 : sN2.(pc) <> 0) by (rewrite hpcN2; clia).
      assert (hpN3 : sN3.(pc) <> 0) by (rewrite hpcN3; clia).
      assert (hpP1 : sP1.(pc) <> 0) by (rewrite hpcP1; clia).
      assert (hpQ1 : sQ1.(pc) <> 0) by (rewrite hpcQ1; clia).
      assert (hpP2 : sP2.(pc) <> 0) by (rewrite hpcP2; clia).
      assert (hpQ2 : sQ2.(pc) <> 0) by (rewrite hpcQ2; clia).
      assert (hpP3 : sP3.(pc) <> 0) by (rewrite hpcP3; clia).
      assert (hpQ3 : sQ3.(pc) <> 0) by (rewrite hpcQ3; clia).
      assert (hpP4 : sP4.(pc) <> 0) by (rewrite hpcP4; clia).
      assert (hpN4 : sN4.(pc) <> 0) by (rewrite hpcN4; clia).
      assert (hrunF : runUntil 0 ((4 + 14) + (6 + 13)) s = sF).
      { rewrite (runUntil_add (4 + 14) (6 + 13)), (runUntil_add 4 14), hrun4, hrunT,
                (runUntil_add 6 13), hrun6.
        rewrite (runUntil_S 12 sM3 hpM3), hu7, (runUntil_S 11 sN0 hpN0), hu8,
                (runUntil_S 10 sN1 hpN1), hu9, (runUntil_S 9 sN2 hpN2), hu10,
                (runUntil_S 8 sN3 hpN3), hu11.
        fold sP1.
        rewrite (runUntil_S 7 sP1 hpP1), hu12, (runUntil_S 6 sQ1 hpQ1), hu13.
        fold sP2.
        rewrite (runUntil_S 5 sP2 hpP2), hu14, (runUntil_S 4 sQ2 hpQ2), hu15.
        fold sP3.
        rewrite (runUntil_S 3 sP3 hpP3), hu16, (runUntil_S 2 sQ3 hpQ3), hu17.
        fold sP4.
        rewrite (runUntil_S 1 sP4 hpP4), hu18, (runUntil_S 0 sN4 hpN4), hu19.
        reflexivity. }
      (* the final memory, pointwise *)
      assert (hmemFx : forall x, sF.(mem) x
                = if x =? A + 3 then (V / 2 ^ 24) mod 256
                  else if x =? A + 2 then (V / 2 ^ 16) mod 256
                  else if x =? A + 1 then (V / 2 ^ 8) mod 256
                  else if x =? A then V mod 256
                  else s.(mem) x).
      { intros x.
        unfold sF. rewrite setPc_mem. unfold sN4. rewrite setPc_mem, rset_mem.
        unfold sP4. rewrite setPc_mem, storeByte_mem. cbv beta.
        destruct (x =? A + 3); [reflexivity|].
        unfold sQ3. rewrite setPc_mem, rset_mem.
        unfold sP3. rewrite setPc_mem, storeByte_mem. cbv beta.
        destruct (x =? A + 2); [reflexivity|].
        unfold sQ2. rewrite setPc_mem, rset_mem.
        unfold sP2. rewrite setPc_mem, storeByte_mem. cbv beta.
        destruct (x =? A + 1); [reflexivity|].
        unfold sQ1. rewrite setPc_mem, rset_mem.
        unfold sP1. rewrite setPc_mem, storeByte_mem. cbv beta.
        destruct (x =? A); [reflexivity|].
        exact (f_equal (fun mm => mm x) hmemN3). }
      assert (hA_eq : A = 2147485184 + Z.of_nat (length emitted)) by reflexivity.
      assert (hframe_out : forall x, x < A \/ A + 4 <= x -> sF.(mem) x = s.(mem) x).
      { intros x hx. rewrite (hmemFx x).
        replace (x =? A + 3) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (x =? A + 2) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (x =? A + 1) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (x =? A) with false by (symmetry; apply Z.eqb_neq; clia).
        reflexivity. }
      set (off := (Z.of_nat p - S4) mod 2 ^ 32) in *.
      assert (hoffr : 0 <= off < 2 ^ 32) by (apply Z.mod_pos_bound; clia).
      assert (hVoff : forall sh, sh = 0 \/ sh = 8 \/ sh = 16 \/ sh = 24 ->
                (V / 2 ^ sh) mod 256 = (off / 2 ^ sh) mod 256).
      { intros sh hsh. unfold V, wsub, wrap, w64, off.
        apply (off_byte_agree (Z.of_nat p - S4) sh hsh). }
      assert (hOB : offBytes p (length emitted)
               = (Z.to_nat (off mod 256) :: Z.to_nat (off / 2 ^ 8 mod 256)
                  :: Z.to_nat (off / 2 ^ 16 mod 256) :: Z.to_nat (off / 2 ^ 24 mod 256)
                  :: nil)).
      { unfold offBytes, off, S4. reflexivity. }
      clearbody V off.
      exists ((4 + 14) + (6 + 13))%nat. left.
      exists rest''. exists (emitted ++ offBytes p (length emitted)).
      rewrite hrunF.
      assert (hlen2 : length (emitted ++ offBytes p (length emitted))
                      = (length emitted + 4)%nat)
        by (rewrite length_app, offBytes_len; clia).
      assert (hothF : forall i, i <> 0 -> i <> 5 -> i <> 6 -> i <> 7 -> i <> 28 ->
                i <> 29 -> i <> 30 -> rget sF i = rget s i).
      { intros i h0 h5 h6 h7 h28 h29 h30.
        unfold sF. rewrite setPc_rget.
        unfold sN4. rewrite setPc_rget, (rset_rget sP4 6 _ i ltac:(clia) h0).
        replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6).
        unfold sP4. rewrite setPc_rget, storeByte_rget.
        unfold sQ3. rewrite setPc_rget, (rset_rget sP3 29 _ i ltac:(clia) h0).
        replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
        unfold sP3. rewrite setPc_rget, storeByte_rget.
        unfold sQ2. rewrite setPc_rget, (rset_rget sP2 29 _ i ltac:(clia) h0).
        replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
        unfold sP2. rewrite setPc_rget, storeByte_rget.
        unfold sQ1. rewrite setPc_rget, (rset_rget sP1 29 _ i ltac:(clia) h0).
        replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
        unfold sP1. rewrite setPc_rget, storeByte_rget.
        unfold sN3. rewrite setPc_rget, (rset_rget sN2 28 _ i ltac:(clia) h0).
        replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
        unfold sN2. rewrite setPc_rget, (rset_rget sN1 29 _ i ltac:(clia) h0).
        replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29).
        unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ i ltac:(clia) h0).
        replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact h30).
        unfold sN0. rewrite setPc_rget.
        exact (hothM i h0 h5 h7 h28 h29). }
      split; [exact hbnd1| split; [exact hbnd2|]].
      assert (hsufx2 : skipn (S idx1) inp = rest'').
      { replace (S idx1) with (1 + idx1)%nat by clia.
        rewrite <- skipn_skipn, hsufx. reflexivity. }
      refine {| p2_wf := hwf; p2_at_loop := _; p2_code := _; p2_a0 := _; p2_a1 := _;
                p2_a2 := _; p2_a3 := _; p2_a4 := _; p2_ra := _; p2_in_mem := _;
                p2_idx := _; p2_suffix := _; p2_outidx := _; p2_out_mem := _;
                p2_tbl := _; p2_m_le := hmle; p2_lab_le := hlable;
                p2_scan_inp := hscaninp; p2_scan_ok := _; p2_spec := _ |}.
      * apply setPc_pc.
      * apply (CodeLoaded1_eqmem sN4); [reflexivity| exact hcN4].
      * rewrite (hothF 10 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact ha0.
      * rewrite (hothF 11 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact ha1.
      * rewrite (hothF 12 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact ha2.
      * rewrite (hothF 13 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact ha3.
      * rewrite (hothF 14 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact ha4.
      * rewrite (hothF 1 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)); exact hra.
      * (* input intact: all 4 stores land in the out region *)
        intros j hj. rewrite hframe_out;
          [exact (hinm j hj)| left; unfold Image1.inputAddr in *; clia].
      * (* t0 *)
        assert (hr5F : rget sF 5 = Z.of_nat idx1 + 1).
        { unfold sF. rewrite setPc_rget.
          unfold sN4. rewrite setPc_rget, (rset_rget sP4 6 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 6) with false by reflexivity.
          unfold sP4. rewrite setPc_rget, storeByte_rget.
          unfold sQ3. rewrite setPc_rget, (rset_rget sP3 29 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sP3. rewrite setPc_rget, storeByte_rget.
          unfold sQ2. rewrite setPc_rget, (rset_rget sP2 29 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sP2. rewrite setPc_rget, storeByte_rget.
          unfold sQ1. rewrite setPc_rget, (rset_rget sP1 29 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sP1. rewrite setPc_rget, storeByte_rget.
          unfold sN3. rewrite setPc_rget, (rset_rget sN2 28 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 28) with false by reflexivity.
          unfold sN2. rewrite setPc_rget, (rset_rget sN1 29 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sN1. rewrite setPc_rget, (rset_rget sN0 30 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 30) with false by reflexivity.
          unfold sN0. rewrite setPc_rget.
          unfold sM3. rewrite setPc_rget, (rset_rget sM2 29 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 29) with false by reflexivity.
          unfold sM2. rewrite setPc_rget, (rset_rget sM1 28 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 28) with false by reflexivity.
          unfold sM1. rewrite setPc_rget, (rset_rget sR3 28 _ 5 ltac:(clia) ltac:(clia)).
          replace (5 =? 28) with false by reflexivity.
          unfold sR3. rewrite setPc_rget, (rset_rget sR2 5 _ 5 ltac:(clia) ltac:(clia)),
            Z.eqb_refl. reflexivity. }
        rewrite hr5F. unfold idx1. simpl length in *. clia.
      * replace (length inp - length rest'')%nat with (S idx1)
          by (unfold idx1; simpl length in *; clia).
        exact hsufx2.
      * (* t1 = |emitted| + 4 *)
        assert (hr6F : rget sF 6 = S4).
        { unfold sF. rewrite setPc_rget.
          unfold sN4. rewrite setPc_rget, (rset_rget sP4 6 _ 6 ltac:(clia) ltac:(clia)),
            Z.eqb_refl. reflexivity. }
        rewrite hr6F, hlen2. unfold S4. clia.
      * (* out region: the 4 offset bytes *)
        unfold Image1.outAddr.
        rewrite hlen2.
        replace (length emitted + 4)%nat
          with (S (S (S (S (length emitted))))) by clia.
        rewrite !readMem_snoc.
        rewrite (readMem_frame (length emitted) s.(mem) sF.(mem) 2147485184
          ltac:(intros a ha; apply hframe_out; clia)).
        rewrite houtmem, hOB.
        replace (2147485184 + Z.of_nat (length emitted)) with A by (unfold A; clia).
        replace (2147485184 + Z.of_nat (S (length emitted))) with (A + 1)
          by (unfold A; clia).
        replace (2147485184 + Z.of_nat (S (S (length emitted)))) with (A + 2)
          by (unfold A; clia).
        replace (2147485184 + Z.of_nat (S (S (S (length emitted))))) with (A + 3)
          by (unfold A; clia).
        rewrite (hmemFx A), (hmemFx (A + 1)), (hmemFx (A + 2)), (hmemFx (A + 3)).
        replace (A =? A + 3) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (A =? A + 2) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (A =? A + 1) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (A + 1 =? A + 3) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (A + 1 =? A + 2) with false by (symmetry; apply Z.eqb_neq; clia).
        replace (A + 2 =? A + 3) with false by (symmetry; apply Z.eqb_neq; clia).
        rewrite !Z.eqb_refl.
        assert (hV0 := hVoff 0 ltac:(clia)).
        change (2 ^ 0) with 1 in hV0. rewrite !Z.div_1_r in hV0.
        rewrite hV0, (hVoff 8 ltac:(clia)),
                (hVoff 16 ltac:(clia)), (hVoff 24 ltac:(clia)).
        rewrite <- !app_assoc. reflexivity.
      * (* table intact: all 4 stores are below lblAddr *)
        intros c0 hc0 k0 hk0.
        rewrite hframe_out;
          [exact (htbl c0 hc0 k0 hk0)|
           right; unfold Image1.lblAddr in *; clia].
      * (* residual scan *)
        rewrite hlen2. exact hscanP.
      * (* emit telescope through the 4 offset bytes *)
        assert (hE : emit1 High1 labF (length emitted) (zin (37 :: l :: rest''))
                     = appOut (offBytes p (length emitted))
                         (emit1 High1 labF (length emitted + 4) (zin rest''))).
        { change (zin (37 :: l :: rest'')) with (37%nat :: zin (l :: rest'')).
          rewrite emit1_pct.
          change (zin (l :: rest'')) with (l' :: zin rest'').
          rewrite emit1_pct_cons, Elab. reflexivity. }
        rewrite hspec, hE. unfold appOut. cbn [fst snd].
        rewrite hlen2, app_assoc. reflexivity.
    + (* undefined label -> Undef exit (700) *)
      assert (hslt : sltb (rget sM3 29) (rget sM3 0) = true).
      { rewrite hr29M3, rget_zero. exact encodeSlot_none_neg. }
      assert (hu7 : step sM3 = setPc sM3 (2147483792 + 700)).
      { rewrite (step1_blt sM3 548 29 0 152 hcM3 ltac:(clia)
          ltac:(rewrite coreBytes1_len; clia) hpcM3 ltac:(vm_compute; reflexivity)), hslt.
        cbn match. rewrite hpcM3, (wadd_id (2147483792 + 548) 152 ltac:(clia)).
        f_equal; clia. }
      set (sX := setPc sM3 (2147483792 + 700)) in *.
      assert (hmemX : sX.(mem) = s.(mem)) by (unfold sX; rewrite setPc_mem; exact hmemM3).
      assert (hcodeX : CodeLoaded1 sX)
        by (apply (CodeLoaded1_eqmem s); [exact hmemX| exact hcode]).
      assert (hpcX : sX.(pc) = Image1.coreAddr + 700)
        by (unfold Image1.coreAddr; reflexivity).
      assert (hraX : rget sX 1 = 0).
      { unfold sX. rewrite setPc_rget.
        rewrite (hothM 1 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)).
        exact hra. }
      assert (h6X : rget sX 6 = Z.of_nat (length emitted)).
      { unfold sX. rewrite setPc_rget.
        rewrite (hothM 6 ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia) ltac:(clia)).
        exact houtidx. }
      assert (hemit : emit1 High1 labF 0 (zin inp) = (emitted, Undef1)).
      { assert (hE : emit1 High1 labF (length emitted) (zin (37 :: l :: rest''))
                     = ([], Undef1)).
        { change (zin (37 :: l :: rest'')) with (37%nat :: zin (l :: rest'')).
          rewrite emit1_pct.
          change (zin (l :: rest'')) with (l' :: zin rest'').
          rewrite emit1_pct_cons, Elab. reflexivity. }
        rewrite hspec, hE. cbn [fst snd]. rewrite app_nil_r. reflexivity. }
      destruct (p2_undef_exit inp cap labF m emitted sX hpcX hcodeX hraX h6X
                  ltac:(clia) ltac:(rewrite hmemX; exact houtmem) hscaninp hmle hemit)
        as (f & hrunE & hres).
      exists ((4 + 14) + (6 + (1 + 3)))%nat. right.
      split; [simpl length; clia|].
      rewrite (runUntil_add (4 + 14) (6 + (1 + 3))), (runUntil_add 4 14), hrun4, hrunT,
              (runUntil_add 6 (1 + 3)), hrun6,
              (runUntil_add 1 3), (runUntil_one sM3 hpM3), hu7.
      fold sX. rewrite hrunE. exact hres.
Qed.

(* Pass-2 EOF: bgeu taken at 368 (t0 = a1 = |inp|) -> Ok exit 628; the
   emit telescope collapses via emit1 [] = ([], Ok1), and scan_ok on []
   pins labF = labNow, m = |emitted|. 1 + 3 steps to a Result1. *)
Lemma p2_eof : forall inp cap labF labNow m emitted s,
  P2Inv inp cap s labF labNow m emitted [] ->
  Result1 (runUntil 0 (1 + 3) s) inp cap.
Proof.
  intros inp cap labF labNow m emitted s inv.
  destruct inv as [hwf hpc0 hcode ha0 ha1 ha2 ha3 ha4 hra hinm hidx hsuf houtidx
                   houtmem htbl hmle hlable hscaninp hscanok hspec].
  (* scan_ok on []: labF = labNow, m = |emitted| *)
  assert (hsc := hscanok).
  change (zin (@nil Z)) with (@nil nat) in hsc.
  rewrite scan1_nil in hsc.
  assert (hlab : labF = labNow) by (inversion hsc; reflexivity).
  assert (hm : m = length emitted) by (inversion hsc; reflexivity).
  subst labF m.
  (* bgeu t0,a1 taken at 368 -> 628 *)
  assert (h5' : rget s 5 = Z.of_nat (length inp))
    by (rewrite hidx; simpl length; lia).
  assert (hbt : step s = setPc s (Image1.coreAddr + 628)).
  { apply (bgeu1_eq_taken s 368 5 11 (Z.of_nat (length inp)) 260 _ hcode ltac:(lia)
      ltac:(rewrite coreBytes1_len; lia) hpc0 h5' ha1 ltac:(vm_compute; reflexivity)).
    rewrite (wadd_id (Image1.coreAddr + 368) 260 ltac:(unfold Image1.coreAddr; lia)).
    lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc0; unfold Image1.coreAddr; lia).
  (* telescope collapse *)
  assert (hemit : emit1 High1 labNow 0 (zin inp) = (emitted, Ok1)).
  { rewrite hspec. change (zin (@nil Z)) with (@nil nat).
    rewrite emit1_nil. cbn [fst snd]. rewrite app_nil_r. reflexivity. }
  set (s1 := setPc s (Image1.coreAddr + 628)).
  assert (hpc1 : s1.(pc) = Image1.coreAddr + 628) by apply setPc_pc.
  assert (hcode1 : CodeLoaded1 s1)
    by (apply (CodeLoaded1_eqmem s); [reflexivity| exact hcode]).
  assert (hra1 : rget s1 1 = 0) by (unfold s1; rewrite setPc_rget; exact hra).
  assert (h61 : rget s1 6 = Z.of_nat (length emitted))
    by (unfold s1; rewrite setPc_rget; exact houtidx).
  assert (hlen1 : Z.of_nat (length emitted) < 2 ^ 63)
    by (pose proof (WellFormed1_cap63 _ _ hwf); lia).
  assert (hout1 : readMem s1.(mem) Image1.outAddr (length emitted) = emitted)
    by (unfold s1; rewrite setPc_mem; exact houtmem).
  destruct (p2_ok_exit inp cap labNow (length emitted) emitted s1 hpc1 hcode1
              hra1 h61 hlen1 hout1 hscaninp hmle hemit) as (f & hrunE & hres).
  rewrite (runUntil_add 1 3), (runUntil_one s hp0), hbt. fold s1.
  rewrite hrunE. exact hres.
Qed.

(* One pass-2 iteration: consume >= 1 char in <= 50 steps/char preserving
   P2Inv (labF, m fixed; labNow/emitted may change), or halt in a Result1.
   The invalid-char branch is vacuous: scan_ok rules it out. *)
Theorem p2_iteration : forall inp cap rest labF labNow m emitted s,
  rest <> [] -> P2Inv inp cap s labF labNow m emitted rest ->
  exists k,
    (exists rest2 labNow2 emitted2, (length rest2 < length rest)%nat /\
        (k <= 50 * (length rest - length rest2))%nat /\
        P2Inv inp cap (runUntil 0 k s) labF labNow2 m emitted2 rest2)
    \/ ((k <= 50 * length rest)%nat /\ Result1 (runUntil 0 k s) inp cap).
Proof.
  intros inp cap rest labF labNow m emitted s hne inv.
  destruct rest as [|c rest']; [exfalso; apply hne; reflexivity|].
  pose proof inv as inv0.
  destruct inv0 as [hwf _ _ _ _ _ _ _ _ _ _ hsuf _ _ _ _ _ _ hscanok _].
  assert (HinC : In c inp).
  { rewrite <- (firstn_skipn (length inp - length (c :: rest')) inp).
    apply in_or_app. right. rewrite hsuf. left; reflexivity. }
  assert (hcr : 0 <= c < 256) by (apply (bytes_ok1 _ _ hwf); exact HinC).
  destruct (isComment (Z.to_nat c)) eqn:Ecm.
  - (* comment *)
    destruct (p2_comment inp cap c rest' labF labNow m emitted s Ecm inv)
      as (k & [ (rest2 & hlt & hk & inv2) | (hk & hres) ]).
    + exists k. left. exists rest2. exists labNow. exists emitted. tauto.
    + exists k. right. tauto.
  - destruct (isSpace (Z.to_nat c)) eqn:Esp.
    + (* spacing *)
      destruct (p2_spacing inp cap c rest' labF labNow m emitted s Esp inv)
        as (k & hk & inv2).
      exists k. left. exists rest'. exists labNow. exists emitted.
      split; [simpl length; lia| split; [simpl length; lia| exact inv2]].
    + destruct (Z.eq_dec c 58) as [-> |hcol].
      * (* label definition: skip *)
        destruct (p2_labelDef inp cap rest' labF labNow m emitted s inv)
          as (k & [ (rest2 & labNow2 & hlt & hk & inv2) | (hk & hres) ]).
        -- exists k. left. exists rest2. exists labNow2. exists emitted. tauto.
        -- exists k. right. tauto.
      * destruct (Z.eq_dec c 37) as [-> |hpct].
        -- (* label reference: 4 offset bytes *)
           destruct (p2_ref inp cap rest' labF labNow m emitted s inv)
             as (k & [ (rest2 & emitted2 & hlt & hk & inv2) | (hk & hres) ]).
           ++ exists k. left. exists rest2. exists labNow. exists emitted2. tauto.
           ++ exists k. right. tauto.
        -- assert (hncol : (Z.to_nat c =? c_colon)%nat = false)
             by (apply Nat.eqb_neq; unfold c_colon; lia).
           assert (hnpct : (Z.to_nat c =? c_pct)%nat = false)
             by (apply Nat.eqb_neq; unfold c_pct; lia).
           destruct (nibble (Z.to_nat c)) as [hi|] eqn:En.
           ++ (* hex byte *)
              destruct (p2_byte inp cap c hi rest' labF labNow m emitted s En inv)
                as (k & [ (rest2 & emitted2 & hlt & hk & inv2) | (hk & hres) ]).
              ** exists k. left. exists rest2. exists labNow. exists emitted2. tauto.
              ** exists k. right. tauto.
           ++ (* invalid char: contradicts the residual scan *)
              exfalso.
              assert (hscan' : scan1 High1 labNow (length emitted)
                                 (zin (c :: rest'))
                               = (labNow, length emitted, Unknown1)).
              { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
                apply scan1_high_unk; assumption. }
              rewrite hscan' in hscanok. inversion hscanok.
Qed.

(* Pass 2 runs to completion within 50*|rest|+4 steps, always a Result1.
   Strong induction on the suffix bound, mirroring pass1_correct. *)
Theorem pass2_correct : forall n inp cap rest labF labNow m emitted s,
  (length rest <= n)%nat ->
  P2Inv inp cap s labF labNow m emitted rest ->
  exists k, (k <= 50 * length rest + 4)%nat /\
    Result1 (runUntil 0 k s) inp cap.
Proof.
  intros n. induction n as [|n IH];
    intros inp cap rest labF labNow m emitted s hn inv.
  - assert (hr : rest = []) by (destruct rest; [reflexivity| simpl in hn; lia]).
    subst rest.
    exists (1 + 3)%nat. split; [simpl; lia|].
    exact (p2_eof inp cap labF labNow m emitted s inv).
  - destruct rest as [|c rest'].
    + exists (1 + 3)%nat. split; [simpl; lia|].
      exact (p2_eof inp cap labF labNow m emitted s inv).
    + destruct (p2_iteration inp cap (c :: rest') labF labNow m emitted s
                  ltac:(discriminate) inv)
        as (k1 & [ (rest2 & labNow2 & emitted2 & hlt & hk1 & inv2) | (hk1 & hres) ]).
      * destruct (IH inp cap rest2 labF labNow2 m emitted2 (runUntil 0 k1 s)
                    ltac:(simpl length in *; lia) inv2)
          as (k2 & hk2 & hres2).
        exists (k1 + k2)%nat. split; [simpl length in *; lia|].
        rewrite runUntil_add. exact hres2.
      * exists k1. split; [simpl length in *; lia| exact hres].
Qed.

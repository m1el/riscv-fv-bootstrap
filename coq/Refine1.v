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
From Hex0Coq Require Import Spec1 Rv64i Harness Harness1 Refine.
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

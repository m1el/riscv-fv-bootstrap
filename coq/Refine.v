(** * General refinement (T1) in Coq -- mirror of lean/Hex0/Refine.lean.

    Proof-grade theorem: for ALL inputs, the real `core` computes `coreSpec`.
    No vm_compute on the general statement -- it is genuine induction.

    STATUS: `core_refines` is PROVED modulo the single per-token dispatch lemma
    `loop_iteration` (the only `Admitted`).  Everything that assembles it is
    kernel-checked, mirroring `lean/Hex0/Refine.lean` §5:
      - `fetch_code` + all 12 `step_*` lemmas + state/storeByte projections
        (`decode (wordAt off)` reduces under `vm_compute` at concrete offsets, so
        the step lemmas apply exactly as in Lean);
      - arithmetic toolkit: `wrap_small`, `wadd_id`, `toS_small`, `sltb_small`;
      - `runUntil` composition: `runUntil_halt`, `runUntil_one`, `runUntil_S`,
        `runUntil_add`, `runUntil_stab` (large-fuel halt absorption);
      - spec-side token decomposition: `decodeS_spacing`/`byte`/`comment`;
      - `core_eof` -- the EOF base case (4-step run to a correct halt);
      - `LoopInv` (the 18-field invariant) + `eof_result`;
      - `loop_correct` -- the induction (fuel bound `50*|rest| + 4`);
      - `init_loopinv` -- the prologue (2-step run to the loop head);
      - `core_refines` -- prologue + induction + `runOn<->coreSpec` conversion.
    Remaining frontier (`Admitted`, line ~425): `loop_iteration` -- the per-token
    dispatch (spacing/byte/comment + the four halting error classes), the large
    mechanical tail (~2500 Lean lines).  `Print Assumptions core_refines` =>
    `loop_iteration` + `functional_extensionality_dep` (a standard, consistent
    axiom, used for `mem : Z -> Z` state equality -- cf. Lean's propext/choice).
    Two Coq-specific notes vs Lean (see PROOF.md §8): (1) `runOn` uses a *fixed*
    fuel (100000), so the assembly bounds the step count (Lean used ∃fuel) and
    absorbs the slack via `runUntil_stab` -- note `lia` cannot reason about the
    nat literal `100000` (it is `Nat.of_num_uint`), so the bound `F <= 100000`
    is proved through `Z` (`Nat2Z.inj_le` + `vm_compute (Z.of_nat 100000)`);
    (2) the model's bytes are `Z` but the spec is on `nat`, so `LoopInv`/dispatch
    carry `Z.of_nat`/`Z.to_nat` (`zin`) conversions. *)

From Coq Require Import ZArith List Lia Bool.
From Equations Require Import Equations.
From Hex0Coq Require Import Spec Rv64i Image Harness.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Per-step reduction primitive (PROVED).
    `core`'s first instruction `li t0,0` = `addi x5,x0,0`, bytes 93 02 00 00,
    word 0x293 = 659. One [step] computes its effect; data stays symbolic. *)
Theorem step_li_t0 : forall s,
  s.(mem) s.(pc) = 147 ->
  s.(mem) (s.(pc) + 1) = 2 ->
  s.(mem) (s.(pc) + 2) = 0 ->
  s.(mem) (s.(pc) + 3) = 0 ->
  s.(pc) = 2147483784 ->
  (step s).(pc) = 2147483788 /\ rget (step s) 5 = 0.
Proof.
  intros s h0 h1 h2 h3 hpc.
  unfold step, fetch32.
  rewrite h0, h1, h2, h3.
  (* fetched word is now the closed value 659; decode + effect compute *)
  change (147 + 2 * 256 + 0 * 65536 + 0 * 16777216) with 659.
  rewrite hpc. cbn. split; reflexivity.
Qed.

(** ** Engine: fetch at a code offset + per-instruction step lemmas.
    Mirror of `Refine.lean`'s `fetch_code` + `step_*`. Words are [Z]; the
    decode of a closed word reduces under [cbn]/[vm_compute] at call sites. *)

Definition nthb (i : Z) : Z := nth (Z.to_nat i) coreBytes 0.

Definition wordAt (off : Z) : Z :=
  nthb off + nthb (off + 1) * 256 + nthb (off + 2) * 65536 + nthb (off + 3) * 16777216.

Definition CodeLoaded (s : State) : Prop :=
  forall i, 0 <= i < Z.of_nat (length coreBytes) -> s.(mem) (coreAddr + i) = nthb i.

(* state projections *)
Lemma setPc_pc s p : (setPc s p).(pc) = p. Proof. reflexivity. Qed.
Lemma setPc_mem s p : (setPc s p).(mem) = s.(mem). Proof. reflexivity. Qed.
Lemma setPc_rget s p i : rget (setPc s p) i = rget s i. Proof. reflexivity. Qed.
Lemma rset_pc s rd v : (rset s rd v).(pc) = s.(pc).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rset_mem s rd v : (rset s rd v).(mem) = s.(mem).
Proof. unfold rset; destruct (rd =? 0); reflexivity. Qed.
Lemma rget_zero s : rget s 0 = 0. Proof. reflexivity. Qed.

Lemma rset_rget s rd v i : rd <> 0 -> i <> 0 ->
  rget (rset s rd v) i = if i =? rd then v else rget s i.
Proof.
  intros hrd hi. unfold rget, rset.
  destruct (rd =? 0) eqn:Erd; [apply Z.eqb_eq in Erd; lia|].
  destruct (i =? 0) eqn:Ei; [apply Z.eqb_eq in Ei; lia|].
  reflexivity.
Qed.

Lemma fetch_code : forall s off,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> fetch32 s = wordAt off.
Proof.
  intros s off hc ho1 ho2 hpc.
  unfold fetch32, wordAt. rewrite hpc.
  replace (coreAddr + off + 1) with (coreAddr + (off + 1)) by lia.
  replace (coreAddr + off + 2) with (coreAddr + (off + 2)) by lia.
  replace (coreAddr + off + 3) with (coreAddr + (off + 3)) by lia.
  rewrite (hc off ltac:(lia)), (hc (off+1) ltac:(lia)),
          (hc (off+2) ltac:(lia)), (hc (off+3) ltac:(lia)).
  reflexivity.
Qed.

Lemma step_addi : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iaddi rd rs1 imm ->
  step s = setPc (rset s rd (wadd (rget s rs1) imm)) (wadd s.(pc) 4).
Proof.
  intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_bgeu : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibgeu rs1 rs2 imm ->
  step s = setPc s (if ultb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof.
  intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity.
Qed.

Lemma step_add : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iadd rd rs1 rs2 ->
  step s = setPc (rset s rd (wadd (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_or : forall s off rd rs1 rs2,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ior rd rs1 rs2 ->
  step s = setPc (rset s rd (wor (rget s rs1) (rget s rs2))) (wadd s.(pc) 4).
Proof. intros s off rd rs1 rs2 hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_slli : forall s off rd rs1 sh,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Islli rd rs1 sh ->
  step s = setPc (rset s rd (wshl (rget s rs1) sh)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 sh hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_lbu : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ilbu rd rs1 imm ->
  step s = setPc (rset s rd ((s.(mem) (wadd (rget s rs1) imm)) mod 256)) (wadd s.(pc) 4).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_sb : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Isb rs1 rs2 imm ->
  step s = setPc (storeByte s (wadd (rget s rs1) imm) (rget s rs2)) (wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_beq : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibeq rs1 rs2 imm ->
  step s = setPc s (if (rget s rs1) =? (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_blt : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Iblt rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) imm else wadd s.(pc) 4).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_bge : forall s off rs1 rs2 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ibge rs1 rs2 imm ->
  step s = setPc s (if sltb (rget s rs1) (rget s rs2) then wadd s.(pc) 4 else wadd s.(pc) imm).
Proof. intros s off rs1 rs2 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jal : forall s off rd imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijal rd imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4)) (wadd s.(pc) imm).
Proof. intros s off rd imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

Lemma step_jalr : forall s off rd rs1 imm,
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> decode (wordAt off) = Ijalr rd rs1 imm ->
  step s = setPc (rset s rd (wadd s.(pc) 4))
                 (wadd (rget s rs1) imm - (wadd (rget s rs1) imm) mod 2).
Proof. intros s off rd rs1 imm hc ho1 ho2 hpc hd.
  unfold step. rewrite (fetch_code s off hc ho1 ho2 hpc), hd. reflexivity. Qed.

(* storeByte touches only memory *)
Lemma storeByte_pc s a b : (storeByte s a b).(pc) = s.(pc). Proof. reflexivity. Qed.
Lemma storeByte_reg s a b : (storeByte s a b).(reg) = s.(reg). Proof. reflexivity. Qed.
Lemma storeByte_rget s a b i : rget (storeByte s a b) i = rget s i. Proof. reflexivity. Qed.
Lemma storeByte_mem s a b : (storeByte s a b).(mem) = (fun x => if x =? a then b mod 256 else s.(mem) x).
Proof. reflexivity. Qed.

(** ** Arithmetic toolkit (mirror of ult_ofNat/slt_ofNat/ofNat_ne/setWidth8). *)

Lemma wrap_small z : 0 <= z < 2 ^ 64 -> wrap z = z.
Proof. unfold wrap, w64. apply Z.mod_small. Qed.

(* address arithmetic with no 64-bit wraparound *)
Lemma wadd_id a b : 0 <= a + b < 2 ^ 64 -> wadd a b = a + b.
Proof. unfold wadd. apply wrap_small. Qed.

Lemma toS_small x : 0 <= x < 2 ^ 63 -> toS x = x.
Proof. unfold toS. intros h. destruct (x >=? 2 ^ 63) eqn:E; [lia | reflexivity]. Qed.

(* signed compare = unsigned compare on small (< 2^63) values *)
Lemma sltb_small a b : 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> sltb a b = (a <? b).
Proof. intros ha hb. unfold sltb. rewrite (toS_small a ha), (toS_small b hb). reflexivity. Qed.

(** ** runUntil (= Lean runFuel) composition. *)

Lemma runUntil_halt n s : s.(pc) = 0 -> runUntil 0 n s = s.
Proof. intros h. destruct n; [reflexivity|]. simpl. rewrite h, Z.eqb_refl. reflexivity. Qed.

Lemma runUntil_one s : s.(pc) <> 0 -> runUntil 0 1 s = step s.
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_S n s : s.(pc) <> 0 -> runUntil 0 (S n) s = runUntil 0 n (step s).
Proof.
  intros h. simpl. destruct (s.(pc) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity].
Qed.

Lemma runUntil_add a b s : runUntil 0 (a + b) s = runUntil 0 b (runUntil 0 a s).
Proof.
  revert b s. induction a as [|k ih]; intros b s; simpl; [reflexivity|].
  destruct (s.(pc) =? 0) eqn:E.
  - apply Z.eqb_eq in E. now rewrite (runUntil_halt b s E).
  - apply ih.
Qed.

(* Once the machine has halted by fuel [f], any larger fuel [g] gives the same
   state.  Used to absorb the fixed 100000-fuel run in [runOn] into the
   step-count bound the loop actually needs (avoids nat-subtraction lia, which
   chokes on the [Nat.of_num_uint 100000] literal). *)
Lemma runUntil_stab f s : (runUntil 0 f s).(pc) = 0 ->
  forall g, (f <= g)%nat -> runUntil 0 g s = runUntil 0 f s.
Proof.
  intros Hhalt g Hle. induction Hle as [|g Hle IH].
  - reflexivity.
  - rewrite <- Nat.add_1_r, (runUntil_add g 1 s), IH.
    exact (runUntil_halt 1 (runUntil 0 f s) Hhalt).
Qed.

(** ** Spec-side token decomposition (mirror of decodeS_spacing/byte/comment). *)

Lemma decodeS_spacing c rest : isComment c = false -> isSpace c = true ->
  decodeS High (c :: rest) = decodeS High rest.
Proof. intros hc hs. simp decodeS. rewrite hc, hs. reflexivity. Qed.

Lemma decodeS_byte chi clo rest hi lo :
  isComment chi = false -> isSpace chi = false -> nibble chi = Some hi ->
  isLowStop clo = false -> nibble clo = Some lo ->
  decodeS High (chi :: clo :: rest) =
    ((hi * 16 + lo)%nat :: fst (decodeS High rest), snd (decodeS High rest)).
Proof.
  intros hc hs hh hlc hl. simp decodeS. rewrite hc, hs, hh. simp decodeS. rewrite hlc, hl.
  destruct (decodeS High rest) as [out st]. reflexivity.
Qed.

Lemma decodeS_comment c rest : isComment c = true ->
  decodeS High (c :: rest) = decodeS High (skipComment rest).
Proof. intros hc. simp decodeS. rewrite hc. reflexivity. Qed.

(** ** EOF base case (mirror of core_eof). *)

Lemma coreBytes_len : Z.of_nat (length coreBytes) = 324. Proof. reflexivity. Qed.
Lemma coreAddr_pos k : 0 <= k -> coreAddr + k <> 0. Proof. unfold coreAddr; lia. Qed.
Lemma CodeLoaded_eqmem s t : t.(mem) = s.(mem) -> CodeLoaded s -> CodeLoaded t.
Proof. intros hm hcs i Hi. rewrite hm. apply hcs; exact Hi. Qed.

Lemma core_eof : forall s L E,
  CodeLoaded s -> s.(pc) = coreAddr + 8 ->
  rget s 5 = L -> rget s 11 = L -> rget s 6 = E -> rget s 1 = 0 -> 0 <= E < 2 ^ 64 ->
  (runUntil 0 4 s).(pc) = 0 /\ rget (runUntil 0 4 s) 10 = 0 /\
  rget (runUntil 0 4 s) 11 = E /\ (runUntil 0 4 s).(mem) = s.(mem).
Proof.
  intros s L E hc hpc h5 h11 h6 h1 hE.
  (* step 1: bgeu t0,a1 taken (t0 = a1) -> .Lok (264) *)
  assert (hs1 : step s = setPc s (coreAddr + 264)).
  { rewrite (step_bgeu s 8 5 11 256 hc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
              ltac:(vm_compute; reflexivity)).
    rewrite h5, h11. unfold ultb. rewrite Z.ltb_irrefl. cbn match.
    rewrite hpc, (wadd_id (coreAddr+8) 256 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 264)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 264) by (unfold s1; apply setPc_pc).
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem s); [reflexivity| exact hc]).
  (* step 2: li a0,0 -> 268 *)
  assert (hs2 : step s1 = setPc (rset s1 10 0) (coreAddr + 268)).
  { rewrite (step_addi s1 264 10 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+264) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 10 0) (coreAddr + 268)) in *.
  assert (hpc2 : s2.(pc) = coreAddr + 268) by (unfold s2; apply setPc_pc).
  assert (hc2 : CodeLoaded s2) by
    (apply (CodeLoaded_eqmem s); [unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity| exact hc]).
  assert (h6_2 : rget s2 6 = E).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 6 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h6. }
  (* step 3: mv a1,t1 -> 272 *)
  assert (hs3 : step s2 = setPc (rset s2 11 E) (coreAddr + 272)).
  { rewrite (step_addi s2 268 11 6 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
              ltac:(vm_compute; reflexivity)).
    rewrite h6_2, (wadd_id E 0 ltac:(lia)), Z.add_0_r, hpc2,
            (wadd_id (coreAddr+268) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 11 E) (coreAddr + 272)) in *.
  assert (hpc3 : s3.(pc) = coreAddr + 272) by (unfold s3; apply setPc_pc).
  assert (hc3 : CodeLoaded s3) by
    (apply (CodeLoaded_eqmem s); [unfold s3,s2,s1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hc]).
  assert (h1_3 : rget s3 1 = 0).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 1 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 1 ltac:(lia) ltac:(lia)).
    unfold s1. rewrite setPc_rget. exact h1. }
  (* step 4: ret -> pc = 0 *)
  assert (hs4 : step s3 = setPc s3 0).
  { rewrite (step_jalr s3 272 0 1 0 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
              ltac:(vm_compute; reflexivity)).
    assert (Hr : rset s3 0 (wadd s3.(pc) 4) = s3) by (unfold rset; reflexivity).
    rewrite Hr, h1_3, (wadd_id 0 0 ltac:(lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = setPc s3 0).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. refine (conj _ (conj _ (conj _ _))).
  - rewrite setPc_pc. reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 10 ltac:(lia) ltac:(lia)).
    unfold s2. rewrite setPc_rget, (rset_rget s1 10 0 10 ltac:(lia) ltac:(lia)). reflexivity.
  - rewrite setPc_rget. unfold s3. rewrite setPc_rget, (rset_rget s2 11 E 11 ltac:(lia) ltac:(lia)).
    reflexivity.
  - rewrite setPc_mem. unfold s3, s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(** ** Helpers for the EOF base case. *)

Lemma decodeS_nil : decodeS High [] = ([], Ok). Proof. now simp decodeS. Qed.

Lemma readMem_eq : forall l m base,
  (forall j, (j < length l)%nat -> m (base + Z.of_nat j) = Z.of_nat (nth j l 0%nat)) ->
  readMem m base (length l) = l.
Proof.
  induction l as [|a l' IH]; intros m base H; simpl; [reflexivity|].
  f_equal.
  - specialize (H 0%nat ltac:(simpl; lia)).
    replace (base + Z.of_nat 0) with base in H by lia. simpl in H. rewrite H. apply Nat2Z.id.
  - apply IH. intros j Hj. specialize (H (S j) ltac:(simpl; lia)). simpl in H.
    rewrite <- H. f_equal. lia.
Qed.

(** ** Loop invariant + the induction backbone (mirror of LoopInv/loop_correct).

    Per the fuel-bound approach: each iteration runs <= 50 instructions per input
    char consumed, so the whole loop halts within [50 * |rest| + 4] steps -- a
    closed (non-existential) bound, so it composes with the fixed-fuel `runOn`. *)

Record LoopInv (inp : list Z) (cap : Z) (s : State) (rest : list Z) (emitted : list nat) : Prop := {
  li_at_loop : s.(pc) = coreAddr + 8;
  li_code    : CodeLoaded s;
  li_a0      : rget s 10 = inputAddr;
  li_a1      : rget s 11 = Z.of_nat (length inp);
  li_a2      : rget s 12 = outAddr;
  li_a3      : rget s 13 = cap;
  li_ra      : rget s 1 = 0;
  li_in_mem  : forall j, 0 <= j < Z.of_nat (length inp) ->
                 s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0;
  li_in_lt   : inputAddr + Z.of_nat (length inp) < 2 ^ 64;
  li_bytes   : forall b, In b inp -> 0 <= b < 256;
  li_in_fits : inputAddr + Z.of_nat (length inp) <= outAddr;
  li_out_lt  : outAddr + cap < 2 ^ 64;
  li_idx     : rget s 5 = Z.of_nat (length inp) - Z.of_nat (length rest);
  li_suffix  : skipn (length inp - length rest) inp = rest;
  li_outidx  : rget s 6 = Z.of_nat (length emitted);
  li_emit_le : (length emitted <= Z.to_nat cap)%nat;
  li_out_mem : forall j, (j < length emitted)%nat ->
                 s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat);
  li_spec    : decodeS High (zin inp) =
                 (emitted ++ fst (decodeS High (zin rest)), snd (decodeS High (zin rest)))
}.

(* The halted observation matches coreSpec. *)
Definition Result (f : State) (inp : list Z) (cap : Z) : Prop :=
  let '(st, bs, ln) := coreSpec (zin inp) (Z.to_nat cap) in
  f.(pc) = 0 /\ rget f 10 = Z.of_nat st /\ rget f 11 = Z.of_nat ln /\
  readMem f.(mem) outAddr ln = bs.

Lemma Result_pc f inp cap : Result f inp cap -> f.(pc) = 0.
Proof. unfold Result. destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln]. tauto. Qed.

(* Base case: input exhausted -> halts Ok with output preserved. (Uses core_eof;
   the readMem/coreSpec packaging is the remaining detail -- Admitted for now.) *)
Theorem eof_result : forall inp cap emitted s,
  LoopInv inp cap s [] emitted -> Result (runUntil 0 4 s) inp cap.
Proof.
  intros inp cap emitted s HI.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  assert (h5 : rget s 5 = Z.of_nat (length inp)) by (rewrite Hidx; simpl length; lia).
  assert (hE : 0 <= Z.of_nat (length emitted) < 2 ^ 64) by (unfold outAddr in Houtlt; lia).
  destruct (core_eof s (Z.of_nat (length inp)) (Z.of_nat (length emitted))
              Hcode Hpc h5 Ha1 Houtidx Hra hE) as [Hp [H10 [H11 Hmem]]].
  (* coreSpec computes to (0, emitted, length emitted) *)
  assert (Hdec : Spec.decode (zin inp) = (emitted, Ok)).
  { unfold Spec.decode. rewrite Hspec. change (zin []) with (@nil nat).
    rewrite decodeS_nil. simpl. rewrite app_nil_r. reflexivity. }
  assert (Hcs : coreSpec (zin inp) (Z.to_nat cap) = (0%nat, emitted, length emitted)).
  { unfold coreSpec. rewrite Hdec.
    destruct (Z.to_nat cap <? length emitted)%nat eqn:Ecap.
    - apply Nat.ltb_lt in Ecap. lia.
    - reflexivity. }
  unfold Result. rewrite Hcs. repeat split.
  - exact Hp.
  - rewrite H10. reflexivity.
  - rewrite H11. reflexivity.
  - rewrite Hmem. apply readMem_eq. intros j Hj. exact (Houtmem j Hj).
Qed.

(** ** Reusable machine-stepping blocks (mirror of lean/Hex0/Refine.lean's
    "reusable blocks").  Ported bottom-up; each is consumed by the per-token
    [loop_*] cases that build [loop_iteration]. *)

(* [li t3,K; beq t2,t3,_] where t2 = c <> K: runs as 2 steps, the beq falling
   through (not taken) to off+8.  Clobbers only t3 (=x28) and pc.  Mirror of the
   Lean [li_beq_ne].  (t2 = x7, t3 = x28.) *)
Lemma li_beq_ne s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K ->
  decode (wordAt (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c <> K ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbeq hK hne.
  rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget; exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget; reflexivity).
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with false by (symmetry; apply Z.eqb_neq; exact hne).
    rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(* [li t3,K; beq t2,t3,_] where t2 = c = K: 2 steps, the beq TAKEN to [target]
   (= pc+imm).  Clobbers only t3/pc.  Mirror of Lean [li_beq_eq]. *)
Lemma li_beq_eq s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K ->
  decode (wordAt (off + 4)) = Ibeq 7 28 imm ->
  0 <= K < 2 ^ 64 ->
  c = K ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbeq hK heq htgt.
  rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero,
      (wadd_id 0 K ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by (unfold s1; rewrite setPc_rget; exact h7).
  assert (h28s1 : rget s1 28 = K) by (unfold s1; rewrite setPc_rget; reflexivity).
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_beq s1 (off + 4) 7 28 imm hc1 ltac:(lia)
              ltac:(rewrite coreBytes_len; lia) hpc1 hbeq), h7s1, h28s1.
    replace (c =? K) with true by (symmetry; apply Z.eqb_eq; exact heq).
    rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; unfold coreAddr; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2.
  unfold s1. reflexivity.
Qed.

(* Frame: a [(rset s 28 v).setPc P] state inherits every register != t3 from s. *)
Lemma li_block_frame s v P i : i <> 28 ->
  rget (setPc (rset s 28 v) P) i = rget s i.
Proof.
  intros hi. rewrite setPc_rget. destruct (i =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. subst i. reflexivity.
  - apply Z.eqb_neq in E0.
    rewrite (rset_rget s 28 v i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact hi).
    reflexivity.
Qed.

(* The shared input-read head (offsets 8..24): from the loop head with a
   non-empty suffix [c :: rest'], 4 steps read the head char [c] into [t2] and
   bump [t0].  Lands at offset 24 (the spacing beq-chain).  Mirror of Lean
   [loop_prefix]. *)
Lemma loop_prefix : forall inp cap c rest' emitted s,
  LoopInv inp cap s (c :: rest') emitted ->
  (runUntil 0 4 s).(pc) = coreAddr + 24 /\
  rget (runUntil 0 4 s) 7 = c /\
  rget (runUntil 0 4 s) 5 = rget s 5 + 1 /\
  (runUntil 0 4 s).(mem) = s.(mem) /\
  CodeLoaded (runUntil 0 4 s) /\
  (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 ->
     rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros inp cap c rest' emitted s HI.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  set (k := (length inp - length (c :: rest'))%nat) in *.
  set (jZ := Z.of_nat (length inp) - Z.of_nat (length (c :: rest'))) in *.
  assert (hlen1 : Z.of_nat (length (c :: rest')) = Z.of_nat (length rest') + 1)
    by (simpl length; lia).
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl.
    fold k in Hl. lia. }
  assert (htonat : Z.to_nat jZ = k).
  { unfold jZ, k. rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id. reflexivity. }
  assert (hjpos : 0 <= jZ) by (unfold jZ; lia).
  assert (hjlt : jZ < Z.of_nat (length inp)) by (unfold jZ; lia).
  assert (Hc : nth k inp 0 = c).
  { transitivity (nth 0 (skipn k inp) 0).
    - rewrite nth_skipn. f_equal. lia.
    - rewrite Hsuf. reflexivity. }
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn k inp). apply in_or_app. right.
    fold k in Hsuf. rewrite Hsuf. left; reflexivity. }
  assert (Hcr : 0 <= c < 256) by (apply Hbytes; exact Hin).
  (* step 1: bgeu t0,a1 NOT taken (idx < len) -> off 12 *)
  assert (hult : ultb (rget s 5) (rget s 11) = true).
  { rewrite Hidx, Ha1. unfold ultb. apply Z.ltb_lt. exact hjlt. }
  assert (hs1 : step s = setPc s (coreAddr + 12)).
  { rewrite (step_bgeu s 8 5 11 256 Hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) Hpc
              ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite Hpc, (wadd_id (coreAddr + 8) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 12)) in *.
  assert (hc1 : CodeLoaded s1)
    by (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact Hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + 12) by reflexivity.
  (* step 2: add t3,a0,t0  (t3 = inputAddr + idx) -> off 16 *)
  assert (haddr : wadd (rget s1 10) (rget s1 5) = inputAddr + jZ).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. unfold inputAddr in *; lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (inputAddr + jZ)) (coreAddr + 16)).
  { rewrite (step_add s1 12 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)), haddr, hpc1,
            (wadd_id (coreAddr + 12) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 28 (inputAddr + jZ)) (coreAddr + 16)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded s2) by (apply (CodeLoaded_eqmem s); [exact hmem2| exact Hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + 16) by reflexivity.
  (* step 3: lbu t2,0(t3)  (t2 = input byte c) -> off 20 *)
  assert (hr28_2 : rget s2 28 = inputAddr + jZ).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) 28 ltac:(lia) ltac:(lia)),
            Z.eqb_refl. reflexivity. }
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = c).
  { rewrite hr28_2, (wadd_id (inputAddr + jZ) 0 ltac:(unfold inputAddr in *; lia)), Z.add_0_r,
            hmem2, (Hinmem jZ ltac:(lia)), htonat, Hc. apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 c) (coreAddr + 20)).
  { rewrite (step_lbu s2 16 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
              ltac:(vm_compute; reflexivity)), hbyte, hpc2,
            (wadd_id (coreAddr + 16) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 7 c) (coreAddr + 20)) in *.
  assert (hmem3 : s3.(mem) = s.(mem))
    by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded s3) by (apply (CodeLoaded_eqmem s); [exact hmem3| exact Hcode]).
  assert (hpc3 : s3.(pc) = coreAddr + 20) by reflexivity.
  (* step 4: addi t0,t0,1  (bump index) -> off 24 *)
  assert (hr5_3 : rget s3 5 = jZ).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact Hidx. }
  assert (hs4 : step s3 = setPc (rset s3 5 (jZ + 1)) (coreAddr + 24)).
  { rewrite (step_addi s3 20 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
              ltac:(vm_compute; reflexivity)), hr5_3,
            (wadd_id jZ 1 ltac:(unfold inputAddr in *; lia)), hpc3,
            (wadd_id (coreAddr + 20) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s4 := setPc (rset s3 5 (jZ + 1)) (coreAddr + 24)) in *.
  assert (hmem4 : s4.(mem) = s.(mem))
    by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  (* assemble runUntil 0 4 s = s4 *)
  assert (hp0 : s.(pc) <> 0) by (rewrite Hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c 7 ltac:(lia) ltac:(lia)), Z.eqb_refl.
    reflexivity.
  - assert (H54 : rget s4 5 = jZ + 1) by
      (unfold s4; rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) 5 ltac:(lia) ltac:(lia)),
            Z.eqb_refl; reflexivity).
    lia.
  - exact hmem4.
  - apply (CodeLoaded_eqmem s); [exact hmem4| exact Hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 (jZ + 1) i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 c i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 (inputAddr + jZ) i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(* The three spacing characters, as Z (mirror of the [isSpace] disjunction). *)
Lemma isSpace_cases c : 0 <= c -> isSpace (Z.to_nat c) = true ->
  c = 10 \/ c = 32 \/ c = 95.
Proof.
  intros h0 hs. unfold isSpace, c_nl, c_sp, c_us in hs.
  rewrite !orb_true_iff, !Nat.eqb_eq in hs.
  assert (Hid : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  destruct hs as [[H|H]|H]; [left|right; left|right; right]; rewrite Hid, H; reflexivity.
Qed.

(* The head char of a non-empty suffix is an input byte. *)
Lemma loopinv_head inp cap c rest' emitted s :
  LoopInv inp cap s (c :: rest') emitted -> In c inp /\ 0 <= c < 256.
Proof.
  intros HI. destruct HI as [_ _ _ _ _ _ _ _ _ Hbytes _ _ _ Hsuf _ _ _ _].
  assert (Hin : In c inp).
  { rewrite <- (firstn_skipn (length inp - length (c :: rest')) inp).
    apply in_or_app. right. rewrite Hsuf. left; reflexivity. }
  split; [exact Hin| apply Hbytes; exact Hin].
Qed.

(* The spacing beq-chain (offsets 24..): from [s4] at off 24 with [t2 = c] a
   spacing char, some number of steps reach LOOP, touching only [t3].  Mirror of
   Lean [spacing_tail]. *)
Lemma spacing_tail s4 c :
  CodeLoaded s4 -> s4.(pc) = coreAddr + 24 -> rget s4 7 = c ->
  0 <= c -> isSpace (Z.to_nat c) = true ->
  exists k, (k <= 10)%nat /\ (runUntil 0 k s4).(pc) = coreAddr + 8 /\
            (runUntil 0 k s4).(mem) = s4.(mem) /\
            (forall i, i <> 28 -> rget (runUntil 0 k s4) i = rget s4 i).
Proof.
  intros hcode hpc ht2 h0 hss.
  destruct (isSpace_cases c h0 hss) as [hc|[hc|hc]].
  all: assert (hne35 : c <> 35) by lia.
  all: assert (hne59 : c <> 59) by lia.
  (* block at off 24 (K=35), not taken *)
  all: pose proof (li_beq_ne s4 24 35 c 208 hcode ltac:(lia)
         ltac:(rewrite coreBytes_len; lia) hpc ht2 ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne35) as hb1.
  all: set (s_b := setPc (rset s4 28 35) (coreAddr + (24 + 8))) in *.
  all: assert (hcb : CodeLoaded s_b) by
         (apply (CodeLoaded_eqmem s4); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcb : s_b.(pc) = coreAddr + 32) by (unfold s_b; reflexivity).
  all: assert (h7b : rget s_b 7 = c) by
         (unfold s_b; rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) 7 ltac:(lia)); exact ht2).
  (* block at off 32 (K=59), not taken *)
  all: pose proof (li_beq_ne s_b 32 59 c 200 hcb ltac:(lia)
         ltac:(rewrite coreBytes_len; lia) hpcb h7b ltac:(vm_compute; reflexivity)
         ltac:(vm_compute; reflexivity) ltac:(lia) hne59) as hb2.
  all: set (s_c := setPc (rset s_b 28 59) (coreAddr + (32 + 8))) in *.
  all: assert (hcc : CodeLoaded s_c) by
         (apply (CodeLoaded_eqmem s4); [unfold s_c; rewrite setPc_mem, rset_mem;
            unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  all: assert (hpcc : s_c.(pc) = coreAddr + 40) by (unfold s_c; reflexivity).
  all: assert (h7c : rget s_c 7 = c) by
         (unfold s_c; rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) 7 ltac:(lia)); exact h7b).
  - (* c = 10: taken at off 40 *)
    pose proof (li_beq_eq s_c 40 10 c (-36) (coreAddr + 8) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (40 + 4)) (-36) ltac:(unfold coreAddr; lia)); lia)) as hb3.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s4 = setPc (rset s_c 28 10) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, hb3; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_c 10 (coreAddr + 8) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
  - (* c = 32: not taken at 40, taken at 48 *)
    pose proof (li_beq_ne s_c 40 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (coreAddr + (40 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = coreAddr + 48) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
    pose proof (li_beq_eq s_d 48 32 c (-44) (coreAddr + 8) hcd ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (48 + 4)) (-44) ltac:(unfold coreAddr; lia)); lia)) as hb4.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s4 = setPc (rset s_d 28 32) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, hb4; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem.
      unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_d 32 (coreAddr + 8) i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
  - (* c = 95: not taken at 40 and 48, taken at 56 *)
    pose proof (li_beq_ne s_c 40 10 c (-36) hcc ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcc h7c ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb3.
    set (s_d := setPc (rset s_c 28 10) (coreAddr + (40 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s4); [unfold s_d; rewrite setPc_mem, rset_mem;
         unfold s_c; rewrite setPc_mem, rset_mem; unfold s_b; rewrite setPc_mem, rset_mem;
         reflexivity| exact hcode]).
    assert (hpcd : s_d.(pc) = coreAddr + 48) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
    pose proof (li_beq_ne s_d 48 32 c (-44) hcd ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpcd h7d ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as hb4.
    set (s_e := setPc (rset s_d 28 32) (coreAddr + (48 + 8))) in *.
    assert (hce : CodeLoaded s_e) by
      (apply (CodeLoaded_eqmem s4); [unfold s_e; rewrite setPc_mem, rset_mem;
         unfold s_d; rewrite setPc_mem, rset_mem; unfold s_c; rewrite setPc_mem, rset_mem;
         unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpce : s_e.(pc) = coreAddr + 56) by (unfold s_e; reflexivity).
    assert (h7e : rget s_e 7 = c) by
      (unfold s_e; rewrite (li_block_frame s_d 32 (coreAddr + (48 + 8)) 7 ltac:(lia)); exact h7d).
    pose proof (li_beq_eq s_e 56 95 c (-52) (coreAddr + 8) hce ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpce h7e ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) hc
      ltac:(rewrite (wadd_id (coreAddr + (56 + 4)) (-52) ltac:(unfold coreAddr; lia)); lia)) as hb5.
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 2)))) s4 = setPc (rset s_e 28 95) (coreAddr + 8))
      by (rewrite runUntil_add, hb1, runUntil_add, hb2, runUntil_add, hb3, runUntil_add, hb4, hb5;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 2))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_e. rewrite setPc_mem, rset_mem.
      unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c. rewrite setPc_mem, rset_mem.
      unfold s_b. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s_e 95 (coreAddr + 8) i hi).
      unfold s_e. rewrite (li_block_frame s_d 32 (coreAddr + (48 + 8)) i hi).
      unfold s_d. rewrite (li_block_frame s_c 10 (coreAddr + (40 + 8)) i hi).
      unfold s_c. rewrite (li_block_frame s_b 59 (coreAddr + (32 + 8)) i hi).
      unfold s_b. rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). reflexivity.
Qed.

(* Rebuild the loop invariant after a spacing token: same [emitted], suffix
   shortened by one, index bumped.  Mirror of Lean [spacing_loopinv]. *)
Lemma spacing_loopinv inp cap c rest' emitted s s' :
  LoopInv inp cap s (c :: rest') emitted ->
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = true ->
  s'.(pc) = coreAddr + 8 -> s'.(mem) = s.(mem) ->
  rget s' 5 = rget s 5 + 1 ->
  rget s' 1 = rget s 1 -> rget s' 6 = rget s 6 ->
  rget s' 10 = rget s 10 -> rget s' 11 = rget s 11 ->
  rget s' 12 = rget s 12 -> rget s' 13 = rget s 13 ->
  LoopInv inp cap s' rest' emitted.
Proof.
  intros HI hsc hss hpc' hmem' h5 hp1 hp6 hp10 hp11 hp12 hp13.
  destruct HI as [Hpc Hcode Ha0 Ha1 Ha2 Ha3 Hra Hinmem Hinlt Hbytes Hinfits Houtlt
                  Hidx Hsuf Houtidx Hemitle Houtmem Hspec].
  assert (hlen1 : Z.of_nat (length (c :: rest')) = Z.of_nat (length rest') + 1)
    by (simpl length; lia).
  assert (hge : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl. lia. }
  refine {| li_at_loop := hpc'; li_code := _; li_a0 := _; li_a1 := _; li_a2 := _;
            li_a3 := _; li_ra := _; li_in_mem := _; li_in_lt := Hinlt;
            li_bytes := Hbytes; li_in_fits := Hinfits; li_out_lt := Houtlt;
            li_idx := _; li_suffix := _; li_outidx := _; li_emit_le := Hemitle;
            li_out_mem := _; li_spec := _ |}.
  - apply (CodeLoaded_eqmem s); [exact hmem'| exact Hcode].
  - rewrite hp10; exact Ha0.
  - rewrite hp11; exact Ha1.
  - rewrite hp12; exact Ha2.
  - rewrite hp13; exact Ha3.
  - rewrite hp1; exact Hra.
  - intros j hj. rewrite hmem'. exact (Hinmem j hj).
  - rewrite h5, Hidx. lia.
  - assert (Hk1 : (length inp - length rest')%nat = S (length inp - length (c :: rest')))
      by (simpl length; lia).
    rewrite Hk1, <- Nat.add_1_l, <- (skipn_skipn 1 (length inp - length (c :: rest')) inp),
            Hsuf. reflexivity.
  - rewrite hp6; exact Houtidx.
  - intros j hj. rewrite hmem'. exact (Houtmem j hj).
  - rewrite Hspec. change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
    rewrite (decodeS_spacing (Z.to_nat c) (zin rest') hsc hss). reflexivity.
Qed.

(* A COMPLETE main-loop iteration for any spacing token: loop_prefix (read the
   char) + spacing_tail (dispatch to LOOP) + spacing_loopinv (rebuild).  Mirror
   of Lean [loop_spacing]. *)
Lemma loop_spacing inp cap c rest' emitted s :
  isSpace (Z.to_nat c) = true ->
  LoopInv inp cap s (c :: rest') emitted ->
  exists k, (k <= 50)%nat /\ LoopInv inp cap (runUntil 0 k s) rest' emitted.
Proof.
  intros hss inv.
  destruct (loopinv_head inp cap c rest' emitted s inv) as [Hin [Hc0 _]].
  assert (hsc : isComment (Z.to_nat c) = false)
    by (destruct (isSpace_cases c Hc0 hss) as [H|[H|H]]; subst c; reflexivity).
  destruct (loop_prefix inp cap c rest' emitted s inv)
    as [hpc4 [ht2 [ht0 [hmem4 [hcode4 hother4]]]]].
  destruct (spacing_tail (runUntil 0 4 s) c hcode4 hpc4 ht2 Hc0 hss)
    as [k [hk [htpc [htmem htother]]]].
  exists (4 + k)%nat. split; [lia|]. rewrite runUntil_add.
  apply (spacing_loopinv inp cap c rest' emitted s (runUntil 0 k (runUntil 0 4 s)) inv hsc hss).
  - exact htpc.
  - rewrite htmem; exact hmem4.
  - rewrite (htother 5 ltac:(lia)); exact ht0.
  - rewrite (htother 1 ltac:(lia)); exact (hother4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 6 ltac:(lia)); exact (hother4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 10 ltac:(lia)); exact (hother4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 11 ltac:(lia)); exact (hother4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 12 ltac:(lia)); exact (hother4 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite (htother 13 ltac:(lia)); exact (hother4 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(** ** Error infrastructure (mirror of error_result/halt_epilogue/bgeu_eq_taken/
    reach_error).  The halting epilogue + spec packaging shared by every error
    class (and the comment-EOF Ok exit). *)

(* From a halted state with the right a0/a1/output, package a [Result] for a
   non-truncating decode.  Mirror of Lean [error_result]. *)
Lemma error_result s inp cap emitted st :
  s.(pc) = 0 -> rget s 10 = Z.of_nat (statusCode st) ->
  rget s 11 = Z.of_nat (length emitted) ->
  (forall j, (j < length emitted)%nat ->
     s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat)) ->
  Spec.decode (zin inp) = (emitted, st) -> (length emitted <= Z.to_nat cap)%nat ->
  Result s inp cap.
Proof.
  intros hp ha0 ha1 hmem hdec hle.
  assert (hcs : coreSpec (zin inp) (Z.to_nat cap) = (statusCode st, emitted, length emitted)).
  { unfold coreSpec. rewrite hdec. destruct (Z.to_nat cap <? length emitted)%nat eqn:E.
    - apply Nat.ltb_lt in E. lia.
    - reflexivity. }
  unfold Result. rewrite hcs. repeat apply conj.
  - exact hp.
  - exact ha0.
  - exact ha1.
  - apply readMem_eq. exact hmem.
Qed.

(* The halting epilogue (li a0,code; mv a1,t1; ret): 3 steps to pc=0 with
   a0=code, a1=t1, memory preserved.  Mirror of Lean [halt_epilogue]. *)
Lemma halt_epilogue s off code n :
  CodeLoaded s -> 0 <= off -> off + 8 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  decode (wordAt off) = Iaddi 10 0 code ->
  decode (wordAt (off + 4)) = Iaddi 11 6 0 ->
  decode (wordAt (off + 8)) = Ijalr 0 1 0 ->
  0 <= code < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  rget s 6 = n -> rget s 1 = 0 ->
  (runUntil 0 3 s).(pc) = 0 /\ rget (runUntil 0 3 s) 10 = code /\
  rget (runUntil 0 3 s) 11 = n /\ (runUntil 0 3 s).(mem) = s.(mem).
Proof.
  intros hcode ho hoff hpc hli hmv hret hcodeR hnR h6 h1.
  rewrite coreBytes_len in hoff.
  assert (hs1 : step s = setPc (rset s 10 code) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 10 0 code hcode ho ltac:(rewrite coreBytes_len; lia) hpc hli), rget_zero,
      (wadd_id 0 code ltac:(lia)), Z.add_0_l, hpc,
      (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 10 code) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h6_1 : rget s1 6 = n).
  { unfold s1. rewrite setPc_rget, (rset_rget s 10 code 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 10) with false by reflexivity. exact h6. }
  assert (hs2 : step s1 = setPc (rset s1 11 n) (coreAddr + (off + 8))).
  { rewrite (step_addi s1 (off + 4) 11 6 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hmv), h6_1,
      (wadd_id n 0 ltac:(lia)), Z.add_0_r, hpc1,
      (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s2 := setPc (rset s1 11 n) (coreAddr + (off + 8))) in *.
  assert (hc2 : CodeLoaded s2) by
    (apply (CodeLoaded_eqmem s); [unfold s2, s1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + (off + 8)) by reflexivity.
  assert (h1_2 : rget s2 1 = 0).
  { unfold s2. rewrite setPc_rget, (rset_rget s1 11 n 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 11) with false by reflexivity. unfold s1.
    rewrite setPc_rget, (rset_rget s 10 code 1 ltac:(lia) ltac:(lia)).
    replace (1 =? 10) with false by reflexivity. exact h1. }
  assert (hs3 : step s2 = setPc s2 0).
  { rewrite (step_jalr s2 (off + 8) 0 1 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2 hret).
    assert (Hr : rset s2 0 (wadd s2.(pc) 4) = s2) by (unfold rset; reflexivity).
    rewrite Hr, h1_2, (wadd_id 0 0 ltac:(lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 3 s = setPc s2 0).
  { rewrite (runUntil_S 2 s hp0), hs1, (runUntil_S 1 s1 hp1), hs2,
            (runUntil_S 0 s2 hp2), hs3. reflexivity. }
  rewrite hrun. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 n 10 ltac:(lia) ltac:(lia)).
    replace (10 =? 11) with false by reflexivity. unfold s1.
    rewrite setPc_rget, (rset_rget s 10 code 10 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - rewrite setPc_rget. unfold s2.
    rewrite setPc_rget, (rset_rget s1 11 n 11 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - rewrite setPc_mem. unfold s2, s1. rewrite !setPc_mem, !rset_mem. reflexivity.
Qed.

(* A [bgeu rs1,rs2] with equal operands branches (1 step to the target).  Mirror
   of Lean [bgeu_eq_taken]. *)
Lemma bgeu_eq_taken s off rs1 rs2 A immB target :
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off ->
  rget s rs1 = A -> rget s rs2 = A ->
  decode (wordAt off) = Ibgeu rs1 rs2 immB ->
  wadd (coreAddr + off) immB = target ->
  runUntil 0 1 s = setPc s target.
Proof.
  intros hcode ho hoff hpc h1 h2 hbgeu htgt.
  assert (hult : ultb (rget s rs1) (rget s rs2) = false)
    by (rewrite h1, h2; unfold ultb; apply Z.ltb_irrefl).
  assert (hu1 : step s = setPc s target).
  { rewrite (step_bgeu s off rs1 rs2 immB hcode ho hoff hpc hbgeu), hult. cbn match.
    rewrite hpc, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  rewrite (runUntil_one s hp0), hu1. reflexivity.
Qed.

(* Run from the loop head to an error label, then halt; package a [Result].
   Mirror of Lean [reach_error]. *)
Lemma reach_error s sE inp cap emitted off code k st :
  runUntil 0 k s = sE ->
  sE.(pc) = coreAddr + off -> CodeLoaded sE -> sE.(mem) = s.(mem) ->
  rget sE 6 = Z.of_nat (length emitted) -> rget sE 1 = 0 ->
  decode (wordAt off) = Iaddi 10 0 code ->
  decode (wordAt (off + 4)) = Iaddi 11 6 0 ->
  decode (wordAt (off + 8)) = Ijalr 0 1 0 ->
  0 <= off -> off + 8 + 3 < Z.of_nat (length coreBytes) ->
  0 <= code < 2 ^ 64 -> Z.of_nat (length emitted) < 2 ^ 64 ->
  code = Z.of_nat (statusCode st) ->
  Spec.decode (zin inp) = (emitted, st) -> (length emitted <= Z.to_nat cap)%nat ->
  (forall j, (j < length emitted)%nat ->
     s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat)) ->
  exists m, (m <= k + 3)%nat /\ Result (runUntil 0 m s) inp cap.
Proof.
  intros hrun hpcE hcodeE hmemE h6E h1E hli hmv hret ho hoff hcodeR hemit_lt
         hcodeval hdec hle hout.
  destruct (halt_epilogue sE off code (Z.of_nat (length emitted)) hcodeE ho hoff hpcE
              hli hmv hret hcodeR ltac:(lia) h6E h1E) as [hp [ha0 [ha1 hm]]].
  exists (k + 3)%nat. split; [lia|]. rewrite runUntil_add, hrun.
  apply (error_result (runUntil 0 3 sE) inp cap emitted st).
  - exact hp.
  - rewrite ha0; exact hcodeval.
  - exact ha1.
  - intros j hj. rewrite hm, hmemE. exact (hout j hj).
  - exact hdec.
  - exact hle.
Qed.

(** ** Signed-branch [li;blt]/[li;bge] blocks for the nibble-parse chains
    (mirror of Lean li_blt_nt/li_bge_nt/li_bge_t/li_blt_t).  Operands are
    bytes (< 256 < 2^63) so signed/unsigned compare agree ([sltb_small]). *)

(* [li t3,K; blt t2,t3] with c >= K: blt NOT taken, 2 steps to off+8. *)
Lemma li_blt_nt s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> K <= c ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hblt hK hcc hge. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = false).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)).
    destruct (c <? K) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. }
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hblt),
      hslt. cbn match. rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; bge t2,t3] with c < K: bge NOT taken, 2 steps to off+8. *)
Lemma li_bge_nt s off K c imm :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> c < K ->
  runUntil 0 2 s = setPc (rset s 28 K) (coreAddr + (off + 8)).
Proof.
  intros hc ho hb hpc h7 hli hbge hK hcc hlt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = true).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)). apply Z.ltb_lt. lia. }
  assert (hu2 : step s1 = setPc s1 (coreAddr + (off + 8))).
  { rewrite (step_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hbge),
      hslt. cbn match. rewrite hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)).
    f_equal. lia. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; bge t2,t3] with c >= K: bge IS taken to [target]. *)
Lemma li_bge_t s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Ibge 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> K <= c ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hbge hK hcc hge htgt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = false).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)).
    destruct (c <? K) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. }
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_bge s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hbge),
      hslt. cbn match. rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(* [li t3,K; blt t2,t3] with c < K: blt IS taken to [target]. *)
Lemma li_blt_t s off K c imm target :
  CodeLoaded s -> 0 <= off -> off + 4 + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s 7 = c ->
  decode (wordAt off) = Iaddi 28 0 K -> decode (wordAt (off + 4)) = Iblt 7 28 imm ->
  0 <= K < 2 ^ 63 -> 0 <= c < 2 ^ 63 -> c < K ->
  wadd (coreAddr + (off + 4)) imm = target ->
  runUntil 0 2 s = setPc (rset s 28 K) target.
Proof.
  intros hc ho hb hpc h7 hli hblt hK hcc hlt htgt. rewrite coreBytes_len in hb.
  assert (ho1 : off + 3 < Z.of_nat (length coreBytes)) by (rewrite coreBytes_len; lia).
  assert (hu1 : step s = setPc (rset s 28 K) (coreAddr + (off + 4))).
  { rewrite (step_addi s off 28 0 K hc ho ho1 hpc hli), rget_zero, (wadd_id 0 K ltac:(lia)),
      Z.add_0_l, hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc (rset s 28 K) (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem, rset_mem; reflexivity| exact hc]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (h7s1 : rget s1 7 = c) by
    (unfold s1; rewrite (li_block_frame s K (coreAddr + (off + 4)) 7 ltac:(lia)); exact h7).
  assert (h28s1 : rget s1 28 = K) by
    (unfold s1; rewrite setPc_rget, (rset_rget s 28 K 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hslt : sltb (rget s1 7) (rget s1 28) = true).
  { rewrite h7s1, h28s1, (sltb_small c K ltac:(lia) ltac:(lia)). apply Z.ltb_lt. lia. }
  assert (hu2 : step s1 = setPc s1 target).
  { rewrite (step_blt s1 (off + 4) 7 28 imm hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hblt),
      hslt. cbn match. rewrite hpc1, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  rewrite (runUntil_S 1 s hp0), hu1, (runUntil_S 0 s1 hp1), hu2. unfold s1. reflexivity.
Qed.

(** ** The high/low beq fall-through chains (mirror of high_beq_ft/low_beq_ft).
    All five [li K; beq] blocks fall through (c is none of the stop chars). *)

(* High beq-chain (offsets 24..60): c not a space/comment char -> reach 64. *)
Lemma high_beq_ft s c :
  CodeLoaded s -> s.(pc) = coreAddr + 24 -> rget s 7 = c -> 0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 ->
  (runUntil 0 10 s).(pc) = coreAddr + 64 /\ (runUntil 0 10 s).(mem) = s.(mem) /\
  (forall i, i <> 28 -> rget (runUntil 0 10 s) i = rget s i).
Proof.
  intros hcode hpc h7 hc h35 h59 h10 h32 h95.
  pose proof (li_beq_ne s 24 35 c 208 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h35) as b1.
  set (sb := setPc (rset s 28 35) (coreAddr + (24 + 8))) in *.
  assert (hcb : CodeLoaded sb) by
    (apply (CodeLoaded_eqmem s); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcb : sb.(pc) = coreAddr + 32) by (unfold sb; reflexivity).
  assert (h7b : rget sb 7 = c) by
    (unfold sb; rewrite (li_block_frame s 35 (coreAddr + (24 + 8)) 7 ltac:(lia)); exact h7).
  pose proof (li_beq_ne sb 32 59 c 200 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h59) as b2.
  set (sc := setPc (rset sb 28 59) (coreAddr + (32 + 8))) in *.
  assert (hcc : CodeLoaded sc) by
    (apply (CodeLoaded_eqmem s); [unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcc : sc.(pc) = coreAddr + 40) by (unfold sc; reflexivity).
  assert (h7c : rget sc 7 = c) by
    (unfold sc; rewrite (li_block_frame sb 59 (coreAddr + (32 + 8)) 7 ltac:(lia)); exact h7b).
  pose proof (li_beq_ne sc 40 10 c (-36) hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h10) as b3.
  set (sd := setPc (rset sc 28 10) (coreAddr + (40 + 8))) in *.
  assert (hcd : CodeLoaded sd) by
    (apply (CodeLoaded_eqmem s); [unfold sd; rewrite setPc_mem, rset_mem; unfold sc;
       rewrite setPc_mem, rset_mem; unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcd : sd.(pc) = coreAddr + 48) by (unfold sd; reflexivity).
  assert (h7d : rget sd 7 = c) by
    (unfold sd; rewrite (li_block_frame sc 10 (coreAddr + (40 + 8)) 7 ltac:(lia)); exact h7c).
  pose proof (li_beq_ne sd 48 32 c (-44) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd h7d
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h32) as b4.
  set (se := setPc (rset sd 28 32) (coreAddr + (48 + 8))) in *.
  assert (hce : CodeLoaded se) by
    (apply (CodeLoaded_eqmem s); [unfold se; rewrite setPc_mem, rset_mem; unfold sd;
       rewrite setPc_mem, rset_mem; unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpce : se.(pc) = coreAddr + 56) by (unfold se; reflexivity).
  assert (h7e : rget se 7 = c) by
    (unfold se; rewrite (li_block_frame sd 32 (coreAddr + (48 + 8)) 7 ltac:(lia)); exact h7d).
  pose proof (li_beq_ne se 56 95 c (-52) hce ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpce h7e
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h95) as b5.
  assert (hfin : runUntil 0 10 s = setPc (rset se 28 95) (coreAddr + (56 + 8)))
    by (rewrite (runUntil_add 2 8), b1, (runUntil_add 2 6), b2, (runUntil_add 2 4), b3,
        (runUntil_add 2 2), b4, b5; reflexivity).
  rewrite hfin. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold se. rewrite setPc_mem, rset_mem. unfold sd.
    rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
    rewrite setPc_mem, rset_mem. reflexivity.
  - intros i hi. rewrite (li_block_frame se 95 (coreAddr + (56 + 8)) i hi).
    unfold se. rewrite (li_block_frame sd 32 (coreAddr + (48 + 8)) i hi).
    unfold sd. rewrite (li_block_frame sc 10 (coreAddr + (40 + 8)) i hi).
    unfold sc. rewrite (li_block_frame sb 59 (coreAddr + (32 + 8)) i hi).
    unfold sb. rewrite (li_block_frame s 35 (coreAddr + (24 + 8)) i hi). reflexivity.
Qed.

(* Low-stop beq-chain (offsets 124..160): l not a stop char -> reach 164. *)
Lemma low_beq_ft s c :
  CodeLoaded s -> s.(pc) = coreAddr + 124 -> rget s 7 = c -> 0 <= c < 256 ->
  c <> 35 -> c <> 59 -> c <> 10 -> c <> 32 -> c <> 95 ->
  (runUntil 0 10 s).(pc) = coreAddr + 164 /\ (runUntil 0 10 s).(mem) = s.(mem) /\
  (forall i, i <> 28 -> rget (runUntil 0 10 s) i = rget s i).
Proof.
  intros hcode hpc h7 hc h35 h59 h10 h32 h95.
  pose proof (li_beq_ne s 124 10 c 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h10) as b1.
  set (sb := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
  assert (hcb : CodeLoaded sb) by
    (apply (CodeLoaded_eqmem s); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcb : sb.(pc) = coreAddr + 132) by (unfold sb; reflexivity).
  assert (h7b : rget sb 7 = c) by
    (unfold sb; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
  pose proof (li_beq_ne sb 132 32 c 152 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h32) as b2.
  set (sc := setPc (rset sb 28 32) (coreAddr + (132 + 8))) in *.
  assert (hcc : CodeLoaded sc) by
    (apply (CodeLoaded_eqmem s); [unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcc : sc.(pc) = coreAddr + 140) by (unfold sc; reflexivity).
  assert (h7c : rget sc 7 = c) by
    (unfold sc; rewrite (li_block_frame sb 32 (coreAddr + (132 + 8)) 7 ltac:(lia)); exact h7b).
  pose proof (li_beq_ne sc 140 95 c 144 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h95) as b3.
  set (sd := setPc (rset sc 28 95) (coreAddr + (140 + 8))) in *.
  assert (hcd : CodeLoaded sd) by
    (apply (CodeLoaded_eqmem s); [unfold sd; rewrite setPc_mem, rset_mem; unfold sc;
       rewrite setPc_mem, rset_mem; unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpcd : sd.(pc) = coreAddr + 148) by (unfold sd; reflexivity).
  assert (h7d : rget sd 7 = c) by
    (unfold sd; rewrite (li_block_frame sc 95 (coreAddr + (140 + 8)) 7 ltac:(lia)); exact h7c).
  pose proof (li_beq_ne sd 148 35 c 136 hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd h7d
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h35) as b4.
  set (se := setPc (rset sd 28 35) (coreAddr + (148 + 8))) in *.
  assert (hce : CodeLoaded se) by
    (apply (CodeLoaded_eqmem s); [unfold se; rewrite setPc_mem, rset_mem; unfold sd;
       rewrite setPc_mem, rset_mem; unfold sc; rewrite setPc_mem, rset_mem; unfold sb;
       rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpce : se.(pc) = coreAddr + 156) by (unfold se; reflexivity).
  assert (h7e : rget se 7 = c) by
    (unfold se; rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) 7 ltac:(lia)); exact h7d).
  pose proof (li_beq_ne se 156 59 c 128 hce ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpce h7e
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) h59) as b5.
  assert (hfin : runUntil 0 10 s = setPc (rset se 28 59) (coreAddr + (156 + 8)))
    by (rewrite (runUntil_add 2 8), b1, (runUntil_add 2 6), b2, (runUntil_add 2 4), b3,
        (runUntil_add 2 2), b4, b5; reflexivity).
  rewrite hfin. repeat apply conj.
  - apply setPc_pc.
  - rewrite setPc_mem, rset_mem. unfold se. rewrite setPc_mem, rset_mem. unfold sd.
    rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
    rewrite setPc_mem, rset_mem. reflexivity.
  - intros i hi. rewrite (li_block_frame se 59 (coreAddr + (156 + 8)) i hi).
    unfold se. rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) i hi).
    unfold sd. rewrite (li_block_frame sc 95 (coreAddr + (140 + 8)) i hi).
    unfold sc. rewrite (li_block_frame sb 32 (coreAddr + (132 + 8)) i hi).
    unfold sb. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
Qed.

(** ** Nibble helpers + the high/low nibble-parse chains. *)

(* nibble (as Z byte): digit '0'..'9' -> c-48, letter 'A'..'F' -> c-55. *)
Lemma nibble_cases c hi : 0 <= c -> nibble (Z.to_nat c) = Some hi ->
  (48 <= c <= 57 /\ c - 48 = Z.of_nat hi) \/ (65 <= c <= 70 /\ c - 55 = Z.of_nat hi).
Proof.
  intros h0 hn.
  assert (Hc : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  unfold nibble in hn. set (n := Z.to_nat c) in *.
  destruct ((48 <=? n) && (n <=? 57))%nat eqn:Ed.
  - apply andb_true_iff in Ed. destruct Ed as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. cbv iota in hn. injection hn as hn.
    left. split; [rewrite Hc; lia|]. rewrite Hc, <- hn, Nat2Z.inj_sub by lia. reflexivity.
  - destruct ((65 <=? n) && (n <=? 70))%nat eqn:El.
    + apply andb_true_iff in El. destruct El as [E1 E2].
      apply Nat.leb_le in E1. apply Nat.leb_le in E2. cbv iota in hn. injection hn as hn.
      right. split; [rewrite Hc; lia|]. rewrite Hc, <- hn, Nat2Z.inj_sub by lia. reflexivity.
    + cbv iota in hn. discriminate hn.
Qed.

Lemma nibble_lt c hi : nibble c = Some hi -> (hi < 16)%nat.
Proof.
  unfold nibble. destruct ((48 <=? c) && (c <=? 57))%nat eqn:Ed.
  - apply andb_true_iff in Ed. destruct Ed as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros H; injection H as H; lia.
  - destruct ((65 <=? c) && (c <=? 70))%nat eqn:El.
    + apply andb_true_iff in El. destruct El as [E1 E2].
      apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros H; injection H as H; lia.
    + discriminate.
Qed.

(* High-nibble parse (offsets 64..104): nibble c = Some hi -> reach have_high
   (108) with t4 (x29) = hi.  Mirror of Lean [high_parse]. *)
Lemma high_parse s c hi :
  CodeLoaded s -> s.(pc) = coreAddr + 64 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = Some hi ->
  exists k, (k <= 9)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 108 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    rget (runUntil 0 k s) 29 = Z.of_nat hi /\
    (forall i, i <> 28 -> i <> 29 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_cases c hi ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit *)
    pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 72) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_nt s_a 72 58 c 12 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + (72 + 8))) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 80) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + (72 + 8)) 7 ltac:(lia)); exact h7a).
    assert (haddi : step s_b = setPc (rset s_b 29 (c + -48)) (coreAddr + 84)).
    { rewrite (step_addi s_b 80 29 7 (-48) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb
        ltac:(vm_compute; reflexivity)), h7b, (wadd_id c (-48) ltac:(lia)), hpcb,
        (wadd_id (coreAddr + 80) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    set (s_c := setPc (rset s_b 29 (c + -48)) (coreAddr + 84)) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 84) by (unfold s_c; reflexivity).
    assert (hjal : step s_c = setPc s_c (coreAddr + 108)).
    { rewrite (step_jal s_c 84 0 24 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc
        ltac:(vm_compute; reflexivity)).
      assert (Hr0 : rset s_c 0 (wadd s_c.(pc) 4) = s_c) by (unfold rset; reflexivity).
      rewrite Hr0, hpcc, (wadd_id (coreAddr + 84) 24 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hbc : runUntil 0 2 s_b = setPc s_c (coreAddr + 108)).
    { assert (hpb0 : s_b.(pc) <> 0) by (rewrite hpcb; apply coreAddr_pos; lia).
      assert (hpc0 : s_c.(pc) <> 0) by (rewrite hpcc; apply coreAddr_pos; lia).
      rewrite (runUntil_S 1 s_b hpb0), haddi, (runUntil_S 0 s_c hpc0), hjal. reflexivity. }
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc s_c (coreAddr + 108))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, hbc; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem. unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b.
      rewrite setPc_mem, rset_mem. unfold s_a. rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget. unfold s_c.
      rewrite setPc_rget, (rset_rget s_b 29 (c + -48) 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi29. rewrite setPc_rget. unfold s_c. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_b 29 (c + -48) i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi29).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + (72 + 8)) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi28). reflexivity.
  - (* letter *)
    pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 72) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t s_a 72 58 c 12 (coreAddr + 88) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (72 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + 88)) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 88) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + 88) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt s_b 88 65 c 220 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (s_c := setPc (rset s_b 28 65) (coreAddr + (88 + 8))) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 96) by (unfold s_c; reflexivity).
    assert (h7c : rget s_c 7 = c) by
      (unfold s_c; rewrite (li_block_frame s_b 65 (coreAddr + (88 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_nt s_c 96 71 c 212 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bD.
    set (s_d := setPc (rset s_c 28 71) (coreAddr + (96 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s_c); [unfold s_d; rewrite setPc_mem, rset_mem; reflexivity| exact hcc]).
    assert (hpcd : s_d.(pc) = coreAddr + 104) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 71 (coreAddr + (96 + 8)) 7 ltac:(lia)); exact h7c).
    assert (haddi : step s_d = setPc (rset s_d 29 (c + -55)) (coreAddr + 108)).
    { rewrite (step_addi s_d 104 29 7 (-55) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd
        ltac:(vm_compute; reflexivity)), h7d, (wadd_id c (-55) ltac:(lia)), hpcd,
        (wadd_id (coreAddr + 104) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hpd0 : s_d.(pc) <> 0) by (rewrite hpcd; apply coreAddr_pos; lia).
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 1)))) s = setPc (rset s_d 29 (c + -55)) (coreAddr + 108))
      by (rewrite (runUntil_add 2 (2 + (2 + (2 + 1)))), bA, (runUntil_add 2 (2 + (2 + 1))), bB,
          (runUntil_add 2 (2 + 1)), bC, (runUntil_add 2 1), bD, (runUntil_one s_d hpd0), haddi;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 1))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c.
      rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. unfold s_a.
      rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget, (rset_rget s_d 29 (c + -55) 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi29. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_d 29 (c + -55) i ltac:(lia) E0).
      replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact hi29).
      unfold s_d. rewrite (li_block_frame s_c 71 (coreAddr + (96 + 8)) i hi28).
      unfold s_c. rewrite (li_block_frame s_b 65 (coreAddr + (88 + 8)) i hi28).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + 88) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi28). reflexivity.
Qed.

(* Low-nibble parse (offsets 164..204): nibble c = Some lo -> reach have_low
   (208) with t5 (x30) = lo.  Mirror of [high_parse] (reg 30, offsets +100). *)
Lemma low_parse s c lo :
  CodeLoaded s -> s.(pc) = coreAddr + 164 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = Some lo ->
  exists k, (k <= 9)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 208 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    rget (runUntil 0 k s) 30 = Z.of_nat lo /\
    (forall i, i <> 28 -> i <> 30 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_cases c lo ltac:(lia) hn) as [[Hr Hv]|[Hr Hv]].
  - (* digit *)
    pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 172) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_nt s_a 172 58 c 12 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + (172 + 8))) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 180) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + (172 + 8)) 7 ltac:(lia)); exact h7a).
    assert (haddi : step s_b = setPc (rset s_b 30 (c + -48)) (coreAddr + 184)).
    { rewrite (step_addi s_b 180 30 7 (-48) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb
        ltac:(vm_compute; reflexivity)), h7b, (wadd_id c (-48) ltac:(lia)), hpcb,
        (wadd_id (coreAddr + 180) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    set (s_c := setPc (rset s_b 30 (c + -48)) (coreAddr + 184)) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 184) by (unfold s_c; reflexivity).
    assert (hjal : step s_c = setPc s_c (coreAddr + 208)).
    { rewrite (step_jal s_c 184 0 24 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc
        ltac:(vm_compute; reflexivity)).
      assert (Hr0 : rset s_c 0 (wadd s_c.(pc) 4) = s_c) by (unfold rset; reflexivity).
      rewrite Hr0, hpcc, (wadd_id (coreAddr + 184) 24 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hbc : runUntil 0 2 s_b = setPc s_c (coreAddr + 208)).
    { assert (hpb0 : s_b.(pc) <> 0) by (rewrite hpcb; apply coreAddr_pos; lia).
      assert (hpc0 : s_c.(pc) <> 0) by (rewrite hpcc; apply coreAddr_pos; lia).
      rewrite (runUntil_S 1 s_b hpb0), haddi, (runUntil_S 0 s_c hpc0), hjal. reflexivity. }
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc s_c (coreAddr + 208))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, hbc; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem. unfold s_c. rewrite setPc_mem, rset_mem. unfold s_b.
      rewrite setPc_mem, rset_mem. unfold s_a. rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget. unfold s_c.
      rewrite setPc_rget, (rset_rget s_b 30 (c + -48) 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi30. rewrite setPc_rget. unfold s_c. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_b 30 (c + -48) i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact hi30).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + (172 + 8)) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi28). reflexivity.
  - (* letter *)
    pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (s_a := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded s_a) by
      (apply (CodeLoaded_eqmem s); [unfold s_a; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : s_a.(pc) = coreAddr + 172) by (unfold s_a; reflexivity).
    assert (h7a : rget s_a 7 = c) by
      (unfold s_a; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t s_a 172 58 c 12 (coreAddr + 188) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (172 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (s_b := setPc (rset s_a 28 58) (coreAddr + 188)) in *.
    assert (hcb : CodeLoaded s_b) by
      (apply (CodeLoaded_eqmem s_a); [unfold s_b; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : s_b.(pc) = coreAddr + 188) by (unfold s_b; reflexivity).
    assert (h7b : rget s_b 7 = c) by
      (unfold s_b; rewrite (li_block_frame s_a 58 (coreAddr + 188) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt s_b 188 65 c 120 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (s_c := setPc (rset s_b 28 65) (coreAddr + (188 + 8))) in *.
    assert (hcc : CodeLoaded s_c) by
      (apply (CodeLoaded_eqmem s_b); [unfold s_c; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : s_c.(pc) = coreAddr + 196) by (unfold s_c; reflexivity).
    assert (h7c : rget s_c 7 = c) by
      (unfold s_c; rewrite (li_block_frame s_b 65 (coreAddr + (188 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_nt s_c 196 71 c 112 hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcc h7c
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bD.
    set (s_d := setPc (rset s_c 28 71) (coreAddr + (196 + 8))) in *.
    assert (hcd : CodeLoaded s_d) by
      (apply (CodeLoaded_eqmem s_c); [unfold s_d; rewrite setPc_mem, rset_mem; reflexivity| exact hcc]).
    assert (hpcd : s_d.(pc) = coreAddr + 204) by (unfold s_d; reflexivity).
    assert (h7d : rget s_d 7 = c) by
      (unfold s_d; rewrite (li_block_frame s_c 71 (coreAddr + (196 + 8)) 7 ltac:(lia)); exact h7c).
    assert (haddi : step s_d = setPc (rset s_d 30 (c + -55)) (coreAddr + 208)).
    { rewrite (step_addi s_d 204 30 7 (-55) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd
        ltac:(vm_compute; reflexivity)), h7d, (wadd_id c (-55) ltac:(lia)), hpcd,
        (wadd_id (coreAddr + 204) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
    assert (hpd0 : s_d.(pc) <> 0) by (rewrite hpcd; apply coreAddr_pos; lia).
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 1)))) s = setPc (rset s_d 30 (c + -55)) (coreAddr + 208))
      by (rewrite (runUntil_add 2 (2 + (2 + (2 + 1)))), bA, (runUntil_add 2 (2 + (2 + 1))), bB,
          (runUntil_add 2 (2 + 1)), bC, (runUntil_add 2 1), bD, (runUntil_one s_d hpd0), haddi;
          reflexivity).
    exists (2 + (2 + (2 + (2 + 1))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold s_d. rewrite setPc_mem, rset_mem. unfold s_c.
      rewrite setPc_mem, rset_mem. unfold s_b. rewrite setPc_mem, rset_mem. unfold s_a.
      rewrite setPc_mem, rset_mem. reflexivity.
    + rewrite setPc_rget, (rset_rget s_d 30 (c + -55) 30 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
    + intros i hi28 hi30. rewrite setPc_rget.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0. rewrite (rset_rget s_d 30 (c + -55) i ltac:(lia) E0).
      replace (i =? 30) with false by (symmetry; apply Z.eqb_neq; exact hi30).
      unfold s_d. rewrite (li_block_frame s_c 71 (coreAddr + (196 + 8)) i hi28).
      unfold s_c. rewrite (li_block_frame s_b 65 (coreAddr + (188 + 8)) i hi28).
      unfold s_b. rewrite (li_block_frame s_a 58 (coreAddr + 188) i hi28).
      unfold s_a. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi28). reflexivity.
Qed.

(** ** The byte store epilogue (mirror of combine_nibbles/store_epilogue). *)

(* low nibble [lo] and high-shifted nibble [16*hi] share no bits. *)
Lemma land_hilo hi lo : 0 <= hi -> 0 <= lo < 16 -> Z.land (16 * hi) lo = 0.
Proof.
  intros Hh Hl. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. apply andb_false_iff.
  destruct (k <? 4) eqn:Ek.
  - apply Z.ltb_lt in Ek. left.
    replace (16 * hi) with (Z.shiftl hi 4) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite Z.shiftl_spec by lia. apply Z.testbit_neg_r. lia.
  - apply Z.ltb_ge in Ek. right.
    apply Z.testbit_false. lia. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. apply Z.lt_le_trans with (2 ^ 4); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* the assembled byte [(hi<<4) | lo], masked to 8 bits, is [hi*16+lo]. *)
Lemma combine_nibbles hi lo : (hi < 16)%nat -> (lo < 16)%nat ->
  (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)) mod 256 = Z.of_nat (hi * 16 + lo).
Proof.
  intros hh hl.
  assert (Hw : wshl (Z.of_nat hi) 4 = 16 * Z.of_nat hi).
  { unfold wshl. rewrite Z.shiftl_mul_pow2 by lia. rewrite wrap_small; [lia| lia]. }
  rewrite Hw. unfold wor.
  assert (Hlor : Z.lor (16 * Z.of_nat hi) (Z.of_nat lo) = 16 * Z.of_nat hi + Z.of_nat lo).
  { pose proof (Z.add_lor_land (16 * Z.of_nat hi) (Z.of_nat lo)) as H.
    rewrite (land_hilo (Z.of_nat hi) (Z.of_nat lo) ltac:(lia) ltac:(lia)) in H. lia. }
  rewrite Hlor, Z.mod_small; [rewrite Nat2Z.inj_add, Nat2Z.inj_mul; lia | lia].
Qed.

(* Capacity-OK store epilogue (offsets 208..232): bgeu(nt); slli;or (assemble);
   add;sb (store at outAddr+n); addi t1; jal LOOP.  Mirror of [store_epilogue]. *)
Lemma store_epilogue s hi lo n cap :
  CodeLoaded s -> s.(pc) = coreAddr + 208 ->
  rget s 6 = Z.of_nat n -> rget s 13 = cap -> rget s 12 = outAddr ->
  rget s 29 = Z.of_nat hi -> rget s 30 = Z.of_nat lo ->
  (hi < 16)%nat -> (lo < 16)%nat -> Z.of_nat n < cap -> outAddr + cap < 2 ^ 64 ->
  exists k, (k <= 7)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 8 /\
    rget (runUntil 0 k s) 6 = Z.of_nat (n + 1) /\
    (forall i, i <> 6 -> i <> 28 -> i <> 29 -> rget (runUntil 0 k s) i = rget s i) /\
    (forall a, (runUntil 0 k s).(mem) a =
       if a =? (outAddr + Z.of_nat n) then Z.of_nat (hi * 16 + lo) else s.(mem) a).
Proof.
  intros hcode hpc h6 h13 h12 h29 h30 hhi hlo hn hout.
  (* step 1: bgeu t1,a3 NOT taken (n < cap) *)
  assert (hult : ultb (rget s 6) (rget s 13) = true)
    by (rewrite h6, h13; unfold ultb; apply Z.ltb_lt; exact hn).
  assert (hu1 : step s = setPc s (coreAddr + 212)).
  { rewrite (step_bgeu s 208 6 13 68 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
      ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc, (wadd_id (coreAddr + 208) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v1 := setPc s (coreAddr + 212)) in *.
  assert (hc1 : CodeLoaded v1) by
    (apply (CodeLoaded_eqmem s); [unfold v1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : v1.(pc) = coreAddr + 212) by reflexivity.
  (* step 2: slli t4,t4,4 *)
  assert (h29v1 : rget v1 29 = Z.of_nat hi) by (unfold v1; rewrite setPc_rget; exact h29).
  assert (hu2 : step v1 = setPc (rset v1 29 (wshl (Z.of_nat hi) 4)) (coreAddr + 216)).
  { rewrite (step_slli v1 212 29 29 4 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
      ltac:(vm_compute; reflexivity)), h29v1, hpc1,
      (wadd_id (coreAddr + 212) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v2 := setPc (rset v1 29 (wshl (Z.of_nat hi) 4)) (coreAddr + 216)) in *.
  assert (hc2 : CodeLoaded v2) by
    (apply (CodeLoaded_eqmem s); [unfold v2, v1; rewrite !setPc_mem, rset_mem; reflexivity| exact hcode]).
  assert (hpc2 : v2.(pc) = coreAddr + 216) by reflexivity.
  (* step 3: or t4,t4,t5 *)
  assert (h29v2 : rget v2 29 = wshl (Z.of_nat hi) 4) by
    (unfold v2; rewrite setPc_rget, (rset_rget v1 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (h30v2 : rget v2 30 = Z.of_nat lo).
  { unfold v2. rewrite setPc_rget, (rset_rget v1 29 _ 30 ltac:(lia) ltac:(lia)).
    replace (30 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h30. }
  assert (hu3 : step v2 = setPc (rset v2 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 220)).
  { rewrite (step_or v2 216 29 29 30 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
      ltac:(vm_compute; reflexivity)), h29v2, h30v2, hpc2,
      (wadd_id (coreAddr + 216) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v3 := setPc (rset v2 29 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 220)) in *.
  assert (hc3 : CodeLoaded v3) by
    (apply (CodeLoaded_eqmem s); [unfold v3, v2, v1; rewrite !setPc_mem, !rset_mem; reflexivity| exact hcode]).
  assert (hpc3 : v3.(pc) = coreAddr + 220) by reflexivity.
  (* step 4: add t3,a2,t1  (t3 := outAddr + n) *)
  assert (h12v3 : rget v3 12 = outAddr).
  { unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ 12 ltac:(lia) ltac:(lia)).
    replace (12 =? 29) with false by reflexivity. unfold v2.
    rewrite setPc_rget, (rset_rget v1 29 _ 12 ltac:(lia) ltac:(lia)).
    replace (12 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h12. }
  assert (h6v3 : rget v3 6 = Z.of_nat n).
  { unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 29) with false by reflexivity. unfold v2.
    rewrite setPc_rget, (rset_rget v1 29 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 29) with false by reflexivity. unfold v1. rewrite setPc_rget. exact h6. }
  assert (hu4 : step v3 = setPc (rset v3 28 (outAddr + Z.of_nat n)) (coreAddr + 224)).
  { rewrite (step_add v3 220 28 12 6 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
      ltac:(vm_compute; reflexivity)), h12v3, h6v3,
      (wadd_id outAddr (Z.of_nat n) ltac:(unfold outAddr in *; lia)), hpc3,
      (wadd_id (coreAddr + 220) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v4 := setPc (rset v3 28 (outAddr + Z.of_nat n)) (coreAddr + 224)) in *.
  assert (hmemv4 : v4.(mem) = s.(mem)) by
    (unfold v4, v3, v2, v1; rewrite !setPc_mem, !rset_mem; reflexivity).
  assert (hc4 : CodeLoaded v4) by (apply (CodeLoaded_eqmem s); [exact hmemv4| exact hcode]).
  assert (hpc4 : v4.(pc) = coreAddr + 224) by reflexivity.
  (* step 5: sb t4,0(t3) *)
  assert (h28v4 : rget v4 28 = outAddr + Z.of_nat n) by
    (unfold v4; rewrite setPc_rget, (rset_rget v3 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (h29v4 : rget v4 29 = wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo)).
  { unfold v4. rewrite setPc_rget, (rset_rget v3 28 _ 29 ltac:(lia) ltac:(lia)).
    replace (29 =? 28) with false by reflexivity. unfold v3.
    rewrite setPc_rget, (rset_rget v2 29 _ 29 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity. }
  assert (hu5 : step v4 = setPc (storeByte v4 (outAddr + Z.of_nat n)
                 (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 228)).
  { rewrite (step_sb v4 224 28 29 0 hc4 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc4
      ltac:(vm_compute; reflexivity)), h28v4,
      (wadd_id (outAddr + Z.of_nat n) 0 ltac:(unfold outAddr in *; lia)), Z.add_0_r, h29v4, hpc4,
      (wadd_id (coreAddr + 224) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v5 := setPc (storeByte v4 (outAddr + Z.of_nat n)
              (wor (wshl (Z.of_nat hi) 4) (Z.of_nat lo))) (coreAddr + 228)) in *.
  assert (hc5 : CodeLoaded v5).
  { intros i Hi. assert (hile : i < 324) by (rewrite coreBytes_len in Hi; lia).
    unfold v5. rewrite setPc_mem, storeByte_mem.
    replace ((coreAddr + i) =? (outAddr + Z.of_nat n)) with false
      by (symmetry; apply Z.eqb_neq; unfold coreAddr, outAddr in *; lia).
    rewrite hmemv4. exact (hcode i Hi). }
  assert (hpc5 : v5.(pc) = coreAddr + 228) by reflexivity.
  (* step 6: addi t1,t1,1 *)
  assert (h6v5 : rget v5 6 = Z.of_nat n).
  { unfold v5. rewrite setPc_rget, storeByte_rget. unfold v4.
    rewrite setPc_rget, (rset_rget v3 28 _ 6 ltac:(lia) ltac:(lia)).
    replace (6 =? 28) with false by reflexivity. exact h6v3. }
  assert (hu6 : step v5 = setPc (rset v5 6 (Z.of_nat n + 1)) (coreAddr + 232)).
  { rewrite (step_addi v5 228 6 6 1 hc5 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc5
      ltac:(vm_compute; reflexivity)), h6v5, (wadd_id (Z.of_nat n) 1 ltac:(unfold outAddr in *; lia)), hpc5,
      (wadd_id (coreAddr + 228) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (v6 := setPc (rset v5 6 (Z.of_nat n + 1)) (coreAddr + 232)) in *.
  assert (hc6 : CodeLoaded v6) by
    (apply (CodeLoaded_eqmem v5); [unfold v6; rewrite setPc_mem, rset_mem; reflexivity| exact hc5]).
  assert (hpc6 : v6.(pc) = coreAddr + 232) by reflexivity.
  (* step 7: jal -> LOOP *)
  assert (hu7 : step v6 = setPc v6 (coreAddr + 8)).
  { rewrite (step_jal v6 232 0 (-224) hc6 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc6
      ltac:(vm_compute; reflexivity)).
    assert (Hr0 : rset v6 0 (wadd v6.(pc) 4) = v6) by (unfold rset; reflexivity).
    rewrite Hr0, hpc6, (wadd_id (coreAddr + 232) (-224) ltac:(unfold coreAddr; lia)). reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : v1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : v2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : v3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hp4 : v4.(pc) <> 0) by (rewrite hpc4; apply coreAddr_pos; lia).
  assert (hp5 : v5.(pc) <> 0) by (rewrite hpc5; apply coreAddr_pos; lia).
  assert (hp6 : v6.(pc) <> 0) by (rewrite hpc6; apply coreAddr_pos; lia).
  assert (hfin : runUntil 0 7 s = setPc v6 (coreAddr + 8)).
  { rewrite (runUntil_S 6 s hp0), hu1, (runUntil_S 5 v1 hp1), hu2, (runUntil_S 4 v2 hp2), hu3,
      (runUntil_S 3 v3 hp3), hu4, (runUntil_S 2 v4 hp4), hu5, (runUntil_S 1 v5 hp5), hu6,
      (runUntil_S 0 v6 hp6), hu7. reflexivity. }
  exists 7%nat. rewrite hfin. repeat apply conj.
  - lia.
  - apply setPc_pc.
  - rewrite setPc_rget. unfold v6.
    rewrite setPc_rget, (rset_rget v5 6 _ 6 ltac:(lia) ltac:(lia)), Z.eqb_refl. lia.
  - intros i h6i h28i h29i. rewrite setPc_rget. unfold v6.
    destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
    apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget v5 6 _ i ltac:(lia) E0).
    replace (i =? 6) with false by (symmetry; apply Z.eqb_neq; exact h6i).
    unfold v5. rewrite setPc_rget, storeByte_rget. unfold v4.
    rewrite setPc_rget, (rset_rget v3 28 _ i ltac:(lia) E0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28i).
    unfold v3. rewrite setPc_rget, (rset_rget v2 29 _ i ltac:(lia) E0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29i).
    unfold v2. rewrite setPc_rget, (rset_rget v1 29 _ i ltac:(lia) E0).
    replace (i =? 29) with false by (symmetry; apply Z.eqb_neq; exact h29i).
    unfold v1. rewrite setPc_rget. reflexivity.
  - intros a. rewrite setPc_mem. unfold v6. rewrite setPc_mem, rset_mem. unfold v5.
    rewrite setPc_mem, storeByte_mem. destruct (a =? (outAddr + Z.of_nat n)) eqn:Ea.
    + rewrite <- (combine_nibbles hi lo hhi hlo). reflexivity.
    + rewrite hmemv4. reflexivity.
Qed.

(* Generic input-read head [bgeu(nt);add;lbu;addi] at any offset [off] of this
   shape (true at off = 8 and off = 108).  Mirror of Lean [read_prefix]. *)
Lemma read_prefix s off immB inp idx ch :
  CodeLoaded s -> s.(pc) = coreAddr + off ->
  decode (wordAt off) = Ibgeu 5 11 immB ->
  decode (wordAt (off + 4)) = Iadd 28 10 5 ->
  decode (wordAt (off + 8)) = Ilbu 7 28 0 ->
  decode (wordAt (off + 12)) = Iaddi 5 5 1 ->
  0 <= off -> off + 12 + 3 < Z.of_nat (length coreBytes) ->
  rget s 10 = inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  rget s 5 = Z.of_nat idx -> (idx < length inp)%nat ->
  inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length inp) -> s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0) ->
  nth idx inp 0 = ch -> 0 <= ch < 256 ->
  (runUntil 0 4 s).(pc) = coreAddr + (off + 16) /\
  rget (runUntil 0 4 s) 7 = ch /\ rget (runUntil 0 4 s) 5 = rget s 5 + 1 /\
  (runUntil 0 4 s).(mem) = s.(mem) /\ CodeLoaded (runUntil 0 4 s) /\
  (forall i, i <> 0 -> i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros hcode hpc hbg hadd hlbu haddi ho hoff Ha0 Ha1 Hidx hlt hin_fit Hinmem Hch Hcr.
  rewrite coreBytes_len in hoff.
  assert (hult : ultb (rget s 5) (rget s 11) = true)
    by (rewrite Hidx, Ha1; unfold ultb; apply Z.ltb_lt; apply Nat2Z.inj_lt; exact hlt).
  assert (hs1 : step s = setPc s (coreAddr + (off + 4))).
  { rewrite (step_bgeu s off 5 11 immB hcode ho ltac:(rewrite coreBytes_len; lia) hpc hbg), hult.
    cbn match. rewrite hpc, (wadd_id (coreAddr + off) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s1 := setPc s (coreAddr + (off + 4))) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + (off + 4)) by reflexivity.
  assert (haddr : wadd (rget s1 10) (rget s1 5) = inputAddr + Z.of_nat idx).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. unfold inputAddr in *; lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + (off + 8))).
  { rewrite (step_add s1 (off + 4) 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1 hadd),
      haddr, hpc1, (wadd_id (coreAddr + (off + 4)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s2 := setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + (off + 8))) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded s2) by (apply (CodeLoaded_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + (off + 8)) by reflexivity.
  assert (hr28 : rget s2 28 = inputAddr + Z.of_nat idx) by
    (unfold s2; rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = ch).
  { rewrite hr28, (wadd_id (inputAddr + Z.of_nat idx) 0 ltac:(unfold inputAddr in *; lia)), Z.add_0_r,
      hmem2, (Hinmem (Z.of_nat idx) ltac:(split; [lia| apply Nat2Z.inj_lt; exact hlt])), Nat2Z.id, Hch.
    apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 ch) (coreAddr + (off + 12))).
  { rewrite (step_lbu s2 (off + 8) 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2 hlbu),
      hbyte, hpc2, (wadd_id (coreAddr + (off + 8)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s3 := setPc (rset s2 7 ch) (coreAddr + (off + 12))) in *.
  assert (hmem3 : s3.(mem) = s.(mem)) by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded s3) by (apply (CodeLoaded_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = coreAddr + (off + 12)) by reflexivity.
  assert (hr5_3 : rget s3 5 = Z.of_nat idx).
  { unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity. unfold s1. rewrite setPc_rget. exact Hidx. }
  assert (hs4 : step s3 = setPc (rset s3 5 (Z.of_nat idx + 1)) (coreAddr + (off + 16))).
  { rewrite (step_addi s3 (off + 12) 5 5 1 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3 haddi),
      hr5_3, (wadd_id (Z.of_nat idx) 1 ltac:(unfold inputAddr in *; lia)), hpc3,
      (wadd_id (coreAddr + (off + 12)) 4 ltac:(unfold coreAddr; lia)). f_equal. lia. }
  set (s4 := setPc (rset s3 5 (Z.of_nat idx + 1)) (coreAddr + (off + 16))) in *.
  assert (hmem4 : s4.(mem) = s.(mem)) by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4. apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 5 _ 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 5) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 7 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - assert (H54 : rget s4 5 = Z.of_nat idx + 1) by
      (unfold s4; rewrite setPc_rget, (rset_rget s3 5 _ 5 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
    rewrite Hidx. lia.
  - exact hmem4.
  - apply (CodeLoaded_eqmem s); [exact hmem4| exact hcode].
  - intros i h0 h5 h7 h28.
    unfold s4. rewrite setPc_rget, (rset_rget s3 5 _ i ltac:(lia) h0).
    replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch i ltac:(lia) h0).
    replace (i =? 7) with false by (symmetry; apply Z.eqb_neq; exact h7).
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ i ltac:(lia) h0).
    replace (i =? 28) with false by (symmetry; apply Z.eqb_neq; exact h28).
    unfold s1. rewrite setPc_rget. reflexivity.
Qed.

(** ** The error-branch parse chains (mirror of high_parse_unknown /
    low_parse_unknown / low_split). *)

Lemma nibble_none_cases c : 0 <= c -> nibble (Z.to_nat c) = None ->
  c < 48 \/ (57 < c < 65) \/ 70 < c.
Proof.
  intros h0 hn.
  assert (Hc : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  unfold nibble in hn. set (n := Z.to_nat c) in *.
  destruct ((48 <=? n) && (n <=? 57))%nat eqn:Ed; [cbv iota in hn; discriminate|].
  destruct ((65 <=? n) && (n <=? 70))%nat eqn:El; [cbv iota in hn; discriminate|].
  apply andb_false_iff in Ed. apply andb_false_iff in El.
  assert (Hd : (n < 48 \/ 57 < n)%nat)
    by (destruct Ed as [E|E]; [left| right]; apply Nat.leb_gt; exact E).
  assert (Hl : (n < 65 \/ 70 < n)%nat)
    by (destruct El as [E|E]; [left| right]; apply Nat.leb_gt; exact E).
  rewrite Hc. destruct Hd as [Hd|Hd]; destruct Hl as [Hl|Hl]; lia.
Qed.

Lemma isLowStop_cases l : 0 <= l -> isLowStop (Z.to_nat l) = true ->
  l = 10 \/ l = 32 \/ l = 95 \/ l = 35 \/ l = 59.
Proof.
  intros h0 hs. unfold isLowStop, isSpace, isComment, c_nl, c_sp, c_us, c_hash, c_semi in hs.
  rewrite !orb_true_iff, !Nat.eqb_eq in hs.
  assert (Hid : l = Z.of_nat (Z.to_nat l)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  destruct hs as [[[H|H]|H]|[H|H]];
    [left|right;left|right;right;left|right;right;right;left|right;right;right;right];
    rewrite Hid, H; reflexivity.
Qed.

(* High-nibble parse, c not a hex digit -> .Lunknown (312). *)
Lemma high_parse_unknown s c :
  CodeLoaded s -> s.(pc) = coreAddr + 64 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = None ->
   exists k, (k <= 8)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 312 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_none_cases c ltac:(lia) hn) as [Hlt|[Hmid|Hgt]].
  - pose proof (li_blt_t s 64 48 c 244 (coreAddr + 312) hcode ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (64 + 4)) 244 ltac:(unfold coreAddr; lia)); lia)) as b.
    exists 2%nat. rewrite b. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s 48 (coreAddr + 312) i hi). reflexivity.
  - pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 72) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = c) by
      (unfold sa; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t sa 72 58 c 12 (coreAddr + 88) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (72 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (sb := setPc (rset sa 28 58) (coreAddr + 88)) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 88) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = c) by
      (unfold sb; rewrite (li_block_frame sa 58 (coreAddr + 88) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_t sb 88 65 c 220 (coreAddr + 312) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcb h7b ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (88 + 4)) 220 ltac:(unfold coreAddr; lia)); lia)) as bC.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc (rset sb 28 65) (coreAddr + 312))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, bC; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. unfold sa.
      rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sb 65 (coreAddr + 312) i hi).
      unfold sb. rewrite (li_block_frame sa 58 (coreAddr + 88) i hi).
      unfold sa. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi). reflexivity.
  - pose proof (li_blt_nt s 64 48 c 244 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 48) (coreAddr + (64 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 72) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = c) by
      (unfold sa; rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t sa 72 58 c 12 (coreAddr + 88) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (72 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (sb := setPc (rset sa 28 58) (coreAddr + 88)) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 88) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = c) by
      (unfold sb; rewrite (li_block_frame sa 58 (coreAddr + 88) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt sb 88 65 c 220 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (sc := setPc (rset sb 28 65) (coreAddr + (88 + 8))) in *.
    assert (hcc : CodeLoaded sc) by
      (apply (CodeLoaded_eqmem sb); [unfold sc; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : sc.(pc) = coreAddr + 96) by (unfold sc; reflexivity).
    assert (h7c : rget sc 7 = c) by
      (unfold sc; rewrite (li_block_frame sb 65 (coreAddr + (88 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_t sc 96 71 c 212 (coreAddr + 312) hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcc h7c ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (96 + 4)) 212 ltac:(unfold coreAddr; lia)); lia)) as bD.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s = setPc (rset sc 28 71) (coreAddr + 312))
      by (rewrite (runUntil_add 2 (2 + (2 + 2))), bA, (runUntil_add 2 (2 + 2)), bB,
          (runUntil_add 2 2), bC, bD; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
      rewrite setPc_mem, rset_mem. unfold sa. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sc 71 (coreAddr + 312) i hi).
      unfold sc. rewrite (li_block_frame sb 65 (coreAddr + (88 + 8)) i hi).
      unfold sb. rewrite (li_block_frame sa 58 (coreAddr + 88) i hi).
      unfold sa. rewrite (li_block_frame s 48 (coreAddr + (64 + 8)) i hi). reflexivity.
Qed.

(* Low-nibble parse, l not a hex digit -> .Lunknown (312).  Offsets +100. *)
Lemma low_parse_unknown s c :
  CodeLoaded s -> s.(pc) = coreAddr + 164 -> rget s 7 = c -> 0 <= c < 256 ->
  nibble (Z.to_nat c) = None ->
   exists k, (k <= 8)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 312 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hn.
  destruct (nibble_none_cases c ltac:(lia) hn) as [Hlt|[Hmid|Hgt]].
  - pose proof (li_blt_t s 164 48 c 144 (coreAddr + 312) hcode ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (164 + 4)) 144 ltac:(unfold coreAddr; lia)); lia)) as b.
    exists 2%nat. rewrite b. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s 48 (coreAddr + 312) i hi). reflexivity.
  - pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 172) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = c) by
      (unfold sa; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t sa 172 58 c 12 (coreAddr + 188) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (172 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (sb := setPc (rset sa 28 58) (coreAddr + 188)) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 188) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = c) by
      (unfold sb; rewrite (li_block_frame sa 58 (coreAddr + 188) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_t sb 188 65 c 120 (coreAddr + 312) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcb h7b ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (188 + 4)) 120 ltac:(unfold coreAddr; lia)); lia)) as bC.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc (rset sb 28 65) (coreAddr + 312))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, bC; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. unfold sa.
      rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sb 65 (coreAddr + 312) i hi).
      unfold sb. rewrite (li_block_frame sa 58 (coreAddr + 188) i hi).
      unfold sa. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi). reflexivity.
  - pose proof (li_blt_nt s 164 48 c 144 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 48) (coreAddr + (164 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 172) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = c) by
      (unfold sa; rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_bge_t sa 172 58 c 12 (coreAddr + 188) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (172 + 4)) 12 ltac:(unfold coreAddr; lia)); lia)) as bB.
    set (sb := setPc (rset sa 28 58) (coreAddr + 188)) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 188) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = c) by
      (unfold sb; rewrite (li_block_frame sa 58 (coreAddr + 188) 7 ltac:(lia)); exact h7a).
    pose proof (li_blt_nt sb 188 65 c 120 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as bC.
    set (sc := setPc (rset sb 28 65) (coreAddr + (188 + 8))) in *.
    assert (hcc : CodeLoaded sc) by
      (apply (CodeLoaded_eqmem sb); [unfold sc; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcc : sc.(pc) = coreAddr + 196) by (unfold sc; reflexivity).
    assert (h7c : rget sc 7 = c) by
      (unfold sc; rewrite (li_block_frame sb 65 (coreAddr + (188 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_bge_t sc 196 71 c 112 (coreAddr + 312) hcc ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcc h7c ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(rewrite (wadd_id (coreAddr + (196 + 4)) 112 ltac:(unfold coreAddr; lia)); lia)) as bD.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s = setPc (rset sc 28 71) (coreAddr + 312))
      by (rewrite (runUntil_add 2 (2 + (2 + 2))), bA, (runUntil_add 2 (2 + 2)), bB,
          (runUntil_add 2 2), bC, bD; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sc. rewrite setPc_mem, rset_mem. unfold sb.
      rewrite setPc_mem, rset_mem. unfold sa. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sc 71 (coreAddr + 312) i hi).
      unfold sc. rewrite (li_block_frame sb 65 (coreAddr + (188 + 8)) i hi).
      unfold sb. rewrite (li_block_frame sa 58 (coreAddr + 188) i hi).
      unfold sa. rewrite (li_block_frame s 48 (coreAddr + (164 + 8)) i hi). reflexivity.
Qed.

(* Low-stop beq-chain, l IS a stop char -> .Lsplit (288). *)
Lemma low_split s l :
  CodeLoaded s -> s.(pc) = coreAddr + 124 -> rget s 7 = l -> 0 <= l < 256 ->
  isLowStop (Z.to_nat l) = true ->
   exists k, (k <= 10)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 288 /\ (runUntil 0 k s).(mem) = s.(mem) /\
    (forall i, i <> 28 -> rget (runUntil 0 k s) i = rget s i).
Proof.
  intros hcode hpc h7 hc hstop.
  destruct (isLowStop_cases l ltac:(lia) hstop) as [H|[H|[H|[H|H]]]]; rewrite H in h7; clear H.
  - (* 10 : taken at 124 *)
    pose proof (li_beq_eq s 124 10 10 160 (coreAddr + 288) hcode ltac:(lia)
      ltac:(rewrite coreBytes_len; lia) hpc h7 ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + (124 + 4)) 160 ltac:(unfold coreAddr; lia)); lia)) as b.
    exists 2%nat. rewrite b. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame s 10 (coreAddr + 288) i hi). reflexivity.
  - (* 32 : nt at 124, taken at 132 *)
    pose proof (li_beq_ne s 124 10 32 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 132) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = 32) by
      (unfold sa; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_beq_eq sa 132 32 32 152 (coreAddr + 288) hca ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpca h7a ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + (132 + 4)) 152 ltac:(unfold coreAddr; lia)); lia)) as bB.
    assert (hfin : runUntil 0 (2 + 2) s = setPc (rset sa 28 32) (coreAddr + 288))
      by (rewrite (runUntil_add 2 2), bA, bB; reflexivity).
    exists (2 + 2)%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sa. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sa 32 (coreAddr + 288) i hi).
      unfold sa. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
  - (* 95 : nt 124,132, taken at 140 *)
    pose proof (li_beq_ne s 124 10 95 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 132) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = 95) by
      (unfold sa; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_beq_ne sa 132 32 95 152 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bB.
    set (sb := setPc (rset sa 28 32) (coreAddr + (132 + 8))) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 140) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = 95) by
      (unfold sb; rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) 7 ltac:(lia)); exact h7a).
    pose proof (li_beq_eq sb 140 95 95 144 (coreAddr + 288) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcb h7b ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + (140 + 4)) 144 ltac:(unfold coreAddr; lia)); lia)) as bC.
    assert (hfin : runUntil 0 (2 + (2 + 2)) s = setPc (rset sb 28 95) (coreAddr + 288))
      by (rewrite (runUntil_add 2 (2 + 2)), bA, (runUntil_add 2 2), bB, bC; reflexivity).
    exists (2 + (2 + 2))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. unfold sa.
      rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sb 95 (coreAddr + 288) i hi).
      unfold sb. rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) i hi).
      unfold sa. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
  - (* 35 : nt 124,132,140, taken at 148 *)
    pose proof (li_beq_ne s 124 10 35 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 132) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = 35) by
      (unfold sa; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_beq_ne sa 132 32 35 152 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bB.
    set (sb := setPc (rset sa 28 32) (coreAddr + (132 + 8))) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 140) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = 35) by
      (unfold sb; rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) 7 ltac:(lia)); exact h7a).
    pose proof (li_beq_ne sb 140 95 35 144 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bC.
    set (sd := setPc (rset sb 28 95) (coreAddr + (140 + 8))) in *.
    assert (hcd : CodeLoaded sd) by
      (apply (CodeLoaded_eqmem sb); [unfold sd; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcd : sd.(pc) = coreAddr + 148) by (unfold sd; reflexivity).
    assert (h7d : rget sd 7 = 35) by
      (unfold sd; rewrite (li_block_frame sb 95 (coreAddr + (140 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_beq_eq sd 148 35 35 136 (coreAddr + 288) hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpcd h7d ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + (148 + 4)) 136 ltac:(unfold coreAddr; lia)); lia)) as bE.
    assert (hfin : runUntil 0 (2 + (2 + (2 + 2))) s = setPc (rset sd 28 35) (coreAddr + 288))
      by (rewrite (runUntil_add 2 (2 + (2 + 2))), bA, (runUntil_add 2 (2 + 2)), bB,
          (runUntil_add 2 2), bC, bE; reflexivity).
    exists (2 + (2 + (2 + 2)))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold sd. rewrite setPc_mem, rset_mem. unfold sb.
      rewrite setPc_mem, rset_mem. unfold sa. rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame sd 35 (coreAddr + 288) i hi).
      unfold sd. rewrite (li_block_frame sb 95 (coreAddr + (140 + 8)) i hi).
      unfold sb. rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) i hi).
      unfold sa. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
  - (* 59 : nt 124,132,140,148, taken at 156 *)
    pose proof (li_beq_ne s 124 10 59 160 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc h7
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bA.
    set (sa := setPc (rset s 28 10) (coreAddr + (124 + 8))) in *.
    assert (hca : CodeLoaded sa) by
      (apply (CodeLoaded_eqmem s); [unfold sa; rewrite setPc_mem, rset_mem; reflexivity| exact hcode]).
    assert (hpca : sa.(pc) = coreAddr + 132) by (unfold sa; reflexivity).
    assert (h7a : rget sa 7 = 59) by
      (unfold sa; rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) 7 ltac:(lia)); exact h7).
    pose proof (li_beq_ne sa 132 32 59 152 hca ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpca h7a
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bB.
    set (sb := setPc (rset sa 28 32) (coreAddr + (132 + 8))) in *.
    assert (hcb : CodeLoaded sb) by
      (apply (CodeLoaded_eqmem sa); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hca]).
    assert (hpcb : sb.(pc) = coreAddr + 140) by (unfold sb; reflexivity).
    assert (h7b : rget sb 7 = 59) by
      (unfold sb; rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) 7 ltac:(lia)); exact h7a).
    pose proof (li_beq_ne sb 140 95 59 144 hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcb h7b
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bC.
    set (sd := setPc (rset sb 28 95) (coreAddr + (140 + 8))) in *.
    assert (hcd : CodeLoaded sd) by
      (apply (CodeLoaded_eqmem sb); [unfold sd; rewrite setPc_mem, rset_mem; reflexivity| exact hcb]).
    assert (hpcd : sd.(pc) = coreAddr + 148) by (unfold sd; reflexivity).
    assert (h7d : rget sd 7 = 59) by
      (unfold sd; rewrite (li_block_frame sb 95 (coreAddr + (140 + 8)) 7 ltac:(lia)); exact h7b).
    pose proof (li_beq_ne sd 148 35 59 136 hcd ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpcd h7d
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) as bE.
    set (se := setPc (rset sd 28 35) (coreAddr + (148 + 8))) in *.
    assert (hce : CodeLoaded se) by
      (apply (CodeLoaded_eqmem sd); [unfold se; rewrite setPc_mem, rset_mem; reflexivity| exact hcd]).
    assert (hpce : se.(pc) = coreAddr + 156) by (unfold se; reflexivity).
    assert (h7e : rget se 7 = 59) by
      (unfold se; rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) 7 ltac:(lia)); exact h7d).
    pose proof (li_beq_eq se 156 59 59 128 (coreAddr + 288) hce ltac:(lia) ltac:(rewrite coreBytes_len; lia)
      hpce h7e ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + (156 + 4)) 128 ltac:(unfold coreAddr; lia)); lia)) as bF.
    assert (hfin : runUntil 0 (2 + (2 + (2 + (2 + 2)))) s = setPc (rset se 28 59) (coreAddr + 288))
      by (rewrite (runUntil_add 2 (2 + (2 + (2 + 2)))), bA, (runUntil_add 2 (2 + (2 + 2))), bB,
          (runUntil_add 2 (2 + 2)), bC, (runUntil_add 2 2), bE, bF; reflexivity).
    exists (2 + (2 + (2 + (2 + 2))))%nat. rewrite hfin. repeat apply conj.
    + lia.
    + apply setPc_pc.
    + rewrite setPc_mem, rset_mem. unfold se. rewrite setPc_mem, rset_mem. unfold sd.
      rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem. unfold sa.
      rewrite setPc_mem, rset_mem. reflexivity.
    + intros i hi. rewrite (li_block_frame se 59 (coreAddr + 288) i hi).
      unfold se. rewrite (li_block_frame sd 35 (coreAddr + (148 + 8)) i hi).
      unfold sd. rewrite (li_block_frame sb 95 (coreAddr + (140 + 8)) i hi).
      unfold sb. rewrite (li_block_frame sa 32 (coreAddr + (132 + 8)) i hi).
      unfold sa. rewrite (li_block_frame s 10 (coreAddr + (124 + 8)) i hi). reflexivity.
Qed.

(** ** Composite navigators reach64 / reach124 (mirror of Lean). *)

Lemma isComment_false_ne c : 0 <= c -> isComment (Z.to_nat c) = false -> c <> 35 /\ c <> 59.
Proof.
  intros h0 hc. unfold isComment, c_hash, c_semi in hc. apply orb_false_iff in hc.
  destruct hc as [H1 H2]. apply Nat.eqb_neq in H1. apply Nat.eqb_neq in H2.
  split; intro E; subst c; [apply H1| apply H2]; reflexivity.
Qed.

Lemma isSpace_false_ne c : 0 <= c -> isSpace (Z.to_nat c) = false ->
  c <> 10 /\ c <> 32 /\ c <> 95.
Proof.
  intros h0 hs. unfold isSpace, c_nl, c_sp, c_us in hs. apply orb_false_iff in hs.
  destruct hs as [H12 H95]. apply orb_false_iff in H12. destruct H12 as [H10 H32].
  apply Nat.eqb_neq in H10. apply Nat.eqb_neq in H32. apply Nat.eqb_neq in H95.
  split; [|split]; intro E; subst c; [apply H10| apply H32| apply H95]; reflexivity.
Qed.

(* From the loop head, a non-space/comment head char [c]: 14 steps reach the
   high-nibble parse (offset 64), carrying all the loop bookkeeping. *)
Lemma reach64 inp cap c rest' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false ->
  LoopInv inp cap s (c :: rest') emitted ->
  (runUntil 0 14 s).(pc) = coreAddr + 64 /\ rget (runUntil 0 14 s) 7 = c /\
  CodeLoaded (runUntil 0 14 s) /\ (runUntil 0 14 s).(mem) = s.(mem) /\
  rget (runUntil 0 14 s) 5 = rget s 5 + 1 /\ rget (runUntil 0 14 s) 6 = Z.of_nat (length emitted) /\
  rget (runUntil 0 14 s) 1 = 0 /\ rget (runUntil 0 14 s) 10 = inputAddr /\
  rget (runUntil 0 14 s) 11 = Z.of_nat (length inp) /\ rget (runUntil 0 14 s) 13 = cap /\
  rget (runUntil 0 14 s) 12 = outAddr /\ 0 <= c < 256.
Proof.
  intros hsc hss inv.
  destruct (loopinv_head inp cap c rest' emitted s inv) as [Hin Hc].
  destruct (isComment_false_ne c ltac:(lia) hsc) as [hc35 hc59].
  destruct (isSpace_false_ne c ltac:(lia) hss) as [hc10 [hc32 hc95]].
  destruct (loop_prefix inp cap c rest' emitted s inv) as [hpc4 [ht2 [ht0 [hmem4 [hcode4 hoth4]]]]].
  destruct (high_beq_ft (runUntil 0 4 s) c hcode4 hpc4 ht2 Hc hc35 hc59 hc10 hc32 hc95)
    as [hpcB [hmemB hothB]].
  destruct inv as [_ _ Ha0 Ha1 Ha2 Ha3 Hra _ _ _ _ _ _ _ Houtidx _ _ _].
  assert (hrun : runUntil 0 14 s = runUntil 0 10 (runUntil 0 4 s))
    by (rewrite <- (runUntil_add 4 10); reflexivity).
  rewrite hrun. repeat apply conj.
  - exact hpcB.
  - rewrite (hothB 7 ltac:(lia)); exact ht2.
  - apply (CodeLoaded_eqmem (runUntil 0 4 s)); [exact hmemB| exact hcode4].
  - rewrite hmemB, hmem4. reflexivity.
  - rewrite (hothB 5 ltac:(lia)); exact ht0.
  - rewrite (hothB 6 ltac:(lia)), (hoth4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Houtidx.
  - rewrite (hothB 1 ltac:(lia)), (hoth4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Hra.
  - rewrite (hothB 10 ltac:(lia)), (hoth4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha0.
  - rewrite (hothB 11 ltac:(lia)), (hoth4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha1.
  - rewrite (hothB 13 ltac:(lia)), (hoth4 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha3.
  - rewrite (hothB 12 ltac:(lia)), (hoth4 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha2.
  - lia.
  - lia.
Qed.

(* From the loop head, a byte head [c] (= hi) with a following char [l]: navigate
   (read c, high-parse, read l) to offset 124 (the low-stop beq chain). *)
Lemma reach124 inp cap c hi l rest'' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false ->
  nibble (Z.to_nat c) = Some hi ->
  LoopInv inp cap s (c :: l :: rest'') emitted ->
  exists k, (k <= 27)%nat /\ (runUntil 0 k s).(pc) = coreAddr + 124 /\ rget (runUntil 0 k s) 7 = l /\
    CodeLoaded (runUntil 0 k s) /\ (runUntil 0 k s).(mem) = s.(mem) /\
    rget (runUntil 0 k s) 6 = Z.of_nat (length emitted) /\ rget (runUntil 0 k s) 1 = 0 /\
    rget (runUntil 0 k s) 13 = cap /\ rget (runUntil 0 k s) 12 = outAddr /\
    rget (runUntil 0 k s) 29 = Z.of_nat hi /\
    rget (runUntil 0 k s) 5 = Z.of_nat (length inp) - Z.of_nat (length rest'') /\
    rget (runUntil 0 k s) 10 = inputAddr /\ rget (runUntil 0 k s) 11 = Z.of_nat (length inp) /\
    0 <= l < 256.
Proof.
  intros hsc hss hnh inv. pose proof inv as inv0.
  destruct (reach64 inp cap c (l :: rest'') emitted s hsc hss inv)
    as [Hpc64 [H7_64 [Hcode64 [Hmem64 [H5_64 [H6_64 [H1_64 [H10_64 [H11_64 [H13_64 [H12_64 Hc256]]]]]]]]]]].
  set (s64 := runUntil 0 14 s) in *.
  destruct (high_parse s64 c hi Hcode64 Hpc64 H7_64 Hc256 hnh)
    as [k1 [Hk1 [HpcC [HmemC [H29C HothC]]]]].
  destruct inv0 as [_ _ _ _ _ _ _ Hinmem Hinlt Hbytes _ _ Hidx Hsuf _ _ _ _].
  set (m := (length inp - length (c :: l :: rest''))%nat) in *.
  assert (hlc : Z.of_nat (length (c :: l :: rest'')) = Z.of_nat (length rest'') + 2)
    by (simpl length; lia).
  assert (hge2 : (length (c :: l :: rest'') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl. fold m in Hl. lia. }
  set (idx := (m + 1)%nat) in *.
  assert (Hin_l : In l inp).
  { rewrite <- (firstn_skipn m inp). apply in_or_app. right. fold m in Hsuf. rewrite Hsuf.
    right; left; reflexivity. }
  assert (Hl256 : 0 <= l < 256) by (apply Hbytes; exact Hin_l).
  assert (Hidx_lt : (idx < length inp)%nat) by (unfold idx, m; simpl length in hge2; lia).
  assert (Hnth : nth idx inp 0 = l).
  { unfold idx. rewrite <- (nth_skipn m inp 1 0), Hsuf. reflexivity. }
  assert (Ht0C : rget (runUntil 0 k1 s64) 5 = Z.of_nat idx).
  { rewrite (HothC 5 ltac:(lia) ltac:(lia)), H5_64, Hidx.
    unfold idx, m. rewrite Nat2Z.inj_add, Nat2Z.inj_sub by lia. lia. }
  assert (HcodeC : CodeLoaded (runUntil 0 k1 s64)) by
    (apply (CodeLoaded_eqmem s64); [exact HmemC| exact Hcode64]).
  destruct (read_prefix (runUntil 0 k1 s64) 108 192 inp idx l HcodeC
    HpcC ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia)
    ltac:(rewrite coreBytes_len; lia)
    ltac:(rewrite (HothC 10 ltac:(lia) ltac:(lia)); exact H10_64)
    ltac:(rewrite (HothC 11 ltac:(lia) ltac:(lia)); exact H11_64)
    Ht0C Hidx_lt Hinlt
    ltac:(intros j hj; rewrite HmemC, Hmem64; exact (Hinmem j hj))
    Hnth Hl256) as [Hpc8 [H7_8 [H5_8 [Hmem8 [Hcode8 Hoth8]]]]].
  exists (14 + (k1 + 4))%nat.
  assert (hchain : runUntil 0 (14 + (k1 + 4)) s = runUntil 0 4 (runUntil 0 k1 s64))
    by (rewrite (runUntil_add 14 (k1 + 4)); fold s64; rewrite (runUntil_add k1 4); reflexivity).
  rewrite hchain. repeat apply conj.
  - lia.
  - exact Hpc8.
  - exact H7_8.
  - exact Hcode8.
  - rewrite Hmem8, HmemC, Hmem64. reflexivity.
  - rewrite (Hoth8 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 6 ltac:(lia) ltac:(lia)). exact H6_64.
  - rewrite (Hoth8 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 1 ltac:(lia) ltac:(lia)). exact H1_64.
  - rewrite (Hoth8 13 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 13 ltac:(lia) ltac:(lia)). exact H13_64.
  - rewrite (Hoth8 12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 12 ltac:(lia) ltac:(lia)). exact H12_64.
  - rewrite (Hoth8 29 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). exact H29C.
  - rewrite H5_8, Ht0C. unfold idx, m. rewrite Nat2Z.inj_add, Nat2Z.inj_sub by lia.
    rewrite hlc. lia.
  - rewrite (Hoth8 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 10 ltac:(lia) ltac:(lia)). exact H10_64.
  - rewrite (Hoth8 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)),
            (HothC 11 ltac:(lia) ltac:(lia)). exact H11_64.
  - lia.
  - lia.
Qed.

(** ** Error-case infrastructure: spec-side token decode + Result packaging. *)

Lemma nibble_not_lowstop l lo : nibble l = Some lo -> isLowStop l = false.
Proof.
  unfold nibble, isLowStop, isSpace, isComment, c_nl, c_sp, c_us, c_hash, c_semi.
  destruct ((48 <=? l) && (l <=? 57))%nat eqn:Ed.
  - apply andb_true_iff in Ed. destruct Ed as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros _.
    repeat (replace (l =? _)%nat with false by (symmetry; apply Nat.eqb_neq; lia)). reflexivity.
  - destruct ((65 <=? l) && (l <=? 70))%nat eqn:El; [|discriminate].
    apply andb_true_iff in El. destruct El as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2. intros _.
    repeat (replace (l =? _)%nat with false by (symmetry; apply Nat.eqb_neq; lia)). reflexivity.
Qed.

Lemma isLowStop_false_ne l : 0 <= l -> isLowStop (Z.to_nat l) = false ->
  l <> 10 /\ l <> 32 /\ l <> 95 /\ l <> 35 /\ l <> 59.
Proof.
  intros h0 hs. unfold isLowStop in hs. apply orb_false_iff in hs. destruct hs as [Hsp Hcm].
  destruct (isSpace_false_ne l h0 Hsp) as [H10 [H32 H95]].
  destruct (isComment_false_ne l h0 Hcm) as [H35 H59].
  repeat split; assumption.
Qed.

Lemma emitted_lt inp cap s rest emitted :
  LoopInv inp cap s rest emitted -> Z.of_nat (length emitted) < 2 ^ 64.
Proof.
  intros inv. destruct inv as [_ _ _ _ _ _ _ _ _ _ _ Houtlt _ _ _ Hemitle _ _].
  apply Nat2Z.inj_le in Hemitle. unfold outAddr in Houtlt. lia.
Qed.

Lemma decode_err inp emitted rest st :
  decodeS High (zin inp) =
    (emitted ++ fst (decodeS High (zin rest)), snd (decodeS High (zin rest))) ->
  decodeS High (zin rest) = ([], st) -> Spec.decode (zin inp) = (emitted, st).
Proof.
  intros Hspec Hd. unfold Spec.decode. rewrite Hspec, Hd. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma decodeS_high_trailing c hi : isComment c = false -> isSpace c = false ->
  nibble c = Some hi -> decodeS High (c :: nil) = (nil, Trailing).
Proof. intros hc hs hn. simp decodeS. rewrite hc, hs, hn. simp decodeS. reflexivity. Qed.

Lemma decodeS_high_unknown c rest : isComment c = false -> isSpace c = false ->
  nibble c = None -> decodeS High (c :: rest) = (nil, Unknown).
Proof. intros hc hs hn. simp decodeS. rewrite hc, hs, hn. reflexivity. Qed.

Lemma decodeS_low_split c l rest hi : isComment c = false -> isSpace c = false ->
  nibble c = Some hi -> isLowStop l = true -> decodeS High (c :: l :: rest) = (nil, Split).
Proof. intros hc hs hn hls. simp decodeS. rewrite hc, hs, hn. simp decodeS. rewrite hls. reflexivity. Qed.

Lemma decodeS_low_unknown c l rest hi : isComment c = false -> isSpace c = false ->
  nibble c = Some hi -> isLowStop l = false -> nibble l = None ->
  decodeS High (c :: l :: rest) = (nil, Unknown).
Proof.
  intros hc hs hn hls hnl. simp decodeS. rewrite hc, hs, hn. simp decodeS. rewrite hls, hnl. reflexivity.
Qed.

(* output-short Result packaging (code 2): the decode [bs] exceeds [cap], so
   coreSpec truncates to [firstn cap bs = emitted].  Mirror of Lean [short_result]. *)
Lemma short_result s inp cap emitted bs st :
  s.(pc) = 0 -> rget s 10 = 2 -> rget s 11 = Z.of_nat (Z.to_nat cap) ->
  (forall j, (j < Z.to_nat cap)%nat ->
     s.(mem) (outAddr + Z.of_nat j) = Z.of_nat (nth j emitted 0%nat)) ->
  Spec.decode (zin inp) = (bs, st) -> (Z.to_nat cap < length bs)%nat ->
  firstn (Z.to_nat cap) bs = emitted -> Result s inp cap.
Proof.
  intros hp ha0 ha1 hmem hdec hbs htake.
  assert (hlen : length emitted = Z.to_nat cap) by (rewrite <- htake, firstn_length_le; lia).
  assert (hcs : coreSpec (zin inp) (Z.to_nat cap) = (2%nat, emitted, Z.to_nat cap)).
  { unfold coreSpec. rewrite hdec. destruct (Z.to_nat cap <? length bs)%nat eqn:E.
    - rewrite htake. reflexivity.
    - apply Nat.ltb_ge in E. lia. }
  unfold Result. rewrite hcs. repeat apply conj.
  - exact hp.
  - rewrite ha0. reflexivity.
  - exact ha1.
  - rewrite <- hlen. apply readMem_eq. intros j hj. apply hmem. lia.
Qed.

(** ** The four halting error classes (mirror of loop_trailing/unknown_high/
    split/unknown_low).  Each navigates to its error label and halts. *)

(* high nibble at EOF -> Trailing (4). *)
Lemma loop_trailing inp cap c hi emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = Some hi ->
  LoopInv inp cap s (c :: nil) emitted ->
  exists k, (k <= 50 * length (c :: nil))%nat /\ Result (runUntil 0 k s) inp cap.
Proof.
  intros hsc hss hnh inv. pose proof inv as inv0.
  destruct (reach64 inp cap c nil emitted s hsc hss inv)
    as [Hpc64 [H7_64 [Hcode64 [Hmem64 [H5_64 [H6_64 [H1_64 [H10_64 [H11_64 [_ [_ Hc256]]]]]]]]]]].
  set (s64 := runUntil 0 14 s) in *.
  destruct (high_parse s64 c hi Hcode64 Hpc64 H7_64 Hc256 hnh) as [k1 [Hk1 [HpcC [HmemC [_ HothC]]]]].
  destruct inv0 as [_ _ _ _ _ _ _ _ _ _ _ _ Hidx Hsuf _ Hemitle Houtmem Hspec].
  assert (HcodeC : CodeLoaded (runUntil 0 k1 s64)) by
    (apply (CodeLoaded_eqmem s64); [exact HmemC| exact Hcode64]).
  assert (h5C : rget (runUntil 0 k1 s64) 5 = Z.of_nat (length inp)).
  { rewrite (HothC 5 ltac:(lia) ltac:(lia)), H5_64, Hidx.
    change (length (c :: nil)) with 1%nat. lia. }
  assert (h11C : rget (runUntil 0 k1 s64) 11 = Z.of_nat (length inp)) by
    (rewrite (HothC 11 ltac:(lia) ltac:(lia)); exact H11_64).
  pose proof (bgeu_eq_taken (runUntil 0 k1 s64) 108 5 11 (Z.of_nat (length inp)) 192
    (coreAddr + 300) HcodeC ltac:(lia) ltac:(rewrite coreBytes_len; lia) HpcC h5C h11C
    ltac:(vm_compute; reflexivity)
    ltac:(rewrite (wadd_id (coreAddr + 108) 192 ltac:(unfold coreAddr; lia)); lia)) as hbt.
  set (sE := setPc (runUntil 0 k1 s64) (coreAddr + 300)) in *.
  cut (exists m, (m <= (14 + (k1 + 1)) + 3)%nat /\ Result (runUntil 0 m s) inp cap).
  { intros [m [Hmb Hm]]. exists m. split; [simpl length; lia| exact Hm]. }
  apply (reach_error s sE inp cap emitted 300 4 (14 + (k1 + 1)) Trailing).
  - rewrite (runUntil_add 14 (k1 + 1)). fold s64. rewrite (runUntil_add k1 1), hbt. reflexivity.
  - unfold sE; apply setPc_pc.
  - apply (CodeLoaded_eqmem (runUntil 0 k1 s64)); [unfold sE; rewrite setPc_mem; reflexivity| exact HcodeC].
  - unfold sE; rewrite setPc_mem, HmemC, Hmem64; reflexivity.
  - unfold sE; rewrite setPc_rget, (HothC 6 ltac:(lia) ltac:(lia)); exact H6_64.
  - unfold sE; rewrite setPc_rget, (HothC 1 ltac:(lia) ltac:(lia)); exact H1_64.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - lia.
  - rewrite coreBytes_len; lia.
  - lia.
  - exact (emitted_lt inp cap s (c :: nil) emitted inv).
  - reflexivity.
  - exact (decode_err inp emitted (c :: nil) Trailing Hspec
            (decodeS_high_trailing (Z.to_nat c) hi hsc hss hnh)).
  - exact Hemitle.
  - exact Houtmem.
Qed.

(* head char not space/comment/hex -> Unknown (5). *)
Lemma loop_unknown_high inp cap c rest' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = None ->
  LoopInv inp cap s (c :: rest') emitted ->
  exists k, (k <= 50 * length (c :: rest'))%nat /\ Result (runUntil 0 k s) inp cap.
Proof.
  intros hsc hss hn inv. pose proof inv as inv0.
  destruct (reach64 inp cap c rest' emitted s hsc hss inv)
    as [Hpc64 [H7_64 [Hcode64 [Hmem64 [_ [H6_64 [H1_64 [_ [_ [_ [_ Hc256]]]]]]]]]]].
  set (s64 := runUntil 0 14 s) in *.
  destruct (high_parse_unknown s64 c Hcode64 Hpc64 H7_64 Hc256 hn) as [k1 [Hk1 [HpcU [HmemU HothU]]]].
  destruct inv0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hemitle Houtmem Hspec].
  set (sE := runUntil 0 k1 s64) in *.
  cut (exists m, (m <= (14 + k1) + 3)%nat /\ Result (runUntil 0 m s) inp cap).
  { intros [m [Hmb Hm]]. exists m. split; [simpl length; lia| exact Hm]. }
  apply (reach_error s sE inp cap emitted 312 5 (14 + k1) Unknown).
  - rewrite (runUntil_add 14 k1). fold s64. reflexivity.
  - exact HpcU.
  - apply (CodeLoaded_eqmem s64); [exact HmemU| exact Hcode64].
  - rewrite HmemU; exact Hmem64.
  - rewrite (HothU 6 ltac:(lia)); exact H6_64.
  - rewrite (HothU 1 ltac:(lia)); exact H1_64.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - lia.
  - rewrite coreBytes_len; lia.
  - lia.
  - exact (emitted_lt inp cap s (c :: rest') emitted inv).
  - reflexivity.
  - exact (decode_err inp emitted (c :: rest') Unknown Hspec
            (decodeS_high_unknown (Z.to_nat c) (zin rest') hsc hss hn)).
  - exact Hemitle.
  - exact Houtmem.
Qed.

(* high nibble, low char is a stop char -> Split (3). *)
Lemma loop_split inp cap c hi l rest'' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = Some hi ->
  isLowStop (Z.to_nat l) = true ->
  LoopInv inp cap s (c :: l :: rest'') emitted ->
  exists k, (k <= 50 * length (c :: l :: rest''))%nat /\ Result (runUntil 0 k s) inp cap.
Proof.
  intros hsc hss hnh hls inv. pose proof inv as inv0.
  destruct (reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv)
    as [k0 [Hk0 [Hpc124 [H7_124 [Hcode124 [Hmem124 [H6_124 [H1_124 [_ [_ [_ [_ [_ [_ Hl256]]]]]]]]]]]]]].
  destruct (low_split (runUntil 0 k0 s) l Hcode124 Hpc124 H7_124 Hl256 hls)
    as [k1 [Hk1 [HpcS [HmemS HothS]]]].
  destruct inv0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hemitle Houtmem Hspec].
  set (sE := runUntil 0 k1 (runUntil 0 k0 s)) in *.
  cut (exists m, (m <= (k0 + k1) + 3)%nat /\ Result (runUntil 0 m s) inp cap).
  { intros [m [Hmb Hm]]. exists m. split; [simpl length; lia| exact Hm]. }
  apply (reach_error s sE inp cap emitted 288 3 (k0 + k1) Split).
  - rewrite (runUntil_add k0 k1). reflexivity.
  - exact HpcS.
  - apply (CodeLoaded_eqmem (runUntil 0 k0 s)); [exact HmemS| exact Hcode124].
  - rewrite HmemS; exact Hmem124.
  - rewrite (HothS 6 ltac:(lia)); exact H6_124.
  - rewrite (HothS 1 ltac:(lia)); exact H1_124.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - lia.
  - rewrite coreBytes_len; lia.
  - lia.
  - exact (emitted_lt inp cap s (c :: l :: rest'') emitted inv).
  - reflexivity.
  - exact (decode_err inp emitted (c :: l :: rest'') Split Hspec
            (decodeS_low_split (Z.to_nat c) (Z.to_nat l) (zin rest'') hi hsc hss hnh hls)).
  - exact Hemitle.
  - exact Houtmem.
Qed.

(* high nibble, low char not stop and not hex -> Unknown (5). *)
Lemma loop_unknown_low inp cap c hi l rest'' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = Some hi ->
  isLowStop (Z.to_nat l) = false -> nibble (Z.to_nat l) = None ->
  LoopInv inp cap s (c :: l :: rest'') emitted ->
  exists k, (k <= 50 * length (c :: l :: rest''))%nat /\ Result (runUntil 0 k s) inp cap.
Proof.
  intros hsc hss hnh hls hnl inv. pose proof inv as inv0.
  destruct (reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv)
    as [k0 [Hk0 [Hpc124 [H7_124 [Hcode124 [Hmem124 [H6_124 [H1_124 [_ [_ [_ [_ [_ [_ Hl256]]]]]]]]]]]]]].
  destruct (isLowStop_false_ne l ltac:(lia) hls) as [Hl10 [Hl32 [Hl95 [Hl35 Hl59]]]].
  destruct (low_beq_ft (runUntil 0 k0 s) l Hcode124 Hpc124 H7_124 Hl256 Hl35 Hl59 Hl10 Hl32 Hl95)
    as [HpcE [HmemE HothE]].
  set (sE0 := runUntil 0 10 (runUntil 0 k0 s)) in *.
  assert (HcodeE0 : CodeLoaded sE0) by
    (apply (CodeLoaded_eqmem (runUntil 0 k0 s)); [exact HmemE| exact Hcode124]).
  assert (H7E0 : rget sE0 7 = l) by (rewrite (HothE 7 ltac:(lia)); exact H7_124).
  destruct (low_parse_unknown sE0 l HcodeE0 HpcE H7E0 Hl256 hnl) as [k1 [Hk1 [HpcU [HmemU HothU]]]].
  destruct inv0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hemitle Houtmem Hspec].
  set (sE := runUntil 0 k1 sE0) in *.
  cut (exists m, (m <= (k0 + (10 + k1)) + 3)%nat /\ Result (runUntil 0 m s) inp cap).
  { intros [m [Hmb Hm]]. exists m. split; [simpl length; lia| exact Hm]. }
  apply (reach_error s sE inp cap emitted 312 5 (k0 + (10 + k1)) Unknown).
  - rewrite (runUntil_add k0 (10 + k1)), (runUntil_add 10 k1). reflexivity.
  - exact HpcU.
  - apply (CodeLoaded_eqmem sE0); [exact HmemU| exact HcodeE0].
  - rewrite HmemU, HmemE, Hmem124. reflexivity.
  - rewrite (HothU 6 ltac:(lia)), (HothE 6 ltac:(lia)); exact H6_124.
  - rewrite (HothU 1 ltac:(lia)), (HothE 1 ltac:(lia)); exact H1_124.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - lia.
  - rewrite coreBytes_len; lia.
  - lia.
  - exact (emitted_lt inp cap s (c :: l :: rest'') emitted inv).
  - reflexivity.
  - exact (decode_err inp emitted (c :: l :: rest'') Unknown Hspec
            (decodeS_low_unknown (Z.to_nat c) (Z.to_nat l) (zin rest'') hi hsc hss hnh hls hnl)).
  - exact Hemitle.
  - exact Houtmem.
Qed.

(* [bgeu rs1,rs2] taken when rs1 >= rs2 (generalises bgeu_eq_taken). *)
Lemma bgeu_ge_taken s off rs1 rs2 A1 A2 immB target :
  CodeLoaded s -> 0 <= off -> off + 3 < Z.of_nat (length coreBytes) ->
  s.(pc) = coreAddr + off -> rget s rs1 = A1 -> rget s rs2 = A2 -> A2 <= A1 ->
  decode (wordAt off) = Ibgeu rs1 rs2 immB -> wadd (coreAddr + off) immB = target ->
  runUntil 0 1 s = setPc s target.
Proof.
  intros hcode ho hoff hpc h1 h2 hle hbgeu htgt.
  assert (hult : ultb (rget s rs1) (rget s rs2) = false).
  { rewrite h1, h2. unfold ultb. destruct (A1 <? A2) eqn:E;
      [apply Z.ltb_lt in E; lia| reflexivity]. }
  assert (hu1 : step s = setPc s target).
  { rewrite (step_bgeu s off rs1 rs2 immB hcode ho hoff hpc hbgeu), hult. cbn match.
    rewrite hpc, htgt. reflexivity. }
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  rewrite (runUntil_one s hp0), hu1. reflexivity.
Qed.

(* valid byte but output full (|emitted| = cap) -> OutputShort (2). *)
Lemma loop_short inp cap c hi l lo rest'' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = Some hi ->
  nibble (Z.to_nat l) = Some lo -> (Z.to_nat cap <= length emitted)%nat ->
  LoopInv inp cap s (c :: l :: rest'') emitted ->
  exists k, (k <= 50 * length (c :: l :: rest''))%nat /\ Result (runUntil 0 k s) inp cap.
Proof.
  intros hsc hss hnh hnl hge inv. pose proof inv as inv0.
  assert (heq : length emitted = Z.to_nat cap) by
    (destruct inv as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hemitle _ _]; lia).
  pose proof (nibble_not_lowstop (Z.to_nat l) lo hnl) as hlls.
  destruct (reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv)
    as [k0 [Hk0 [Hpc124 [H7_124 [Hcode124 [Hmem124 [H6_124 [H1_124 [H13_124 [_ [_ [_ [_ [_ Hl256]]]]]]]]]]]]]].
  destruct (isLowStop_false_ne l ltac:(lia) hlls) as [Hl10 [Hl32 [Hl95 [Hl35 Hl59]]]].
  destruct (low_beq_ft (runUntil 0 k0 s) l Hcode124 Hpc124 H7_124 Hl256 Hl35 Hl59 Hl10 Hl32 Hl95)
    as [HpcE [HmemE HothE]].
  set (sE0 := runUntil 0 10 (runUntil 0 k0 s)) in *.
  assert (HcodeE0 : CodeLoaded sE0) by
    (apply (CodeLoaded_eqmem (runUntil 0 k0 s)); [exact HmemE| exact Hcode124]).
  assert (H7E0 : rget sE0 7 = l) by (rewrite (HothE 7 ltac:(lia)); exact H7_124).
  destruct (low_parse sE0 l lo HcodeE0 HpcE H7E0 Hl256 hnl) as [k2 [Hk2 [HpcF [HmemF [_ HothF]]]]].
  set (sP := runUntil 0 k2 sE0) in *.
  assert (HmemP : sP.(mem) = s.(mem)) by (rewrite HmemF, HmemE, Hmem124; reflexivity).
  assert (HcodeP : CodeLoaded sP) by (apply (CodeLoaded_eqmem s); [exact HmemP| destruct inv0 as [_ Hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact Hc]).
  assert (H6P : rget sP 6 = Z.of_nat (length emitted)) by
    (rewrite (HothF 6 ltac:(lia) ltac:(lia)), (HothE 6 ltac:(lia)); exact H6_124).
  assert (H13P : rget sP 13 = cap) by
    (rewrite (HothF 13 ltac:(lia) ltac:(lia)), (HothE 13 ltac:(lia)); exact H13_124).
  assert (H1P : rget sP 1 = 0) by
    (rewrite (HothF 1 ltac:(lia) ltac:(lia)), (HothE 1 ltac:(lia)); exact H1_124).
  pose proof (bgeu_ge_taken sP 208 6 13 (Z.of_nat (length emitted)) cap 68 (coreAddr + 276)
    HcodeP ltac:(lia) ltac:(rewrite coreBytes_len; lia) HpcF H6P H13P ltac:(lia)
    ltac:(vm_compute; reflexivity)
    ltac:(rewrite (wadd_id (coreAddr + 208) 68 ltac:(unfold coreAddr; lia)); lia)) as hbt.
  set (sS := setPc sP (coreAddr + 276)) in *.
  assert (HcodeS : CodeLoaded sS) by
    (apply (CodeLoaded_eqmem sP); [unfold sS; rewrite setPc_mem; reflexivity| exact HcodeP]).
  destruct (halt_epilogue sS 276 2 (Z.of_nat (length emitted)) HcodeS
    ltac:(lia) ltac:(rewrite coreBytes_len; lia) ltac:(unfold sS; apply setPc_pc)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(lia) ltac:(split; [apply Nat2Z.is_nonneg| exact (emitted_lt inp cap s (c :: l :: rest'') emitted inv)])
    ltac:(unfold sS; rewrite setPc_rget; exact H6P) ltac:(unfold sS; rewrite setPc_rget; exact H1P))
    as [Hhp [Hha0 [Hha1 Hhm]]].
  pose (bs := emitted ++ (hi * 16 + lo)%nat :: fst (decodeS High (zin rest''))).
  pose (st := snd (decodeS High (zin rest''))).
  destruct inv0 as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Houtmem Hspec].
  assert (hdec : Spec.decode (zin inp) = (bs, st)).
  { unfold Spec.decode, bs, st. rewrite Hspec.
    change (zin (c :: l :: rest'')) with (Z.to_nat c :: Z.to_nat l :: zin rest'').
    rewrite (decodeS_byte (Z.to_nat c) (Z.to_nat l) (zin rest'') hi lo hsc hss hnh hlls hnl).
    reflexivity. }
  assert (hbslen : (Z.to_nat cap < length bs)%nat) by
    (unfold bs; rewrite app_length; simpl; lia).
  assert (htake : firstn (Z.to_nat cap) bs = emitted).
  { rewrite <- heq. unfold bs. rewrite firstn_app, Nat.sub_diag, firstn_all. simpl firstn.
    rewrite app_nil_r. reflexivity. }
  exists (k0 + (10 + (k2 + (1 + 3))))%nat. split; [simpl length; lia|].
  assert (hchain : runUntil 0 (k0 + (10 + (k2 + (1 + 3)))) s = runUntil 0 3 sS).
  { rewrite (runUntil_add k0 (10 + (k2 + (1 + 3)))), (runUntil_add 10 (k2 + (1 + 3))),
            (runUntil_add k2 (1 + 3)). fold sE0. fold sP.
    rewrite (runUntil_add 1 3), hbt. reflexivity. }
  rewrite hchain.
  apply (short_result (runUntil 0 3 sS) inp cap emitted bs st).
  - exact Hhp.
  - rewrite Hha0. reflexivity.
  - rewrite Hha1. rewrite heq. reflexivity.
  - intros j hj. rewrite Hhm. unfold sS. rewrite setPc_mem, HmemP. apply Houtmem. lia.
  - exact hdec.
  - exact hbslen.
  - exact htake.
Qed.

(* A COMPLETE main-loop iteration for a byte token (high nibble [c]=hi, low
   nibble [l]=lo, capacity to spare): emits [hi*16+lo] and returns to LOOP with
   the suffix one shorter and one more emitted byte.  Mirror of Lean [loop_byte]. *)
Lemma loop_byte inp cap c hi l lo rest'' emitted s :
  isComment (Z.to_nat c) = false -> isSpace (Z.to_nat c) = false -> nibble (Z.to_nat c) = Some hi ->
  isLowStop (Z.to_nat l) = false -> nibble (Z.to_nat l) = Some lo ->
  Z.of_nat (length emitted) < cap ->
  LoopInv inp cap s (c :: l :: rest'') emitted ->
  exists k, (k <= 50 * (length (c :: l :: rest'') - length rest''))%nat /\
            LoopInv inp cap (runUntil 0 k s) rest'' (emitted ++ (hi * 16 + lo)%nat :: nil).
Proof.
  intros hsc hss hnh hlls hnl hcap inv. pose proof inv as inv0.
  destruct (reach124 inp cap c hi l rest'' emitted s hsc hss hnh inv)
    as [k0 [Hk0 [Hpc124 [H7_124 [Hcode124 [Hmem124 [H6_124 [H1_124 [H13_124 [H12_124 [H29_124
        [H5_124 [H10_124 [H11_124 Hl256]]]]]]]]]]]]]].
  destruct (isLowStop_false_ne l ltac:(lia) hlls) as [Hl10 [Hl32 [Hl95 [Hl35 Hl59]]]].
  destruct (low_beq_ft (runUntil 0 k0 s) l Hcode124 Hpc124 H7_124 Hl256 Hl35 Hl59 Hl10 Hl32 Hl95)
    as [HpcE [HmemE HothE]].
  set (sE0 := runUntil 0 10 (runUntil 0 k0 s)) in *.
  assert (HcodeE0 : CodeLoaded sE0) by
    (apply (CodeLoaded_eqmem (runUntil 0 k0 s)); [exact HmemE| exact Hcode124]).
  assert (H7E0 : rget sE0 7 = l) by (rewrite (HothE 7 ltac:(lia)); exact H7_124).
  destruct (low_parse sE0 l lo HcodeE0 HpcE H7E0 Hl256 hnl) as [k2 [Hk2 [HpcF [HmemF [H30F HothF]]]]].
  set (sP := runUntil 0 k2 sE0) in *.
  assert (HmemP : sP.(mem) = s.(mem)) by (rewrite HmemF, HmemE, Hmem124; reflexivity).
  destruct inv0 as [_ Hcode_s _ _ _ _ _ Hinmem Hinlt Hbytes Hinfits Houtlt _ Hsuf _ _ Houtmem Hspec].
  assert (HcodeP : CodeLoaded sP) by (apply (CodeLoaded_eqmem s); [exact HmemP| exact Hcode_s]).
  assert (H6P : rget sP 6 = Z.of_nat (length emitted)) by
    (rewrite (HothF 6 ltac:(lia) ltac:(lia)), (HothE 6 ltac:(lia)); exact H6_124).
  assert (H13P : rget sP 13 = cap) by
    (rewrite (HothF 13 ltac:(lia) ltac:(lia)), (HothE 13 ltac:(lia)); exact H13_124).
  assert (H12P : rget sP 12 = outAddr) by
    (rewrite (HothF 12 ltac:(lia) ltac:(lia)), (HothE 12 ltac:(lia)); exact H12_124).
  assert (H29P : rget sP 29 = Z.of_nat hi) by
    (rewrite (HothF 29 ltac:(lia) ltac:(lia)), (HothE 29 ltac:(lia)); exact H29_124).
  assert (H10P : rget sP 10 = inputAddr) by
    (rewrite (HothF 10 ltac:(lia) ltac:(lia)), (HothE 10 ltac:(lia)); exact H10_124).
  assert (H11P : rget sP 11 = Z.of_nat (length inp)) by
    (rewrite (HothF 11 ltac:(lia) ltac:(lia)), (HothE 11 ltac:(lia)); exact H11_124).
  assert (H5P : rget sP 5 = Z.of_nat (length inp) - Z.of_nat (length rest'')) by
    (rewrite (HothF 5 ltac:(lia) ltac:(lia)), (HothE 5 ltac:(lia)); exact H5_124).
  assert (H1P : rget sP 1 = 0) by
    (rewrite (HothF 1 ltac:(lia) ltac:(lia)), (HothE 1 ltac:(lia)); exact H1_124).
  assert (hhi16 : (hi < 16)%nat) by (apply (nibble_lt (Z.to_nat c)); exact hnh).
  assert (hlo16 : (lo < 16)%nat) by (apply (nibble_lt (Z.to_nat l)); exact hnl).
  destruct (store_epilogue sP hi lo (length emitted) cap HcodeP HpcF H6P H13P H12P H29P H30F
    hhi16 hlo16 hcap Houtlt) as [k3 [Hk3 [HpcSF [H6SF [HothSF HmemSF]]]]].
  set (sF := runUntil 0 k3 sP) in *.
  exists (k0 + (10 + (k2 + k3)))%nat. split; [simpl length; lia|].
  assert (hchain : runUntil 0 (k0 + (10 + (k2 + k3))) s = sF).
  { rewrite (runUntil_add k0 (10 + (k2 + k3))), (runUntil_add 10 (k2 + k3)), (runUntil_add k2 k3).
    fold sE0. fold sP. reflexivity. }
  assert (hge2 : (length (c :: l :: rest'') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl |- *. lia. }
  rewrite hchain.
  refine {| li_at_loop := HpcSF; li_code := _; li_a0 := _; li_a1 := _; li_a2 := _;
            li_a3 := _; li_ra := _; li_in_mem := _; li_in_lt := Hinlt;
            li_bytes := Hbytes; li_in_fits := Hinfits; li_out_lt := Houtlt;
            li_idx := _; li_suffix := _; li_outidx := _; li_emit_le := _;
            li_out_mem := _; li_spec := _ |}.
  - intros i Hi. assert (hile : i < 324) by (rewrite coreBytes_len in Hi; lia).
    rewrite HmemSF. replace ((coreAddr + i) =? (outAddr + Z.of_nat (length emitted))) with false
      by (symmetry; apply Z.eqb_neq; unfold coreAddr, outAddr; lia).
    rewrite HmemP. exact (Hcode_s i Hi).
  - rewrite (HothSF 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact H10P.
  - rewrite (HothSF 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact H11P.
  - rewrite (HothSF 12 ltac:(lia) ltac:(lia) ltac:(lia)); exact H12P.
  - rewrite (HothSF 13 ltac:(lia) ltac:(lia) ltac:(lia)); exact H13P.
  - rewrite (HothSF 1 ltac:(lia) ltac:(lia) ltac:(lia)); exact H1P.
  - intros j hj. rewrite HmemSF.
    replace ((inputAddr + j) =? (outAddr + Z.of_nat (length emitted))) with false
      by (symmetry; apply Z.eqb_neq; unfold inputAddr, outAddr in *; lia).
    rewrite HmemP. exact (Hinmem j hj).
  - rewrite (HothSF 5 ltac:(lia) ltac:(lia) ltac:(lia)); exact H5P.
  - replace (length inp - length rest'')%nat with (2 + (length inp - length (c :: l :: rest'')))%nat
      by (simpl length in hge2 |- *; lia).
    rewrite <- (skipn_skipn 2 (length inp - length (c :: l :: rest'')) inp), Hsuf. reflexivity.
  - rewrite H6SF, app_length. simpl length. reflexivity.
  - rewrite app_length. simpl length. lia.
  - intros j hj. rewrite app_length in hj. simpl length in hj. rewrite HmemSF.
    destruct (Nat.eq_dec j (length emitted)) as [Heq|Hne].
    + subst j. replace ((outAddr + Z.of_nat (length emitted)) =? (outAddr + Z.of_nat (length emitted)))
        with true by (symmetry; apply Z.eqb_eq; reflexivity).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    + replace ((outAddr + Z.of_nat j) =? (outAddr + Z.of_nat (length emitted))) with false
        by (symmetry; apply Z.eqb_neq; lia).
      rewrite HmemP, app_nth1 by lia. exact (Houtmem j ltac:(lia)).
  - destruct (decodeS High (zin rest'')) as [out st] eqn:Erest.
    rewrite Hspec. change (zin (c :: l :: rest'')) with (Z.to_nat c :: Z.to_nat l :: zin rest'').
    rewrite (decodeS_byte (Z.to_nat c) (Z.to_nat l) (zin rest'') hi lo hsc hss hnh hlls hnl), Erest.
    simpl. rewrite <- app_assoc. reflexivity.
Qed.

(** ** The comment branch (mirror of comment_read/comment_loop/loop_comment). *)

(* The comment inner-loop head (offsets 236..248): bgeu(nt); add; lbu (read
   inp[idx]); li t3,10.  Reaches offset 252 with t2 = inp[idx], t3 = 10. *)
Lemma comment_read s inp idx ch :
  CodeLoaded s -> s.(pc) = coreAddr + 236 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = inputAddr -> rget s 11 = Z.of_nat (length inp) -> (idx < length inp)%nat ->
  inputAddr + Z.of_nat (length inp) < 2 ^ 64 ->
  (forall j, 0 <= j < Z.of_nat (length inp) -> s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0) ->
  nth idx inp 0 = ch -> 0 <= ch < 256 ->
  (runUntil 0 4 s).(pc) = coreAddr + 252 /\ rget (runUntil 0 4 s) 7 = ch /\
  rget (runUntil 0 4 s) 28 = 10 /\ rget (runUntil 0 4 s) 5 = Z.of_nat idx /\
  (runUntil 0 4 s).(mem) = s.(mem) /\ CodeLoaded (runUntil 0 4 s) /\
  (forall i, i <> 7 -> i <> 28 -> rget (runUntil 0 4 s) i = rget s i).
Proof.
  intros hcode hpc Hidx Ha0 Ha1 hlt hin_fit Hinmem Hch Hcr.
  assert (hult : ultb (rget s 5) (rget s 11) = true)
    by (rewrite Hidx, Ha1; unfold ultb; apply Z.ltb_lt; apply Nat2Z.inj_lt; exact hlt).
  assert (hs1 : step s = setPc s (coreAddr + 240)).
  { rewrite (step_bgeu s 236 5 11 28 hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc
      ltac:(vm_compute; reflexivity)), hult. cbn match.
    rewrite hpc, (wadd_id (coreAddr + 236) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc s (coreAddr + 240)) in *.
  assert (hc1 : CodeLoaded s1) by
    (apply (CodeLoaded_eqmem s); [unfold s1; rewrite setPc_mem; reflexivity| exact hcode]).
  assert (hpc1 : s1.(pc) = coreAddr + 240) by reflexivity.
  assert (haddr : wadd (rget s1 10) (rget s1 5) = inputAddr + Z.of_nat idx).
  { unfold s1. rewrite !setPc_rget, Ha0, Hidx. apply wadd_id. unfold inputAddr in *; lia. }
  assert (hs2 : step s1 = setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + 244)).
  { rewrite (step_add s1 240 28 10 5 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
      ltac:(vm_compute; reflexivity)), haddr, hpc1,
      (wadd_id (coreAddr + 240) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 28 (inputAddr + Z.of_nat idx)) (coreAddr + 244)) in *.
  assert (hmem2 : s2.(mem) = s.(mem))
    by (unfold s2, s1; rewrite setPc_mem, rset_mem, setPc_mem; reflexivity).
  assert (hc2 : CodeLoaded s2) by (apply (CodeLoaded_eqmem s); [exact hmem2| exact hcode]).
  assert (hpc2 : s2.(pc) = coreAddr + 244) by reflexivity.
  assert (hr28 : rget s2 28 = inputAddr + Z.of_nat idx) by
    (unfold s2; rewrite setPc_rget, (rset_rget s1 28 _ 28 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
  assert (hbyte : s2.(mem) (wadd (rget s2 28) 0) mod 256 = ch).
  { rewrite hr28, (wadd_id (inputAddr + Z.of_nat idx) 0 ltac:(unfold inputAddr in *; lia)), Z.add_0_r,
      hmem2, (Hinmem (Z.of_nat idx) ltac:(split; [lia| apply Nat2Z.inj_lt; exact hlt])), Nat2Z.id, Hch.
    apply Z.mod_small. exact Hcr. }
  assert (hs3 : step s2 = setPc (rset s2 7 ch) (coreAddr + 248)).
  { rewrite (step_lbu s2 244 7 28 0 hc2 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc2
      ltac:(vm_compute; reflexivity)), hbyte, hpc2,
      (wadd_id (coreAddr + 244) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s3 := setPc (rset s2 7 ch) (coreAddr + 248)) in *.
  assert (hmem3 : s3.(mem) = s.(mem)) by (unfold s3; rewrite setPc_mem, rset_mem; exact hmem2).
  assert (hc3 : CodeLoaded s3) by (apply (CodeLoaded_eqmem s); [exact hmem3| exact hcode]).
  assert (hpc3 : s3.(pc) = coreAddr + 248) by reflexivity.
  assert (hs4 : step s3 = setPc (rset s3 28 10) (coreAddr + 252)).
  { rewrite (step_addi s3 248 28 0 10 hc3 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc3
      ltac:(vm_compute; reflexivity)), rget_zero, (wadd_id 0 10 ltac:(lia)), Z.add_0_l, hpc3,
      (wadd_id (coreAddr + 248) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s4 := setPc (rset s3 28 10) (coreAddr + 252)) in *.
  assert (hmem4 : s4.(mem) = s.(mem)) by (unfold s4; rewrite setPc_mem, rset_mem; exact hmem3).
  assert (hp0 : s.(pc) <> 0) by (rewrite hpc; apply coreAddr_pos; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hp2 : s2.(pc) <> 0) by (rewrite hpc2; apply coreAddr_pos; lia).
  assert (hp3 : s3.(pc) <> 0) by (rewrite hpc3; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 4 s = s4).
  { rewrite (runUntil_S 3 s hp0), hs1, (runUntil_S 2 s1 hp1), hs2,
            (runUntil_S 1 s2 hp2), hs3, (runUntil_S 0 s3 hp3), hs4. reflexivity. }
  rewrite hrun. repeat apply conj.
  - unfold s4; apply setPc_pc.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 7 ltac:(lia) ltac:(lia)).
    replace (7 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 7 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 28 ltac:(lia) ltac:(lia)), Z.eqb_refl. reflexivity.
  - unfold s4. rewrite setPc_rget, (rset_rget s3 28 10 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s3. rewrite setPc_rget, (rset_rget s2 7 ch 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 7) with false by reflexivity.
    unfold s2. rewrite setPc_rget, (rset_rget s1 28 _ 5 ltac:(lia) ltac:(lia)).
    replace (5 =? 28) with false by reflexivity.
    unfold s1. rewrite setPc_rget. exact Hidx.
  - exact hmem4.
  - apply (CodeLoaded_eqmem s); [exact hmem4| exact hcode].
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

Lemma skipComment_cons_eq c rest : (c =? c_nl)%nat = true -> skipComment (c :: rest) = rest.
Proof. intros H. simpl. rewrite H. reflexivity. Qed.

Lemma skipComment_cons_ne c rest : (c =? c_nl)%nat = false -> skipComment (c :: rest) = skipComment rest.
Proof. intros H. simpl. rewrite H. reflexivity. Qed.

Lemma skipn_cons_nth {A} (d : A) : forall idx (l : list A),
  (idx < length l)%nat -> skipn idx l = nth idx l d :: skipn (S idx) l.
Proof.
  induction idx; intros l Hl.
  - destruct l; [simpl in Hl; lia| reflexivity].
  - destruct l; [simpl in Hl; lia| simpl; apply IHidx; simpl in Hl; lia].
Qed.

(* The comment inner loop (.Lcomment, offsets 236..260): scan [inp] from [idx]
   one char/turn to the first newline or EOF.  Either it reaches LOOP on the
   newline at position q (so the main loop skips it as a space), or it reaches
   .Lok (264) at EOF.  Induction on the scanned span.  Mirror of [comment_loop]. *)
Lemma comment_loop inp : forall n s idx,
  CodeLoaded s -> s.(pc) = coreAddr + 236 -> rget s 5 = Z.of_nat idx ->
  rget s 10 = inputAddr -> rget s 11 = Z.of_nat (length inp) ->
  (forall j, 0 <= j < Z.of_nat (length inp) -> s.(mem) (inputAddr + j) = nth (Z.to_nat j) inp 0) ->
  inputAddr + Z.of_nat (length inp) < 2 ^ 64 -> (forall b, In b inp -> 0 <= b < 256) ->
  (idx <= length inp)%nat -> (length inp - idx <= n)%nat ->
  exists k,
    (exists q, (idx <= q < length inp)%nat /\ (k <= 7 * (q - idx) + 5)%nat /\ nth q inp 0 = 10 /\
        skipComment (zin (skipn idx inp)) = zin (skipn (S q) inp) /\
        (runUntil 0 k s).(pc) = coreAddr + 8 /\ rget (runUntil 0 k s) 5 = Z.of_nat q /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i))
    \/ ((k <= 7 * (length inp - idx) + 1)%nat /\ skipComment (zin (skipn idx inp)) = nil /\
        (runUntil 0 k s).(pc) = coreAddr + 264 /\ rget (runUntil 0 k s) 5 = Z.of_nat (length inp) /\
        (runUntil 0 k s).(mem) = s.(mem) /\
        (forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget (runUntil 0 k s) i = rget s i)).
Proof.
  induction n; intros s idx hcode hpc Hidx Ha0 Ha1 Hinmem hin_fit Hbytes Hle Hn.
  - (* idx = length inp *)
    assert (hidxeq : idx = length inp) by lia. subst idx.
    pose proof (bgeu_ge_taken s 236 5 11 (Z.of_nat (length inp)) (Z.of_nat (length inp)) 28
      (coreAddr + 264) hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc Hidx Ha1 ltac:(lia)
      ltac:(vm_compute; reflexivity)
      ltac:(rewrite (wadd_id (coreAddr + 236) 28 ltac:(unfold coreAddr; lia)); lia)) as hbt.
    exists 1%nat. right. rewrite hbt. repeat apply conj.
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
      destruct (comment_read s inp idx (nth idx inp 0) hcode hpc Hidx Ha0 Ha1 Hlt hin_fit Hinmem
        eq_refl Hch256) as [hpc4 [h7_4 [h28_4 [h5_4 [hmem4 [hcode4 hoth4]]]]]].
      set (s4 := runUntil 0 4 s) in *.
      destruct (Z.eq_dec (nth idx inp 0) 10) as [Hnl|Hnnl].
      * (* newline at idx -> LOOP *)
        assert (hbeq : step s4 = setPc s4 (coreAddr + 8)).
        { rewrite (step_beq s4 252 7 28 (-244) hcode4 ltac:(lia) ltac:(rewrite coreBytes_len; lia)
            hpc4 ltac:(vm_compute; reflexivity)), h7_4, h28_4, Hnl, Z.eqb_refl, hpc4,
            (wadd_id (coreAddr + 252) (-244) ltac:(unfold coreAddr; lia)). reflexivity. }
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; apply coreAddr_pos; lia).
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
        (* step 5: beq not taken -> 256 *)
        assert (hbeq : step s4 = setPc s4 (coreAddr + 256)).
        { rewrite (step_beq s4 252 7 28 (-244) hcode4 ltac:(lia) ltac:(rewrite coreBytes_len; lia)
            hpc4 ltac:(vm_compute; reflexivity)), h7_4, h28_4.
          replace (nth idx inp 0 =? 10) with false by (symmetry; apply Z.eqb_neq; exact Hnnl).
          rewrite hpc4, (wadd_id (coreAddr + 252) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
        set (v5 := setPc s4 (coreAddr + 256)) in *.
        assert (hc5 : CodeLoaded v5) by
          (apply (CodeLoaded_eqmem s4); [unfold v5; rewrite setPc_mem; reflexivity| exact hcode4]).
        assert (hpc5 : v5.(pc) = coreAddr + 256) by reflexivity.
        assert (h5v5 : rget v5 5 = Z.of_nat idx) by (unfold v5; rewrite setPc_rget; exact h5_4).
        (* step 6: addi t0,t0,1 -> 260 *)
        assert (haddi : step v5 = setPc (rset v5 5 (Z.of_nat (S idx))) (coreAddr + 260)).
        { rewrite (step_addi v5 256 5 5 1 hc5 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc5
            ltac:(vm_compute; reflexivity)), h5v5,
            (wadd_id (Z.of_nat idx) 1 ltac:(unfold inputAddr in *; lia)), hpc5,
            (wadd_id (coreAddr + 256) 4 ltac:(unfold coreAddr; lia)).
          rewrite Nat2Z.inj_succ. reflexivity. }
        set (v6 := setPc (rset v5 5 (Z.of_nat (S idx))) (coreAddr + 260)) in *.
        assert (hc6 : CodeLoaded v6) by
          (apply (CodeLoaded_eqmem s4); [unfold v6, v5; rewrite !setPc_mem, rset_mem; reflexivity| exact hcode4]).
        assert (hpc6 : v6.(pc) = coreAddr + 260) by reflexivity.
        (* step 7: jal -> 236 *)
        assert (hjal : step v6 = setPc v6 (coreAddr + 236)).
        { rewrite (step_jal v6 260 0 (-24) hc6 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc6
            ltac:(vm_compute; reflexivity)).
          assert (Hr0 : rset v6 0 (wadd v6.(pc) 4) = v6) by (unfold rset; reflexivity).
          rewrite Hr0, hpc6, (wadd_id (coreAddr + 260) (-24) ltac:(unfold coreAddr; lia)). reflexivity. }
        set (s' := setPc v6 (coreAddr + 236)) in *.
        assert (hp4 : s4.(pc) <> 0) by (rewrite hpc4; apply coreAddr_pos; lia).
        assert (hp5 : v5.(pc) <> 0) by (rewrite hpc5; apply coreAddr_pos; lia).
        assert (hp6 : v6.(pc) <> 0) by (rewrite hpc6; apply coreAddr_pos; lia).
        assert (hrun3 : runUntil 0 3 s4 = s').
        { rewrite (runUntil_S 2 s4 hp4), hbeq, (runUntil_S 1 v5 hp5), haddi,
                  (runUntil_S 0 v6 hp6), hjal. reflexivity. }
        assert (hmems' : s'.(mem) = s.(mem))
          by (unfold s', v6, v5; rewrite !setPc_mem, rset_mem, setPc_mem; exact hmem4).
        assert (hcs' : CodeLoaded s') by (apply (CodeLoaded_eqmem s); [exact hmems'| exact hcode]).
        assert (hpcs' : s'.(pc) = coreAddr + 236) by reflexivity.
        assert (h5s' : rget s' 5 = Z.of_nat (S idx)) by
          (unfold s'; rewrite setPc_rget; unfold v6;
           rewrite setPc_rget, (rset_rget v5 5 _ 5 ltac:(lia) ltac:(lia)), Z.eqb_refl; reflexivity).
        assert (hother' : forall i, i <> 5 -> i <> 7 -> i <> 28 -> rget s' i = rget s i).
        { intros i h5 h7 h28. unfold s'. rewrite setPc_rget. unfold v6.
          destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
          apply Z.eqb_neq in E0. rewrite setPc_rget, (rset_rget v5 5 _ i ltac:(lia) E0).
          replace (i =? 5) with false by (symmetry; apply Z.eqb_neq; exact h5).
          unfold v5. rewrite setPc_rget. exact (hoth4 i h7 h28). }
        assert (h10s' : rget s' 10 = inputAddr) by
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
    + (* idx >= length inp -> idx = length inp *)
      assert (hidxeq : idx = length inp) by lia. subst idx.
      pose proof (bgeu_ge_taken s 236 5 11 (Z.of_nat (length inp)) (Z.of_nat (length inp)) 28
        (coreAddr + 264) hcode ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc Hidx Ha1 ltac:(lia)
        ltac:(vm_compute; reflexivity)
        ltac:(rewrite (wadd_id (coreAddr + 236) 28 ltac:(unfold coreAddr; lia)); lia)) as hbt.
      exists 1%nat. right. rewrite hbt. repeat apply conj.
      * lia.
      * rewrite skipn_all. reflexivity.
      * apply setPc_pc.
      * rewrite setPc_rget. exact Hidx.
      * apply setPc_mem.
      * intros i _ _ _. apply setPc_rget.
Qed.

Lemma isComment_cases c : 0 <= c -> isComment (Z.to_nat c) = true -> c = 35 \/ c = 59.
Proof.
  intros h0 hc. unfold isComment, c_hash, c_semi in hc. rewrite !orb_true_iff, !Nat.eqb_eq in hc.
  assert (Hid : c = Z.of_nat (Z.to_nat c)) by (rewrite Z2Nat.id; [reflexivity| exact h0]).
  destruct hc as [H|H]; [left|right]; rewrite Hid, H; reflexivity.
Qed.

(* The comment case: head char [c] is #/;.  Reads [c], dispatches to .Lcomment,
   scans to the newline ([comment_loop]).  Newline -> back to LOOP on it (suffix
   shrinks, invariant rebuilt via decodeS_comment + the newline being a space);
   EOF -> halt Ok.  Mirror of Lean [loop_comment]. *)
Lemma loop_comment inp cap c rest' emitted s :
  isComment (Z.to_nat c) = true ->
  LoopInv inp cap s (c :: rest') emitted ->
  exists k, (exists rest'' emitted', (length rest'' < length (c :: rest'))%nat /\
              (k <= 50 * (length (c :: rest') - length rest''))%nat /\
              LoopInv inp cap (runUntil 0 k s) rest'' emitted')
         \/ ((k <= 50 * length (c :: rest'))%nat /\ Result (runUntil 0 k s) inp cap).
Proof.
  intros hcm inv. pose proof inv as inv0.
  destruct (loopinv_head inp cap c rest' emitted s inv) as [Hin Hc].
  destruct (loop_prefix inp cap c rest' emitted s inv) as [hpc4 [ht2 [ht0 [hmem4 [hcode4 hoth4]]]]].
  set (s4 := runUntil 0 4 s) in *.
  assert (Hreach236 : exists kb, (kb <= 4)%nat /\ (runUntil 0 kb s4).(pc) = coreAddr + 236 /\
      (runUntil 0 kb s4).(mem) = s4.(mem) /\ rget (runUntil 0 kb s4) 5 = rget s4 5 /\
      (forall i, i <> 28 -> rget (runUntil 0 kb s4) i = rget s4 i)).
  { destruct (isComment_cases c ltac:(lia) hcm) as [Hc35|Hc59].
    - exists 2%nat. split; [lia|]. rewrite (li_beq_eq s4 24 35 c 208 (coreAddr + 236) hcode4 ltac:(lia)
        ltac:(rewrite coreBytes_len; lia) hpc4 ht2 ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(lia) Hc35
        ltac:(rewrite (wadd_id (coreAddr + (24 + 4)) 208 ltac:(unfold coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem; reflexivity.
      + apply (li_block_frame s4 35 (coreAddr + 236) 5 ltac:(lia)).
      + intros i hi. apply (li_block_frame s4 35 (coreAddr + 236) i hi).
    - exists (2 + 2)%nat. split; [lia|].
      rewrite (runUntil_add 2 2),
        (li_beq_ne s4 24 35 c 208 hcode4 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc4 ht2
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)).
      set (sb := setPc (rset s4 28 35) (coreAddr + (24 + 8))) in *.
      assert (hcb : CodeLoaded sb) by
        (apply (CodeLoaded_eqmem s4); [unfold sb; rewrite setPc_mem, rset_mem; reflexivity| exact hcode4]).
      assert (hpcb : sb.(pc) = coreAddr + 32) by (unfold sb; reflexivity).
      assert (h7b : rget sb 7 = c) by
        (unfold sb; rewrite (li_block_frame s4 35 (coreAddr + (24 + 8)) 7 ltac:(lia)); exact ht2).
      rewrite (li_beq_eq sb 32 59 c 200 (coreAddr + 236) hcb ltac:(lia) ltac:(rewrite coreBytes_len; lia)
        hpcb h7b ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) Hc59
        ltac:(rewrite (wadd_id (coreAddr + (32 + 4)) 200 ltac:(unfold coreAddr; lia)); lia)).
      repeat apply conj.
      + apply setPc_pc.
      + rewrite setPc_mem, rset_mem. unfold sb. rewrite setPc_mem, rset_mem; reflexivity.
      + rewrite (li_block_frame sb 59 (coreAddr + 236) 5 ltac:(lia)).
        unfold sb. apply (li_block_frame s4 35 (coreAddr + (24 + 8)) 5 ltac:(lia)).
      + intros i hi. rewrite (li_block_frame sb 59 (coreAddr + 236) i hi).
        unfold sb. apply (li_block_frame s4 35 (coreAddr + (24 + 8)) i hi). }
  destruct Hreach236 as [kb [Hkbb [Hpc236 [Hmem236 [H5_236 Hother236]]]]].
  set (s236 := runUntil 0 kb s4) in *.
  destruct inv0 as [_ _ Ha0 Ha1 _ _ Hra Hinmem Hinlt Hbytes Hinfits Houtlt Hidx Hsuf Houtidx
                    Hemitle Houtmem Hspec].
  set (idx0 := (length inp - length rest')%nat) in *.
  assert (hge1 : (length (c :: rest') <= length inp)%nat).
  { pose proof (f_equal (@length Z) Hsuf) as Hl. rewrite length_skipn in Hl.
    simpl length in Hl |- *. lia. }
  assert (Hskipidx0 : skipn idx0 inp = rest').
  { unfold idx0. replace (length inp - length rest')%nat
      with (1 + (length inp - length (c :: rest')))%nat by (simpl length in hge1 |- *; lia).
    rewrite <- (skipn_skipn 1 (length inp - length (c :: rest')) inp), Hsuf. reflexivity. }
  assert (H5idx0 : rget s236 5 = Z.of_nat idx0).
  { rewrite H5_236, ht0, Hidx. unfold idx0.
    rewrite Nat2Z.inj_sub by (simpl length in hge1; lia). simpl length. lia. }
  assert (H10_236 : rget s236 10 = inputAddr) by
    (rewrite (Hother236 10 ltac:(lia)), (hoth4 10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha0).
  assert (H11_236 : rget s236 11 = Z.of_nat (length inp)) by
    (rewrite (Hother236 11 ltac:(lia)), (hoth4 11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha1).
  assert (Hmem236s : s236.(mem) = s.(mem)) by (rewrite Hmem236, hmem4; reflexivity).
  assert (Hcode236 : CodeLoaded s236) by
    (apply (CodeLoaded_eqmem s); [exact Hmem236s|
       destruct inv as [_ Hcs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact Hcs]).
  destruct (comment_loop inp (length inp - idx0) s236 idx0 Hcode236 Hpc236 H5idx0 H10_236 H11_236
    ltac:(intros j hj; rewrite Hmem236s; exact (Hinmem j hj)) Hinlt Hbytes ltac:(lia) ltac:(lia))
    as [kc [[q [Hq1 [Hkbc [Hq2 [Hqskip [Hppc [H5q [Hmemq Hothq]]]]]]]]|
            [Hkbc [Hskip0 [Hppc [H5q [Hmemq Hothq]]]]]]].
  - (* newline at q -> LOOP on the newline *)
    exists (4 + (kb + kc))%nat. left. exists (skipn q inp). exists emitted.
    assert (hbig : runUntil 0 (4 + (kb + kc)) s = runUntil 0 kc s236)
      by (rewrite (runUntil_add 4 (kb + kc)); fold s4; rewrite (runUntil_add kb kc); reflexivity).
    rewrite hbig.
    assert (Hdropq : skipn q inp = nth q inp 0 :: skipn (S q) inp) by (apply skipn_cons_nth; lia).
    assert (hkey : decodeS High (zin (skipn q inp)) = decodeS High (zin (c :: rest'))).
    { change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      rewrite (decodeS_comment (Z.to_nat c) (zin rest') hcm).
      rewrite <- Hskipidx0, Hqskip, Hdropq.
      change (zin (nth q inp 0 :: skipn (S q) inp))
        with (Z.to_nat (nth q inp 0) :: zin (skipn (S q) inp)).
      rewrite Hq2. change (Z.to_nat 10) with 10%nat.
      rewrite (decodeS_spacing 10 (zin (skipn (S q) inp)) ltac:(reflexivity) ltac:(reflexivity)).
      reflexivity. }
    assert (hother : forall i, i <> 5 -> i <> 7 -> i <> 28 ->
              rget (runUntil 0 kc s236) i = rget s i).
    { intros i h5 h7 h28.
      destruct (i =? 0) eqn:E0; [apply Z.eqb_eq in E0; subst i; reflexivity|].
      apply Z.eqb_neq in E0.
      rewrite (Hothq i h5 h7 h28), (Hother236 i h28), (hoth4 i E0 h5 h7 h28). reflexivity. }
    split; [|split].
    + rewrite length_skipn. unfold idx0 in Hq1. simpl length in hge1 |- *. lia.
    + rewrite length_skipn. simpl length. unfold idx0 in Hq1, Hkbc. simpl length in hge1. lia.
    + refine {| li_at_loop := Hppc; li_code := _; li_a0 := _; li_a1 := _; li_a2 := _;
                li_a3 := _; li_ra := _; li_in_mem := _; li_in_lt := Hinlt;
                li_bytes := Hbytes; li_in_fits := Hinfits; li_out_lt := Houtlt;
                li_idx := _; li_suffix := _; li_outidx := _; li_emit_le := Hemitle;
                li_out_mem := _; li_spec := _ |}.
      * intros i Hi. rewrite Hmemq, Hmem236s.
        destruct inv as [_ Hcs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. exact (Hcs i Hi).
      * rewrite (hother 10 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha0.
      * rewrite (hother 11 ltac:(lia) ltac:(lia) ltac:(lia)); exact Ha1.
      * rewrite (hother 12 ltac:(lia) ltac:(lia) ltac:(lia)).
        destruct inv as [_ _ _ _ Hcs _ _ _ _ _ _ _ _ _ _ _ _ _]. exact Hcs.
      * rewrite (hother 13 ltac:(lia) ltac:(lia) ltac:(lia)).
        destruct inv as [_ _ _ _ _ Hcs _ _ _ _ _ _ _ _ _ _ _ _]. exact Hcs.
      * rewrite (hother 1 ltac:(lia) ltac:(lia) ltac:(lia)); exact Hra.
      * intros j hj. rewrite Hmemq, Hmem236s. exact (Hinmem j hj).
      * rewrite H5q, length_skipn, Nat2Z.inj_sub by lia. lia.
      * rewrite length_skipn. replace (length inp - (length inp - q))%nat with q by lia. reflexivity.
      * rewrite (hother 6 ltac:(lia) ltac:(lia) ltac:(lia)); exact Houtidx.
      * intros j hj. rewrite Hmemq, Hmem236s. exact (Houtmem j hj).
      * rewrite Hspec, hkey. reflexivity.
  - (* EOF (no newline) -> .Lok, Ok *)
    assert (hbig : runUntil 0 (4 + (kb + kc)) s = runUntil 0 kc s236)
      by (rewrite (runUntil_add 4 (kb + kc)); fold s4; rewrite (runUntil_add kb kc); reflexivity).
    assert (hdec : Spec.decode (zin inp) = (emitted, Ok)).
    { unfold Spec.decode. rewrite Hspec.
      change (zin (c :: rest')) with (Z.to_nat c :: zin rest').
      rewrite (decodeS_comment (Z.to_nat c) (zin rest') hcm), <- Hskipidx0, Hskip0, decodeS_nil.
      simpl. rewrite app_nil_r. reflexivity. }
    cut (exists m, (m <= 4 + (kb + kc) + 3)%nat /\ Result (runUntil 0 m s) inp cap).
    { intros [m [Hmb Hm]]. exists m. right. split; [unfold idx0 in Hkbc; simpl length; lia| exact Hm]. }
    apply (reach_error s (runUntil 0 kc s236) inp cap emitted 264 0 (4 + (kb + kc)) Ok).
    + exact hbig.
    + exact Hppc.
    + apply (CodeLoaded_eqmem s); [rewrite Hmemq, Hmem236s; reflexivity|
        destruct inv as [_ Hcs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]; exact Hcs].
    + rewrite Hmemq, Hmem236s; reflexivity.
    + rewrite (Hothq 6 ltac:(lia) ltac:(lia) ltac:(lia)), (Hother236 6 ltac:(lia)),
        (hoth4 6 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Houtidx.
    + rewrite (Hothq 1 ltac:(lia) ltac:(lia) ltac:(lia)), (Hother236 1 ltac:(lia)),
        (hoth4 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); exact Hra.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + lia.
    + rewrite coreBytes_len; lia.
    + lia.
    + exact (emitted_lt inp cap s (c :: rest') emitted inv).
    + reflexivity.
    + exact hdec.
    + exact Hemitle.
    + exact Houtmem.
Qed.

(* One iteration: consume >= 1 char in <= 50 steps/char, preserving LoopInv, or
   halt correctly. The per-token dispatch (FRONTIER) -- Admitted for now. *)
Theorem loop_iteration : forall inp cap rest emitted s,
  rest <> [] -> LoopInv inp cap s rest emitted ->
  exists k,
    (exists rest' emitted', (length rest' < length rest)%nat /\
        (k <= 50 * (length rest - length rest'))%nat /\
        LoopInv inp cap (runUntil 0 k s) rest' emitted')
    \/ ((k <= 50 * length rest)%nat /\ Result (runUntil 0 k s) inp cap).
Admitted.

(* The induction (PROVED): from any LoopInv state the machine halts correctly
   within [50 * |rest| + 4] steps. The fuel-bound (point 1) made fully explicit. *)
Theorem loop_correct : forall inp cap n rest emitted s,
  (length rest <= n)%nat -> LoopInv inp cap s rest emitted ->
  Result (runUntil 0 (50 * length rest + 4) s) inp cap.
Proof.
  intros inp cap n. induction n as [|n IH]; intros rest emitted s hn hinv.
  - assert (rest = []) by (destruct rest; [reflexivity| simpl in hn; lia]).
    subst rest. exact (eof_result inp cap emitted s hinv).
  - destruct rest as [|c rest''] eqn:Er.
    + exact (eof_result inp cap emitted s hinv).
    + destruct (loop_iteration inp cap (c :: rest'') emitted s ltac:(discriminate) hinv)
        as [k [ [rest' [emitted' [Hlt [Hkb Hinv']]]] | [Hkb Hres] ]].
      * (* continue: k <= 50*(|rest|-|rest'|) chars consumed *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        assert (HBle : (50 * length rest' + 4 <= A - k)%nat) by (unfold A; simpl length in *; lia).
        replace (A - k)%nat with ((50 * length rest' + 4) + ((A - k) - (50 * length rest' + 4)))%nat by lia.
        rewrite runUntil_add.
        assert (HIH : Result (runUntil 0 (50 * length rest' + 4) (runUntil 0 k s)) inp cap)
          by (apply (IH rest' emitted'); [simpl length in *; lia | exact Hinv']).
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ HIH)). exact HIH.
      * (* halt *)
        set (A := (50 * length (c :: rest'') + 4)%nat).
        assert (HkA : (k <= A)%nat) by (unfold A; lia).
        replace A with (k + (A - k))%nat by lia. rewrite runUntil_add.
        rewrite (runUntil_halt _ _ (Result_pc _ _ _ Hres)). exact Hres.
Qed.

(** ** Well-formedness: input region fits before the output region, etc. *)
Record WellFormed (inp : list Z) (cap : Z) : Prop := {
  in_fits  : inputAddr + Z.of_nat (length inp) <= outAddr;
  out_fits : outAddr + cap < 2 ^ 64;
  bytes_ok : forall b, In b inp -> 0 <= b < 256
}.

(** ** Prologue: from the initial state, `li t0,0; li t1,0` reach the loop head
    establishing the initial invariant (full input remaining, nothing emitted). *)
Theorem init_loopinv : forall inp cap, WellFormed inp cap ->
  LoopInv inp cap (runUntil 0 2 (mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr))) inp [].
Proof.
  intros inp cap HW. destruct HW as [Hfits Hfit2 Hbytes].
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)).
  assert (Hmem0 : init.(mem) = memWith inp inputAddr) by reflexivity.
  assert (Hpc0 : init.(pc) = coreAddr) by reflexivity.
  assert (Hcode0 : CodeLoaded init).
  { intros i Hi. rewrite coreBytes_len in Hi. rewrite Hmem0. unfold memWith.
    replace ((coreAddr <=? coreAddr + i) && (coreAddr + i <? coreAddr + Z.of_nat (length coreBytes)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; rewrite coreBytes_len; lia]).
    cbv iota. replace (coreAddr + i - coreAddr) with i by lia. unfold nthb. reflexivity. }
  assert (hs1 : step init = setPc (rset init 5 0) (coreAddr + 4)).
  { rewrite (step_addi init 0 5 0 0 Hcode0 ltac:(lia) ltac:(rewrite coreBytes_len; lia) Hpc0
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), Hpc0,
            (wadd_id coreAddr 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s1 := setPc (rset init 5 0) (coreAddr + 4)) in *.
  assert (hpc1 : s1.(pc) = coreAddr + 4) by reflexivity.
  assert (hc1 : CodeLoaded s1) by (apply (CodeLoaded_eqmem init); [reflexivity| exact Hcode0]).
  assert (hs2 : step s1 = setPc (rset s1 6 0) (coreAddr + 8)).
  { rewrite (step_addi s1 4 6 0 0 hc1 ltac:(lia) ltac:(rewrite coreBytes_len; lia) hpc1
              ltac:(vm_compute; reflexivity)).
    rewrite rget_zero, (wadd_id 0 0 ltac:(lia)), hpc1,
            (wadd_id (coreAddr+4) 4 ltac:(unfold coreAddr; lia)). reflexivity. }
  set (s2 := setPc (rset s1 6 0) (coreAddr + 8)) in *.
  assert (hp0 : init.(pc) <> 0) by (rewrite Hpc0; unfold coreAddr; lia).
  assert (hp1 : s1.(pc) <> 0) by (rewrite hpc1; apply coreAddr_pos; lia).
  assert (hrun : runUntil 0 2 init = s2)
    by (rewrite (runUntil_S 1 init hp0), hs1, (runUntil_S 0 s1 hp1), hs2; reflexivity).
  rewrite hrun.
  assert (Hmem2 : s2.(mem) = memWith inp inputAddr)
    by (unfold s2, s1; rewrite !setPc_mem, !rset_mem; exact Hmem0).
  assert (R10 : rget s2 10 = inputAddr) by (unfold s2, s1, init; reflexivity).
  assert (R11 : rget s2 11 = Z.of_nat (length inp)) by (unfold s2, s1, init; reflexivity).
  assert (R12 : rget s2 12 = outAddr) by (unfold s2, s1, init; reflexivity).
  assert (R13 : rget s2 13 = cap) by (unfold s2, s1, init; reflexivity).
  assert (R1 : rget s2 1 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R5 : rget s2 5 = 0) by (unfold s2, s1, init; reflexivity).
  assert (R6 : rget s2 6 = 0) by (unfold s2, s1, init; reflexivity).
  refine {| li_at_loop := _; li_code := _; li_a0 := R10; li_a1 := R11; li_a2 := R12;
            li_a3 := R13; li_ra := R1; li_in_mem := _; li_in_lt := _; li_bytes := Hbytes;
            li_in_fits := Hfits; li_out_lt := Hfit2; li_idx := _; li_suffix := _;
            li_outidx := _; li_emit_le := _; li_out_mem := _; li_spec := _ |}.
  - reflexivity.
  - apply (CodeLoaded_eqmem init); [exact Hmem2| exact Hcode0].
  - intros j Hj. rewrite Hmem2. unfold memWith.
    replace ((coreAddr <=? inputAddr + j) && (inputAddr + j <? coreAddr + Z.of_nat (length coreBytes)))
      with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge;
          rewrite coreBytes_len; unfold coreAddr, inputAddr; lia).
    cbv iota.
    replace ((inputAddr <=? inputAddr + j) && (inputAddr + j <? inputAddr + Z.of_nat (length inp)))
      with true
      by (symmetry; apply andb_true_iff; split;
          [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
    cbv iota. replace (inputAddr + j - inputAddr) with j by lia. reflexivity.
  - unfold inputAddr, outAddr in *; lia.
  - rewrite R5; lia.
  - rewrite Nat.sub_diag; reflexivity.
  - rewrite R6; reflexivity.
  - simpl; lia.
  - intros j Hj; simpl in Hj; lia.
  - rewrite app_nil_l; apply surjective_pairing.
Qed.

(** ** The general refinement theorem: PROVED modulo the per-token dispatch
    (`loop_iteration`). Mirrors the Lean assembly; the fixed 100000 fuel suffices
    because the loop halts within [2 + 50*|inp| + 4] steps and |inp| <= 484. *)
Theorem core_refines : forall (inp : list Z) (cap : Z),
  WellFormed inp cap ->
  runOn inp cap = specOn (zin inp) (Z.to_nat cap).
Proof.
  intros inp cap HW.
  assert (Hlen : (length inp <= 484)%nat)
    by (destruct HW as [Hfits _ _]; unfold inputAddr, outAddr in Hfits; lia).
  pose proof (init_loopinv inp cap HW) as HLI.
  set (init := mkInit (Z.of_nat (length inp)) cap (memWith inp inputAddr)) in *.
  pose proof (loop_correct inp cap (length inp) inp [] (runUntil 0 2 init) (le_n _) HLI) as HR.
  rewrite <- (runUntil_add 2 (50 * length inp + 4) init) in HR.
  (* The loop halts by fuel [2 + (50*|inp| + 4)] <= 100000 (since |inp| <= 484),
     so the fixed 100000-fuel run in [runOn] coincides with it. *)
  assert (HF : (2 + (50 * length inp + 4) <= 100000)%nat).
  { apply Nat2Z.inj_le.
    replace (Z.of_nat 100000) with 100000%Z by (vm_compute; reflexivity).
    lia. }
  assert (Hhalt : runUntil 0 100000 init
                  = runUntil 0 (2 + (50 * length inp + 4)) init)
    by (apply (runUntil_stab _ _ (Result_pc _ _ _ HR)); exact HF).
  unfold runOn. fold init. rewrite Hhalt.
  unfold specOn, Result in *.
  destruct (coreSpec (zin inp) (Z.to_nat cap)) as [[st bs] ln].
  destruct HR as [Hp [H10 [H11 Hmemr]]].
  rewrite H10, H11, Nat2Z.id, Hmemr. reflexivity.
Qed.

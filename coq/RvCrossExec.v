(** * RvCrossExec.v -- the execute/step cross-check (task #7, T2), completed.

    Builds on [RvCrossStep.v]'s foundations (word/Z bridge, fetch bridge, [run1]
    reduction toolkit, the state-bridge relation [Rrel]/[WFfetch]) to prove the
    full per-instruction simulation of our [Rv64i.step] against riscv-coq's
    [Run.run1 RV64I] over the Minimal [OState] machine -- all [Admitted]-free.

    Contents:
    - inversion lemmas [inv_*] (recover the [field] operands from a decode result);
    - pure state-projection facts about [rget]/[rset]/[setPc]/[storeByte];
    - the bit-clear bridge [clearbit0] ([Z.land a (2^64-2) = a - a mod 2], JALR);
    - monad-reduction toolkit ([OState_bind_step], [getReg_bind], [getPC_bind],
      [setPC_red], [loadByte_bind], [storeByte_red], translate-is-identity);
    - of_Z value bridges ([wor_of_Z], [wshl_of_Z], [eqb_of_Z], [lts_of_Z],
      [ltu_of_Z], [jalr_target], ...) and range helpers;
    - the cycle finishers [finish_cycle] / [writeReg_cycle] / [setPC_cycle] /
      [noop_cycle] / [writeReg_setPC_cycle] / [store_cycle];
    - the 12 per-instruction lemmas [exec_addi/add/or/slli/lbu/sb/beq/blt/bge/
      bgeu/jal/jalr], each: fetch -> [run1] reduce -> [decode_agrees] (T1) ->
      [ExecuteI] reduce via the bridges -> reassemble [Rrel];
    - [step_agrees]: one [Rv64i.step] = one riscv-coq [run1] cycle, dispatching on
      [decode (fetch32 s)] to the 12 [exec_*] under [Rrel] + [WFstep] (the §5
      alignment / data-domain side conditions, all true of the loaded [core]).

    Remaining for T2: the transport corollary [core_refines_riscv] (lift
    [step_agrees] to a whole run by induction and compose with [core_refines]). *)

From Coq Require Import ZArith List Lia Bool. Import ListNotations.
Require Import Hex0Coq.Rv64i Hex0Coq.RvCross Hex0Coq.RvCrossStep.
Require Import riscv.Spec.Decode riscv.Spec.Machine riscv.Spec.Execute riscv.Spec.ExecuteI.
Require Import riscv.Utility.Utility riscv.Utility.MkMachineWidth riscv.Platform.Memory.
Require Import riscv.Platform.RiscvMachine riscv.Platform.Minimal riscv.Platform.Run.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.Monads. Import OStateOperations.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Word.LittleEndian coqutil.Word.LittleEndianList.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Byte.
Require Import coqutil.Z.BitOps coqutil.Z.prove_Zeq_bitwise coqutil.Z.bitblast.
Require Import bedrock2.ZnWords.
Local Open Scope Z_scope.

(* bit-clear bridge: JALR's [and _ (lnot 1)] equals our [a - a mod 2]. *)
Lemma lxor_1_ones : Z.lxor 1 (2 ^ 64 - 1) = 2 ^ 64 - 2.
Proof. vm_compute. reflexivity. Qed.

Lemma clearbit_range : forall a, 0 <= a < 2 ^ 64 -> 0 <= a - a mod 2 < 2 ^ 64.
Proof.
  intros a Ha. pose proof (Z.div_mod a 2 ltac:(lia)). pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
  pose proof (Z.div_pos a 2 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma clearbit0 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 2) = a - a mod 2.
Proof.
  intros a Ha.
  replace (a - a mod 2) with (2 * (a / 2)) by (pose proof (Z.div_mod a 2); lia).
  Z.bitblast.
  destruct (Z.eqb_spec i 0) as [->|N0].
  - replace (2 ^ 64 - 2) with (2 * Z.ones 63) by (rewrite Z.ones_equiv; lia).
    rewrite (Z.testbit_even_0 (Z.ones 63)), (Z.testbit_even_0 (a / 2)), andb_false_r. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    replace (2 ^ 64 - 2) with (2 * Z.ones 63) by (rewrite Z.ones_equiv; lia).
    rewrite (Z.testbit_even_succ (Z.ones 63) (i-1)) by lia.
    rewrite (Z.testbit_even_succ (a / 2) (i-1)) by lia.
    replace (Z.succ (i - 1)) with ((i-1) + 1) by lia.
    rewrite <- (Z.shiftr_spec a 1 (i-1)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
    rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec (i-1) 63) as [Hlt|Hge].
    + rewrite andb_true_r. reflexivity.
    + rewrite andb_false_r. symmetry.
      apply Z.bits_above_log2; [ apply Z.div_pos; lia | ].
      assert (Hd: a / 2 < 2 ^ 63) by (apply Z.div_lt_upper_bound; lia).
      destruct (Z.eq_dec (a / 2) 0) as [->|Nz].
      * rewrite Z.log2_nonpos by lia. lia.
      * assert (0 <= a / 2) by (apply Z.div_pos; lia).
        assert (0 < a / 2) by lia.
        assert (Z.log2 (a / 2) < 63) by (apply (proj1 (Z.log2_lt_pow2 (a/2) 63 ltac:(lia))); exact Hd).
        lia.
Qed.

(* inversion: extract the field operands from a decode equation *)
Ltac inv_decode H :=
  unfold Rv64i.decode in H;
  repeat (match type of H with context[if ?b then _ else _] => destruct b end);
  try discriminate; inversion H; subst; clear H.

Lemma inv_addi : forall w rd rs1 imm, Rv64i.decode w = Iaddi rd rs1 imm ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5.
Proof. intros w rd rs1 imm H. inv_decode H. auto. Qed.
Lemma inv_add : forall w rd rs1 rs2, Rv64i.decode w = Iadd rd rs1 rs2 ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rd rs1 rs2 H. inv_decode H. auto. Qed.
Lemma inv_or : forall w rd rs1 rs2, Rv64i.decode w = Ior rd rs1 rs2 ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rd rs1 rs2 H. inv_decode H. auto. Qed.
Lemma inv_slli : forall w rd rs1 sh, Rv64i.decode w = Islli rd rs1 sh ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5 /\ sh = Rv64i.field w 20 6.
Proof. intros w rd rs1 sh H. inv_decode H. auto. Qed.
Lemma inv_beq : forall w rs1 rs2 imm, Rv64i.decode w = Ibeq rs1 rs2 imm ->
  rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rs1 rs2 imm H. inv_decode H. auto. Qed.
Lemma inv_blt : forall w rs1 rs2 imm, Rv64i.decode w = Iblt rs1 rs2 imm ->
  rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rs1 rs2 imm H. inv_decode H. auto. Qed.
Lemma inv_bge : forall w rs1 rs2 imm, Rv64i.decode w = Ibge rs1 rs2 imm ->
  rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rs1 rs2 imm H. inv_decode H. auto. Qed.
Lemma inv_bgeu : forall w rs1 rs2 imm, Rv64i.decode w = Ibgeu rs1 rs2 imm ->
  rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rs1 rs2 imm H. inv_decode H. auto. Qed.
Lemma inv_lbu : forall w rd rs1 imm, Rv64i.decode w = Ilbu rd rs1 imm ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5.
Proof. intros w rd rs1 imm H. inv_decode H. auto. Qed.
Lemma inv_sb : forall w rs1 rs2 imm, Rv64i.decode w = Isb rs1 rs2 imm ->
  rs1 = Rv64i.field w 15 5 /\ rs2 = Rv64i.field w 20 5.
Proof. intros w rs1 rs2 imm H. inv_decode H. auto. Qed.
Lemma inv_jal : forall w rd imm, Rv64i.decode w = Ijal rd imm ->
  rd = Rv64i.field w 7 5.
Proof. intros w rd imm H. inv_decode H. auto. Qed.
Lemma inv_jalr : forall w rd rs1 imm, Rv64i.decode w = Ijalr rd rs1 imm ->
  rd = Rv64i.field w 7 5 /\ rs1 = Rv64i.field w 15 5.
Proof. intros w rd rs1 imm H. inv_decode H. auto. Qed.

(* pure state-projection facts about our model's setters *)
Lemma rget_rset_same : forall s i v, i <> 0 -> Rv64i.rget (Rv64i.rset s i v) i = v.
Proof. intros s i v Hi. unfold Rv64i.rget, Rv64i.rset.
  rewrite (proj2 (Z.eqb_neq i 0) Hi). cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma rget_rset_diff : forall s i v r, r <> i -> Rv64i.rget (Rv64i.rset s i v) r = Rv64i.rget s r.
Proof. intros s i v r Hr. unfold Rv64i.rget, Rv64i.rset.
  destruct (Z.eqb_spec i 0) as [->|Hi]; [reflexivity|]. cbn.
  rewrite (proj2 (Z.eqb_neq r i) Hr). reflexivity. Qed.
Lemma rget_setPc : forall s p r, Rv64i.rget (Rv64i.setPc s p) r = Rv64i.rget s r.
Proof. intros. unfold Rv64i.rget, Rv64i.setPc. reflexivity. Qed.
Lemma mem_rset : forall s i v, (Rv64i.rset s i v).(mem) = s.(mem).
Proof. intros. unfold Rv64i.rset. destruct (i =? 0); reflexivity. Qed.
Lemma mem_setPc : forall s p, (Rv64i.setPc s p).(mem) = s.(mem).
Proof. reflexivity. Qed.
Lemma pc_setPc : forall s p, (Rv64i.setPc s p).(pc) = p.
Proof. reflexivity. Qed.
Lemma rget_storeByte : forall s a b r, Rv64i.rget (Rv64i.storeByte s a b) r = Rv64i.rget s r.
Proof. intros. unfold Rv64i.rget, Rv64i.storeByte. reflexivity. Qed.
Lemma pc_storeByte : forall s a b, (Rv64i.storeByte s a b).(pc) = s.(pc).
Proof. reflexivity. Qed.
Lemma mem_storeByte_at : forall s a b x,
  (Rv64i.storeByte s a b).(mem) x = (if x =? a then b mod 256 else s.(mem) x).
Proof. reflexivity. Qed.

Section Step.
  Context {BW: Bitwidth 64}.
  Context {word: word.word 64} {word_ok: word.ok word}.
  Context {Mem: map.map word Init.Byte.byte} {Mem_ok: map.ok Mem}.
  Context {Registers: map.map Z word} {Reg_ok: map.ok Registers}.

  Notation RMach := (@RiscvMachine.RiscvMachine 64 word Registers Mem).

  (* fetch connection: produce the loaded bytes and connect to fetch32 *)
  Lemma fetch_byte : forall s (m:RMach) D i, Rrel s m D -> WFfetch s m D -> 0 <= i < 4 ->
    word.unsigned (word.add m.(getPc) (word.of_Z i)) = s.(pc) + i /\
    map.get m.(getMem) (word.add m.(getPc) (word.of_Z i)) = Some (byte.of_Z (s.(mem) (s.(pc) + i))) /\
    0 <= s.(mem) (s.(pc) + i) < 256.
  Proof.
    intros s m D i HR HWF Hi.
    destruct HR as (HRA & HMA & HPA). destruct HPA as (Hpc & Hnext).
    destruct HWF as (Hnw & Hin & Hx).
    assert (Haddr: word.unsigned (word.add m.(getPc) (word.of_Z i)) = s.(pc) + i).
    { rewrite <- Hpc. ZnWords. }
    split; [exact Haddr|].
    destruct (HMA _ (Hin i Hi)) as (Hg & Hrg).
    rewrite Haddr in Hg, Hrg. split; assumption.
  Qed.

  Lemma fetch_conn : forall s (m:RMach) D, Rrel s m D -> WFfetch s m D ->
    exists bs, Memory.load_bytes 4 m.(getMem) m.(getPc) = Some bs /\
               LittleEndian.combine 4 bs = Rv64i.fetch32 s.
  Proof.
    intros s m D HR HWF.
    pose proof (fetch_byte s m D 0 HR HWF ltac:(lia)) as (A0 & G0 & R0).
    pose proof (fetch_byte s m D 1 HR HWF ltac:(lia)) as (A1 & G1 & R1).
    pose proof (fetch_byte s m D 2 HR HWF ltac:(lia)) as (A2 & G2 & R2).
    pose proof (fetch_byte s m D 3 HR HWF ltac:(lia)) as (A3 & G3 & R3).
    destruct HR as (HRA & HMA & HPA). destruct HPA as (Hpc & Hnext).
    destruct HWF as (Hnw & Hin & Hx).
    destruct (fetch_combine m.(getMem) m.(getPc) (fun i => s.(mem) (s.(pc) + i))
                ltac:(lia)) as (bs & Hl & Hc).
    { intros i Hi. assert (Hi': i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      destruct Hi' as [E|[E|[E|E]]]; subst i; assumption. }
    { intros i Hi. assert (Hi': i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
      destruct Hi' as [E|[E|[E|E]]]; subst i; assumption. }
    cbv beta in Hc.
    exists bs. split; [exact Hl|]. apply (eq_trans Hc).
    unfold Rv64i.fetch32. replace (s.(pc) + 0) with s.(pc) by lia. reflexivity.
  Qed.

  Lemma fetch32_range : forall s (m:RMach) D, Rrel s m D -> WFfetch s m D ->
    0 <= Rv64i.fetch32 s < 2 ^ 32.
  Proof.
    intros s m D HR HWF.
    pose proof (fetch_byte s m D 0 HR HWF ltac:(lia)) as (_ & _ & R0).
    pose proof (fetch_byte s m D 1 HR HWF ltac:(lia)) as (_ & _ & R1).
    pose proof (fetch_byte s m D 2 HR HWF ltac:(lia)) as (_ & _ & R2).
    pose proof (fetch_byte s m D 3 HR HWF ltac:(lia)) as (_ & _ & R3).
    unfold Rv64i.fetch32.
    replace (s.(pc) + 0) with s.(pc) in R0 by lia.
    change (2 ^ 32) with 4294967296. nia.
  Qed.

  (* monad-agnostic bind reduction (does NOT touch the bound computation's own
     monad argument, unlike a blanket [unfold OState_Monad]). *)
  Lemma OState_bind_value : forall {A B} (c: OState RiscvMachine A)
      (k: A -> OState RiscvMachine B) (m:RMach) a,
    c m = (Some a, m) -> Bind c k m = k a m.
  Proof. intros A B c k m a H. unfold Bind, OState_Monad. cbn beta. rewrite H. reflexivity. Qed.

  (* general version: the bound computation may change the state. *)
  Lemma OState_bind_step : forall {A B} (c: OState RiscvMachine A)
      (k: A -> OState RiscvMachine B) (m m1:RMach) a,
    c m = (Some a, m1) -> Bind c k m = k a m1.
  Proof. intros A B c k m m1 a H. unfold Bind, OState_Monad. cbn beta. rewrite H. reflexivity. Qed.

  (* monadic register read: resolve [Bind (getRegister r) k] to [k (of_Z (rget s r))]. *)
  Lemma getReg_bind : forall s (m:RMach) r (k: word -> OState RiscvMachine unit),
    RegAgree s m -> 0 <= r < 32 ->
    Bind (Machine.getRegister r) k m = k (word.of_Z (Rv64i.rget s r)) m.
  Proof.
    intros s m r k HRA Hr.
    apply (OState_bind_value (Machine.getRegister r) k m _ (getReg_R s m r HRA Hr)).
  Qed.

  (* value-range helpers *)
  Lemma wadd_range : forall a b, 0 <= Rv64i.wadd a b < 2 ^ 64.
  Proof. intros. unfold Rv64i.wadd, Rv64i.wrap, Rv64i.w64. apply Z.mod_pos_bound. lia. Qed.
  Lemma wor_range : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Rv64i.wor a b < 2 ^ 64.
  Proof. intros. unfold Rv64i.wor. apply lor_lt; lia. Qed.
  Lemma wshl_range : forall a sh, 0 <= Rv64i.wshl a sh < 2 ^ 64.
  Proof. intros. unfold Rv64i.wshl, Rv64i.wrap, Rv64i.w64. apply Z.mod_pos_bound. lia. Qed.

  (* registers read in [0,2^64) under [RegAgree] (x0 reads 0). *)
  Lemma rget_range : forall s (m:RMach) r, RegAgree s m -> 0 <= r < 32 ->
    0 <= Rv64i.rget s r < 2 ^ 64.
  Proof.
    intros s m r HRA Hr. destruct (Z.eq_dec r 0) as [->|N].
    - unfold Rv64i.rget; cbn. lia.
    - destruct (HRA r ltac:(lia)) as (_ & Hrg). exact Hrg.
  Qed.

  (* of_Z value bridges for [or] and [sll]. *)
  Lemma wor_of_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
    word.of_Z (word:=word) (Rv64i.wor a b) = word.or (word.of_Z a) (word.of_Z b).
  Proof.
    intros a b Ha Hb. apply word.unsigned_inj. rewrite br_or.
    rewrite (word.unsigned_of_Z_nowrap a) by lia.
    rewrite (word.unsigned_of_Z_nowrap b) by lia.
    rewrite (word.unsigned_of_Z_nowrap (Rv64i.wor a b)) by (apply wor_range; lia).
    reflexivity.
  Qed.
  Lemma wshl_of_Z : forall a sh, 0 <= a < 2^64 -> 0 <= sh < 64 ->
    word.of_Z (word:=word) (Rv64i.wshl a sh) = word.slu (word.of_Z a) (word.of_Z sh).
  Proof.
    intros a sh Ha Hsh. apply word.unsigned_inj.
    rewrite word.unsigned_slu_shamtZ by lia.
    rewrite (word.unsigned_of_Z_nowrap a) by lia.
    rewrite (word.unsigned_of_Z_nowrap (Rv64i.wshl a sh)) by (apply wshl_range).
    unfold Rv64i.wshl, Rv64i.wrap, Rv64i.w64, word.wrap. reflexivity.
  Qed.

  (* the common cycle finisher: from a machine [mset] whose registers/memory already
     agree with the post-state [s'] and whose nextPc carries the new pc, [endCycleNormal]
     lands in a fully [Rrel]-related state. *)
  Lemma finish_cycle : forall (s':Rv64i.State) (mset:RMach) D,
    RegAgree s' mset -> MemAgree s' mset D ->
    word.unsigned mset.(getNextPc) = s'.(pc) ->
    exists m', endCycleNormal mset = (Some tt, m') /\ Rrel s' m' D.
  Proof.
    intros s' mset D HRA HMA Hpc.
    rewrite endcycle_red. eexists. split; [reflexivity|].
    destruct mset as [regs pc npc mem xa lg]. cbn in *.
    unfold Rrel, PcAgree. cbn. split; [exact HRA | split; [exact HMA|]].
    split; [exact Hpc | reflexivity].
  Qed.

  (* a register-writing, pc+4 instruction: setRegister then endCycleNormal lands related. *)
  Lemma writeReg_cycle : forall s (m:RMach) D rd v,
    RegAgree s m -> MemAgree s m D -> PcAgree s m ->
    0 <= rd < 32 -> 0 <= v < 2 ^ 64 ->
    exists m',
      (let (o, m3) := (Machine.setRegister rd (word.of_Z v) : OState RiscvMachine unit) m in
         match o with Some _ => endCycleNormal m3 | None => (None, m3) end) = (Some tt, m')
      /\ Rrel (Rv64i.setPc (Rv64i.rset s rd v) (Rv64i.wadd s.(pc) 4)) m' D.
  Proof.
    intros s m D rd v HRA HMA HPA Hrd Hv.
    pose proof HPA as (Hpc & Hnext).
    destruct m as [regs pc0 npc0 mem xa lg]. cbn in Hpc, Hnext.
    destruct (Z.eq_dec rd 0) as [E0|N0].
    - (* rd = 0: no write *) subst rd.
      assert (Hset: (Machine.setRegister 0 (word.of_Z v) : OState RiscvMachine unit)
                      (mkRiscvMachine regs pc0 npc0 mem xa lg) = (Some tt, mkRiscvMachine regs pc0 npc0 mem xa lg)).
      { unfold Machine.setRegister, IsRiscvMachine.
        destruct (Z.eq_dec 0 Register0) as [_|C]; [reflexivity| exfalso; cbn in C; lia]. }
      rewrite Hset. cbn match.
      apply finish_cycle.
      + (* RegAgree: rset s 0 v leaves r in [1,32) unchanged *)
        unfold RegAgree; cbn [getRegs]. intros r Hr.
        rewrite rget_setPc, rget_rset_diff by lia. exact (HRA r Hr).
      + unfold MemAgree; cbn [getMem]. intros a Ha. rewrite mem_setPc, mem_rset. exact (HMA a Ha).
      + cbn [getNextPc]. rewrite Hnext, br_add, pc_setPc.
        rewrite word.unsigned_of_Z_nowrap by lia. rewrite Hpc. reflexivity.
    - (* rd <> 0: real write *)
      assert (Hrd': 1 <= rd < 32) by lia.
      rewrite (setReg_red (mkRiscvMachine regs pc0 npc0 mem xa lg) rd (word.of_Z v) Hrd'). cbn match.
      apply finish_cycle.
      + (* RegAgree of the put map *)
        unfold RegAgree; cbn [getRegs withRegs]. intros r Hr. rewrite rget_setPc.
        destruct (Z.eq_dec r rd) as [->|Nr].
        * rewrite map.get_put_same, rget_rset_same by lia. split; [reflexivity | exact Hv].
        * rewrite map.get_put_diff by (intro; apply Nr; congruence).
          rewrite rget_rset_diff by lia. exact (HRA r Hr).
      + unfold MemAgree; cbn [getMem withRegs]. intros a Ha. rewrite mem_setPc, mem_rset. exact (HMA a Ha).
      + cbn [getNextPc withRegs]. rewrite Hnext, br_add, pc_setPc.
        rewrite word.unsigned_of_Z_nowrap by lia. rewrite Hpc. reflexivity.
  Qed.

  (* --- PC read/write monad reductions --- *)
  Lemma getPC_red : forall (m:RMach), Machine.getPC m = (Some m.(getPc), m).
  Proof.
    intros. unfold Machine.getPC, IsRiscvMachine.
    cbv [Bind Return OState_Monad get]. cbn [fst snd]. reflexivity.
  Qed.
  Lemma getPC_bind : forall (m:RMach) (k: word -> OState RiscvMachine unit),
    Bind Machine.getPC k m = k m.(getPc) m.
  Proof. intros. apply (OState_bind_value Machine.getPC k m _ (getPC_red m)). Qed.
  Lemma setPC_red : forall (m:RMach) (p:word),
    (Machine.setPC p : OState RiscvMachine unit) m = (Some tt, withNextPc p m).
  Proof.
    intros. unfold Machine.setPC, IsRiscvMachine, update.
    cbv [Bind Return OState_Monad get put]. cbn [fst snd]. reflexivity.
  Qed.

  (* --- guard/align bridges --- *)
  Lemma eqb_of_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
    word.eqb (word.of_Z (word:=word) a) (word.of_Z b) = (a =? b).
  Proof.
    intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|N].
    - apply word.eqb_eq. reflexivity.
    - apply word.eqb_ne. intro C. apply N.
      apply (f_equal word.unsigned) in C.
      rewrite !word.unsigned_of_Z_nowrap in C by lia. exact C.
  Qed.
  Lemma lts_of_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
    word.lts (word.of_Z (word:=word) a) (word.of_Z b) = Rv64i.sltb a b.
  Proof. intros a b Ha Hb. rewrite br_lts, !word.unsigned_of_Z_nowrap by lia. reflexivity. Qed.
  Lemma ltu_of_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
    word.ltu (word.of_Z (word:=word) a) (word.of_Z b) = Rv64i.ultb a b.
  Proof. intros a b Ha Hb. rewrite br_ltu, !word.unsigned_of_Z_nowrap by lia. reflexivity. Qed.
  Lemma wadd_newPC : forall (p:word) imm,
    word.unsigned (word.add p (word.of_Z imm)) = Rv64i.wadd (word.unsigned p) imm.
  Proof.
    intros. rewrite br_add, word.unsigned_of_Z.
    unfold Rv64i.wadd, Rv64i.wrap, Rv64i.w64, word.wrap.
    rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.
  Lemma add_of_Z_r : forall (p:word) k,
    word.add p (word.of_Z k) = word.of_Z (Rv64i.wadd (word.unsigned p) k).
  Proof.
    intros. apply word.unsigned_inj.
    rewrite wadd_newPC, word.unsigned_of_Z_nowrap by (apply wadd_range). reflexivity.
  Qed.
  (* JALR target: [and (of_Z a) (lnot (of_Z 1))] = [of_Z (a - a mod 2)] (clears bit 0). *)
  Lemma jalr_target : forall a, 0 <= a < 2 ^ 64 ->
    word.and (word.of_Z (word:=word) a) (word.xor (word.of_Z 1) (word.of_Z (2 ^ 64 - 1)))
      = word.of_Z (a - a mod 2).
  Proof.
    intros a Ha.
    assert (Hb: 0 <= a - a mod 2 < 2 ^ 64).
    { pose proof (Z.div_mod a 2 ltac:(lia)). pose proof (Z.mod_pos_bound a 2 ltac:(lia)).
      pose proof (Z.div_pos a 2 ltac:(lia) ltac:(lia)). lia. }
    apply word.unsigned_inj.
    rewrite word.unsigned_and_nowrap, word.unsigned_xor_nowrap.
    rewrite (word.unsigned_of_Z_nowrap a) by lia.
    rewrite (word.unsigned_of_Z_nowrap 1) by lia.
    rewrite (word.unsigned_of_Z_nowrap (2 ^ 64 - 1)) by lia.
    rewrite lxor_1_ones.
    rewrite (word.unsigned_of_Z_nowrap (a - a mod 2)) by lia.
    apply clearbit0; lia.
  Qed.
  Lemma remu4_aligned : forall (a:word), word.unsigned a mod 4 = 0 ->
    word.eqb (word.modu a (word.of_Z 4)) (word.of_Z 0) = true.
  Proof.
    intros a Ha. apply word.eqb_eq. apply word.unsigned_inj.
    rewrite word.unsigned_modu_nowrap by (rewrite word.unsigned_of_Z_nowrap by lia; lia).
    rewrite (word.unsigned_of_Z_nowrap 4) by lia. rewrite Ha.
    rewrite (word.unsigned_of_Z_nowrap 0) by lia. reflexivity.
  Qed.

  (* --- branch/jump finishers (no reg write): taken sets PC, not-taken advances pc+4 --- *)
  Lemma setPC_cycle : forall s (m:RMach) D (p:word) P,
    RegAgree s m -> MemAgree s m D -> word.unsigned p = P ->
    exists m', (let (o, m3) := (Machine.setPC p : OState RiscvMachine unit) m in
                  match o with Some _ => endCycleNormal m3 | None => (None, m3) end) = (Some tt, m')
               /\ Rrel (Rv64i.setPc s P) m' D.
  Proof.
    intros s m D p P HRA HMA HP. destruct m as [regs pc0 npc0 mem xa lg].
    rewrite setPC_red. cbn match. apply finish_cycle.
    - unfold RegAgree; cbn [getRegs withNextPc]. intros r Hr. rewrite rget_setPc. exact (HRA r Hr).
    - unfold MemAgree; cbn [getMem withNextPc]. intros a Ha. rewrite mem_setPc. exact (HMA a Ha).
    - cbn [getNextPc withNextPc]. rewrite pc_setPc. exact HP.
  Qed.
  Lemma noop_cycle : forall s (m:RMach) D,
    RegAgree s m -> MemAgree s m D -> PcAgree s m ->
    exists m', (let (o, m3) := ((Return tt : OState RiscvMachine unit) m) in
                  match o with Some _ => endCycleNormal m3 | None => (None, m3) end) = (Some tt, m')
               /\ Rrel (Rv64i.setPc s (Rv64i.wadd s.(pc) 4)) m' D.
  Proof.
    intros s m D HRA HMA HPA. pose proof HPA as (Hpc & Hnext).
    destruct m as [regs pc0 npc0 mem xa lg]. cbn in Hpc, Hnext.
    cbv [Return OState_Monad]. cbn match. apply finish_cycle.
    - unfold RegAgree; cbn [getRegs]. intros r Hr. rewrite rget_setPc. exact (HRA r Hr).
    - unfold MemAgree; cbn [getMem]. intros a Ha. rewrite mem_setPc. exact (HMA a Ha).
    - cbn [getNextPc]. rewrite Hnext, br_add, pc_setPc.
      rewrite word.unsigned_of_Z_nowrap by lia. rewrite Hpc. reflexivity.
  Qed.

  (* a jump: write rd, then set PC to an arbitrary (aligned) target. *)
  Lemma writeReg_setPC_cycle : forall s (m:RMach) D rd v (p:word) P,
    RegAgree s m -> MemAgree s m D ->
    0 <= rd < 32 -> 0 <= v < 2 ^ 64 -> word.unsigned p = P ->
    exists m',
      (let (o, m3) := (Bind (Machine.setRegister rd (word.of_Z v)) (fun _ => Machine.setPC p)
                         : OState RiscvMachine unit) m in
         match o with Some _ => endCycleNormal m3 | None => (None, m3) end) = (Some tt, m')
      /\ Rrel (Rv64i.setPc (Rv64i.rset s rd v) P) m' D.
  Proof.
    intros s m D rd v p P HRA HMA Hrd Hv HP.
    destruct m as [regs pc0 npc0 mem xa lg].
    destruct (Z.eq_dec rd 0) as [E0|N0].
    - (* rd = 0 *) subst rd.
      assert (Hset: (Machine.setRegister 0 (word.of_Z v) : OState RiscvMachine unit)
                      (mkRiscvMachine regs pc0 npc0 mem xa lg) = (Some tt, mkRiscvMachine regs pc0 npc0 mem xa lg)).
      { unfold Machine.setRegister, IsRiscvMachine.
        destruct (Z.eq_dec 0 Register0) as [_|C]; [reflexivity| exfalso; cbn in C; lia]. }
      rewrite (OState_bind_step _ (fun _ => Machine.setPC p) _ _ _ Hset). cbn beta.
      rewrite setPC_red. cbn match. apply finish_cycle.
      + unfold RegAgree; cbn [getRegs withNextPc]. intros r Hr.
        rewrite rget_setPc, rget_rset_diff by lia. exact (HRA r Hr).
      + unfold MemAgree; cbn [getMem withNextPc]. intros a Ha. rewrite mem_setPc, mem_rset. exact (HMA a Ha).
      + cbn [getNextPc withNextPc]. rewrite pc_setPc. exact HP.
    - (* rd <> 0 *)
      assert (Hrd': 1 <= rd < 32) by lia.
      rewrite (OState_bind_step _ (fun _ => Machine.setPC p) _ _ _
                 (setReg_red (mkRiscvMachine regs pc0 npc0 mem xa lg) rd (word.of_Z v) Hrd')).
      cbn beta. rewrite setPC_red. cbn match. apply finish_cycle.
      + unfold RegAgree; cbn [getRegs withNextPc withRegs]. intros r Hr. rewrite rget_setPc.
        destruct (Z.eq_dec r rd) as [->|Nr].
        * rewrite map.get_put_same, rget_rset_same by lia. split; [reflexivity | exact Hv].
        * rewrite map.get_put_diff by (intro; apply Nr; congruence).
          rewrite rget_rset_diff by lia. exact (HRA r Hr).
      + unfold MemAgree; cbn [getMem withNextPc withRegs]. intros a Ha.
        rewrite mem_setPc, mem_rset. exact (HMA a Ha).
      + cbn [getNextPc withNextPc withRegs]. rewrite pc_setPc. exact HP.
  Qed.

  (* --- memory access reductions (translate is identity on Minimal) --- *)
  Lemma translate_red : forall acc al (addr:word) (m:RMach),
    (Spec.Machine.translate acc al addr : OState RiscvMachine word) m = (Some addr, m).
  Proof. reflexivity. Qed.
  Lemma translate_bind : forall acc al (addr:word) (k: word -> OState RiscvMachine unit) (m:RMach),
    Bind (Spec.Machine.translate acc al addr) k m = k addr m.
  Proof. intros. apply (OState_bind_value _ k m _ (translate_red acc al addr m)). Qed.

  Lemma loadByte_red : forall (m:RMach) (a:word) b,
    map.get m.(getMem) a = Some b ->
    (Machine.loadByte Spec.Machine.Execute a : OState RiscvMachine w8) m
      = (Some (PrimitivePair.pair.mk b tt), m).
  Proof.
    intros m a b H. unfold Machine.loadByte, IsRiscvMachine, loadN, fail_if_None.
    cbv [Bind Return OState_Monad get]. cbn [fst snd].
    unfold Memory.load_bytes, Memory.footprint.
    cbn [HList.tuple.unfoldn map.getmany_of_tuple HList.tuple.map HList.tuple.option_all].
    rewrite H. reflexivity.
  Qed.
  Lemma loadByte_bind : forall (m:RMach) (a:word) b (k: w8 -> OState RiscvMachine unit),
    map.get m.(getMem) a = Some b ->
    Bind (Machine.loadByte Spec.Machine.Execute a) k m = k (PrimitivePair.pair.mk b tt) m.
  Proof. intros. apply (OState_bind_value _ k m _ (loadByte_red m a b H)). Qed.

  Lemma combine1 : forall b, LittleEndian.combine 1 (PrimitivePair.pair.mk b tt) = byte.unsigned b.
  Proof.
    intros. rewrite combine_eq. cbn [HList.tuple.to_list]. cbv [LittleEndianList.le_combine].
    rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
  Qed.

  Lemma byte_of_Z_mod : forall v, byte.of_Z (v mod 256) = byte.of_Z v.
  Proof.
    intros. apply byte.unsigned_inj. rewrite !byte.unsigned_of_Z. unfold byte.wrap.
    change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  Qed.

  Lemma regToInt8_of_Z : forall v, 0 <= v < 2 ^ 64 ->
    regToInt8 (word.of_Z (word:=word) v) = PrimitivePair.pair.mk (byte.of_Z v) tt.
  Proof.
    intros v Hv. cbn [regToInt8 MachineWidth_XLEN].
    rewrite word.unsigned_of_Z_nowrap by lia.
    cbn [LittleEndian.split_deprecated]. reflexivity.
  Qed.

  Lemma storeByte_red : forall (m:RMach) (addr:word) (b b0:Init.Byte.byte),
    map.get m.(getMem) addr = Some b0 ->
    (Machine.storeByte Spec.Machine.Execute addr (PrimitivePair.pair.mk b tt) : OState RiscvMachine unit) m
      = (Some tt, withXAddrs (invalidateWrittenXAddrs 1 addr m.(getXAddrs))
                    (withMem (map.put m.(getMem) addr b) m)).
  Proof.
    intros m addr b b0 H.
    unfold Machine.storeByte, IsRiscvMachine, storeN, fail_if_None, update.
    cbv [Bind Return OState_Monad get put]. cbn [fst snd].
    unfold Memory.store_bytes, Memory.load_bytes, Memory.footprint.
    cbn [HList.tuple.unfoldn map.getmany_of_tuple HList.tuple.map HList.tuple.option_all].
    rewrite H. cbn [fst snd].
    unfold Memory.unchecked_store_bytes, Memory.footprint.
    cbn [HList.tuple.unfoldn map.putmany_of_tuple]. reflexivity.
  Qed.

  (* a store: write one byte to [addr] (which must be mapped), then pc += 4. *)
  Lemma store_cycle : forall s (m:RMach) D (addr:word) az v b0,
    RegAgree s m -> MemAgree s m D -> PcAgree s m ->
    word.unsigned addr = az ->
    map.get m.(getMem) addr = Some b0 ->
    exists m',
      (let (o, m3) := (Machine.storeByte Spec.Machine.Execute addr
                         (PrimitivePair.pair.mk (byte.of_Z v) tt) : OState RiscvMachine unit) m in
         match o with Some _ => endCycleNormal m3 | None => (None, m3) end) = (Some tt, m')
      /\ Rrel (Rv64i.setPc (Rv64i.storeByte s az v) (Rv64i.wadd s.(pc) 4)) m' D.
  Proof.
    intros s m D addr az v b0 HRA HMA HPA Haz Hget. subst az.
    pose proof HPA as (Hpc & Hnext).
    rewrite (storeByte_red m addr (byte.of_Z v) b0 Hget). cbn match.
    destruct m as [regs pc0 npc0 mem xa lg]. cbn [getMem withMem withXAddrs] in Hget |- *.
    cbn in Hpc, Hnext.
    apply finish_cycle.
    - unfold RegAgree; cbn [getRegs withMem withXAddrs]. intros r Hr.
      rewrite rget_setPc, rget_storeByte. exact (HRA r Hr).
    - unfold MemAgree; cbn [getMem withMem withXAddrs]. intros a Ha.
      destruct (Z.eq_dec (word.unsigned a) (word.unsigned addr)) as [Eq|Nq].
      + assert (a = addr) by (apply word.unsigned_inj; exact Eq). subst a.
        rewrite map.get_put_same, mem_setPc, mem_storeByte_at, Z.eqb_refl, byte_of_Z_mod.
        split; [reflexivity | apply Z.mod_pos_bound; lia].
      + rewrite map.get_put_diff by (intro Hc; subst a; apply Nq; reflexivity).
        rewrite mem_setPc, mem_storeByte_at, (proj2 (Z.eqb_neq _ _) Nq).
        exact (HMA a Ha).
    - cbn [getNextPc withMem withXAddrs]. rewrite Hnext, br_add, pc_setPc.
      rewrite word.unsigned_of_Z_nowrap by lia. rewrite Hpc. reflexivity.
  Qed.

  (* shared prologue: fetch, reduce run1, pin decode via T1, expose the ExecuteI body. *)
  Ltac exec_setup s m HR HWF Hdec ctor :=
    destruct (fetch_conn s m _ HR HWF) as (bs & Hload & Hcomb);
    pose proof (fetch32_range s m _ HR HWF) as Hfr;
    pose proof HR as (HRA & HMA & HPA);
    pose proof HWF as (Hnw & Hin & Hx);
    unfold Rv64i.step; cbv zeta; rewrite Hdec;
    rewrite (run1_fetch m bs (isXAddr4B_true _ _ Hx) Hload);
    replace (LittleEndian.combine 4 bs) with (Rv64i.fetch32 s) by (symmetry; exact Hcomb);
    rewrite (decode_agrees (Rv64i.fetch32 s) Hfr ctor Hdec ltac:(discriminate));
    cbn [embed Execute.execute ExecuteI.execute].

  Lemma exec_addi : forall s (m:RMach) D rd rs1 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Iaddi rd rs1 imm ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 imm HR HWF Hdec.
    pose proof (inv_addi _ _ _ _ Hdec) as (Erd & Ers1).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Iaddi rd rs1 imm).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    cbn [add ZToReg MachineWidth_XLEN].
    rewrite <- (wadd_of_Z (rget s rs1) imm).
    apply writeReg_cycle; try assumption. apply wadd_range.
  Qed.

  Lemma exec_add : forall s (m:RMach) D rd rs1 rs2,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Iadd rd rs1 rs2 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 rs2 HR HWF Hdec.
    pose proof (inv_add _ _ _ _ Hdec) as (Erd & Ers1 & Ers2).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Iadd rd rs1 rs2).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    rewrite (getReg_bind s m rs2 _ HRA Hrs2).
    cbn [add MachineWidth_XLEN].
    rewrite <- (wadd_of_Z (rget s rs1) (rget s rs2)).
    apply writeReg_cycle; try assumption. apply wadd_range.
  Qed.

  Lemma exec_or : forall s (m:RMach) D rd rs1 rs2,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ior rd rs1 rs2 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 rs2 HR HWF Hdec.
    pose proof (inv_or _ _ _ _ Hdec) as (Erd & Ers1 & Ers2).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ior rd rs1 rs2).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    rewrite (getReg_bind s m rs2 _ HRA Hrs2).
    cbn [or MachineWidth_XLEN].
    rewrite <- (wor_of_Z (rget s rs1) (rget s rs2)) by (eapply rget_range; eassumption).
    apply writeReg_cycle; try assumption. apply wor_range; eapply rget_range; eassumption.
  Qed.

  Lemma exec_slli : forall s (m:RMach) D rd rs1 sh,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Islli rd rs1 sh ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 sh HR HWF Hdec.
    pose proof (inv_slli _ _ _ _ Hdec) as (Erd & Ers1 & Esh).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hsh: 0 <= sh < 64) by (rewrite Esh; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Islli rd rs1 sh).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    cbn [sll MachineWidth_XLEN].
    rewrite <- (wshl_of_Z (rget s rs1) sh) by (try (eapply rget_range; eassumption); lia).
    apply writeReg_cycle; try assumption. apply wshl_range.
  Qed.

  Lemma exec_beq : forall s (m:RMach) D rs1 rs2 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ibeq rs1 rs2 imm ->
    (Rv64i.wadd s.(pc) imm) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rs1 rs2 imm HR HWF Hdec Halign.
    pose proof (inv_beq _ _ _ _ Hdec) as (Ers1 & Ers2).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ibeq rs1 rs2 imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    rewrite (getReg_bind s m rs2 _ HRA Hrs2).
    rewrite getPC_bind.
    unfold when. cbn [reg_eqb MachineWidth_XLEN].
    rewrite (eqb_of_Z (rget s rs1) (rget s rs2)) by (eapply rget_range; eassumption).
    destruct (Z.eqb_spec (rget s rs1) (rget s rs2)) as [Eq|Neq].
    - (* taken *)
      cbn [remu reg_eqb ZToReg add MachineWidth_XLEN].
      rewrite remu4_aligned by (rewrite wadd_newPC, Hpc; exact Halign).
      cbn match.
      apply (setPC_cycle s m D _ (Rv64i.wadd s.(pc) imm) HRA HMA).
      rewrite wadd_newPC, Hpc. reflexivity.
    - (* not taken *)
      apply (noop_cycle s m D HRA HMA HPA).
  Qed.

  (* taken-branch tail: discharge alignment, set PC to wadd pc imm. *)
  Ltac take_branch s m imm HRA HMA Hpc Halign :=
    cbn [remu reg_eqb ZToReg add MachineWidth_XLEN];
    rewrite remu4_aligned by (rewrite wadd_newPC, Hpc; exact Halign);
    cbn match;
    apply (setPC_cycle s m _ _ (Rv64i.wadd s.(pc) imm) HRA HMA);
    rewrite wadd_newPC, Hpc; reflexivity.

  Lemma exec_blt : forall s (m:RMach) D rs1 rs2 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Iblt rs1 rs2 imm ->
    (Rv64i.wadd s.(pc) imm) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rs1 rs2 imm HR HWF Hdec Halign.
    pose proof (inv_blt _ _ _ _ Hdec) as (Ers1 & Ers2).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Iblt rs1 rs2 imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1), (getReg_bind s m rs2 _ HRA Hrs2), getPC_bind.
    unfold when. cbn [signed_less_than MachineWidth_XLEN].
    rewrite (lts_of_Z (rget s rs1) (rget s rs2)) by (eapply rget_range; eassumption).
    destruct (Rv64i.sltb (rget s rs1) (rget s rs2)).
    - take_branch s m imm HRA HMA Hpc Halign.
    - apply (noop_cycle s m D HRA HMA HPA).
  Qed.

  Lemma exec_bge : forall s (m:RMach) D rs1 rs2 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ibge rs1 rs2 imm ->
    (Rv64i.wadd s.(pc) imm) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rs1 rs2 imm HR HWF Hdec Halign.
    pose proof (inv_bge _ _ _ _ Hdec) as (Ers1 & Ers2).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ibge rs1 rs2 imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1), (getReg_bind s m rs2 _ HRA Hrs2), getPC_bind.
    unfold when. cbn [signed_less_than MachineWidth_XLEN].
    rewrite (lts_of_Z (rget s rs1) (rget s rs2)) by (eapply rget_range; eassumption).
    destruct (Rv64i.sltb (rget s rs1) (rget s rs2)); cbn [negb].
    - cbn match. apply (noop_cycle s m D HRA HMA HPA).
    - cbn match. take_branch s m imm HRA HMA Hpc Halign.
  Qed.

  Lemma exec_bgeu : forall s (m:RMach) D rs1 rs2 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ibgeu rs1 rs2 imm ->
    (Rv64i.wadd s.(pc) imm) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rs1 rs2 imm HR HWF Hdec Halign.
    pose proof (inv_bgeu _ _ _ _ Hdec) as (Ers1 & Ers2).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ibgeu rs1 rs2 imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1), (getReg_bind s m rs2 _ HRA Hrs2), getPC_bind.
    unfold when. cbn [ltu MachineWidth_XLEN].
    rewrite (ltu_of_Z (rget s rs1) (rget s rs2)) by (eapply rget_range; eassumption).
    destruct (Rv64i.ultb (rget s rs1) (rget s rs2)); cbn [negb].
    - cbn match. apply (noop_cycle s m D HRA HMA HPA).
    - cbn match. take_branch s m imm HRA HMA Hpc Halign.
  Qed.

  Lemma exec_lbu : forall s (m:RMach) D rd rs1 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ilbu rd rs1 imm ->
    D (word.of_Z (Rv64i.wadd (Rv64i.rget s rs1) imm)) ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 imm HR HWF Hdec Haddr.
    pose proof (inv_lbu _ _ _ _ Hdec) as (Erd & Ers1).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ilbu rd rs1 imm).
    destruct (HMA _ Haddr) as (Hget & Hbrange).
    rewrite (word.unsigned_of_Z_nowrap (Rv64i.wadd (Rv64i.rget s rs1) imm)) in Hget, Hbrange
      by (apply wadd_range).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    rewrite translate_bind.
    cbn [add ZToReg MachineWidth_XLEN].
    rewrite <- (wadd_of_Z (rget s rs1) imm).
    rewrite (loadByte_bind m _ _ _ Hget).
    cbn [uInt8ToReg MachineWidth_XLEN].
    rewrite combine1, byte_uoz by exact Hbrange.
    assert (Hm: (s.(mem) (Rv64i.wadd (Rv64i.rget s rs1) imm)) mod 256
                  = s.(mem) (Rv64i.wadd (Rv64i.rget s rs1) imm))
      by (apply Z.mod_small; exact Hbrange).
    rewrite Hm.
    apply writeReg_cycle; try assumption.
    change (2 ^ 64) with 18446744073709551616; lia.
  Qed.

  Lemma exec_jal : forall s (m:RMach) D rd imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ijal rd imm ->
    (Rv64i.wadd s.(pc) imm) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd imm HR HWF Hdec Halign.
    pose proof (inv_jal _ _ _ Hdec) as Erd.
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ijal rd imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite getPC_bind.
    cbn [remu reg_eqb ZToReg add MachineWidth_XLEN].
    rewrite remu4_aligned by (rewrite wadd_newPC, Hpc; exact Halign).
    cbn match.
    rewrite !add_of_Z_r, Hpc.
    apply (writeReg_setPC_cycle s m D rd (Rv64i.wadd s.(pc) 4)
             (word.of_Z (Rv64i.wadd s.(pc) imm)) (Rv64i.wadd s.(pc) imm) HRA HMA Hrd).
    - apply wadd_range.
    - rewrite word.unsigned_of_Z_nowrap by (apply wadd_range). reflexivity.
  Qed.

  Lemma exec_jalr : forall s (m:RMach) D rd rs1 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Ijalr rd rs1 imm ->
    ((Rv64i.wadd (Rv64i.rget s rs1) imm) - (Rv64i.wadd (Rv64i.rget s rs1) imm) mod 2) mod 4 = 0 ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rd rs1 imm HR HWF Hdec Halign.
    pose proof (inv_jalr _ _ _ _ Hdec) as (Erd & Ers1).
    assert (Hrd: 0 <= rd < 32) by (rewrite Erd; apply field_range; lia).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Ijalr rd rs1 imm).
    pose proof HPA as (Hpc & Hnext).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1). rewrite getPC_bind.
    cbn [add ZToReg and xor maxUnsigned MachineWidth_XLEN Utility.lnot].
    rewrite <- (wadd_of_Z (rget s rs1) imm).
    rewrite (jalr_target (Rv64i.wadd (Rv64i.rget s rs1) imm) (wadd_range _ _)).
    cbn [remu reg_eqb ZToReg MachineWidth_XLEN].
    rewrite remu4_aligned
      by (rewrite word.unsigned_of_Z_nowrap by (apply clearbit_range; apply wadd_range); exact Halign).
    cbn match.
    rewrite add_of_Z_r, Hpc.
    apply (writeReg_setPC_cycle s m D rd (Rv64i.wadd s.(pc) 4)
             (word.of_Z (Rv64i.wadd (Rv64i.rget s rs1) imm - (Rv64i.wadd (Rv64i.rget s rs1) imm) mod 2))
             (Rv64i.wadd (Rv64i.rget s rs1) imm - (Rv64i.wadd (Rv64i.rget s rs1) imm) mod 2) HRA HMA Hrd).
    - apply wadd_range.
    - rewrite word.unsigned_of_Z_nowrap by (apply clearbit_range; apply wadd_range). reflexivity.
  Qed.

  Lemma exec_sb : forall s (m:RMach) D rs1 rs2 imm,
    Rrel s m D -> WFfetch s m D ->
    Rv64i.decode (Rv64i.fetch32 s) = Isb rs1 rs2 imm ->
    D (word.of_Z (Rv64i.wadd (Rv64i.rget s rs1) imm)) ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D rs1 rs2 imm HR HWF Hdec Haddr.
    pose proof (inv_sb _ _ _ _ Hdec) as (Ers1 & Ers2).
    assert (Hrs1: 0 <= rs1 < 32) by (rewrite Ers1; apply field_range; lia).
    assert (Hrs2: 0 <= rs2 < 32) by (rewrite Ers2; apply field_range; lia).
    exec_setup s m HR HWF Hdec (Isb rs1 rs2 imm).
    destruct (HMA _ Haddr) as (Hget & Hbrange).
    rewrite (word.unsigned_of_Z_nowrap (Rv64i.wadd (Rv64i.rget s rs1) imm)) in Hget by (apply wadd_range).
    rewrite (getReg_bind s m rs1 _ HRA Hrs1).
    rewrite translate_bind.
    cbn [add ZToReg MachineWidth_XLEN].
    rewrite <- (wadd_of_Z (rget s rs1) imm).
    rewrite (getReg_bind s m rs2 _ HRA Hrs2).
    rewrite (regToInt8_of_Z (rget s rs2) (rget_range s m rs2 HRA Hrs2)).
    apply (store_cycle s m D (word.of_Z (Rv64i.wadd (Rv64i.rget s rs1) imm))
             (Rv64i.wadd (Rv64i.rget s rs1) imm) (rget s rs2)
             (byte.of_Z (s.(mem) (Rv64i.wadd (Rv64i.rget s rs1) imm))) HRA HMA HPA).
    - apply word.unsigned_of_Z_nowrap. apply wadd_range.
    - exact Hget.
  Qed.

  (* ================================================================ *)
  (* step_agrees: one [Rv64i.step] matches one riscv-coq [run1] cycle. *)
  (* ================================================================ *)

  (* the per-step well-formedness side conditions (CROSSCHECK.md §5): branch/jump
     targets are 4-aligned and data accesses land in the tracked domain [D].
     Each holds for the loaded [core] (aligned code, mapped data). *)
  Definition WFstep (s:Rv64i.State) (m:RMach) (D: word -> Prop) : Prop :=
    WFfetch s m D
    /\ (forall a b imm, Rv64i.decode (Rv64i.fetch32 s) = Ibeq a b imm -> (Rv64i.wadd s.(pc) imm) mod 4 = 0)
    /\ (forall a b imm, Rv64i.decode (Rv64i.fetch32 s) = Iblt a b imm -> (Rv64i.wadd s.(pc) imm) mod 4 = 0)
    /\ (forall a b imm, Rv64i.decode (Rv64i.fetch32 s) = Ibge a b imm -> (Rv64i.wadd s.(pc) imm) mod 4 = 0)
    /\ (forall a b imm, Rv64i.decode (Rv64i.fetch32 s) = Ibgeu a b imm -> (Rv64i.wadd s.(pc) imm) mod 4 = 0)
    /\ (forall rd imm, Rv64i.decode (Rv64i.fetch32 s) = Ijal rd imm -> (Rv64i.wadd s.(pc) imm) mod 4 = 0)
    /\ (forall rd a imm, Rv64i.decode (Rv64i.fetch32 s) = Ijalr rd a imm ->
          ((Rv64i.wadd (Rv64i.rget s a) imm) - (Rv64i.wadd (Rv64i.rget s a) imm) mod 2) mod 4 = 0)
    /\ (forall rd a imm, Rv64i.decode (Rv64i.fetch32 s) = Ilbu rd a imm ->
          D (word.of_Z (Rv64i.wadd (Rv64i.rget s a) imm)))
    /\ (forall a b imm, Rv64i.decode (Rv64i.fetch32 s) = Isb a b imm ->
          D (word.of_Z (Rv64i.wadd (Rv64i.rget s a) imm))).

  Theorem step_agrees : forall s (m:RMach) D,
    Rrel s m D -> WFstep s m D ->
    Rv64i.decode (Rv64i.fetch32 s) <> Iunknown ->
    exists m', Run.run1 RV64I m = (Some tt, m') /\ Rrel (Rv64i.step s) m' D.
  Proof.
    intros s m D HR HWF Hni.
    destruct HWF as (Hf & Hbeq & Hblt & Hbge & Hbgeu & Hjal & Hjalr & Hlbu & Hsb).
    destruct (Rv64i.decode (Rv64i.fetch32 s)) as
      [rd rs1 imm|rd rs1 rs2|rd rs1 rs2|rd rs1 sh|rd rs1 imm|rs1 rs2 imm
      |rs1 rs2 imm|rs1 rs2 imm|rs1 rs2 imm|rs1 rs2 imm|rd imm|rd rs1 imm|] eqn:Hdec.
    - apply (exec_addi s m D rd rs1 imm HR Hf Hdec).
    - apply (exec_add s m D rd rs1 rs2 HR Hf Hdec).
    - apply (exec_or s m D rd rs1 rs2 HR Hf Hdec).
    - apply (exec_slli s m D rd rs1 sh HR Hf Hdec).
    - apply (exec_lbu s m D rd rs1 imm HR Hf Hdec (Hlbu _ _ _ eq_refl)).
    - apply (exec_sb s m D rs1 rs2 imm HR Hf Hdec (Hsb _ _ _ eq_refl)).
    - apply (exec_beq s m D rs1 rs2 imm HR Hf Hdec (Hbeq _ _ _ eq_refl)).
    - apply (exec_blt s m D rs1 rs2 imm HR Hf Hdec (Hblt _ _ _ eq_refl)).
    - apply (exec_bge s m D rs1 rs2 imm HR Hf Hdec (Hbge _ _ _ eq_refl)).
    - apply (exec_bgeu s m D rs1 rs2 imm HR Hf Hdec (Hbgeu _ _ _ eq_refl)).
    - apply (exec_jal s m D rd imm HR Hf Hdec (Hjal _ _ eq_refl)).
    - apply (exec_jalr s m D rd rs1 imm HR Hf Hdec (Hjalr _ _ _ eq_refl)).
    - exfalso; apply Hni; reflexivity.
  Qed.

End Step.

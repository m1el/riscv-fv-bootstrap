/-
  LowIR.Prog — the D7/D8 IR: LowIR.Ctrl's structured control flow plus
  activation-local CALLS and per-function stack FRAMES (LOWIR-DESIGN.md D7/D8).

  D7 (calls): a program is an `Env : Name → FunDef`. A call runs the callee's
  body in a FRESH zero-initialized register file with only the parameters bound
  to the caller's argument values; on return, only the declared return registers
  are copied back into the caller's file. Call sites carry their own arities
  (arity-indexed `Vector`s, fixed-size by construction); `wf` cross-checks them
  against the env. NOT SSA — registers are mutable locals.

  D8 (frames): `St` carries a semantic, program-unwritable stack pointer `sp`.
  Entering a function subtracts its `frameSize` (overflow below `stackLo` →
  `none`) and binds the new frame base to the function's designated `frameReg`
  (an ordinary IL register — the ONLY way a program observes sp). Returning
  restores the caller's `sp` structurally. No `alloca`.

  Also new over Ctrl: `ld`/`sd` (64-bit little-endian load/store, byte order
  identical to `Rv64i.State.loadWord/storeWord`) and `annot` (Ext. 9 — a
  semantic no-op carrying a string).

  `LowIR.Ctrl` is untouched (hex0 proofs stay green); `Outcome` is reused.
-/
import LowIR.Ctrl

namespace LowIR.Prog

open LowIR (Cond evalCond)
open LowIR.Ctrl (Outcome)
open Rv64i (Word Byte)

abbrev Reg := Nat
abbrev Name := String

/-- Structured statements. Ctrl's constructs minus its toy `call (g : Stmt)`,
    plus `ld`/`sd`/`annot` and the D7 named call. -/
inductive Stmt where
  | skip
  | seq    (a b : Stmt)
  | addi   (rd rs : Reg) (imm : BitVec 12)
  | add    (rd rs1 rs2 : Reg)
  | sub    (rd rs1 rs2 : Reg)
  | orr    (rd rs1 rs2 : Reg)
  | slli   (rd rs : Reg) (sh : Nat)
  | srli   (rd rs : Reg) (sh : Nat)
  | lbu    (rd rs : Reg) (imm : BitVec 12)
  | sb     (rbase rval : Reg) (imm : BitVec 12)
  | ld     (rd rs : Reg) (imm : BitVec 12)          -- rd := mem64[rs + sext imm]
  | sd     (rbase rval : Reg) (imm : BitVec 12)     -- mem64[rbase + sext imm] := rval
  | annot  (a : String)                             -- semantic no-op (Ext. 9)
  | ife    (c : Cond) (a b : Reg) (t e : Stmt)
  | while  (c : Cond) (a b : Reg) (body : Stmt)     -- continue scope
  | block  (body : Stmt)                            -- break scope
  | brkB   (k : Nat)
  | contL  (k : Nat)
  | ret
  | call   (argc rvc : Nat) (f : Name)
           (args : Vector Reg argc) (rets : Vector Reg rvc)
  | cref   (rd : Reg) (d : Name)     -- rd := address of const data object d
  | clen   (rd : Reg) (d : Name)     -- rd := length of const data object d
deriving Repr

/-- A function: declared parameter/return registers (callee-side names), a
    frame size in bytes, the register that receives the frame base, a body. -/
structure FunDef where
  argc      : Nat
  rvc       : Nat
  params    : Vector Reg argc
  rets      : Vector Reg rvc
  frameSize : Nat
  frameReg  : Reg
  body      : Stmt

abbrev Env := List (Name × FunDef)

/-- The program's read-only data segment: named constant byte objects,
    referenced from code as slices via `cref` (address) + `clen` (length). -/
abbrev Data := List (Name × List Byte)

/-- A whole program: functions plus const data. Where the data objects LIVE
    is not part of the program — the semantics takes a base map (`dbase`),
    ∀-quantifiable like D8's `sp₀`, so programs stay address-independent. -/
structure Program where
  env  : Env
  data : Data

/-- Data-free view (keeps pre-data call sites unchanged). -/
instance : Coe Env Program := ⟨fun env => ⟨env, []⟩⟩

/-- IL machine state: register file (x0 hardwired 0), byte memory, and the
    semantic stack pointer — no instruction writes `sp`; only call/return move it. -/
structure St where
  regs : Reg → Word
  mem  : Word → Byte
  sp   : Word

@[inline] def St.rget (s : St) (i : Reg) : Word := if i = 0 then 0 else s.regs i

@[inline] def St.rset (s : St) (i : Reg) (v : Word) : St :=
  if i = 0 then s else { s with regs := fun j => if j = i then v else s.regs j }

@[inline] def St.loadByte (s : St) (a : Word) : Byte := s.mem a

@[inline] def St.storeByte (s : St) (a : Word) (b : Byte) : St :=
  { s with mem := fun x => if x = a then b else s.mem x }

/-- Little-endian 64-bit load — byte order identical to `Rv64i.State.loadWord`. -/
def St.loadWord (s : St) (a : Word) : Word :=
  (s.mem a).setWidth 64 |||
  ((s.mem (a + 1)).setWidth 64) <<< 8 |||
  ((s.mem (a + 2)).setWidth 64) <<< 16 |||
  ((s.mem (a + 3)).setWidth 64) <<< 24 |||
  ((s.mem (a + 4)).setWidth 64) <<< 32 |||
  ((s.mem (a + 5)).setWidth 64) <<< 40 |||
  ((s.mem (a + 6)).setWidth 64) <<< 48 |||
  ((s.mem (a + 7)).setWidth 64) <<< 56

/-- Little-endian 64-bit store — identical to `Rv64i.State.storeWord`. -/
def St.storeWord (s : St) (a : Word) (v : Word) : St :=
  (((((((s.storeByte a (v.setWidth 8)
    ).storeByte (a + 1) ((v >>> 8).setWidth 8)
    ).storeByte (a + 2) ((v >>> 16).setWidth 8)
    ).storeByte (a + 3) ((v >>> 24).setWidth 8)
    ).storeByte (a + 4) ((v >>> 32).setWidth 8)
    ).storeByte (a + 5) ((v >>> 40).setWidth 8)
    ).storeByte (a + 6) ((v >>> 48).setWidth 8)
    ).storeByte (a + 7) ((v >>> 56).setWidth 8)

/-- Zero out `[base, base+len)` in a byte map — fresh-frame initialization, so a
    callee reads `0` (not a returned sibling's leftover slot-bytes) for any
    not-yet-written frame byte. This is the IL half of the zero-init decision
    (RESUME-CALL ★); the machine prologue's zero-frame segment is the other half.
    Without it the callee's entry `StInv` memory agreement is FALSE on the user
    frame (a sibling's dead `[ra][slots]` can land inside a later, larger frame). -/
def zeroRange (mem : Word → Byte) (base : Word) (len : Nat) : Word → Byte :=
  fun a => if base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + len then 0 else mem a

/-- Build the callee's entry state (D7/D8): check stack overflow against
    `stackLo`, fresh zero registers with params bound to the argument VALUES,
    frame base in `frameReg` (binds after params — `wf` keeps them disjoint),
    callee `sp` dropped by `frameSize` PLUS the padding oracle `pad`, caller's
    memory.  `none` = overflow.

    **P1 — the frame-padding oracle** (RESUME-PROGSIM §2): `frameReg` (the only
    IL-observable frame base) sits at `spCaller − frameSize`, its position
    UNCHANGED by `pad`; the propagated `sp` drops an extra `pad` bytes — the
    hole the IL skips over so that, instantiating `pad f := userOff f` at
    `compile_sim`, IL `sp` coincides with the machine `x2` at every call depth
    (the `[ra][slots]` overhead the compiler adds below each user frame). The
    overflow check accounts for the hole too, subsuming the stack budget.
    `pad = fun _ => 0` reproduces the pre-P1 semantics exactly. -/
def frameEnter (stackLo : Word) (fd : FunDef) (pad : Nat) (argVals : List Word)
    (mem : Word → Byte) (spCaller : Word) : Option St :=
  if spCaller.toNat < stackLo.toNat + fd.frameSize + pad then none
  else
    let frameBase := spCaller - BitVec.ofNat 64 fd.frameSize
    let newSp := frameBase - BitVec.ofNat 64 pad
    let withParams : Reg → Word :=
      (fd.params.toList.zip argVals).foldl
        (fun rf pv => fun r => if r = pv.1 then pv.2 else rf r) (fun _ => 0)
    some { regs := fun r => if r = fd.frameReg then frameBase else withParams r
           mem  := zeroRange mem frameBase fd.frameSize
           sp   := newSp }

/-- Clocked big-step semantics with outcomes. Ctrl's equations verbatim for the
    shared constructs; every recursive call is at `fuel` from `fuel+1`.

    `call`: lookup + arity check (`wf` guarantees them; dynamic `none` keeps the
    semantics total), enter the frame, run the body accepting `normal`/`ret`
    (an escaping brk/cont is `none` — `wf` bans it), then return to the CALLER's
    registers and `sp` (structural restore), with only `rets` copied back and
    the callee's memory kept. -/
def exec (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) :
    Nat → Stmt → St → Option (St × Outcome)
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some (s, .normal)
    | .annot _         => some (s, .normal)
    | .cref rd d       =>
        match dbase d with
        | some a => some (s.rset rd a, .normal)
        | none   => none
    | .clen rd d       =>
        match List.lookup d P.data with
        | some bs => some (s.rset rd (BitVec.ofNat 64 bs.length), .normal)
        | none    => none
    | .addi rd rs imm  => some (s.rset rd (s.rget rs + imm.signExtend 64), .normal)
    | .add  rd r1 r2   => some (s.rset rd (s.rget r1 + s.rget r2), .normal)
    | .sub  rd r1 r2   => some (s.rset rd (s.rget r1 - s.rget r2), .normal)
    | .orr  rd r1 r2   => some (s.rset rd (s.rget r1 ||| s.rget r2), .normal)
    | .slli rd rs sh   => some (s.rset rd (s.rget rs <<< sh), .normal)
    | .srli rd rs sh   => some (s.rset rd (s.rget rs >>> sh), .normal)
    | .lbu  rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd ((s.loadByte a).setWidth 64), .normal)
    | .sb   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeByte a ((s.rget rv).setWidth 8), .normal)
    | .ld   rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd (s.loadWord a), .normal)
    | .sd   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeWord a (s.rget rv), .normal)
    | .ife c a b t e   =>
        if evalCond c (s.rget a) (s.rget b)
        then exec P dbase pad stackLo fuel t s else exec P dbase pad stackLo fuel e s
    | .seq a b         =>
        match exec P dbase pad stackLo fuel a s with
        | some (s', .normal) => exec P dbase pad stackLo fuel b s'
        | other              => other
    | .block body      =>
        match exec P dbase pad stackLo fuel body s with
        | some (s', .normal)     => some (s', .normal)
        | some (s', .brk 0)      => some (s', .normal)
        | some (s', .brk (k+1))  => some (s', .brk k)
        | some (s', .cont k)     => some (s', .cont k)
        | some (s', .ret)        => some (s', .ret)
        | none                   => none
    | .while c a b body =>
        if evalCond c (s.rget a) (s.rget b) then
          match exec P dbase pad stackLo fuel body s with
          | some (s', .normal)     => exec P dbase pad stackLo fuel (.while c a b body) s'
          | some (s', .cont 0)     => exec P dbase pad stackLo fuel (.while c a b body) s'
          | some (s', .cont (k+1)) => some (s', .cont k)
          | some (s', .brk k)      => some (s', .brk k)
          | some (s', .ret)        => some (s', .ret)
          | none                   => none
        else some (s, .normal)
    | .brkB k          => some (s, .brk k)
    | .contL k         => some (s, .cont k)
    | .ret             => some (s, .ret)
    | .call argc rvc f args rets =>
        match List.lookup f P.env with
        | none => none
        | some fd =>
          if fd.argc == argc && fd.rvc == rvc then
            match frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp with
            | none => none                                       -- stack overflow
            | some callee =>
              match exec P dbase pad stackLo fuel fd.body callee with
              | some (s1, .normal) | some (s1, .ret) =>
                  let retVals := fd.rets.toList.map s1.rget
                  some ((rets.toList.zip retVals).foldl
                          (fun st rv => st.rset rv.1 rv.2)
                          { s with mem := s1.mem },              -- caller regs+sp, callee mem
                        .normal)
              | some _ => none                                   -- escaping brk/cont
              | none   => none
          else none

/-- Well-formedness (Ext. 8): brk/cont indices in scope, shifts `< 64`, call
    arities agree with the env. `blockD`/`loopD` = enclosing block/loop counts. -/
def wf (P : Program) : Nat → Nat → Stmt → Bool
  | bD, lD, .seq a b          => wf P bD lD a && wf P bD lD b
  | bD, lD, .ife _ _ _ t e    => wf P bD lD t && wf P bD lD e
  | bD, lD, .while _ _ _ body => wf P bD (lD+1) body
  | bD, lD, .block body       => wf P (bD+1) lD body
  | bD, _,  .brkB k           => k < bD
  | _,  lD, .contL k          => k < lD
  | _,  _,  .slli _ _ sh      => sh < 64
  | _,  _,  .srli _ _ sh      => sh < 64
  | _,  _,  .call argc rvc f _ _ =>
      match List.lookup f P.env with
      | some fd => fd.argc == argc && fd.rvc == rvc
      | none    => false
  | _,  _,  .cref _ d         => (List.lookup d P.data).isSome
  | _,  _,  .clen _ d         => (List.lookup d P.data).isSome
  | _,  _,  _                 => true

/-- Program well-formedness: every body is `wf` with NO enclosing block/loop
    (an escaping brk/cont at function level is ill-formed), no function binds
    its `frameReg` as a parameter (frameReg would shadow the param binding),
    every function name is non-empty (the `compileProgT` entry stub reserves the
    `""` key and `fns.filter (·.1 != "")` would silently drop a `""`-named
    function — closing that gap discharges ProgSim `hfn`'s `g ≠ ""` premise), and
    data object names are unique. -/
def wfProgram (P : Program) : Bool :=
  P.env.all (fun nf =>
    wf P 0 0 nf.2.body && !(nf.2.params.toList.contains nf.2.frameReg) && nf.1 != "")
  && (P.data.map Prod.fst).eraseDups.length == P.data.length

/-- Data-free convenience (pre-data name, used by the existing tests). -/
def wfEnv (env : Env) : Bool := wfProgram env

/-! ### Data-segment layout — the SINGLE source of truth.

    Both altitudes consume these: the IL harness places `dataSegment` at a
    chosen base (`installData`) with addresses from `dataOffsetsFrom 0`
    (`dbaseOf`); the compiler appends the SAME `dataSegment` to the blob with
    addresses from `dataOffsetsFrom segStart`. There is no second layout
    convention to keep in sync — and `dataSegment_at`/`installData_at` below
    PROVE the offsets↔bytes correspondence once, for both. -/

/-- Round up to 8. -/
def pad8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- Byte offset of each object, packed 8-aligned starting at `start`. -/
def dataOffsetsFrom (start : Nat) : Data → List (Name × Nat)
  | [] => []
  | (n, bs) :: rest => (n, start) :: dataOffsetsFrom (start + pad8 bs.length) rest

/-- The flat data segment: each object zero-padded to 8 (offsets are exactly
    `dataOffsetsFrom 0`). -/
def dataSegment : Data → List Byte
  | [] => []
  | (_, bs) :: rest =>
      bs ++ List.replicate (pad8 bs.length - bs.length) 0 ++ dataSegment rest

/-- The address map when the segment sits at `base`. -/
def dbaseOf (base : Word) (data : Data) : Name → Option Word := fun d =>
  (List.lookup d (dataOffsetsFrom 0 data)).map (fun off => base + BitVec.ofNat 64 off)

/-- Memory with the segment installed at `base` (out of range → `mem`). -/
def installData (base : Word) (data : Data) (mem : Word → Byte) : Word → Byte :=
  fun a => (((dataSegment data)[(a - base).toNat]?).getD (mem a))

/-! #### The correspondence lemmas (proved once, used by both altitudes). -/

theorem pad8_ge (n : Nat) : n ≤ pad8 n := by unfold pad8; omega

/-- Offsets are monotone in the start. -/
theorem dataOffsetsFrom_le {n : Name} :
    ∀ (start : Nat) (data : Data) {off : Nat},
      List.lookup n (dataOffsetsFrom start data) = some off → start ≤ off
  | _, [], _, h => by simp [dataOffsetsFrom] at h
  | start, (n', bs') :: rest, off, h => by
      simp only [dataOffsetsFrom, List.lookup] at h
      split at h
      · cases h; exact Nat.le_refl _
      · exact Nat.le_trans (by omega)
          (dataOffsetsFrom_le (start + pad8 bs'.length) rest h)

/-- Shifting the start shifts every offset — the compiler's table
    (`dataOffsetsFrom segStart`) IS the harness's (`dataOffsetsFrom 0`)
    translated by `segStart`; no separate convention. -/
theorem dataOffsetsFrom_shift (s : Nat) {n : Name} :
    ∀ (start : Nat) (data : Data),
      List.lookup n (dataOffsetsFrom (s + start) data)
        = (List.lookup n (dataOffsetsFrom start data)).map (s + ·)
  | _, [] => by simp [dataOffsetsFrom]
  | start, (n', bs') :: rest => by
      simp only [dataOffsetsFrom, List.lookup]
      split
      · rfl
      · rw [Nat.add_assoc]; exact dataOffsetsFrom_shift s (start + pad8 bs'.length) rest

/-- An object's bytes fit inside the segment at its offset. -/
theorem dataOffsetsFrom_fits {n : Name} {bs : List Byte} :
    ∀ (start : Nat) (data : Data) {off : Nat},
      List.lookup n data = some bs →
      List.lookup n (dataOffsetsFrom start data) = some off →
      off - start + bs.length ≤ (dataSegment data).length
  | _, [], _, hn, _ => by simp [List.lookup] at hn
  | start, (n', bs') :: rest, off, hn, ho => by
      simp only [dataOffsetsFrom, List.lookup] at hn ho
      simp only [dataSegment, List.length_append, List.length_replicate]
      split at hn
      · cases hn
        split at ho
        · cases ho; have := pad8_ge bs.length; omega
        · simp_all
      · split at ho
        · simp_all
        · have hle := dataOffsetsFrom_le (start + pad8 bs'.length) rest ho
          have := dataOffsetsFrom_fits (start + pad8 bs'.length) rest hn ho
          have := pad8_ge bs'.length
          omega

/-- THE correspondence: byte `i` of object `n` sits at `offset n + i` in the
    segment — whoever placed the segment (IL harness or compiler blob). -/
theorem dataSegment_at {n : Name} {bs : List Byte} :
    ∀ (start : Nat) (data : Data) {off i : Nat},
      List.lookup n data = some bs →
      List.lookup n (dataOffsetsFrom start data) = some off →
      (h : i < bs.length) →
      (dataSegment data)[off - start + i]? = some bs[i]
  | _, [], _, _, hn, _, _ => by simp [List.lookup] at hn
  | start, (n', bs') :: rest, off, i, hn, ho, hi => by
      simp only [dataOffsetsFrom, List.lookup] at hn ho
      simp only [dataSegment]
      split at hn
      · cases hn
        split at ho
        · cases ho
          rw [Nat.sub_self, Nat.zero_add,
              List.getElem?_append_left (by simp; omega),
              List.getElem?_append_left hi,
              List.getElem?_eq_getElem hi]
        · simp_all
      · split at ho
        · simp_all
        · have hle := dataOffsetsFrom_le (start + pad8 bs'.length) rest ho
          have hrec := dataSegment_at (start + pad8 bs'.length) rest hn ho hi
          have hp := pad8_ge bs'.length
          rw [List.append_assoc, List.getElem?_append_right (by omega),
              List.getElem?_append_right (by simp [List.length_replicate]; omega)]
          simp only [List.length_replicate]
          have heq : off - start + i - bs'.length - (pad8 bs'.length - bs'.length)
              = off - (start + pad8 bs'.length) + i := by omega
          rw [heq]; exact hrec

/-- The IL-side read: `installData` returns exactly the object's byte at any
    in-range index (no side conditions beyond the segment fitting in 2⁶⁴ —
    BitVec cancellation handles the base). -/
theorem installData_at (base : Word) {data : Data} (mem : Word → Byte)
    {n : Name} {bs : List Byte} {off i : Nat}
    (hn : List.lookup n data = some bs)
    (ho : List.lookup n (dataOffsetsFrom 0 data) = some off)
    (hi : i < bs.length) (hsz : (dataSegment data).length < 2 ^ 64) :
    installData base data mem (base + BitVec.ofNat 64 (off + i)) = bs[i] := by
  have hfits := dataOffsetsFrom_fits 0 data hn ho
  have hseg := dataSegment_at 0 data hn ho hi
  unfold installData
  have hcancel : base + BitVec.ofNat 64 (off + i) - base = BitVec.ofNat 64 (off + i) := by
    rw [BitVec.add_comm base, BitVec.add_sub_cancel]
  rw [hcancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.sub_zero] at hseg
  rw [hseg]; rfl

/-- Top-level entry: install the data objects at `dataBase`, then call `f`
    with argument VALUES on a fresh machine — memory `mem`, stack top `sp0`.
    Returns the callee's final state (read results from `f`'s `rets`). -/
def run (P : Program) (stackLo : Word) (fuel : Nat) (f : Name) (argVals : List Word)
    (mem : Word → Byte) (sp0 : Word) (pad : Name → Nat := fun _ => 0)
    (dataBase : Word := 0x30000) : Option St :=
  match List.lookup f P.env with
  | none => none
  | some fd =>
    let dbase := dbaseOf dataBase P.data
    let mem'  := installData dataBase P.data mem
    match frameEnter stackLo fd (pad f) argVals mem' sp0 with
    | none => none
    | some st0 =>
      match exec P dbase pad stackLo fuel fd.body st0 with
      | some (s1, .normal) | some (s1, .ret) => some s1
      | _ => none

/-! ### Sanity battery (`#guard` — executable, no proofs). -/

def zeroMem : Word → Byte := fun _ => 0

/-- Test fixture: `sub3 (a,b,c) = (a+b)-c`, no frame. Params x10 x11 x12 → ret x10. -/
def sub3 : FunDef :=
  { argc := 3, rvc := 1, params := #v[10, 11, 12], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.add 6 10 11) (.sub 10 6 12) }

/-- `sumTo (n) = 1+2+…+n` via a while loop with continue-free body. x10=n → x10. -/
def sumTo : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.addi 6 0 0) <|                    -- acc := 0
            .seq (.addi 7 0 1) <|                    -- i := 1
            .seq (.while .geu 10 7                   -- while n ≥u i  (i counts up)
                   (.seq (.add 6 6 7) (.addi 7 7 1)))
                 (.addi 10 6 0) }                    -- ret := acc

/-- `frameLocal (v) : write v to the frame local at frameReg+0 via sd, read it
    back via ld, return it` — the D8 ld/sd/frame roundtrip. x8 = frame base. -/
def frameLocal : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
    frameSize := 16, frameReg := 8
    body := .seq (.sd 8 10 0) <|                     -- mem64[frame+0] := v
            .seq (.addi 10 0 0) <|                   -- clobber x10
            (.ld 10 8 0) }                           -- x10 := mem64[frame+0]

/-- `caller (v) = frameLocal(v+1) + 1`, i.e. v+2 — a two-function call. -/
def caller : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.addi 11 10 1) <|                          -- x11 := v+1
            .seq (.call 1 1 "frameLocal" #v[11] #v[12]) <|   -- x12 := frameLocal(x11)
            (.addi 10 12 1) }                                -- ret := x12+1

/-- Early `ret` via block/brk interplay: returns 7 out of a nested block. -/
def early : FunDef :=
  { argc := 0, rvc := 1, params := #v[], rets := #v[10]
    frameSize := 0, frameReg := 5
    body := .seq (.block (.seq (.addi 10 0 7) (.seq .ret (.addi 10 0 9))))
                 (.addi 10 0 3) }   -- unreachable: ret escapes the block

/-- Hog: frameSize bigger than the whole stack — must trip the overflow check. -/
def hog : FunDef :=
  { argc := 0, rvc := 0, params := #v[], rets := #v[]
    frameSize := 0x10000, frameReg := 8, body := .skip }

def testEnv : Env :=
  [("sub3", sub3), ("sumTo", sumTo), ("frameLocal", frameLocal),
   ("caller", caller), ("early", early), ("hog", hog),
   ("hogCaller", { argc := 0, rvc := 0, params := #v[], rets := #v[]
                   frameSize := 0, frameReg := 5
                   body := .call 0 0 "hog" #v[] #v[] })]

def STACK_LO : Word := 0x4000
def SP0      : Word := 0x8000

def testRun (f : Name) (args : List Word) : Option St :=
  run testEnv STACK_LO 1000 f args zeroMem SP0

-- the whole test env is well-formed
#guard wfEnv testEnv

-- arithmetic: (30+12)-2 = 40
#guard (testRun "sub3" [30, 12, 2]).map (·.rget 10 |>.toNat) = some 40

-- loop: sum 1..10 = 55; sum 1..0 = 0
#guard (testRun "sumTo" [10]).map (·.rget 10 |>.toNat) = some 55
#guard (testRun "sumTo" [0]).map (·.rget 10 |>.toNat) = some 0

-- frame local sd/ld roundtrip
#guard (testRun "frameLocal" [0xDEAD]).map (·.rget 10 |>.toNat) = some 0xDEAD

-- two-function call: caller(5) = 7; callee's regs must NOT leak (x11 stays caller's v+1)
#guard (testRun "caller" [5]).map (fun s => ((s.rget 10).toNat, (s.rget 11).toNat))
        = some (7, 6)

-- callee frame is BELOW caller's sp; caller's sp is restored after the call:
-- run "caller" and check final sp = entry sp (sp0 - caller.frameSize = sp0)
#guard (testRun "caller" [5]).map (·.sp) = some SP0

-- ret escapes block and skips the rest of the function
#guard (testRun "early" []).map (·.rget 10 |>.toNat) = some 7

-- annot is a no-op
#guard (run testEnv STACK_LO 100 "sub3" [1, 2, 0] zeroMem SP0).map (·.rget 10)
        = (run [("sub3", { sub3 with body := .seq (.annot "hi") sub3.body })]
               STACK_LO 100 "sub3" [1, 2, 0] zeroMem SP0).map (·.rget 10)

-- stack overflow: hog's frame doesn't fit → none (directly and through a call)
#guard testRun "hog" [] = none
#guard testRun "hogCaller" [] = none

-- unknown function / bad arity at a call site → none
#guard (run testEnv STACK_LO 100 "nosuch" [] zeroMem SP0) = none
#guard (run [("bad", { caller with body := .call 2 1 "frameLocal" #v[10, 11] #v[12] }),
             ("frameLocal", frameLocal)]
            STACK_LO 100 "bad" [1] zeroMem SP0) = none

/-! Nested calls, 3 deep: f3(v) = f2(v)+1 = (f1(v)+1)+1 = v+3, each with a
    frame local proving the frames don't clobber each other. -/
def chainFn (callee : Option Name) : FunDef :=
  { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
    frameSize := 8, frameReg := 8
    body :=
      match callee with
      | none   => .seq (.sd 8 10 0) (.seq (.addi 10 0 0) (.seq (.ld 10 8 0) (.addi 10 10 1)))
      | some g => .seq (.sd 8 10 0) <|                 -- park v in my frame
                  .seq (.call 1 1 g #v[10] #v[11]) <|  -- x11 := g(v)
                  .seq (.ld 12 8 0) <|                 -- reload v — must be intact
                  .seq (.sub 13 11 12) <|              -- g(v) - v  (sanity distance)
                  (.addi 10 11 1) }                    -- ret := g(v)+1

def chainEnv : Env :=
  [("f1", chainFn none), ("f2", chainFn (some "f1")), ("f3", chainFn (some "f2"))]

#guard wfEnv chainEnv
#guard (run chainEnv STACK_LO 1000 "f3" [40] zeroMem SP0).map (·.rget 10 |>.toNat)
        = some 43

/-! Recursion smoke test (policy C5 open — executably it just works on fuel):
    rec(n) = n + rec(n-1), rec(0) = 0 — sumTo again, but recursive, with each
    activation parking `n` in its own frame across the recursive call. -/
def recSum : Env :=
  [("rec", { argc := 1, rvc := 1, params := #v[10], rets := #v[10]
             frameSize := 8, frameReg := 8
             body := .seq (.addi 7 0 1) <|
                     .ife .geu 10 7                            -- if n ≥u 1:
                       (.seq (.sd 8 10 0) <|                   --   park n
                        .seq (.addi 10 10 (-1 : BitVec 12)) <| --   n-1
                        .seq (.call 1 1 "rec" #v[10] #v[11]) <| --  x11 := rec(n-1)
                        .seq (.ld 12 8 0) <|                   --   reload n
                        (.add 10 12 11))                       --   ret := n + rec(n-1)
                       (.addi 10 0 0) })]                      -- else ret := 0

#guard wfEnv recSum
#guard (run recSum STACK_LO 1000 "rec" [10] zeroMem SP0).map (·.rget 10 |>.toNat)
        = some 55
-- deep recursion eats stack: 8 bytes/frame, 0x4000 stack → 2048 frames max;
-- rec(3000) must hit the overflow check, not wrap
#guard (run recSum STACK_LO 100000 "rec" [3000] zeroMem SP0) = none

/-! Const data: `cref`/`clen` — sum the bytes of a data object (slice = ptr+len). -/
def sumdFn : FunDef :=
  { argc := 0, rvc := 2, params := #v[], rets := #v[10, 11]
    frameSize := 0, frameReg := 3
    body := .seq (.cref 5 "tbl") <|            -- p := &tbl
            .seq (.clen 11 "tbl") <|           -- ret2 := len
            .seq (.addi 6 0 0) <|              -- acc := 0
            .seq (.addi 7 0 0) <|              -- i := 0
            .seq (.while .lt 7 11
                   (.seq (.add 30 5 7) <|
                    .seq (.lbu 9 30 0) <|
                    .seq (.add 6 6 9) (.addi 7 7 1)))
                 (.addi 10 6 0) }              -- ret1 := acc

def sumData : Program :=
  { env := [("sumd", sumdFn)], data := [("tbl", [1, 2, 3, 250])] }

#guard wfProgram sumData
#guard (run sumData 0 1000 "sumd" [] zeroMem SP0).map
        (fun s => ((s.rget 10).toNat, (s.rget 11).toNat)) = some (256, 4)
-- unknown data object: wf rejects, exec goes none
#guard !wfProgram { sumData with
        env := [("bad", { sumdFn with body := .cref 5 "nope" })] }
#guard (run { sumData with data := [] } 0 1000 "sumd" [] zeroMem SP0) = none

end LowIR.Prog

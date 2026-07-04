/-
  LowIR.ProgSim.Defs — the `compile_sim`-for-Prog relation and its executable
  scaffolding (RESUME-PROGSIM §3). This file is the FOUNDATION of the D7/D8
  compiler-correctness campaign: the simulation `Layout`/`Installed`/`StInv`,
  the write-footprint instrumentation `execT`, and (in ProgSim/Main, later) the
  top-level theorems. Everything here is a real, `sorry`-free DEFINITION plus a
  handful of `sorry`'d equivalence theorems whose statements are the deliverable
  — the proofs land in later phases.

  Discipline (RESUME-PROGSIM §6): every relation piece gets an EXECUTABLE
  sanity check (`#guard`) against real compiled programs BEFORE any lemma leans
  on it. This file's #guards compile fixtures through the FROZEN compiler, load
  the bytes into the trusted `Rv64i` machine, and check the relation's
  computable shadow holds — a wrong def is caught here in seconds, not inside
  Phase 5 in weeks.

  Commit A (this file, first cut): `Layout`, `layoutOf`, `Installed` + the
  computable `codeInstalledB`/`dataInstalledB`, `execT` + `execT_erase`. The
  relation `StInv`/`MachPriv`/`SimPre` and the `lower_sim`/`call_sim`/`prog_sim`
  statements arrive in a follow-up commit.
-/
import LowIR.Compile
import LowIR.ProgSim.ExecFacts
import LowIR.ProgSim.WordMem

namespace LowIR.ProgSim

open LowIR (Cond evalCond)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (Reg Name FunDef Env Data Program frameEnter
                 dataSegment dataOffsetsFrom pad8 dbaseOf installData)
open LowIR.Compile (compileProgT progBytes userOff totalFrame slotOff maxRegF)
open Rv64i (Word Byte Instr State)

-- `St`/`exec`/`Stmt` collide with the Ctrl-level `LowIR.St`/`LowIR.exec`
-- (enclosing-namespace lookup wins over `open LowIR.Prog`), so alias the Prog
-- ones locally and qualify the rest.
local notation "PStmt" => LowIR.Prog.Stmt
abbrev St := LowIR.Prog.St

/-! ## §3.1 (part) — where the code and data live: `Layout` and `Installed` -/

/-- The compiled artifact's placement, per RESUME-PROGSIM §3.1: the base
    address, the resolved instruction stream (`= (compileProgT P entry).1`), the
    function→byte-offset table, the byte offset where the data segment starts
    inside the blob (`pad8 (4 * #instrs)` — every instruction is 4 bytes after
    resolution), and the program's const data. -/
structure Layout where
  codeBase : Word
  instrs   : List Instr
  fnTab    : List (Name × Nat)
  segStart : Nat
  data     : Data
  stackLo  : Word          -- the stack floor (a fixed per-run constant, like
                           -- `codeBase`); the free stack `[stackLo, sp)` below the
                           -- current frame is machine-private (C2 — see `StInv`).
deriving Repr

/-- Build the `Layout` for `entry` at `codeBase` straight from the FROZEN
    compiler. `none` iff the program is uncompilable (same condition as
    `compileProgT`). `segStart` is recomputed here from the resolved stream
    and is DEFINITIONALLY the compiler's `pad8 codeEnd` (proved in Phase 2). -/
def layoutOf (P : Program) (entry : Name) (codeBase stackLo : Word) : Option Layout :=
  match compileProgT P entry with
  | some (is, fns, _) =>
      some { codeBase, instrs := is, fnTab := fns,
             segStart := pad8 (4 * is.length), data := P.data, stackLo }
  | none => none

/-- The machine halt pc: the self-loop landing pad the compiler puts at
    `codeBase+4` (the entry stub is `jal ra,entry` at `codeBase`; the entry
    returns to `codeBase+4`). Run the machine with `runFuel L.haltPc`. -/
def Layout.haltPc (L : Layout) : Word := L.codeBase + 4

/-- Address one past the last instruction — the code window's top. -/
def Layout.codeEnd (L : Layout) : Word :=
  L.codeBase + BitVec.ofNat 64 (4 * L.instrs.length)

/-- `Installed L m` — the compiled blob is faithfully present in `m`'s memory:
    (code) the 32-bit word at `codeBase + 4j` decodes via the TRUSTED
    `Rv64i.decode` to `instrs[j]`; (data) the const-data byte at
    `codeBase + segStart + i` equals `dataSegment data`'s byte `i`
    (`Prog.dataSegment_at` already relates that segment to the object bytes). -/
def Installed (L : Layout) (m : State) : Prop :=
  (∀ (j : Nat) (h : j < L.instrs.length),
      Rv64i.decode (Rv64i.fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) })
        = L.instrs[j]'h)
  ∧ (∀ (i : Nat) (h : i < (dataSegment L.data).length),
      m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i)) = (dataSegment L.data)[i]'h)

/-! ### Computable shadows of `Installed` (the #guard oracle). -/

/-- Every instruction slot decodes correctly (computable form of `Installed`'s
    code conjunct). -/
def codeInstalledB (L : Layout) (m : State) : Bool :=
  (List.range L.instrs.length).all fun j =>
    Rv64i.decode (Rv64i.fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) })
      == L.instrs.getD j .unknown

/-- Every data byte is present (computable form of `Installed`'s data conjunct). -/
def dataInstalledB (L : Layout) (m : State) : Bool :=
  (List.range (dataSegment L.data).length).all fun i =>
    m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i))
      == (dataSegment L.data).getD i 0

/-! ## §3.4 — the write-footprint instrumentation `execT`.

    `execT` is `Prog.exec` verbatim, additionally accumulating the list of BYTE
    ADDRESSES written (`sb` → 1, `sd` → 8, calls → the callee's footprint). The
    `lower_sim` footprint side condition is then `ws.all (¬ MachPriv ·)` — no
    IL store lands in the machine's private bytes (code, spill slots, saved ra,
    pad holes). `execT_erase` says the instrumentation is observationally
    invisible: erasing the footprint recovers `exec` exactly. -/
def execT (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) :
    Nat → PStmt → St → Option (St × Outcome × List Word)
  | 0,      _,    _ => none
  | fuel+1, stmt, s =>
    match stmt with
    | .skip            => some (s, .normal, [])
    | .annot _         => some (s, .normal, [])
    | .cref rd d       =>
        match dbase d with
        | some a => some (s.rset rd a, .normal, [])
        | none   => none
    | .clen rd d       =>
        match List.lookup d P.data with
        | some bs => some (s.rset rd (BitVec.ofNat 64 bs.length), .normal, [])
        | none    => none
    | .addi rd rs imm  => some (s.rset rd (s.rget rs + imm.signExtend 64), .normal, [])
    | .add  rd r1 r2   => some (s.rset rd (s.rget r1 + s.rget r2), .normal, [])
    | .sub  rd r1 r2   => some (s.rset rd (s.rget r1 - s.rget r2), .normal, [])
    | .orr  rd r1 r2   => some (s.rset rd (s.rget r1 ||| s.rget r2), .normal, [])
    | .slli rd rs sh   => some (s.rset rd (s.rget rs <<< sh), .normal, [])
    | .srli rd rs sh   => some (s.rset rd (s.rget rs >>> sh), .normal, [])
    | .lbu  rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd ((s.loadByte a).setWidth 64), .normal, [])
    | .sb   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeByte a ((s.rget rv).setWidth 8), .normal, [a])
    | .ld   rd rs imm  => let a := s.rget rs + imm.signExtend 64
                          some (s.rset rd (s.loadWord a), .normal, [])
    | .sd   rb rv imm  => let a := s.rget rb + imm.signExtend 64
                          some (s.storeWord a (s.rget rv), .normal,
                                [a, a+1, a+2, a+3, a+4, a+5, a+6, a+7])
    | .ife c a b t e   =>
        if evalCond c (s.rget a) (s.rget b)
        then execT P dbase pad stackLo fuel t s else execT P dbase pad stackLo fuel e s
    | .seq a b         =>
        match execT P dbase pad stackLo fuel a s with
        | some (s', .normal, ws) =>
            match execT P dbase pad stackLo fuel b s' with
            | some (s'', o, ws') => some (s'', o, ws ++ ws')
            | none               => none
        | other                  => other
    | .block body      =>
        match execT P dbase pad stackLo fuel body s with
        | some (s', .normal, ws)     => some (s', .normal, ws)
        | some (s', .brk 0, ws)      => some (s', .normal, ws)
        | some (s', .brk (k+1), ws)  => some (s', .brk k, ws)
        | some (s', .cont k, ws)     => some (s', .cont k, ws)
        | some (s', .ret, ws)        => some (s', .ret, ws)
        | none                       => none
    | .while c a b body =>
        if evalCond c (s.rget a) (s.rget b) then
          match execT P dbase pad stackLo fuel body s with
          | some (s', .normal, ws) =>
              match execT P dbase pad stackLo fuel (.while c a b body) s' with
              | some (s'', o, ws') => some (s'', o, ws ++ ws')
              | none               => none
          | some (s', .cont 0, ws) =>
              match execT P dbase pad stackLo fuel (.while c a b body) s' with
              | some (s'', o, ws') => some (s'', o, ws ++ ws')
              | none               => none
          | some (s', .cont (k+1), ws) => some (s', .cont k, ws)
          | some (s', .brk k, ws)      => some (s', .brk k, ws)
          | some (s', .ret, ws)        => some (s', .ret, ws)
          | none                       => none
        else some (s, .normal, [])
    | .brkB k          => some (s, .brk k, [])
    | .contL k         => some (s, .cont k, [])
    | .ret             => some (s, .ret, [])
    | .call argc rvc f args rets =>
        match List.lookup f P.env with
        | none => none
        | some fd =>
          if fd.argc == argc && fd.rvc == rvc then
            match frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp with
            | none => none
            | some callee =>
              match execT P dbase pad stackLo fuel fd.body callee with
              | some (s1, .normal, ws) | some (s1, .ret, ws) =>
                  let retVals := fd.rets.toList.map s1.rget
                  some ((rets.toList.zip retVals).foldl
                          (fun st rv => st.rset rv.1 rv.2)
                          { s with mem := s1.mem }, .normal, ws)
              | some _ => none
              | none   => none
          else none

/-- Erase a footprint-carrying result to a plain `exec` result. -/
def eraseW : St × Outcome × List Word → St × Outcome := fun t => (t.1, t.2.1)

/-- The core equivalence: erasing `execT`'s footprint (via `Option.map`) yields
    `exec` EXACTLY. Both functions recurse only at `fuel` (structural), so a
    plain fuel induction with the IH quantified over all `stmt`/`s` suffices;
    every case is `exec`/`execT`'s shared control structure with the footprint
    dropped by `eraseW`. -/
theorem execT_map_exec (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) :
    ∀ (fuel : Nat) (stmt : PStmt) (s : St),
      (execT P dbase pad stackLo fuel stmt s).map eraseW
        = LowIR.Prog.exec P dbase pad stackLo fuel stmt s := by
  intro fuel
  induction fuel with
  | zero => intro stmt s; rfl
  | succ fuel ih =>
    intro stmt s
    cases stmt with
    | skip => rfl
    | annot a => rfl
    | addi rd rs imm => rfl
    | add rd r1 r2 => rfl
    | sub rd r1 r2 => rfl
    | orr rd r1 r2 => rfl
    | slli rd rs sh => rfl
    | srli rd rs sh => rfl
    | lbu rd rs imm => rfl
    | sb rb rv imm => rfl
    | ld rd rs imm => rfl
    | sd rb rv imm => rfl
    | brkB k => rfl
    | contL k => rfl
    | ret => rfl
    | cref rd d =>
        simp only [execT, LowIR.Prog.exec]; cases dbase d <;> rfl
    | clen rd d =>
        simp only [execT, LowIR.Prog.exec]; cases List.lookup d P.data <;> rfl
    | ife c a b t e =>
        simp only [execT, LowIR.Prog.exec, apply_ite (Option.map eraseW), ih t s, ih e s]
    | seq a b =>
        simp only [execT, LowIR.Prog.exec, ← ih a s]
        cases execT P dbase pad stackLo fuel a s with
        | none => rfl
        | some t =>
            obtain ⟨sa, oa, wa⟩ := t
            cases oa with
            | normal =>
                simp only [Option.map_some, eraseW, ← ih b sa]
                cases execT P dbase pad stackLo fuel b sa with
                | none => rfl
                | some t2 => obtain ⟨sb, ob, wb⟩ := t2; rfl
            | brk k => rfl
            | cont k => rfl
            | ret => rfl
    | block body =>
        simp only [execT, LowIR.Prog.exec, ← ih body s]
        cases execT P dbase pad stackLo fuel body s with
        | none => rfl
        | some t =>
            obtain ⟨sb, ob, wb⟩ := t
            cases ob with
            | normal => rfl
            | brk k => cases k <;> rfl
            | cont k => rfl
            | ret => rfl
    | «while» c a b body =>
        simp only [execT, LowIR.Prog.exec]
        split
        · simp only [← ih body s]
          cases execT P dbase pad stackLo fuel body s with
          | none => rfl
          | some t =>
              obtain ⟨s', oc, ws⟩ := t
              cases oc with
              | normal =>
                  simp only [Option.map_some, eraseW, ← ih (.while c a b body) s']
                  cases execT P dbase pad stackLo fuel (.while c a b body) s' with
                  | none => rfl
                  | some t2 => obtain ⟨s2, o2, ws2⟩ := t2; rfl
              | cont k =>
                  cases k with
                  | zero =>
                      simp only [Option.map_some, eraseW, ← ih (.while c a b body) s']
                      cases execT P dbase pad stackLo fuel (.while c a b body) s' with
                      | none => rfl
                      | some t2 => obtain ⟨s2, o2, ws2⟩ := t2; rfl
                  | succ k => rfl
              | brk k => rfl
              | ret => rfl
        · rfl
    | call argc rvc f args rets =>
        simp only [execT, LowIR.Prog.exec]
        cases hL : List.lookup f P.env with
        | none => simp [hL]
        | some fd =>
            cases ha : (fd.argc == argc && fd.rvc == rvc) with
            | false => simp [hL, ha]
            | true =>
                cases hF : frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp with
                | none => simp [hL, ha, hF]
                | some callee =>
                    simp only [hL, ha, hF, if_true, ← ih fd.body callee]
                    cases execT P dbase pad stackLo fuel fd.body callee with
                    | none => rfl
                    | some t => obtain ⟨s1, o1, ws⟩ := t; cases o1 <;> rfl

/-- **`execT_erase`** — the footprint instrumentation is observationally
    invisible: whenever `execT` succeeds with some footprint, `exec` succeeds
    with the SAME final state and outcome (corollary of `execT_map_exec`). -/
theorem execT_erase (P : Program) (dbase : Name → Option Word) (pad : Name → Nat)
    (stackLo : Word) (fuel : Nat) (stmt : PStmt) (s s' : St) (o : Outcome)
    (ws : List Word) :
    execT P dbase pad stackLo fuel stmt s = some (s', o, ws) →
    LowIR.Prog.exec P dbase pad stackLo fuel stmt s = some (s', o) := by
  intro h
  rw [← execT_map_exec P dbase pad stackLo fuel stmt s, h]
  rfl

/-- Instrumented top-level runner (mirrors `Prog.run`, keeps the footprint) —
    the executable interface `execT_erase` and the #guards go through. -/
def runT (P : Program) (stackLo : Word) (fuel : Nat) (f : Name) (argVals : List Word)
    (mem : Word → Byte) (sp0 : Word) (pad : Name → Nat := fun _ => 0)
    (dataBase : Word := 0x30000) : Option (St × Outcome × List Word) :=
  match List.lookup f P.env with
  | none => none
  | some fd =>
    let dbase := dbaseOf dataBase P.data
    let mem'  := installData dataBase P.data mem
    match frameEnter stackLo fd (pad f) argVals mem' sp0 with
    | none => none
    | some st0 => execT P dbase pad stackLo fuel fd.body st0

/-! ## §3.1 — the simulation relation: `MachPriv`, `StInv`, `SimPre`.

    P1 (the frame-padding oracle) makes the relation PLAIN EQUALITY: every
    IL-visible value is numerically identical on both sides, so `StInv` needs no
    injection — only that IL registers live in their machine slots, `sp ≡ x2`,
    the code is installed, and memory agrees off the machine-private bytes. -/

/-- Half-open byte range `[base, base+len)` in `toNat` (no wrap — all our
    addresses sit far below 2⁶⁴). -/
def memRange (a base : Word) (len : Nat) : Prop :=
  base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + len
def memRangeB (a base : Word) (len : Nat) : Bool :=
  base.toNat ≤ a.toNat && a.toNat < base.toNat + len

/-- A machine-private hole: the `[ra][slots]` area an activation adds BELOW its
    user frame — `(base = that activation's sp, len = userOff)`. Listed per live
    activation by the `CallChain` ghost (Phase 5). -/
abbrev Hole := Word × Nat

/-- Total loadable blob length (code + zero-pad + data segment). -/
def Layout.blobLen (L : Layout) : Nat := L.segStart + (dataSegment L.data).length

/-- `MachPriv L holes a` — `a` is machine-private: inside the code+data blob, or
    inside some live activation's `[ra][slots]` hole. The IL never writes these;
    the footprint side condition forbids IL stores here. -/
def MachPriv (L : Layout) (holes : List Hole) (a : Word) : Prop :=
  memRange a L.codeBase L.blobLen ∨ ∃ h ∈ holes, memRange a h.1 h.2
def machPrivB (L : Layout) (holes : List Hole) (a : Word) : Bool :=
  memRangeB a L.codeBase L.blobLen || holes.any (fun h => memRangeB a h.1 h.2)

/-- The whole shared stack region `[stackLo, sp0)` — used by `prog_sim`'s
    coarse top-level memory agreement (the harness's output buffers live OUTSIDE
    it, so "agree off blob and off stack" is the composable observable; the
    per-hole `MachPriv` is the finer invariant `StInv` carries mid-run). -/
def MachStack (stackLo sp0 : Word) (a : Word) : Prop :=
  memRange a stackLo (sp0.toNat - stackLo.toNat)

/-- **C2 — `OffPriv L holes sp a`**: `a` is neither machine-private (blob + live
    holes) NOR in the free stack `[stackLo, sp)` below the current frame. This is
    the domain on which IL and machine memory agree (`StInv`), and the region an
    IL memory op must stay inside (`MemAccOff`). The free-stack carve-out is what
    makes the caller's invariant RESTORABLE after a call returns: the machine
    dirties the callee's `[ra][slots]` there, and the IL never wrote it — but it
    is below `sp`, so it is outside `OffPriv` and agreement is not demanded. -/
def OffPriv (L : Layout) (holes : List Hole) (sp a : Word) : Prop :=
  ¬ MachPriv L holes a ∧ ¬ memRange a L.stackLo (sp.toNat - L.stackLo.toNat)

/-- **`StInv L fd holes s m`** — the per-statement simulation invariant
    (RESUME-PROGSIM §3.1). At every IL statement boundary during `fd`'s body:
    `sp ≡ x2`; each live IL register sits in its 8-byte machine slot at
    `sp + slotOff r`; the code+data is installed; IL and machine memory agree
    off the machine-private bytes; and the current activation's hole is
    `[sp, sp + userOff fd)` with `sp` 8-aligned. -/
def StInv (L : Layout) (fd : FunDef) (holes : List Hole) (s : St) (m : State) : Prop :=
  m.rget 2 = s.sp
  ∧ (∀ r, 1 ≤ r → r ≤ maxRegF fd →
        s.rget r = m.loadWord (s.sp + BitVec.ofNat 64 (slotOff r)))
  ∧ Installed L m
  ∧ (∀ a, OffPriv L holes s.sp a → s.mem a = m.mem a)
  ∧ holes.head? = some (s.sp, userOff fd)
  ∧ s.sp.toNat % 8 = 0
  ∧ (∀ h ∈ holes, s.sp.toNat ≤ h.1.toNat)          -- C2: live holes sit at-or-above sp (LIFO)
  ∧ (∀ h ∈ holes, h.1.toNat + h.2 ≤ 2 ^ 64)        -- C2: each hole is wrap-free

/-- The top-level separation bundle for `prog_sim`: the entry stack `[stackLo,
    sp0)` is well-formed and disjoint from the code+data blob, and `sp0` is
    8-aligned. (The per-function stack budget is SUBSUMED by P1's overflow
    check, so it is NOT a hypothesis here — that is the point of §2.) -/
structure SimPre (L : Layout) (stackLo sp0 : Word) : Prop where
  spAligned    : sp0.toNat % 8 = 0
  stackNonEmpty : stackLo.toNat ≤ sp0.toNat
  blobStackDisjoint : ∀ a, memRange a L.codeBase L.blobLen → ¬ MachStack stackLo sp0 a

/-- The padding oracle `compile_sim` instantiates: `userOff` of each function.
    With this, IL `sp` ≡ machine `x2` at every depth (validated in
    `CompileTests.p1_*`). -/
def userPad (env : Env) : Name → Nat := fun f => (List.lookup f env).elim 0 userOff

/-! ## §3.3 — the program-level payoff `prog_sim` (statement; proof deferred).

    `lower_sim`/`call_sim` (§3.2/§3.3) are the induction's workhorses; their
    statements need the compile-time `Emitted` predicate (byte-stream ↔ lowering
    + resolved label addresses) that Phase 2 (AsmFacts) characterizes and the
    Phase 4.1 VERTICAL SLICE validates against the differential oracle — the
    go/no-go checkpoint for this whole relation. They land there, not guessed
    here. `prog_sim` below is self-contained (no `Emitted`) and is the corollary
    every ProgLib function composes with. -/

/-- **`prog_sim`** — if the D7/D8 IL says `entry(args)` computes `s'` (with the
    P1 padding `userPad`), then the compiled RV64I blob, started at `codeBase`
    with `args` in `a0..` and `sp = sp0`, runs to the halt pad in a state whose
    `a0..` hold `entry`'s return values and whose memory agrees with `s'`
    everywhere outside the blob and the stack. Const data is placed at
    `codeBase + segStart` on BOTH sides (`dataOffsetsFrom_shift`). -/
theorem prog_sim
    {P : Program} {entry : Name} {fd : FunDef} {args : List Word}
    {stackLo sp0 : Word} {fuel : Nat} {s' : St} {L : Layout} {m0 : State}
    (hlk    : List.lookup entry P.env = some fd)
    (hL     : layoutOf P entry L.codeBase L.stackLo = some L)
    (hpre   : SimPre L stackLo sp0)
    (hpc    : m0.pc = L.codeBase)
    (hsp    : m0.rget 2 = sp0)
    (hargs  : ∀ i, i < fd.argc → m0.rget (10 + i) = args.getD i 0)
    (hinst  : Installed L m0)
    (hmem   : ∀ a, ¬ MachPriv L [] a →
                installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a
                  = m0.mem a)
    (hrun   : LowIR.Prog.run P stackLo fuel entry args (fun _ => 0) sp0
                (userPad P.env) (L.codeBase + BitVec.ofNat 64 L.segStart) = some s') :
    ∃ k, (Rv64i.runFuel L.haltPc k m0).pc = L.haltPc
       ∧ (∀ j, j < fd.rvc →
            (Rv64i.runFuel L.haltPc k m0).rget (10 + j) = s'.rget (fd.rets.toList.getD j 0))
       ∧ (∀ a, ¬ memRange a L.codeBase L.blobLen → ¬ MachStack stackLo sp0 a →
            s'.mem a = (Rv64i.runFuel L.haltPc k m0).mem a) := by
  sorry

/-! ## Executable sanity (`#guard`) — the def oracle (RESUME-PROGSIM §6). -/

section Guards
open LowIR.Prog (chainEnv sumData frameLocal sub3 caller STACK_LO SP0 zeroMem)

/-- A bare machine with `blob` loaded at `CB`, everything else zero. -/
private def CB : Word := 0x10000
private def mkM (blob : List Byte) : State :=
  { reg := fun _ => 0, pc := CB, mem := LowIR.loadMem CB blob 0x20000 [] }

-- CODE half of `Installed`: the compiled chain decodes back, byte-for-byte.
#guard (do let blob ← progBytes chainEnv "f3"
           let L ← layoutOf chainEnv "f3" CB 0x4000
           pure (codeInstalledB L (mkM blob))).getD false = true

-- CODE + DATA halves: `sumData` has a const-data object in the blob.
#guard (do let blob ← progBytes sumData "sumd"
           let L ← layoutOf sumData "sumd" CB 0
           pure (codeInstalledB L (mkM blob) && dataInstalledB L (mkM blob))).getD false = true

-- `execT` erases to `exec`: same observable return on the fixtures.
#guard (runT [("sub3", sub3)] STACK_LO 1000 "sub3" [30, 12, 2] zeroMem SP0).map
        (fun soo => (soo.1.rget 10).toNat) = some 40
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => (soo.1.rget 10).toNat) = some 0xDEAD

-- FOOTPRINTS: sub3 writes no memory; frameLocal's `sd` writes exactly 8 bytes;
-- caller inherits the callee `frameLocal`'s 8-byte footprint through the call.
#guard (runT [("sub3", sub3)] STACK_LO 1000 "sub3" [30, 12, 2] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 0
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 8
#guard (runT [("caller", caller), ("frameLocal", frameLocal)]
             STACK_LO 1000 "caller" [5] zeroMem SP0).map
        (fun soo => soo.2.2.length) = some 8

-- and the footprint bytes are the 8 consecutive frame addresses of the `sd`
-- (frameLocal's frameReg = sp0 - frameSize = SP0 - 16), in order.
#guard (runT [("frameLocal", frameLocal)] STACK_LO 1000 "frameLocal" [0xDEAD] zeroMem SP0).map
        (fun soo => soo.2.2) = some ((List.range 8).map (fun i => SP0 - 16 + BitVec.ofNat 64 i))

/-! ### `MachPriv` classification arithmetic (validated on the chain layout). -/

-- Build the chain's layout at CB; classify a blob byte, a stack slot, and a
-- user-frame byte. The entry (f3) frame: machine sp = SP0 - totalFrame, its
-- hole = [sp, sp + userOff) is the [ra][slots] area; the user frame sits ABOVE.
open LowIR.Prog (chainEnv chainFn)
open LowIR.Compile (userOff totalFrame)

private def Lchain : Layout := (layoutOf chainEnv "f3" CB 0x4000).getD ⟨0, [], [], 0, [], 0⟩
private def f3fd : FunDef := chainFn (some "f2")
private def spTop : Word := 0x8000
private def f3sp  : Word := spTop - BitVec.ofNat 64 (totalFrame f3fd)   -- machine sp
private def f3hole : Hole := (f3sp, userOff f3fd)                        -- [ra][slots]

-- a byte inside the code blob is machine-private (holes irrelevant)
#guard machPrivB Lchain [] (CB + 4) = true
-- the user-frame base (frameReg = f3sp + userOff) is NOT in the hole and is off
-- the blob ⇒ NOT private (this is where the IL legitimately writes)
#guard machPrivB Lchain [f3hole] (f3sp + BitVec.ofNat 64 (userOff f3fd)) = false
-- a slot byte (f3sp + 8, i.e. slot 0) IS inside the hole ⇒ private
#guard machPrivB Lchain [f3hole] (f3sp + 8) = true
-- the P1 frame arithmetic: hole top (sp + userOff) = user-frame base
--   = sp0 - frameSize (frameReg's value), so the hole and user frame tile the
--   whole machine frame with no gap or overlap.
#guard (f3sp + BitVec.ofNat 64 (userOff f3fd)) = spTop - BitVec.ofNat 64 f3fd.frameSize

end Guards

end LowIR.ProgSim

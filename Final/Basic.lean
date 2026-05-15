-- syntax and semantics: top-level functions + tuples + exceptions

abbrev Var := String

inductive Expr where
  | int (i : Int) : Expr
  | succ (e : Expr) : Expr
  | pred (e : Expr) : Expr
  | plus (e1 : Expr) (e2 : Expr) : Expr
  | times (e1 : Expr) (e3 : Expr) : Expr
  | ifte (e1 e2 e3 : Expr) : Expr
  | bool (b : Bool) : Expr
  | neg (e : Expr) : Expr
  | bind (x : Var) (e1 e2 : Expr) : Expr
  | var (x : Var) : Expr
  | call (f : Var) (e : Expr) : Expr
  | pair (e1 e2 : Expr) : Expr
  | fst (e : Expr) : Expr
  | snd (e : Expr) : Expr
  | throw (e : Expr) : Expr
  | handle (e : Expr) (f : Var) : Expr

inductive Defn where
  | defn (f x : Var) (e : Expr)

inductive Val where
  | int (i : Int) : Val
  | bool (b : Bool) : Val
  | pair (v1 v2 : Val)

inductive Ans where
  | val (v : Val) : Ans
  | exn (v : Val) : Ans

abbrev Env := List (Var × Val)

abbrev Defns := List Defn

abbrev Prog := Defns × Expr

def Env.lookup (r : Env) (x : Var) : Option Val :=
  match r with
  | [] => none
  | (y,v) :: r =>
    if x = y then some v else Env.lookup r x

def Defns.lookup (ds : Defns) (f : Var) : Option Defn :=
  match ds with
  | [] => none
  | ((.defn g y e) :: ds) =>
    if f = g then some (.defn g y e) else Defns.lookup ds f

inductive Eval : Defns → Env → Expr → Ans → Prop where
  | intr {ds r} (i : Int) :
    Eval ds r (.int i) (.val (.int i))
  | boolr {ds r} (b : Bool) :
    Eval ds r (.bool b) (.val (.bool b))
  | succr {ds r e i} :
    Eval ds r e (.val (.int i)) →
    Eval ds r (.succ e) (.val (.int (i + 1)))
  | succ_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.succ e) (.exn v)
  | predr {ds r e i} :
    Eval ds r e (.val (.int i)) →
    Eval ds r (.pred e) (.val (.int (i - 1)))
  | pred_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.pred e) (.exn v)
  | plusr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.val (.int i1)) →
    Eval ds r e2 (.val (.int i2)) →
    Eval ds r (.plus e1 e2) (.val (.int (i1 + i2)))
  | plus_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.plus e1 e2) (.exn v)
  | plus_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.plus e1 e2) (.exn v2)
  | timesr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.val (.int i1)) →
    Eval ds r e2 (.val (.int i2)) →
    Eval ds r (.times e1 e2) (.val (.int (i1 * i2)))
  | times_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.times e1 e2) (.exn v)
  | times_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.times e1 e2) (.exn v2)
  | iftr {ds r e1 e2 a e3} :
    Eval ds r e1 (.val (.bool true)) →
    Eval ds r e2 a →
    Eval ds r (.ifte e1 e2 e3) a
  | iffr {ds r e1 e3 a e2} :
    Eval ds r e1 (.val (.bool false)) →
    Eval ds r e3 a →
    Eval ds r (.ifte e1 e2 e3) a
  | if_propr {ds r e1 v e2 e3} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.ifte e1 e2 e3) (.exn v)
  | negtr {ds r e} :
    Eval ds r e (.val (.bool true)) →
    Eval ds r (.neg e) (.val (.bool false))
  | negfr {ds r e} :
    Eval ds r e (.val (.bool false)) →
    Eval ds r (.neg e) (.val (.bool true))
  | neg_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.neg e) (.exn v)
  | varr {ds r v x} :
    Env.lookup r x = some v →
    Eval ds r (.var x) (.val v)
  | bindr {ds r e1 v1 x a e2} :
    Eval ds r e1 (.val v1) →
    Eval ds ((x, v1) :: r) e2 a →
    Eval ds r (.bind x e1 e2) a
  | bind_propr {ds r e1 v x e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.bind x e1 e2) (.exn v)
  | callr {ds r e v1 f x e' a} :
    Eval ds r e (.val v1) →
    Defns.lookup ds f = some (.defn f x e') →
    Eval ds [(x,v1)] e' a →
    Eval ds r (.call f e) a
  | call_propr {ds r e f v} :
    Eval ds r e (.exn v) →
    Eval ds r (.call f e) (.exn v)
  | pairr {ds r e1 v1 e2 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.val v2) →
    Eval ds r (.pair e1 e2) (.val (.pair v1 v2))
  | pair_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.pair e1 e2) (.exn v)
  | pair_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.pair e1 e2) (.exn v2)
  | fstr {ds r e v1 v2} :
    Eval ds r e (.val (.pair v1 v2)) →
    Eval ds r (.fst e) (.val v1)
  | fst_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.fst e) (.exn v)
  | sndr {ds r e v1 v2} :
    Eval ds r e (.val (.pair v1 v2)) →
    Eval ds r (.snd e) (.val v2)
  | snd_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.snd e) (.exn v)
  | throwr {ds r e v} :
    Eval ds r e (.val v) →
    Eval ds r (.throw e) (.exn v)
  | throw_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.throw e) (.exn v)
  | handle_valr {ds r e v f} :
    Eval ds r e (.val v) →
    Eval ds r (.handle e f) (.val v)
  | handle_exnr {ds r e v f x e' a} :
    Eval ds r e (.exn v) →
    Defns.lookup ds f = some (.defn f x e') →
    Eval ds [(x,v)] e' a →
    Eval ds r (.handle e f) a


-- A little stack machine semantics

inductive Op where
| plus | times | flip

inductive Instr where
| push (i : Int) : Instr
| op (o : Op) : Instr
| branch (is1 is2 : List Instr)
| get (n : Nat) : Instr
| pop : Instr
| exch : Instr
| call : Instr
| dup : Instr
| alloc (n : Nat) : Instr
| read (o : Int) : Instr
| write (o : Int) : Instr
| trycatch (is1 is2 : List Instr) : Instr
| abort : Instr

abbrev Instrs := List Instr

abbrev Stack := List Int

abbrev IDefns := List Instrs

inductive OpEval : Op → List Int → Int → Prop where
| flip0 : OpEval .flip [0] 1
| flip1 : OpEval .flip [1] 0
| plus {i j} : OpEval .plus [j, i] (i+j)
| mult {i j} : OpEval .times [j, i] (i*j)

abbrev Heap := List (Int × Int)

def Heap.lookup (h : Heap) (i : Int) : Option Int :=
  match h with
  | [] => none
  | (j,k) :: h =>
    if i = j then some k else Heap.lookup h i

def Heap.ext (h : Heap) (i j : Int) : Heap :=
  (i, j) :: h

def FreshBlock (h : Heap) (base : Int) (n : Nat) : Prop :=
  ∀ k : Nat, k < n → Heap.lookup h (base + Int.ofNat k) = none

inductive Frame where
  | ret (is : Instrs)
  | handler (handler : Instrs) (k : Instrs) (s : Stack)

inductive Step : IDefns →
                 Instrs → List Frame → Stack → Heap →
                 Instrs → List Frame → Stack → Heap → Prop where
| pushr {ds v is cs s h} :
  Step ds (.push v :: is) cs s h is cs (v :: s) h
| opr {ds o vs v is cs s h} : OpEval o vs v →
  Step ds (.op o :: is) cs (vs ++ s) h is cs (v :: s) h
| branchtr {ds is1 is2 is cs s h} :
  Step ds (.branch is1 is2 :: is) cs (1 :: s) h (is1 ++ is) cs s h
| branchfr {ds is1 is2 is cs s h} :
  Step ds (.branch is1 is2 :: is) cs (0 :: s) h (is2 ++ is) cs s h
| popr {ds is cs i s h} :
  Step ds (.pop :: is) cs (i :: s) h is cs s h
| getr {ds n is cs s h i} :
  s[n]? = some i →
  Step ds (.get n :: is) cs s h is cs (i :: s) h
| exchr {ds is cs v1 v2 s h} :
  Step ds (.exch :: is) cs (v1 :: v2 :: s) h is cs (v2 :: v1 :: s) h
| callr {ds i is' is cs s h} :
  ds[i.toNat]? = some is' →
  Step ds (.call :: is) cs (i :: s) h (is' ++ is) cs s h
| dupr {ds is cs i s h} :
  Step ds (.dup :: is) cs (i :: s) h is cs (i :: i :: s) h
| allocr {ds is cs s h n i} :
  FreshBlock h i n →
  Step ds (.alloc n :: is) cs s h is cs (i :: s) h
| readr {ds h i j o is cs s} :
  Heap.lookup h (i + o) = some j →
  Step ds (.read o :: is) cs (i :: s) h is cs (j :: s) h
| writer {ds is cs i j o s h} :
  Step ds (.write o :: is) cs (i :: j :: s) h is cs (i :: s) (Heap.ext h (i + o) j)
| trycatchr {ds is body handle cs s h} :
  Step ds (.trycatch body handle :: is) cs s h
    body (.handler handle is s :: cs) s h
| ret_handler {ds handle k og_stack cs s h} :
  Step ds [] (.handler handle k og_stack :: cs) s h k cs s h
| abort_handler {ds is' handle k og_stack cs h i} :
    Step ds (.abort :: is') (.handler handle k og_stack :: cs) (i :: _) h handle (.ret k :: cs) (i :: og_stack) h
| abort_retr {ds is' k cs s h} :
  Step ds (.abort :: is') (.ret k :: cs) s h (.abort :: is') cs s h
| retr {ds is cs s h} :
  Step ds [] (.ret is :: cs) s h is cs s h

inductive Steps : IDefns →
  Instrs → List Frame → Stack → Heap →
  Instrs → List Frame → Stack → Heap → Prop where
| refl {ds s is cs h} : Steps ds is cs s h is cs s h
| trans {ds is cs s h is1 cs1 s1 h1 is' cs' s' h'} :
  Steps ds is cs s h is1 cs1 s1 h1 ->
  Step ds is1 cs1 s1 h1 is' cs' s' h' ->
  Steps ds is cs s h is' cs' s' h'

-- compiler

abbrev CEnv := List (Option Var)

def CEnv.lookup (c : CEnv) (x : Var) : Option Nat :=
  match c with
  | [] => none
  | some y :: c =>
    if x = y then some 0 else
      (CEnv.lookup c x).map .succ
  | none :: c =>
      (CEnv.lookup c x).map .succ

def Defns.indexOf (ds : Defns) (f : Var) : Option Nat :=
  match ds with
  | [] => none
  | (.defn g _ _) :: ds =>
    if f = g then some 0 else (indexOf ds f).map .succ

def compile (ds : Defns) (c : CEnv) (e : Expr) : List Instr :=
  match e with
  | .int i => [.push i]
  | .bool b => [.push (if b then 1 else 0)]
  | .succ e =>
    compile ds c e ++
    [.push 1, .op .plus]
  | .pred e =>
    compile ds c e ++
    [.push (-1), .op .plus]
  | .neg e =>
    compile ds c e ++
    [.op .flip]
  | .plus e1 e2 =>
    compile ds c e1 ++
    compile ds (none :: c) e2 ++
    [.op .plus]
  | .times e1 e2 =>
    compile ds c e1 ++
    compile ds (none :: c) e2 ++
    [.op .times]
  | .ifte e1 e2 e3 =>
    compile ds c e1 ++
    [.branch (compile ds c e2) (compile ds c e3)]
  | .var x =>
    match CEnv.lookup c x with
    | some n =>
      [.get n]
    | none => [] -- whatever
  | .bind x e1 e2 =>
    compile ds c e1 ++
    compile ds (some x :: c) e2 ++
    [.exch, .pop]
  | .call f e =>
    compile ds c e ++
    match Defns.indexOf ds f with
    | some n => [.push (Int.ofNat n), .call, .exch, .pop]
    | none => [] -- whatever
  | .pair e1 e2 =>
    compile ds c e1 ++
    compile ds (none :: c) e2 ++
    [.alloc 2, .write 1, .write 0]
  | .fst e =>
    compile ds c e ++
    [.read 0]
  | .snd e =>
    compile ds c e ++
    [.read 1]
  | .throw e =>
    compile ds c e ++
    [.abort]
  | .handle e f =>
    [.trycatch (compile ds c e)
      (match Defns.indexOf ds f with
       | some n => [.push (Int.ofNat n), .call, .exch, .pop]
       | none   => [])]

def compile_defn (ds : Defns) (d : Defn) :=
  match d with
  | .defn _ x e => compile ds [some x] e

def compile_defns (ds : Defns) :=
  ds.map (compile_defn ds)

-- proof

inductive Represents : Val -> Int -> Heap -> Prop where
  | int {i h} : Represents (.int i) i h
  | bool {b h} : Represents (.bool b) (if b then 1 else 0) h
  | pair {v1 i1 h v2 i2 i} :
    Represents v1 i1 h ->
    Represents v2 i2 h ->
    Heap.lookup h (i+0) = i1 ->
    Heap.lookup h (i+1) = i2 ->
    Represents (.pair v1 v2) i h

inductive Related : Stack -> CEnv -> Env -> Heap -> Prop where
  | mt {s h} : Related s [] [] h
  | push {s c r i h} :
    Related s c r h ->
    Related (i :: s) (none :: c) r h
  | bind {s c r x v h i} :
    Related s c r h ->
    Represents v i h ->
    Related (i :: s) ((some x) :: c) ((x,v) :: r) h

def AnsRep : Ans → Int → Heap → Prop
  | .val v, i, h => Represents v i h
  | .exn v, i, h => Represents v i h

-- * values return normally;
-- * exceptions skip .ret frames;
-- * exceptions jump to the nearest .handler;
-- * if there is no handler, they leave the machine at (.abort :: is).

-- the thing from piazza
inductive ExnContinuesWith :
  Instrs → List Frame →
  Int → Instrs → List Frame → Stack → Prop where
  | exn_nil {is i is'} (s : Stack) :
    ExnContinuesWith is [] i (.abort :: is') [] s
  | exn_ret {is k cs i is' cs' og_stack} :
    ExnContinuesWith is cs i is' cs' og_stack →
    ExnContinuesWith is (.ret k :: cs) i is' cs' og_stack
  | exn_handler {is handle k cs i og_stack} :
    ExnContinuesWith is (.handler handle k og_stack :: cs) i
      handle (.ret k :: cs) (i :: og_stack)

inductive ContinuesWith :
  Ans → Instrs → List Frame → Stack →
  Int → Instrs → List Frame → Stack → Prop where
  | val {v is cs s i} :
    ContinuesWith (.val v) is cs s i
      is cs (i :: s)
  | exn {v is cs s i is' cs' og_stack} :
    ExnContinuesWith is cs i is' cs' og_stack →
    ContinuesWith (.exn v) is cs s i is' cs' og_stack

def HeapExtends (h h' : Heap) : Prop :=
  ∀ a v,
  Heap.lookup h a = some v ->
  Heap.lookup h' a = some v

-- lemma about heap stability
theorem heap_stab_lemma {v i h h'} :
  Represents v i h →
  HeapExtends h h' →
  Represents v i h' := by
  intro repr ext
  induction repr with
  | int =>
    apply Represents.int
  | bool =>
    apply Represents.bool
  | pair rl rr lookl lookr extl extr =>
    apply Represents.pair (extl ext) (extr ext)
    · apply ext
      exact lookl
    · apply ext
      exact lookr

-- lemma about state stability across env/stack and heap
theorem state_stability_lemma {s c r h h'} :
  Related s c r h →
  HeapExtends h h' →
  Related s c r h' := by
  intro rel ext
  induction rel with
  | mt =>
    apply Related.mt
  | push rel_ih ih =>
    apply Related.push
    apply ih
    assumption
  | bind rel_ih repr_ih ih =>
    apply Related.bind
    · apply ih
      assumption
    · apply heap_stab_lemma repr_ih
      assumption

-- this lemma states the rest of the instructions don't
-- matter if we are propagating an exception since control
-- flow is yielded to the exception
theorem exn_lemma
  {v is1 is2 cs s i is' cs' s'} :
  ContinuesWith (.exn v) is1 cs s i is' cs' s' →
  ContinuesWith (.exn v) is2 cs s i is' cs' s' := by
  intro h
  cases h with
  | exn h' =>
    apply ContinuesWith.exn
    induction h' with
    | exn_nil s =>
      apply ExnContinuesWith.exn_nil
    | exn_ret ih =>
      apply ExnContinuesWith.exn_ret
      assumption
    | exn_handler =>
      apply ExnContinuesWith.exn_handler

-- transitivitiy between sequences of steps
theorem Steps.trans_steps {ds is1 cs1 s1 h1 is2 cs2 s2 h2 is3 cs3 s3 h3} :
  Steps ds is1 cs1 s1 h1 is2 cs2 s2 h2 →
  Steps ds is2 cs2 s2 h2 is3 cs3 s3 h3 →
  Steps ds is1 cs1 s1 h1 is3 cs3 s3 h3 := by
  intro h12 h23
  induction h23 with
  | refl => assumption
  | trans _ step ih =>
      apply Steps.trans (ih h12) step

theorem compiler_correct_general
  {ds c r e a is cs s h} :
  Related s c r h →
  Eval ds r e a →
  ∃ i h' is' cs' s',
    Steps (compile_defns ds) (compile ds c e ++ is) cs s h is' cs' s' h' ∧
    ContinuesWith a is cs s i is' cs' s' ∧
    AnsRep a i h' ∧
    HeapExtends h h' := by
  intros rel eval
  induction eval generalizing is s c h cs with
  -- | intr x =>
  --   exists x, h, is, cs, x :: s
  --   -- steps part of conjunction
  --   constructor
  --   · apply Steps.trans Steps.refl Step.pushr
  --   -- continues part of conjunction
  --   constructor
  --   · apply ContinuesWith.val
  --   -- repr part of conjunction
  --   constructor
  --   · apply Represents.int
  --   -- heap part of conjunction
  --   · intros _ _ h_lookup
  --     assumption
  -- | boolr x =>
  --   -- same idea as above but x witness is bounded
  --   exists (if x then 1 else 0), h, is, cs, (if x then 1 else 0) :: s
  --   constructor
  --   · apply Steps.trans Steps.refl Step.pushr
  --   constructor
  --   · apply ContinuesWith.val
  --   constructor
  --   · apply Represents.bool
  --   · intro _ _ h_lookup
  --     assumption
  -- | succr e ih =>
  --   -- wow learning this tactic would have made earlier proofs a lot more concise
  --   obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push 1, .op .plus] ++ is) rel
  --   simp [compile, List.append_assoc]
  --   cases cont
  --   exists (x + 1), h', is, cs, (x + 1) :: s
  --   constructor
  --   · apply Steps.trans (Steps.trans steps Step.pushr) (Step.opr OpEval.plus)
  --   constructor
  --   · apply ContinuesWith.val
  --   constructor
  --   · cases repr
  --     apply Represents.int
  --   assumption
  -- | predr e ih =>
  --   obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push (-1), .op .plus] ++ is) rel
  --   simp [compile, List.append_assoc]
  --   cases cont
  --   exists (x - 1), h', is, cs, (x - 1) :: s
  --   constructor
  --   · apply Steps.trans (Steps.trans steps Step.pushr) (Step.opr OpEval.plus)
  --   constructor
  --   · apply ContinuesWith.val
  --   constructor
  --   · cases repr
  --     apply Represents.int
  --   assumption
  -- | succ_propr e ih =>
  --   obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push 1, .op .plus] ++ is) rel
  --   exists x, h', is', cs', s'
  --   simp [compile, List.append_assoc]
  --   constructor
  --   · assumption
  --   constructor
  --   · apply exn_lemma
  --     assumption
  --   constructor
  --   assumption
  --   assumption
  -- | pred_propr e ih =>
  --   obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push (-1), .op .plus] ++ is) rel
  --   exists x, h', is', cs', s'
  --   simp [compile, List.append_assoc]
  --   constructor
  --   · assumption
  --   constructor
  --   · apply exn_lemma
  --     assumption
  --   constructor
  --   assumption
  --   assumption
  -- | plusr evl evr ihl ihr =>
  --   rename_i r el il er ir
  --   -- draw from the first inductive hypothesis
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
  --   cases contl
  --   -- show the heap and env are stable through compiling the first expr?
  --   have rel_stable : Related s c r hl' := state_stability_lemma rel extnl
  --   have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable
  --   -- now that we have a new relation that represents the state after compiling
  --   -- we can go ahead and use the second hypothesis
  --   obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
  --     ihr (is := Instr.op Op.plus :: is) rel_r
  --   cases contr
  --   -- show the conjunction holds
  --   exists (xl + xr), hr', is, cs, (xl + xr) :: s
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     apply Steps.trans_steps stepsl
  --     apply Steps.trans_steps stepsr
  --     apply Steps.trans Steps.refl
  --     apply Step.opr OpEval.plus
  --   constructor
  --   · apply ContinuesWith.val
  --   constructor
  --   · cases reprl
  --     cases reprr
  --     apply Represents.int
  --   intros _ _ lookup
  --   apply extnr
  --   apply extnl
  --   assumption
  -- | timesr evl evr ihl ihr =>
  --   rename_i r el il er ir
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
  --   cases contl

  --   have rel_stable : Related s c r hl' := state_stability_lemma rel extnl
  --   have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

  --   obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
  --     ihr (is := Instr.op Op.times :: is) rel_r
  --   cases contr

  --   exists (xl * xr), hr', is, cs, (xl * xr) :: s
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     apply Steps.trans_steps stepsl
  --     apply Steps.trans_steps stepsr
  --     apply Steps.trans Steps.refl
  --     apply Step.opr OpEval.mult
  --   constructor
  --   · apply ContinuesWith.val
  --   constructor
  --   · cases reprl
  --     cases reprr
  --     apply Represents.int
  --   intros _ _ lookup
  --   apply extnr
  --   apply extnl
  --   assumption
  -- compiling the left expr gives us an error
  -- | plus_proplr evl ihl =>
  --   rename_i _ _ _ er
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (cs := cs) (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
  --   exists xl, hl', isl', csl', sl'
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     assumption
  --   constructor
  --   · apply exn_lemma
  --     assumption
  --   constructor
  --   assumption
  --   assumption
  -- | plus_proprr evl evr ihl ihr =>
  --   rename_i r _ er _ _
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
  --   cases contl

  --   have rel_stable : Related s c r hl' := state_stability_lemma rel extnl
  --   have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

  --   obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
  --     ihr (is := Instr.op Op.plus :: is) rel_r
  --   cases contr with | exn =>

  --   exists xr, hr', isr', csr', sr'
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     apply Steps.trans_steps stepsl
  --     exact stepsr

  --   constructor
  --   · apply exn_lemma
  --     apply ContinuesWith.exn
  --     assumption
  --   constructor
  --   assumption
  --   intros _ _ lookup
  --   apply extnr
  --   apply extnl
  --   assumption
  -- | times_proplr evl ihl =>
  --   rename_i er
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (cs := cs) (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
  --   exists xl, hl', isl', csl', sl'
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     assumption
  --   constructor
  --   · apply exn_lemma
  --     assumption
  --   constructor
  --   assumption
  --   assumption
  -- | times_proprr evl evr ihl ihr =>
  --   rename_i r _ er _ _
  --   obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
  --     ihl (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
  --   cases contl

  --   have rel_stable : Related s c r hl' := state_stability_lemma rel extnl
  --   have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

  --   obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
  --     ihr (is := Instr.op Op.times :: is) rel_r
  --   cases contr with | exn =>

  --   exists xr, hr', isr', csr', sr'
  --   constructor
  --   · simp [compile, List.append_assoc]
  --     apply Steps.trans_steps stepsl
  --     exact stepsr

  --   constructor
  --   · apply exn_lemma
  --     apply ContinuesWith.exn
  --     assumption
  --   constructor
  --   assumption
  --   intros _ _ lookup
  --   apply extnr
  --   apply extnl
  --   assumption
  | iftr evg evt ihg iht =>
    rename_i r eg et _ ef
    obtain ⟨ xg, hg', isg', csg', sg', stepsg, contg, reprg, extng ⟩ :=
      ihg (is := Instr.branch (compile ds c et) (compile ds c ef) :: is) rel
    cases contg
    cases reprg
    have rel_stable : Related s c r hg' := state_stability_lemma rel extng
    obtain ⟨ xt, ht', ist', cst', st', stepst, contt, reprt, extnt ⟩ := iht (is := is) rel_stable
    cases contt with
    | val =>
      exists xt, ht', is, cs, (xt :: s)
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchtr)
        assumption
      constructor
      · apply ContinuesWith.val
      constructor
      assumption
      intros _ _ look
      apply extnt
      apply extng
      assumption
    | exn =>
      exists xt, ht', ist', cst', st'
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchtr)
        assumption
      constructor
      · apply ContinuesWith.exn
        assumption
      constructor
      assumption
      intros _ _ look
      · apply extnt
        apply extng
        assumption
  | iffr evg evt ihg ihf =>
    rename_i r eg ef _ et
    obtain ⟨ xg, hg', isg', csg', sg', stepsg, contg, reprg, extng ⟩ :=
      ihg (is := Instr.branch (compile ds c et) (compile ds c ef) :: is) rel
    cases contg
    cases reprg
    have rel_stable : Related s c r hg' := state_stability_lemma rel extng
    obtain ⟨ xf, hf', isf', csf', sf', stepsf, contf, reprf, extnf ⟩ := ihf (is := is) rel_stable
    cases contf with
    | val =>
      exists xf, hf', is, cs, (xf :: s)
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchfr)
        assumption
      constructor
      · apply ContinuesWith.val
      constructor
      assumption
      intros _ _ look
      apply extnf
      apply extng
      assumption
    | exn =>
      exists xf, hf', isf', csf', sf'
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchfr)
        assumption
      constructor
      · apply ContinuesWith.exn
        assumption
      constructor
      assumption
      intros _ _ look
      · apply extnf
        apply extng
        assumption
  | if_propr ev1 ih1 =>
    rename_i e2 e3
    obtain ⟨ x1, h1', is1', cs1', s1', steps1, cont1, repr1, extn1 ⟩ :=
      ih1 (is := Instr.branch (compile ds c e2) (compile ds c e3) :: is) rel
    exists x1, h1', is1', cs1', s1'
    constructor
    · simp [compile, List.append_assoc]
      exact steps1
    constructor
    · apply exn_lemma
      assumption
    constructor
    · assumption
    · assumption
  | negtr ev ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ :=
      ih (is := Instr.op Op.flip :: is) rel
    cases cont
    cases repr
    exists 0, h', is, cs, (0 :: s)
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.flip1
    constructor
    · apply ContinuesWith.val
    constructor
    · apply Represents.bool
    · assumption
  | negfr ev ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ :=
      ih (is := Instr.op Op.flip :: is) rel
    cases cont
    cases repr
    exists 1, h', is, cs, (1 :: s)
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.flip0
    constructor
    · apply ContinuesWith.val
    constructor
    · apply Represents.bool
    · assumption
  | neg_propr ev ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ :=
      ih (is := Instr.op Op.flip :: is) rel
    exists x, h', is', cs', s'
    constructor
    · simp [compile, List.append_assoc]
      exact steps
    constructor
    · apply exn_lemma
      assumption
    constructor
    · assumption
    · assumption
  

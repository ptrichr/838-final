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
  | handler (handler : Instrs) (k : Instrs)

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
    body (.handler handle is :: cs) s h
| ret_handler {ds handle k cs s h} :
  Step ds [] (.handler handle k :: cs) s h k cs s h
| abort_handler {ds is' handle k cs s h} :
  Step ds (.abort :: is') (.handler handle k :: cs) s h handle (.ret k :: cs) s h
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
inductive ContinuesWith :
  Ans → Instrs → List Frame → Stack →
  Int → Instrs → List Frame → Stack → Prop where
| val {v is cs s i} :
  ContinuesWith (.val v) is cs s i
    is cs (i :: s)
| exn_nil {v is s i} :
  ContinuesWith (.exn v) is [] s i
    (.abort :: is) [] (i :: s)
| exn_ret {v is k cs s i is' cs' s'} :
  ContinuesWith (.exn v) is cs s i is' cs' s' →
  ContinuesWith (.exn v) is (.ret k :: cs) s i is' cs' s'
| exn_handler {v is handle k cs s i} :
  ContinuesWith (.exn v) is (.handler handle k :: cs) s i
    handle (.ret k :: cs) (i :: s)

def HeapExtends (h h' : Heap) : Prop :=
  ∀ a v,
  Heap.lookup h a = some v ->
  Heap.lookup h' a = some v

theorem compiler_correct_general
  {ds c r e a is cs s h} :
  Related s c r h →
  Eval ds r e a →
  ∃ i h' is' cs' s',
    Steps (compile_defns ds) (compile ds c e ++ is) cs s h is' cs' s' h' ∧
    ContinuesWith a is cs s i is' cs' s' ∧
    AnsRep a i h' ∧
    HeapExtends h h' := by sorry

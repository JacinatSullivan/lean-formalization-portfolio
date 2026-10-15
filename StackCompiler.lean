/-!
# Verified stack compiler for arithmetic expressions

A small expression language, a stack-machine target, and a compiler between
them, together with machine-checked proofs that

1. the compiler preserves semantics (`compile_correct`), and
2. a constant-folding pass preserves semantics (`fold_sound`),

so the optimised pipeline `compile ∘ fold` is correct end to end
(`compile_fold_correct`).

Depends only on Lean 4 core.

## Layout
* `Syntax`   : source language and its denotational semantics
* `Machine`  : stack machine and its operational semantics
* `Compile`  : the compiler and its correctness proof
* `Optimise` : constant folding and its soundness proof
-/

set_option autoImplicit false

namespace StackCompiler

/-! ## Syntax -/

/-- Source expressions over natural numbers with variables indexed by `Nat`. -/
inductive Expr where
  | const : Nat → Expr
  | var   : Nat → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  deriving Repr

/-- A variable assignment. -/
abbrev Env := Nat → Nat

/-- Denotational semantics of expressions. -/
def Expr.eval (env : Env) : Expr → Nat
  | .const n => n
  | .var i   => env i
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env

/-! ## Target machine -/

/-- Stack machine instructions. -/
inductive Instr where
  | push : Nat → Instr
  | load : Nat → Instr
  | add  : Instr
  | mul  : Instr
  deriving Repr

/-- Machine stack; the head of the list is the top of the stack. -/
abbrev Stack := List Nat

/-- Execute one instruction. Returns `none` on stack underflow. -/
def Instr.step (env : Env) : Instr → Stack → Option Stack
  | .push n, s         => some (n :: s)
  | .load i, s         => some (env i :: s)
  | .add,    b :: a :: s => some ((a + b) :: s)
  | .mul,    b :: a :: s => some ((a * b) :: s)
  | _,       _         => none

/-- Execute a program from an initial stack. -/
def run (env : Env) : List Instr → Stack → Option Stack
  | [],      s => some s
  | i :: is, s =>
    match i.step env s with
    | none    => none
    | some s' => run env is s'

/-- Running `p ++ q` is running `p` and then feeding the result to `q`. -/
theorem run_append (env : Env) (p q : List Instr) (s : Stack) :
    run env (p ++ q) s = (run env p s).bind (fun s' => run env q s') := by
  induction p generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    simp only [List.cons_append, run]
    cases h : i.step env s with
    | none    => simp
    | some s' => simp [ih]

/-! ## Compilation -/

/-- Compile an expression to a postfix instruction sequence. -/
def Expr.compile : Expr → List Instr
  | .const n => [.push n]
  | .var i   => [.load i]
  | .add a b => a.compile ++ b.compile ++ [.add]
  | .mul a b => a.compile ++ b.compile ++ [.mul]

/-- **Compiler correctness.** Running the compiled code pushes exactly the value
of the expression onto the stack and leaves the rest of the stack untouched. -/
theorem compile_correct (env : Env) (e : Expr) (s : Stack) :
    run env e.compile s = some (e.eval env :: s) := by
  induction e generalizing s with
  | const n => simp [Expr.compile, Expr.eval, run, Instr.step]
  | var i   => simp [Expr.compile, Expr.eval, run, Instr.step]
  | add a b iha ihb =>
    simp [Expr.compile, Expr.eval, run_append, iha, ihb, run, Instr.step]
  | mul a b iha ihb =>
    simp [Expr.compile, Expr.eval, run_append, iha, ihb, run, Instr.step]

/-! ## Optimisation: constant folding -/

/-- Smart constructor: add two constants at compile time. -/
def Expr.mkAdd : Expr → Expr → Expr
  | .const m, .const n => .const (m + n)
  | a,        b        => .add a b

/-- Smart constructor: multiply two constants at compile time. -/
def Expr.mkMul : Expr → Expr → Expr
  | .const m, .const n => .const (m * n)
  | a,        b        => .mul a b

theorem Expr.mkAdd_eval (env : Env) (a b : Expr) :
    (Expr.mkAdd a b).eval env = a.eval env + b.eval env := by
  unfold Expr.mkAdd
  split <;> simp [Expr.eval]

theorem Expr.mkMul_eval (env : Env) (a b : Expr) :
    (Expr.mkMul a b).eval env = a.eval env * b.eval env := by
  unfold Expr.mkMul
  split <;> simp [Expr.eval]

/-- Bottom-up constant folding. -/
def Expr.fold : Expr → Expr
  | .const n => .const n
  | .var i   => .var i
  | .add a b => Expr.mkAdd a.fold b.fold
  | .mul a b => Expr.mkMul a.fold b.fold

/-- Constant folding does not change the value of an expression. -/
theorem fold_sound (env : Env) (e : Expr) : e.fold.eval env = e.eval env := by
  induction e with
  | const n => simp [Expr.fold, Expr.eval]
  | var i   => simp [Expr.fold, Expr.eval]
  | add a b iha ihb =>
    simp [Expr.fold, Expr.mkAdd_eval, Expr.eval, iha, ihb]
  | mul a b iha ihb =>
    simp [Expr.fold, Expr.mkMul_eval, Expr.eval, iha, ihb]

/-- End-to-end correctness of the optimising pipeline. -/
theorem compile_fold_correct (env : Env) (e : Expr) (s : Stack) :
    run env e.fold.compile s = some (e.eval env :: s) := by
  rw [compile_correct, fold_sound]

/-! ## Tests -/

private def sample : Expr :=
  .add (.const 2) (.mul (.const 3) (.const 4))

example : sample.eval (fun _ => 0) = 14 := rfl
example : run (fun _ => 0) sample.compile [] = some [14] := rfl
example : sample.fold = .const 14 := rfl

end StackCompiler

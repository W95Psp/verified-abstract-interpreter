module OperationalSemantic
open LangDef
open MachineIntegers
open Set
module T = FStar.Tactics
open FStar.ReflexiveTransitiveClosure
open FStar.FunctionalExtensionality
open NumTC

/// This section defines an operational semantics for $\AbIntImp{}$. It is
/// also a good way of introducing more \gls{fstar} features.

///
/// We choose to formulate our semantics in terms of sets.

//!open Set

/// The binary operations we consider are enumerated by
/// \fcode{binop}. The function \fcode{concrete_binop} associates these syntactic operations to integer operations.

/// For convenience, \fcode{lift} maps a \fcode{binop} to a set
/// operation, using \fcode{lift_binop}. This function is inlined by
/// \gls{fstar} directly when used because of the keyword
/// \fcode{unfold}; intuitively \fcode{lift} behaves as a macro.

//@regexp'=Plus.*\n.*-->>Plus -> n_add | Lt -> lt_m | ... | Or -> ori_m
unfold let concrete_binop (op: binop): int_m -> int_m -> int_m
  = match op with | Plus  -> n_add | Minus -> n_sub | Mult  -> n_mul
     | Eq   -> n_eq | Lt    -> n_lt  | And -> n_and  | Or    -> n_or

//@hide-because-shown-at-module=Set
unfold let lift op = lift_binop (concrete_binop op)

/// The operational semantics for expressions is given as a map from
/// memories and expressions to sets of integers.

/// Notice the use of both the syntax \fcode{val} and \fcode{let} for
/// the function \fcode{osem_expr}.

/// The \fcode{val} syntax gives \fcode{osem_expr} the type
/// \fcode{mem->expr->set int_m}, while the \fcode{let} declaration
/// gives its definition.

/// The semantics itself is uncomplicated: \fcode{Unknown} returns
/// the set of every \fcode{int_m}, a constant or a \fcode{Var}
/// returns a singleton set. For binary operations, we lift them as
/// set operations, and make use of recursion.

//@offset-start-line=-1
val osem_expr: mem -> expr -> set int_m
let rec osem_expr m e = fun (i: int_m) 
  -> match e with | Const x -> i==x | Var v -> i==m v | Unknown -> True
  | BinOp op x y -> lift op (osem_expr m x) (osem_expr m y) i

/// The operational semantics for statements maps a statement and an
/// initial memory to a set of admissible final memories.

/// Given a statement \fcode{s}, an initial memory \fcode{m_i} and a
/// final one \fcode{m_f}, \fcode{osem_stmt s m_i m_f}
/// (defined below) is a proposition stating whether the
/// transition is possible.

//@hide=but shown as comment below
let rec neg_expr (e: expr): expr
  = match e with | BinOp And a b -> BinOp Or (neg_expr a) (neg_expr b)
  | BinOp Or a b -> BinOp And (neg_expr a) (neg_expr b)
  | BinOp Lt  (Const a)  b -> if a = 127 then Const 1
                         else BinOp Lt b (Const (a + (1 <: int_m)))
  | BinOp Lt  a  (Const b) -> if b = -127 then Const 1
                         else BinOp Lt (Const (b - (1 <: int_m))) a
  | BinOp Lt a b -> BinOp Or (BinOp Lt b a) (BinOp Eq a b)
  | Const 0 -> Const 1 | Const _ -> Const 0 | _ -> BinOp Eq e (Const 0)

//@offset-start-line=-1
//@regexp=Tot \((.*)\) \(decreases s\)|$1
//@replace=(decreases s)|(decreases s)   (neg_expr : expr -> expr)
val osem_stmt (s: stmt): Tot (mem -> set mem) (decreases s)
let rec osem_stmt (s: stmt) (m_i m_f: mem)
  = match s with
  | Assign v e -> ∀w. if v = w then m_f v ∈ osem_expr m_i e
                              else m_f w == m_i w
  | Seq a b  -> exists (m1: mem). m1 ∈ osem_stmt a m_i /\ m_f ∈ osem_stmt b m1
  | Choice a b -> m_f ∈ (osem_stmt a m_i ∪ osem_stmt b m_i)
  | Assume e -> m_i == m_f /\ (exists (x: int_m). x <> 0 /\ x ∈ osem_expr m_i e)
  | Loop a -> closure (osem_stmt a) m_i m_f

/// The simplest operation is the assignment of a variable \fcode{v}
/// to an expression \fcode{e}: the transition is allowed if every
/// variable but \fcode{v} in \fcode{m_i} and \fcode{m_f} is equal and
/// the final value of \fcode{v} matches with the semantics of
/// \fcode{e}.

/// Assuming that an expression is true amounts to require the initial
/// memory to be such that at least a non-zero integer (that is, the
/// encoding of \fcode{true}) belongs to \fcode{osem_expr m_i e}.

/// The statement \fcode{Seq a b} starting from the initial memory
/// \fcode{m_i} admits \fcode{m_f} as a final memory when there exists
/// \begin{enumi} \item a transition from \fcode{m_i} to an
/// intermediate memory \fcode{m1} with statement \fcode{a} and \item
/// a transition from \fcode{m1} to \fcode{m_f} with statement
/// \fcode{b}.  \end{enumi}

/// The operational semantics for a loop is defined as the reflexive
/// transitive closure of the semantics of its body.

/// The \fcode{closure} function computes such a closure, and is
/// provided by \gls{fstar}'s standard library.



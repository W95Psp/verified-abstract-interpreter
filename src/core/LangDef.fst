module LangDef
open MachineIntegers

/// \label{abint:section:lang-def}

/// To present our abstract intrepreter, we first show the language on
/// which it operates: $\AbIntImp{}$. It is a simple imperative language,
/// equipped with memories represented as functions from variable names
/// \fcode{varname} to signed integers, \fcode{int_m}.

/// This presentation lets the reader unfamiliar with \gls{fstar} get
/// used to its syntax: $\AbIntImp{}$'s \gls{fstar} definition looks like
/// OCaml; the main difference is the explicit type signatures for
/// constructors in algebraic data types.

/// $\AbIntImp{}$ has numeric expressions, encoded by the type
/// \fcode{expr}, and statements \fcode{stmt}.

/// Booleans are represented numerically: $0$ represents
/// \fcode{false}, and any other value stands for true.

/// The enumeration \fcode{binop} equips $\AbIntImp{}$ with
/// various binary operations. The constructor \fcode{Unknown} encodes an
/// arbitrary number.
 
/// Statements in $\AbIntImp{}$ are the assignment, the
/// non-deterministic choice, the sequence and the loop.

type varname = | VA | VB | VC | VD (*@replace-newline:  *)

// mem is split in two for genericity, and because it enhance
// normalization in Mem.ADom for the field ma_mem
//@hide
type mem' 'a = varname -> 'a
//@regexp=^.*|type mem 'a = varname -> 'a
unfold type mem = mem' int_m

type binop = | Plus | Minus | Mult | Eq | Lt | And | Or
type expr = | Const:  int_m -> expr   | Var: varname -> expr
            | BinOp: binop -> expr -> expr -> expr | Unknown
  
type stmt = | Assign: varname -> expr -> stmt | Assume: expr -> stmt
            | Seq:       stmt -> stmt -> stmt | Loop:   stmt -> stmt
            | Choice: stmt -> stmt -> stmt

/// The type \fcode{int_m} is a \emph{refinement} of the built-in
/// \gls{fstar} type \fcode{int}: while every integer lives in the
/// type \fcode{int}, only those that respect certain bounds live in
/// \fcode{int_m}.

/// Numerical operations (\fcode{+}, \fcode{-} and \fcode{*}) on
/// machine integers wrap on overflow, i.e. adding one to the maximal
/// machine integer results in the minimum machine integer.

/// We do not give the detail of their implementation.


//!open MachineIntegers


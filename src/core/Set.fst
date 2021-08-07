module Set
open Prop


/// Sets are encoded as maps from values to propositions~\fcode{prop}.

/// Those are logical statements and shouln't be confused with
/// booleans.

/// Below, \fcode{⊆} quantifies over every \emph{inhabitant} of a
/// type: stating whether such a statement is true or false is clearly
/// not computable.

/// Arbitrarily complex properties can be expressed as propositions of
/// type \fcode{prop}.

///
/// In the listing below, notice the greek letters: we use them
/// throughout the paper.

/// They denote implicit type arguments: for instance, below, $\in$
/// works for any set \fcode{set 'a}, with any type \fcode{'a}.

/// \gls{fstar} provides the propositional operators $\wedge$, $\vee$
/// and \fcode{==}, in addition to boolean
/// ones~(\fcode{&&},~\fcode{||} and~\fcode{=}).

/// We use them below to define the union, intersection and
/// differences of sets.

type set 'a = 'a -> prop (*@replace-newline:            *)
//@regexp=^.*|let (∈) (x: 'a) (s: set 'a) = s x
unfold let (∈) #r ($x: 'a{r x}) (s: set 'a) = s x
//@replace=(s0 s1: set 'a): set 'a|s0 s1
let (∩) (s0 s1: set 'a): set 'a = fun x -> x ∈ s0 /\ x ∈ s1 (*@replace-newline: *)
//@replace=(s0 s1: set 'a): set 'a|s0 s1
let (∖) (s0 s1: set 'a): set 'a = fun v -> s0 v /\ ~(s1 v)
let (∪) (s0 s1: set 'a): set 'a = fun x -> x ∈ s0 \/ x ∈ s1
let (⊆) (s0 s1: set 'a): prop = forall (x: 'a). x ∈ s0 ==> x ∈ s1

open FStar.Classical

open MachineIntegers
let set_inverse (s: set int_m): set int_m = fun (i: int_m) -> s (-i)
open NumTC

/// To be able to work conveniently with binary operations on integers
/// in our semantics, we define \fcode{lift_binop}, that lifts them as
/// set operations.

/// For example, the set \fcode{lift_binop (+) a b} (\fcode{a} and
/// \fcode{b} being two sets of integers) corresponds to

/// $\left\{
/// va + vb \mid va\in \textrm{\fcode{a}} \wedge vb \in \textrm{\fcode{b}}
/// \right\}$.

let lift_binop (op: 'a -> 'a -> 'a) (a b: set 'a): set 'a
  = fun r -> exists (va:'a). exists (vb:'a). va ∈ a /\ vb ∈ b /\ r == op va vb
//!show OperationalSemantic.lift

//@hide
instance set_arith: num (set int_m) = { n_add = lift_binop n_add
  ; n_sub= lift_binop n_sub; n_mul = lift_binop n_mul ; n_eq = lift_binop n_eq
  ; n_lt = lift_binop n_lt ; n_and= lift_binop n_and; n_or= lift_binop n_or}


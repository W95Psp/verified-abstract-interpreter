module ADom.Num

open Set
open MachineIntegers
open LangDef
open OperationalSemantic
open ADom
open FStar.Tactics.Typeclasses

/// In the section \ref{abint:sub:backward-op-itv}, we explain what a sound
/// backward operator is in the case of the abstract domain of
/// intervals.

/// There, we mention a more generic type
/// \fcode{sound_backward_op} that states soundness for such operators
/// in the context of any abstract domain. We present its definition
/// below:

type sound_backward_op (a:Type) {|l:adom a|} (op:l.c->l.c->l.c)
  = backward_op: (a -> a -> a -> (a & a)) {
      forall (xⵌ yⵌ rⵌ: a). let xⵌⵌ, yⵌⵌ = backward_op xⵌ yⵌ rⵌ in
         (forall (x y: l.c). (x ∈ gamma xⵌ /\ y ∈ gamma yⵌ /\ op x y ∈ gamma rⵌ)
                  ==> (x ∈ gamma xⵌⵌ /\ y ∈ gamma yⵌⵌ))}

/// We define the specialized typeclass \fcode{num_adom} for abstract
/// domains that concretize to machine integers.

/// A type that implements an instance of \fcode{num_adom} should also
/// have an instance of \fcode{adom}, with \fcode{int_m} as concrete
/// type.

/// Whence the fields \fcode{na_adom}, and \fcode{adom_num}.

/// Moreover, we require a computable concretization function
/// \fcode{cgamma}, that is, a function that maps abstract values to
/// computable sets of machine integers: \fcode{int_m -> bool}.

/// The \fcode{beta} operator lifts a concrete value in the abstract
/// world.

/// We also require the abstract domain to provide both sound forward
/// and backward operator for every syntactic operator of type
/// \fcode{binop} presented in Section~\ref{abint:section:lang-def}.

/// The function \fcode{abstract_binop} maps an operator \fcode{op} of
/// type \fcode{binop} to a sound forward abstract operator.

/// Its soundness is encoded as a refinement.

/// Similarly, \fcode{backward_abstract_binop} maps a \fcode{binop}
/// to a corresponding sound backward operator.

/// To ease backward analysis, \fcode{gt0} and \fcode{lt0} are
/// abstractions for non-null positive and negative integers.

//@replace=[@@@tcinstance] |
class num_adom (a: Type) = 
{ [@@@tcinstance] na_adom: adom a; adom_num: squash (na_adom.c == int_m)
; cgamma: xⵌ:a -> x:int_m -> b:bool {b <==> x ∈ gamma xⵌ}
; abstract_binop: op:_ -> i:a -> j:a -> r:a {lift op (gamma i) (gamma j) ⊆ gamma r}
; backward_abstract_binop: (op: binop) -> sound_backward_op a (concrete_binop op)
; gt0: xⵌ:a {forall(x:int_m). x>0 ==> x  ∈  gamma  xⵌ}
; lt0: xⵌ:a {forall(x:int_m). x<0 ==> x  ∈  gamma  xⵌ}; beta: x:int_m -> r:a{x  ∈  gamma  r} }

/// For a proposition \fcode{p}, the \gls{fstar} standard library
/// defines \fcode{squash p} as the type \fcode{_:unit{p}}, that is, a
/// refinement of the unit type. This can be seen as a lemma with no
/// parameter.

/// \subsubsection{Instance for intervals}

/// The section \ref{abint:section:intervals} defines everything required by
/// \fcode{num_adom}, thus below we give an instance of the typeclass
/// \fcode{num_adom} for intervals.

//@regexp'=function \| +([^ ]+) +-> +([^ \n]+)[^)]+ ([^ ]+) +-> +([^ \n]+ *)\)-->>function | $1 -> $2 ... | $3 -> $4)
//!show Interval.itv_num_adom


module AbstractSemantic

open Set
open MachineIntegers
open LangDef
open OperationalSemantic
open WithBottom
open ADom
open ADom.Num
open Order
open Prop

/// Wrapping up the implementation of our abstract interpreter, this
/// section presents the abstract interpretation of $\AbIntImp{}$
/// statements.

/// For every memory type \fcode{'m} that instantiates the typeclass
/// of abstract memories \fcode{mem_adom}, the abstract semantics
/// \fcode{asem_stmt} maps statements and initial abstract memories
/// to final memories.

/// \fcode{mem_adom} is defined and proven correct below.

open FStar.Classical
module T = FStar.Tactics

open FStar.ReflexiveTransitiveClosure

open FStar.Preorder
open Fixpoint
open ADom.Mem


///
/// Given a statement \fcode{s}, and an initial abstract memory
/// \fcode{mⵌ0}, \fcode{mem_adom s mⵌ0} is a final abstract memory so
/// that for any initial concrete memory \fcode{m} approximated by
/// \fcode{mⵌ0} and for any acceptable final concrete memory
/// \fcode{m'} considering the operational semantics, \fcode{m'} is
/// approximated by \fcode{mem_adom s mⵌ0}.

/// Here, we give two hints to the SMT solver: by normalization
/// (\fcode{assert_norm}), we unfold the operational semantics in the
/// case of choices or sequences.

/// The analysis of an assignment or an assume is very easy since we
/// already have operators defined for these cases.

/// In the case of the sequence of two statements, we simply recurse.

/// Similarly, when the statement is a choice, we recurse on its two
/// possibilities.

/// Then the two resulting abstract memories are merged back together.

/// The last case to be handled is the loop, that is some statement of
/// the shape \fcode{Loop body}.

/// We compute a fixpoint \fcode{mⵌ1} for \fcode{body}, by widening:
/// it therefore approximates correctly the operational semantics of
/// \fcode{Loop body}, since it is defined as a transitive closure.

/// \gls{fstar}'s standard library provides the lemma
/// \fcode{stable_on_closure}; of which we give a simplified signature
/// below. The concretization \fcode{gamma mⵌ1} is a set, that is a
/// predicate: we use this lemma with \fcode{gamma mⵌ1} as predicate
/// \fcode{p} and with the operational semantics as relation
/// \fcode{r}.

/// \begin{fstarcode}
/// val simplified_stable_on_closure: r:('a -> 'a -> prop) -> p:('a -> prop)
///   -> Lemma (requires forall x y. p x /\ r x y ==> p y)
///           (ensures forall x y. p x /\ closure r x y ==> p y)
/// \end{fstarcode}
/// 

// this is a copy-paste of `FStar.Preorder.stable_on_closure`: the
//`:pattern` clauses seems to yields some kind of bad SMT encoding
//concerning decreases clauses of `osem_stmt`. Thus we just copy-paste
//`FStar.Preorder.stable_on_closure` and remove those `pattern`
//clauses.

//@hide=but shown as comment above
val stable_on_closure: #a:Type u#a -> r:relation a -> p:(a -> Type0)
  -> p_stable_on_r: (squash (forall x y. p x /\ r x y ==> p y))
  -> Lemma (forall x y. p x /\ closure r x y ==> p y)
let stable_on_closure = stable_on_closure

//@hide
private unfold let bottom {|l:lattice 'a|}: r:'a{True} = l.bottom

// the flag `enableWiden` is not interesting for the paper
// thus we remove it

//@regexp= \(?enableWiden(:bool\))?|
//@regexp'=\(if not.* else (.*)\) mⵌ0-->>$1
let rec asem_stmt {| md: mem_adom 'm |} (enableWiden:bool) (s: stmt) (mⵌ0: 'm)
  : (mⵌ1:'m {forall(m m':mem). (m ∈ gamma  mⵌ0 /\ m' ∈ osem_stmt s  m) ==> m' ∈ gamma  mⵌ1})
  = assert_norm(∀s0 s1 (m0 mf:mem). osem_stmt (Seq s0 s1) m0 mf
     == (exists(m1:mem). m1 ∈ osem_stmt s0 m0 /\ mf ∈ osem_stmt s1 m1));
    assert_norm(∀a b (m0 mf:mem). osem_stmt (Choice a b) m0 mf
     == (mf ∈ (osem_stmt a m0 ∪ osem_stmt b m0)));
    if mⵌ0 ⊑ bottom then bottom
    else match s with         | Assign v e -> assign mⵌ0 v e
    | Assume e -> assume_ mⵌ0 e | Seq s t -> asem_stmt enableWiden t (asem_stmt enableWiden s mⵌ0)
    | Choice a b -> asem_stmt enableWiden a mⵌ0 ⊔ asem_stmt enableWiden b mⵌ0
    | Loop body -> let mⵌ1: 'm = postfixpoint corder order_measure
                   (if not enableWiden then (fun (mⵌ:'m) -> join mⵌ (asem_stmt enableWiden body mⵌ <: 'm)) else (fun (mⵌ:'m) -> widen mⵌ (asem_stmt enableWiden body mⵌ <: 'm))) mⵌ0
                  in stable_on_closure (osem_stmt body) (gamma mⵌ1) (); mⵌ1

/// Below we show the definition of \fcode{postfixpoint}, which is
/// similar to \fcode{prefixpoint}. However, it is simpler because
/// it only ensures its outcome is a postfixpoint.

//@regexp'=`o`-->>⊑
//@regexp=\bo\b|(⊑)
//!show Fixpoint.postfixpoint



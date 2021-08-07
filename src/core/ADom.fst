module ADom
open FStar.Tactics.Typeclasses
open FStar.Tactics.Typeclasses
open Order
open Set
open Prop

/// Our abstract interpreter is parametrized over relational domains.

/// We instantiate it later with a weakly-relational~\cite{astree}
/// memory.

/// This section defines lattices and abstract domains.

/// Such structures are a natural fit for typeclasses~\cite{metafstar},
/// which allow for ad hoc polymorphism.

/// In our case, it means that we can have one abstraction for
/// lattices for instance, and then instantiate this abstraction with
/// implementations for, say, sets of integers, then intervals, etc.

/// Typeclasses can be seen as record types with dedicated dependency
/// inference.

/// Below, we define the typeclass \fcode{lattice}: defining an
/// instance for a given type equips this type with a lattice
/// srtucture.

/// \paragraph{Refinement types}

/// Below, the syntax \fcode{x:'t{p x}} denotes the type whose
/// inhabitants both belong to \fcode{'t} and satisfy the predicate
/// \fcode{p}.

/// For example, the inhabitant of the type

/// \fcode{bot:nat{forall(n:nat).  bot <= n}} is \fcode{0}: it is the
/// (only) smallest natural number.

/// To typecheck \fcode{x:'t}, \gls{fstar} collects the \textit{proof
/// obligations} implied by "\fcode{x} has the type \fcode{'t}", and
/// tries to discharge them with the help of the SMT solver.

/// If the SMT solver is able to deal with the proof obligations, then
/// \fcode{x:'t} typechecks.

/// In the case of "\fcode{0} is of type
/// \fcode{bot:nat{forall(n:nat).  bot <= n}}", the proof obligation
/// is \fcode{forall(n:nat). 0 <= n}.
/// 

/// Below, most of the types of the fields from the record type
///  \fcode{lattice} are refined.

/// Typechecking \fcode{i} against the type \fcode{lattice 'a} yields
/// a proof obligation asking (among other things) for \fcode{i.join}
/// to go up in the lattice and for \fcode{bottom} to be a lower
/// bound.

/// Thus, if "\fcode{i} has type \fcode{lattice 'a}" typechecks, it
/// means there exists a proof that the properties written as
/// refinements in \fcode{lattice}'s definition hold on \fcode{i}.

/// We found convenient to let \fcode{bottom} represent unreachable
/// states.

/// Note \fcode{lattice} is under-specified, i.e. it doesn't require
/// \fcode{join} to be provably a least upper bound, since such a
/// property plays no role in our proof of soundness. This choice
/// follows Blazy and al.~\cite{SAS13:Blazy:al}.

class lattice 'a = { corder: order 'a
  ; join: x:'a -> y:'a -> r:'a {corder x r /\ corder y r}
  ; meet: x:'a -> y:'a -> r:'a {corder r x /\ corder r y}
  ; bottom:  bot:'a {∀x. corder bot x}; top:  top:'a {∀x. corder x top}}

/// For our purpose, we need to define what an abstract domain is. In
/// our setting, we consider concrete domains with powerset structure.

/// The typeclass \fcode{adom} encodes them: it is parametrized by a
/// type \fcode{'a} of abstract values.

/// For instance, consider \fcode{itv} the type for intervals:
/// \fcode{adom itv} would be the type inhabited by correct abstract
/// domains for intervals.
/// 

/// Implementing an abstract domain amounts to implementing the
/// following fields: \begin{enumi}

/// \item \fcode{c}, that represents the type to which abstract values
/// \fcode{'a} concretizes;

/// \item \fcode{adom_lat}, a lattice for \fcode{'a};

/// \item \fcode{widen}, a widening operator;

/// \item \fcode{gamma}, a monotonic concretization function from \fcode{'a}
/// to \fcode{set c};

/// \item \fcode{order_measure}, a measure ensuring the abstract
/// domain doesn't admit infinite increasing chains, so that
/// termination is provable for fixpoint iterations;

/// \item \fcode{meet_law}, that requires \fcode{meet} to be a correct
/// approximation of set intersection;

/// \item \fcode{top_law} and \fcode{bot_law}, that ensure the lattice's
/// bottom concretization matches with the empty set, and similarly
/// for \fcode{top}.
/// \end{enumi}

open Fixpoint
//@replace=[@@@tcinstance] |
class adom 'a = { c: Type; [@@@tcinstance] adom_lat: lattice 'a
  ; gamma: (gamma: ('a -> set c) {forall (x y: 'a). corder x y ==> (gamma x ⊆ gamma y)})
  ; widen: x:'a -> y:'a -> r:'a {corder x r /\ corder y r}
  ; order_measure: measure adom_lat.corder
  ; meet_law: x:'a -> y:'a -> Lemma ((gamma x ∩ gamma y) ⊆ gamma (meet x y))
  ; bot_law: unit -> Lemma (forall (x:c). ~(x ∈ gamma bottom))
  ; top_law: unit -> Lemma (forall (x:c). x ∈ gamma top)}

/// Notice the refinement types: we require for instance the monotony
/// of \fcode{gamma}.

/// Every single instance for \fcode{adom} will be checked against
/// these specifications. No instance of \fcode{adom} where
/// \fcode{gamma} is not monotonic can exist.

/// With a proposition \fcode{p}, the \fcode{Lemma p} syntax signals a
/// function whose outcome is computationally irrelevant, since it
/// simply produces \fcode{()}, the inhabitant of the type
/// \fcode{unit}.

/// However, it does not produces an arbitrary \fcode{unit}: it
/// produces an inhabitant of \fcode{_:unit {p}}, that is, the type
/// \fcode{unit} refined with the goal \fcode{p} of the lemma itself.


///
/// For praticity, we define some infix operators for \fcode{adom_lat}
/// functions.

/// The syntax \fcode{{|...|}} lets one formulate typeclass
/// constraints: for example, \fcode{(⊑)} below ask \gls{fstar} to
/// resolve an instance of the typeclass \fcode{adom} for the type
/// \fcode{'a}, and name it \fcode{l}.

/// Below, \fcode{(⊓)} instantiates the lemma \fcode{meet_law}
/// explicitly: \fcode{meet_law x y} is a unit value that carries a
/// proof in the type system.

let (⊑) {|l:adom 'a|} = l.adom_lat.corder
let (⊔) {|l:adom 'a|} (x y:'a): r:'a { corder x r /\ corder y r 
                                 /\ (gamma x ∪ gamma y) ⊆ gamma r } = join x y
let (⊓) {|l:adom 'a|} (x y:'a): r:'a { corder r x /\ corder r y
                                 /\ (gamma x ∩ gamma y) ⊆ gamma r }
  = let _ = meet_law x y in meet x y

/// Lemmas are functions that produce refined \fcode{unit} values
/// carrying proofs.

/// Below, given an abstract domain \fcode{i}, and two abstract values
/// \fcode{x} and \fcode{y}, \fcode{join_lemma i x y} is a proof
/// concerning \fcode{i}, \fcode{x} and \fcode{y}.

/// Such an instantiation can be manual (i.e. below, \fcode{i.top_law
/// ()} in \fcode{top_lemma}), or automatic.

/// The automatic instantiation of a lemma is decided by the
/// SMT solver.

/// Below, we make use of the \fcode{SMTPat} syntax, that allows us to
/// give the SMT solver a list of patterns.

/// Whenever the SMT solver matches a pattern from the list, it
/// instantiates the lemma in stake.

/// The lemma \fcode{join_lemma} below states that the union of the
/// concretization of two abstract values \fcode{x} and \fcode{y} is
/// below the concretization of the abstract join of \fcode{x} and
/// \fcode{y}.

/// This is true because of \fcode{gamma}'s monotony: we help a bit
/// the SMT solver by giving a hint with \fcode{assert}.

/// This lemma is instantiated each time a proof goal contains
/// \fcode{x ⊑ y}.
///
/// Because of a technical limitation, we cannot write SMT patterns
/// directly in the \fcode{meet_law}, \fcode{bot_law} and
/// \fcode{top_law} fields of the class \fcode{adom}: thus, below we
/// reformulate them.

//@replace=a)|a)      (let bot_lemma, meet_lemma = ...)
let top_lemma (i: adom 'a)
  : Lemma (forall (x: i.c). x ∈ i.gamma i.adom_lat.top)
          [SMTPat (i.gamma i.adom_lat.top)] = i.top_law ()

//@hide=but shown as comment above
let bottom_lemma (i: adom 'a)
  : Lemma (forall (x: i.c). ~(x ∈ i.gamma i.adom_lat.bottom))
          [SMTPat (i.gamma i.adom_lat.bottom)]
  = i.bot_law ()

//@hide=but shown as comment above
let meet_lemma (i: adom 'a) (x y: 'a)
  : Lemma ((i.gamma x ∩ i.gamma y) ⊆ i.gamma (i.adom_lat.meet x y))
          [SMTPat (i.adom_lat.meet x y)]
  = meet_law x y

let join_lemma (i: adom 'a) (x y: 'a)
  : Lemma ((i.gamma x ∪ i.gamma y) ⊆ i.gamma (i.adom_lat.join x y))
          [SMTPat (i.adom_lat.join x y)]
  = let r = i.adom_lat.join x y in assert (gamma x ⊆ gamma r /\ gamma y ⊆ gamma r)


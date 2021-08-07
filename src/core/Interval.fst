module Interval

open Set
open MachineIntegers
open WithBottom
open FStar.Classical
open FStar.Tactics.Typeclasses
open ADom
open Order

/// Until now, the \gls{fstar} code we presented was mostly
/// specificational.

/// This section presents the abstract domain of intervals, and thus
/// shows how proof obligations are dealt with in \gls{fstar}.

/// Below, the type \fcode{itv'} is a dependent tuple: the refinement
/// type on its right-hand side component \fcode{up} depends on
/// \fcode{low}.

/// If a pair \fcode{(|x,y|)} is of type \fcode{itv'}, we have a proof
/// that \fcode{x <= y}.

type itv' = low:int_m & up:int_m {low <= up} (*@replace-newline:   *)
type itv  =  withbot itv'

/// The machine integers being finite, \fcode{itv'} naturally has a
/// top element.

/// However, \fcode{itv'} cannot represent the empty set of integers,
/// whence \fcode{itv}, that adds an explicit bottom element using
/// \fcode{withbot}.

/// The syntax \fcode{Val?} returns true when a value is not
/// \fcode{Bot}.

/// For convenience, \fcode{mk} makes an interval out of two numbers,
/// and \fcode{itv_card} computes the cardinality of an interval. We
/// use it later to define a measure for intervals.

/// \fcode{inbounds x} holds when \fcode{x:int} fits machine integer
/// bounds.

//!show WithBottom.withbot
let mk (x y: int): itv = if inbounds x && inbounds y && x <= y
                       then Val (|x,y|) else Bot
let itv_card (i:itv):nat = match  i  with | Bot -> 0 | Val i -> dsnd i - dfst i + 1

// This is due to a bug in F*'s normalizer: F* is supposed to be able
// to strongly normalize `x=y` (`x` and `y` being terms without any
// free variable) intro either `true` or `false`. However, it does not
// for dependent types.
// See [https://github.com/FStarLang/FStar/issues/2269].

//@hide
unfold let itv_equality (x y:itv): (r: bool {r <==> x== y})
  = match x, y with | Val (|a,b|), Val (|c,d|) -> a=c && b=d
                    | Bot, Bot -> true  | _ -> false


open Fixpoint

/// Below, \fcode{lat_itv} is an instance of the typeclass
/// \fcode{lattice} for intervals: intervals are ordered by inclusion,
/// the \fcode{meet} and \fcode{join} operations consist in unwrapping
/// \fcode{withbot}, then playing with bounds.

/// \fcode{lat_itv} is of type \fcode{lattice itv}: it means for
/// instance that we have the proof that the join and meet operators
/// respect the order \fcode{lat_itv.corder}, as stated in the
/// definition of \fcode{lattice}.

/// Note that here, not a single line of proof is required:
/// \gls{fstar} transparently builds up proof obligations, and asks
/// the SMT to discharge them, that does so automatically.

instance lat_itv: lattice itv =
  { corder = withbot_ord #itv' (fun (|a,b|) (|c,d|) -> a>=c && b<=d)
  ; join = (fun (i j: itv) -> match i, j with
       | Bot, k | k, Bot -> k
       | Val (|a,b|), Val (|c,d|) -> Val (|min a c, max b d|))
  ; meet = (fun (x y: itv) -> match x, y with
       | Val (|a,b|), Val (|c,d|) -> mk (max a c) (min b d)
       | _ -> Bot); bottom = Bot; top = mk min_int_m max_int_m }

/// Such automation is possible even with more complicated
/// definitions: for instance, below we define the classical widening
/// with thresholds.

/// Without a single line of proof, \fcode{widen} is shown as
/// respecting the order \fcode{corder}.

open FStar.List.Tot
//@hide
let find' (f:'a -> bool) (l:list 'a {Some? (find f l)}): (x:'a{f x}) = Some?.v (find f l)

//@regexp=;6.*|...]
let thresholds: list int_m  =  [min_int_m;-64;-32;-16;-8;-4;4;8;16;32;64;max_int_m]

#push-options "--fuel 14"
// @regexp=m(..)_int_m|m$1!${}_{\texttt{i{n}t}_\texttt{\kern.1mm m}}$!
let widen_bound_r (b: int_m): (r:int_m {r>b \/ b=max_int_m}) =
  if b=max_int_m then b else find' (fun (u:int_m) -> u>b) thresholds
// @regexp=m(..)_int_m|m$1!${}_{\texttt{i{n}t}_\texttt{\kern.1mm m}}$!
let widen_bound_l (b: int_m): (r:int_m {r<b \/ b=min_int_m}) =
  if b=min_int_m then b else find' (fun (u:int_m) -> u<b) (rev thresholds)
#pop-options

let widen (i j: itv): r:itv {corder i r /\ corder j r}
  = match i, j with | Bot, x | x, Bot -> x
  | Val(|a,b|),Val(|c,d|) -> Val (| (if a <= c then  a  else  widen_bound_l  c)
                              , (if b >= d then  b  else  widen_bound_r  d)|)

/// Similarly, turning \fcode{itv} into an abstract domain requires
/// no proof effort.

/// Below \fcode{itv_adom} explains that intervals concretize to
/// machine integers (\fcode{c = int_m}), how it does so (with
/// \fcode{gamma = itv_gamma}), and which lattice is associated with
/// the abstract domain (\fcode{adom_lat = lat_itv}).

/// As explained previously, the proof of a proposition $p$ in F* can
/// be encoded as an inhabitant of a refinement of \fcode{unit},
/// whence the "empty" lambdas: we let the SMT solver figure out the
/// proof on its own.

let itv_gamma: itv -> set int_m =  withbot_gamma  (fun (i:itv') x -> dfst i <= x /\ x <= dsnd i)

instance itv_adom: adom itv = { c = int_m   ; adom_lat = lat_itv; gamma = itv_gamma
    ; meet_law = (fun _ _->()); bot_law = (fun _->());  top_law = (fun _->())
    ; widen = widen     ; order_measure={f=itv_card;max=size_int_m}}

open FStar.Tactics.Logic
open ADom.Num
//@hide
private let gamma = itv_gamma

open NumTC
open Set

// /// As an example, we can tests our abstract domain by stating a few
// /// examples of inclusion, and let \gls{fstar} prove those
// /// automatically.

// let example0 (): Lemma (  v 0 ∈ (gamma (mk 0 2) + gamma (mk 0 2)) ) = ()
// let example1 (): Lemma (~(v 7 ∈ (gamma (mk 0 2) + gamma (mk 0 2)))) = ()

/// \subsection{Forward Binary Operations on Intervals}
/// \label{abint:sub:forward-op-itv}

/// Most of the binary operations on intervals can be written and
/// shown correct without any proof. Our operators handle machine
/// integer overflowing: for instance, \fcode{add_overflows} returns a
/// boolean indicating whether the addition of two integers overflows,
/// solely by performing machine integer operations.

/// The refinement of \fcode{add_overflows} states that the returned
/// boolean \fcode{r} should be true if and only if the addition in
/// \fcode{int} differs from the one in \fcode{int_m}.

/// The correctness of \fcode{itv_add} is specified as a refinement:
/// the set of the additions between the concretized values from the
/// input intervals is to be included in the concretization of the
/// abstract addition.

/// Its implementation is very simple, and its correctness proved
/// automatically.

let add_overflows (a b: int_m)
  : (r: bool {r <==> int_arith.n_add a b <> int_m_arith.n_add a b})
  = ((b<0) = (a<0)) && abs a > max_int_m - abs b

#push-options "--z3rlimit 10"
let itv_add (x y: itv): (r: itv {(gamma x + gamma y) ⊆ gamma r})
  = match x, y with | Val (|a, b|), Val (|c, d|)
                    -> if add_overflows a c || add_overflows b d
                      then top else Val (|a + c, b + d|) | _->Bot
#pop-options

/// However the SMT solver sometimes misses some necessary lemmas.

/// In such cases, we can either guide the SMT solver by
/// discriminating cases and inserting hints, or go fully manual with
/// a tactic system à la Coq.

/// Below, the \fcode{assert} uses tactics: everything within the
/// parenthesis following the \fcode{by} keyword is a computation that
/// manipulates proof goals.

/// Our aim is to prove that subtracting two numerical sets $a$ and
/// $b$ is equivalent to adding $a$ with the inverse of $b$.
///
/// \sloppy Unfortunately, due to the nature of \fcode{lift_binop},
/// this yields existential quantifications which are difficult for
/// the SMT solver to deal with. After normalizing our goal (with
/// \fcode{compute ()}), and dealing with quantifiers and implications
/// (\fcode{forall_intro}, \fcode{implies_intro} and
/// \fcode{elim_exists}), we are left with

/// \fcode{∃y. b (-y) /\ r=x+y}

/// knowing \fcode{b z /\ r=x-z} given some \fcode{z} as an
/// hypothesis.

/// Eliminating \fcode{∃y} with \fcode{-z} is enough to complete the
/// proof.
///
/// We sadly had to prove that (not too complicated) fact by hand.

/// This however shows the power of \gls{fstar}. Its type system is
/// very expressive: one can state arbitrarily mathematically hard
/// propositions (for which automation is hopeless).

/// In such cases, one can always resort to Coq-like manual proving to
/// handle hard proofs.

//!show Set.set_inverse

open FStar.Tactics
let lemma_inv (a b: set int_m)
  : Lemma ((a-b) ⊆ (a+set_inverse b)) [SMTPat (a+set_inverse b)]
  = assert ((a-b) ⊆ (a+set_inverse b)) by (  compute ();
      let _= forall_intro () in let p0 = implies_intro () in
      let witX,p1 = elim_exists (binder_to_term p0) in
      let witY,p1 = elim_exists (binder_to_term p1) in
      let z: int = unquote (binder_to_term witY) in
      witness witX; witness (quote (-z)))

/// Notice the SMT pattern: the lemma \fcode{lemma_inv} will be
/// instantiated each time the SMT deals with an addition involving an
/// inverse.

/// Defining the subtraction \fcode{itv_sub} is a breeze: it simply
/// performs an interval addition and an interval inversion.

/// Here, no need for a single line of proof for its correctness
/// (expressed as a refinement).

#push-options "--z3rlimit 8 --z3rlimit_factor 16"
let itv_inv (i: itv): (r: itv {set_inverse (gamma i) ⊆ gamma r})
  = match i with | Val(|lower, upper|) -> Val(|-upper, -lower|) | _ -> i
let itv_sub (x y:itv): (r: itv {(gamma  x - gamma  y) ⊆ gamma  r}) = itv_add x (itv_inv y)

/// Proving multiplication sound on intervals requires a lemma which is
/// not inferred automatically:

/// \[
/// \forall x \in [a,b], y\in[b,c].
///    \left[
///        \mathrm{min}\left(ac,ad,bc,bd\right)
///      , \mathrm{max}\left(ac,ad,bc,bd\right)
///    \right]
/// \]

/// In that case, decomposing that latter lemma into sublemmas
/// \fcode{lemma_min} and \fcode{lemma_mul} is enough.

/// Apart from this lemma, \fcode{itv_mul} is free of any proof term.

//!open MinMaxLemma
open MinMaxLemma

///

let mul_overflows (a b:int_m):(r:bool{r<>inbounds (int_arith.n_mul a b)})
  = a <> 0 && abs b > max_int_m `div_m` (abs a)

// @replace=(a*c) `min` (a*d) `min` (b*c) `min` (b*d)|min4 (a*b) (a*d) (a*c) (b*d)
//@regexp=let.*op_Star.*\n +|
let itv_mul (x y: itv): r:itv {(gamma x * gamma y) ⊆ gamma r}
  = match x, y with
    | Val (|a, b|), Val (|c, d|) ->
        let ( * ) = FStar.Mul.op_Star in
        let l = (a*c) `min` (a*d) `min` (b*c) `min` (b*d) in
        let r = (a*c) `max` (a*d) `max` (b*c) `max` (b*d) in
        if mul_overflows a c || mul_overflows a d
        || mul_overflows b c || mul_overflows b d 
        then top else Val (|l, r|)
    | _ -> Bot

/// The forward boolean operators for intervals require no proof at
/// all; here we only give their type signatures.

/// A function of interest is \fcode{itv_as_bool}: it returns
/// \fcode{TT} when an interval does not contain 0, \fcode{FF} when
/// it is the singleton 0, \fcode{Unk} otherwise.

//@replace=private |
private let beta (x: int_m): itv = mk x x
//@...
//@regexp=$|  let itv_lt=!\shortdots!
let itv_eq (x y:itv): r:itv {(gamma  x `n_eq` gamma  y)  ⊆  gamma  r}
  = if x `itv_equality` y && itv_card x = 1
    then beta 1 else if Bot? (x ⊓ y) then beta 0 else mk 0 1

//@hide=but shown as comment above
let itv_lt (x y: itv): (r: itv {(gamma x `n_lt` gamma y) ⊆ gamma r})
  = match x, y with | Bot, _ | _, Bot -> beta 1
  | Val(|a,b|),Val(|c,d|) -> if b<c then beta 1
                               else if a>d then beta 0 else mk 0 1

//@...
let itv_cgamma (i: itv) (x:int_m): r:bool {r <==> itv_gamma i x}
  = match i with | Bot -> false | Val (|l, u|) -> l <= x && x <= u

//@hide=but shown as comment below
type ubool = | Unk | TT | FF
//@regexp'=ubool-->>ubool !\textcolor{gray}{\texttt{ /{}/ with \textbf{type ubool = |Unk|TT|FF}}}!
let itv_as_bool (x:itv): ubool
  = if beta 0`itv_equality`x || Bot?x then FF else if itv_cgamma x 0 then Unk else TT

let itv_andi (x y: itv): (r: itv {(gamma x `n_and` gamma y) ⊆ gamma r})
  = match itv_as_bool x, itv_as_bool y with
  | TT, TT  -> beta 1 | FF, _ | _, FF -> beta 0 | _, _ -> mk 0 1
//@...
let itv_ori (x y: itv): (r: itv {(gamma x `n_or` gamma y) ⊆ gamma r})
  = match itv_as_bool x, itv_as_bool y with
  | FF, FF -> beta 0 | TT, _ | _, TT  -> beta 1 | _, _ -> mk 0 1
#pop-options

//@hide
instance itv_arith: num itv = {n_lt=itv_lt; n_and=itv_andi; n_or=itv_ori
   ; n_add=itv_add; n_sub=itv_sub; n_mul=itv_mul; n_eq = itv_eq}

/// \subsection{Backward Operators}
/// \label{abint:sub:backward-op-itv}

/// While a forward analysis for expressions is essential, another
/// powerful analysis can be made thanks to backward operators.

/// Typically, it aims at extracting information from a test, and at
/// refining the abstract values involved in this test, so that we
/// gain in precision on those abstract values.

/// Given a concrete binary operator \fcode{⊕}, we define
/// $\overleftarrow{⊕}$ its abstract backward counterpart.

/// Let three intervals \fcode{xⵌ}, \fcode{yⵌ}, and \fcode{rⵌ}.

/// $\overleftarrow{⊕}\fcodemm{ xⵌ yⵌ rⵌ}$ tries to find the most
/// precise intervals \fcode{xⵌⵌ} and
/// \fcode{yⵌⵌ} supposing

/// \fcode{gamma xⵌ ⊕ gamma yⵌ ⊆ gamma rⵌ}.

/// The soundness of $\overleftarrow{⊕}\fcodemm{ xⵌ yⵌ rⵌ}$ can be
/// formulated as below.

/// We later generalize this notion of soundness with the type
/// \fcode{sound_backward_op}, which is indexed by an abstract domain
/// and a binary operation.

/// \begin{fequation}
/// let xⵌⵌ, yⵌⵌ = (!$\overleftarrow{⊕}$!) xⵌ yⵌ rⵌ in
///  forall x y. (x ∈ gamma xⵌ /\ y ∈ gamma yⵌ /\ op x y ∈ gamma rⵌ)
///     ==> (x ∈ gamma xⵌⵌ /\ y ∈ gamma yⵌⵌ)
/// \end{fequation}

/// As the reader will discover in the rest of this section, this
/// statement of soundness is proved entirely automatically against
/// each and every backward operator for the interval domain.

/// For \fcode{op} a concrete operator, \fcode{sound_backward_op itv
/// op} is inhabited by sound backward operators for \fcode{op} in the
/// domain of intervals.

/// If one shows that $\overleftarrow{⊕}$ is of type

/// \fcode{sound_backward_op itv (+)}, it means exactly that
/// $\overleftarrow{⊕}$ is a sound backward binary interval operator
/// for \fcode{(+)}.

/// The rest of the listing shows how light in proof and OCaml-looking
/// the backward operations are.

/// Below, we explain how \fcode{backward_lt} works: it is a bit
/// complicated because it hides a "\fcode{backward_ge}" operator.

//@regexp=unfold |
// unfold type sound_bbop op = b:(itv->itv->itv->itv&itv){bkwd_bp_is_sound b op}

#push-options "--z3rlimit 200 --z3rlimit_factor 4"
let backward_add: sound_backward_op itv n_add = fun x y r -> x ⊓ (r-y), y ⊓ (r-x)
let backward_sub: sound_backward_op itv n_sub = fun x y r -> x ⊓ (r+y), y ⊓ (x-r)
#pop-options

#push-options "--z3rlimit_factor 8"
let backward_mul: sound_backward_op itv n_mul = fun x y r -> 
  let h (i j:itv) = (if j=beta 1 then i ⊓ r else i) in h x y, h y x
#pop-options
   
let backward_eq:  sound_backward_op itv n_eq
  = fun x y r -> match itv_as_bool r with | TT -> x ⊓ y,x ⊓ y | _ -> x,y

//@...
let (∖) (x y: itv): (r: itv {(gamma x ∖ gamma y) ⊆ gamma r})
  = if x ⊑ y then Bot
    else if Bot? x || Bot? y || Bot? (x ⊓ y) then x
         else let Val (| a, b |) = x in
              let Val (| c, d |) = y in
              if x ⊔ y `itv_equality` x && a<>c && b<>d then x
              else if c<=a then mk (1 + d) b
                          else mk a (-1 + c)

#push-options "--z3rlimit 80"
let backward_and: sound_backward_op itv n_and
  = fun x y r -> match itv_as_bool r,itv_as_bool x,itv_as_bool y with
    | FF, TT, _ -> x, y ⊓ beta 0         | FF, _, TT -> x ⊓ beta 0, y
    | TT,  _, _ -> x ∖ beta 0, y ∖ beta 0   | _ -> x, y

let backward_or: sound_backward_op itv n_or
  = fun x y r -> match itv_as_bool r,itv_as_bool x,itv_as_bool y with
    | TT,FF,Unk | TT,FF,FF -> x, y ∖ beta 0 | TT,Unk,FF -> x ∖ beta 0, y
    | FF, _, TT | FF, TT, _ -> x ⊓ beta 0, y ⊓ beta 0 | _ -> x, y
#pop-options

/// Let us look at \fcode{backward_lt}.

/// Knowing whether \fcode{x < y} holds, \fcode{backward_lt} helps us
/// refining \fcode{x} and \fcode{y} to more precise intervals.

/// Let \fcode{x} be the interval $[0;\fcodemm{max_int_m}]$, \fcode{y}
/// be $[5;15]$ and \fcode{r} be $[0;0]$.

/// Since the singleton $[0;0]$ represents \fcode{false},
/// \fcode{backward_lt x y r} aims at refining \fcode{x} and \fcode{y}
/// knowing that \fcode{x < y} doesn't hold, that is, knowing
/// $\fcodemm{x} \geq \fcodemm{y}$.

/// In this case, \fcode{backward_lt} finds $\fcodemm{x'} =
/// [5;\fcodemm{max_int_m}]$ and $\fcodemm{y'} = [5;15]$.

/// Indeed, when \fcode{r} is $[0;0]$, \fcode{itv_as_bool r} equals to
/// \fcode{FF}.

/// Then we rewrite $\neg(\fcodemm{x} < \fcodemm{y})$ either as
/// $\fcodemm{y} < \fcodemm{x} + 1$ (when \fcode{x} is
/// \fcode{incrementable}) or as $\fcodemm{y}-1 < \fcodemm{x}$.

/// In our case, \fcode{x}'s upper bound is \fcode{max_int_m} (the
/// biggest \fcode{int_m}): x is not incrementable.

/// Thus we rewrite $\neg([0;\fcodemm{max_int_m}] < [5;15])$ as $[6;16]
/// < [0;\fcodemm{max_int_m}]$.

///
/// Despite of these different case handling, the implementation of
/// \fcode{backward_lt} required no proof: the SMT solver takes care
/// of everything automatically.


let backward_lt_true (x y: itv)
  = match x, y with | Bot, _ | _, Bot -> x,y
  | Val(|a,b|), Val(|c,d|) -> mk a (min b (d-1)), mk (max (a+1) c) d

//@regexp=$|  let incr.=...
//@regexp'=\(i:itv\)-->>i
let decrementable (i:itv)=Val?i&&dfst(Val?.v i)>min_int_m
//@hide=but shown as comment above
let incrementable (i:itv)=Val?i&&dsnd(Val?.v i)<max_int_m
#push-options "--z3rlimit 100 --z3rlimit_factor 4"
let backward_lt: sound_backward_op itv n_lt
  = fun x y r -> match itv_as_bool r with | TT -> backward_lt_true x y
  | FF -> if incrementable x // x < y ⇔ y > x+1
         then let ry, rx = backward_lt_true y (itv_add x (beta 1)) in
              itv_sub rx (beta 1), ry
         else if decrementable y // x < y ⇔ y-1 > x
              then let ry, rx = backward_lt_true (itv_sub y (beta 1)) x in
                   rx, itv_add ry (beta 1)
              else x,y | _ -> x, y
#pop-options

open LangDef

//@regexp'=function \| +([^ ]+) +-> +([^ \n]+)[^)]+ ([^ ]+) +-> +([^ \n]+ *)\)-->>function | $1 -> $2 ... | $3 -> $4)
//@hide-because-shown-at-module=ADom.Num
instance itv_num_adom: num_adom itv = {
  na_adom = solve; adom_num = (); cgamma = itv_cgamma; beta = (λ x -> beta x);
  abstract_binop = (function | Plus  -> itv_add
                             | Minus -> itv_sub
                             | Mult  -> itv_mul
                             | Eq    -> itv_eq
                             | Lt    -> itv_lt
                             | And   -> itv_andi
                             | Or    -> itv_ori);
  backward_abstract_binop = (function | Plus  -> backward_add
                   | Minus -> backward_sub
                   | Mult  -> backward_mul
                   | Eq    -> backward_eq
                   | Lt    -> backward_lt
                   | And   -> backward_and
                   | Or    -> backward_or );
  lt0 = (mk min_int_m (-1)); gt0 = (mk ( 1) max_int_m) }


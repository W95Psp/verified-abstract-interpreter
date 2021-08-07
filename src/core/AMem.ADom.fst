module AMem.ADom

open FStar.Tactics.Typeclasses

open LangDef
open ADom
open Set
open MachineIntegers
open AbstractSemantic
open ADom.Num
open ADom.Mem
open AMem
open WithBottom
open OperationalSemantic

//@hide
instance adom_to_alat {| l: num_adom 'a |}: lattice 'a
  = l.na_adom.adom_lat

//@hide
private unfold let bottom {|l:lattice 'a|}: r:'a{True} = l.bottom

/// The rest of this section defines a \fcode{mem_adom} instance for
/// our memories \fcode{amem}.

/// The typeclass \fcode{mem_adom} is an essential piece in our
/// abstract interpreter: it provides the abstract operations for
/// handling assumes and assignments.

/// \subsubsection{Forward expression analysis}

/// We define \fcode{asem_expr}, mapping expressions to abstract
/// values of type \fcode{'a}.

/// It is defined for any abstract domain, whence the typeclass
/// argument

/// \fcode{{|num_adom 'a|}}.

/// The abstract interpretation of an expression \fcode{e} given
/// \fcode{mⵌ0} an initial memory is defined below as

/// \fcode{asem_expr mⵌ0 e}.

/// It is specified via a refinement type to be a sound abstraction of
/// \fcode{e}'s operational semantics \fcode{osem_expr m0 e}.

/// This function leverages the operators from the different
/// typeclasses for which we defined instances just above.

/// \fcode{beta:int_m->'a} and \fcode{abstract_binop:binop->...} come
/// from \fcode{num_adom}, while \fcode{top:'a} comes from
/// \fcode{lattice}.

open ADom.Mem

val get: m:amem 'a {Val? m} -> varname -> 'a (*@replace-newline:    *)
let get (Val m) = get' m

#push-options "--z3rlimit 30 --z3rlimit_factor 4"
let rec asem_expr {|num_adom 'a|} (mⵌ0: amem 'a) (e: expr)
 : (r: 'a { forall (m0: mem). m0 ∈ gamma mⵌ0 ==> osem_expr m0 e ⊆ gamma r })
 = if mⵌ0 ⊑ bottom then bottom else
   match e with | Const x -> beta x | Unknown -> top | Var v -> get mⵌ0 v
   | BinOp op x y -> abstract_binop  op  (asem_expr  mⵌ0  x) (asem_expr  mⵌ0  y)
#pop-options

/// \subsubsection{Backward analysis}

/// Our aim is to have an instance for our memory of \fcode{mem_adom}:
/// it expects an \fcode{assume_} operator. Thus, below a backward
/// analysis is defined for expressions.

/// Given an expression \fcode{e}, an abstract value \fcode{rⵌ} and a
/// memory \fcode{mⵌ0}, \fcode{backward_asem e rⵌ mⵌ} computes a new
/// abstract memory.

/// That abstract memory refines the abstract values held in
/// \fcode{mⵌ0} as much as possible under the hypothesis that \fcode{e}
/// lives in \fcode{rⵌ}.

/// The soundness of this analysis is encoded as a refinement on the
/// output memory. Given any concrete memory \fcode{m0} and integer
/// \fcode{v} approximated by \fcode{rⵌ}, if the operational semantics of
/// \fcode{e} at memory \fcode{m0} contains \fcode{v}, then \fcode{m0}
/// should also be approximated by the output memory.

///
/// When \fcode{e} is a constant which is not contained in the
/// concretization of the target abstract value \fcode{rⵌ}, the
/// hypothesis "\fcode{e} lives in \fcode{rⵌ}" is false, thus we
/// translate that fact by outputting the unreachable memory
/// \fcode{bottom}.

/// In opposition, when \fcode{e} is \fcode{Unknown}, the hypothesis
/// brings no new knowledge, thus we return the initial memory
/// \fcode{mⵌ0}.

/// In the case of a variable lookup (i.e. \fcode{e = Var v} for some
/// \fcode{v}), we consider \fcode{xⵌ}, the abstract value living at
/// \fcode{v}.

/// Since our goal is to craft the most precise memory such that
/// \fcode{Var v} is approximated by \fcode{rⵌ}, we alter \fcode{mⵌ0}
/// by assigning \fcode{xⵌ ⊓ rⵌ} at the variable \fcode{v}.

/// Finally, in the case of binary operations, we make use of the
/// backward operators and of recursion.

/// Note that it is the only place where we need to insert a hint for
/// the SMT solver: we assert an equality by asking \gls{fstar} to
/// normalize the terms.

/// We state explicitly that the operational semantics of a binary
/// operation reduces to two existentials: we manually unfold the
/// definition of \fcode{osem_expr} and \fcode{lift_binop}. The
/// \fcode{decreases} clause explains to \gls{fstar} why and how the
/// recursion terminates.

#push-options "--z3rlimit 100 --z3rlimit_factor 8"
let rec backward_asem {|l:num_adom 'a|} (e: expr) (rⵌ: 'a) (mⵌ0: amem 'a)
: Tot (mⵌ1: amem 'a { (* decreases: *) mⵌ1 ⊑ mⵌ0 /\ (* soundness: *)
      (forall(m0:mem) (v:int_m). (v ∈ gamma  rⵌ /\ m0 ∈ gamma  mⵌ0 /\ v ∈ osem_expr m0 e)
                               ==> m0 ∈ gamma mⵌ1)}) (decreases e)
  = if mⵌ0 ⊑ bottom then bottom else match e with
  | Const x -> if cgamma rⵌ x then mⵌ0 else bottom | Unknown -> mⵌ0
  | Var v -> let xⵌ: 'a =  rⵌ ⊓ get  mⵌ0 v  in
            if xⵌ ⊑ bottom then Bot else amem_update v xⵌ  mⵌ0
  | BinOp op ex ey -> let backward_op = backward_abstract_binop op in
      let xⵌ, yⵌ = backward_op (asem_expr mⵌ0 ex) (asem_expr mⵌ0 ey) rⵌ in
      let rⵌ: amem 'a = backward_asem ex xⵌ mⵌ0 ⊓ backward_asem ey yⵌ mⵌ0 in
      assert_norm (forall (m: mem) (v: int_m). v ∈ osem_expr m e
        <==> (exists (x y:int_m). x ∈ osem_expr m ex /\ y ∈ osem_expr m ey
                         /\ v == concrete_binop op x y));
      rⵌ  
#pop-options

open Fixpoint

/// \subsubsection{Iterating the backward analysis}

/// While a concrete test is idempotent, it is not the case for
/// abstract ones.

/// Our goal is to refine an abstract memory under a hypothesis as
/// much as possible.

/// Since \fcode{backward_asem} is proven sound and decreasing, we can
/// repeat the analysis as much as we want. We introduce
/// \fcode{prefixpoint} that computes a pre-fixpoint.

//!open Fixpoint

/// Below is defined \fcode{backward_asem_fp} the iterated version of
/// \fcode{backward_asem}.

/// Besides using \fcode{prefixpoint}, the only thing required here is
/// to spell out \fcode{t}, the relation we want to ensure.

let backward_asem_fp {|num_adom 'a|} (e:expr) (r:'a) (mⵌ0:amem 'a)
  : Tot (mⵌ1: amem 'a {(forall (m0:mem) (v:int_m). mⵌ1 ⊑ mⵌ0 /\
                   (v ∈ gamma r /\ m0 ∈ gamma mⵌ0 /\ v ∈ osem_expr m0 e) ==> m0 ∈ gamma mⵌ1)})
  = let t (mⵌ0 mⵌ1: amem 'a) = forall (m: mem) (v: int_m).
      (v ∈ gamma r /\ m ∈ gamma mⵌ0 /\ v ∈ osem_expr m e) ==> m ∈ gamma mⵌ1 in
    prefixpoint corder order_measure t (backward_asem e r) mⵌ0

/// \subsubsection{A \fcode{mem_adom} instance} We defined both a
/// forward and backward analysis for expressions. Implementing an
/// \fcode{mem_adom} instance for \fcode{amem} is thus easy, as shown
/// below.

/// For any numerical abstract domain \fcode{'a},
/// \fcode{amemory_mem_adom} provides an \fcode{mem_adom}, that is,
/// an abstract domain for memories, providing nontrivial proofs of
/// correctness. Still, this is proven automatically.

#push-options "--z3rlimit 30 --z3rlimit_factor 4"
instance amemory_mem_adom {| nd: num_adom 'a |}: mem_adom (amem 'a) =
  let adom: adom (amem 'a) = amem_adom in { ma_adom = adom; ma_mem = ()
  ; assume_ = (fun mⵌ e -> backward_asem_fp e gt0 mⵌ ⊔ backward_asem_fp e lt0 mⵌ)
  ; assign = (fun mⵌ v e -> let vⵌ: 'a = asem_expr mⵌ e in
                if vⵌ ⊑ bottom then Bot else amem_update v vⵌ mⵌ)}
#pop-options


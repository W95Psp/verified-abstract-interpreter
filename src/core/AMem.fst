module AMem

open Set
open NumTC
open WithBottom
open FStar.FunctionalExtensionality
open Interval
open LangDef
open FStar.Tactics.Typeclasses
open ADom

/// In this section, we define a weakly-relational abstract memory.

/// This abstraction is said weakly-relational because the entrance of
/// an empty abstract value in the map systematically launches a
/// reduction of the whole map to \fcode{Bot}.

/// Below we define an abstract memory (\fcode{amem}) as either an
/// unreachable state (\fcode{Bot}), or a mapping (\fcode{map 't})
/// from \fcode{varname} to abstract values \fcode{'t}.

/// The mappings \fcode{map 'a} are equipped with the utility
/// functions \fcode{mapi}, \fcode{map1}, \fcode{map2} and
/// \fcode{fold}.

/// \begin{fstarcode}
/// type map 'a =!\shortdots!                 type amem 'a = withbot (map 't)
/// let get': map 'a -> varname -> 'a =!\shortdots!  let fold: ('a->'a->'a) -> map 'a -> 'a =!\shortdots!
/// let mapi: (varname -> 'a -> 'b) -> map 'a -> map 'b =!\shortdots!
/// let map1: ('a->'b) -> map 'a -> map 'b = fun f -> mapi (fun _ -> f)
/// let map2: ('a->'b->'c) -> map 'a -> map 'b -> map 'c =!\shortdots!
/// \end{fstarcode}

//@hide=but shown as comment above
type map 't = {va:'t;vb:'t;vc:'t;vd:'t}

//@hide=but shown as comment above
let get' (m: map 't) (k: varname): 't
  = match k with | VA -> m.va | VB -> m.vb | VC -> m.vc | VD -> m.vd

//@hide=but shown as comment above
let mapi (f: varname -> 'a -> 'b) (m: map 'a): r:map 'b //{forall v. get' r v == f v (get' m v)}
  = { va = f VA (get' m VA); vb = f VB (get' m VB); vc = f VC (get' m VC); vd = f VD (get' m VD)}


////@hide=but shown as comment above
// let (<*>) (f: map ('a -> 'b)) (m: map 'a)
// //  : r:map 'b {forall v. get' r v == (get' f v) (get' m v)}
//   = { va = (get' f VA) (get' m VA); vb = (get' f VB) (get' m VB)
//     ; vc = (get' f VC) (get' m VC); vd = (get' f VD) (get' m VD)}

//@hide=but shown as comment above
let fold (f:'a->'a->'a) (m:map 'a): 'a
    = f (f (f m.va m.vb) m.vc) m.vd
    
//@hide=but shown as comment above
let map1 (f:'a->'b) = mapi (fun _ -> f)

//@hide=but shown as comment above
let map2 (f: 'a -> 'b -> 'c) (m1: map 'a) (m2: map 'b): map 'c
  = { va = f (get' m1 VA) (get' m2 VA); vb = f (get' m1 VB) (get' m2 VB); vc = f (get' m1 VC) (get' m2 VC); vd = f (get' m1 VD) (get' m2 VD)}

//@hide=but shown as comment above
type amem 't = withbot (map 't)

/// \subsubsection{A lattice structure}
/// The listing below presents \fcode{amem} instances for the
/// typeclasses \fcode{order}, \fcode{lattice} and \fcode{mem_adom}.

/// Once again, the various constraints imposed by these different
/// typeclasses are discharged automatically by the SMT solver.

let amem_update (k: varname) (v: 't) (m: amem 't): amem 't
  = match m with | Bot -> Bot
    | Val m -> Val (mapi (fun k' v' -> if k'=k then v else v') m)

open Order

#push-options "--z3rlimit 30 --z3rlimit_factor 4"
//@regexp=top.*|top = ...}
instance amem_lat {| l: adom 'a |}: lattice (amem 'a) =
  { corder = withbot_ord (fun m0 m1 -> fold (&&) (map2 corder  m0  m1))
  ; join = (fun x y -> match x, y with
      | Val x, Val y -> Val (map2 join x y) | m,Bot | _,m -> m)
  ; meet = (fun x y -> match x, y with
      | Val x, Val y ->
        let m = map2 (⊓) x y in
        if fold ( || ) (mapi (fun _ v -> l.adom_lat.corder v bottom) m)
        then Bot else Val m
      | _ -> Bot); bottom = Bot; top = Val ({ va = top; vb = top; vc = top; vd = top })}
#pop-options

open Fixpoint

//@hide
private let ( + ) (x:nat) (y:nat): nat = Prims.op_Addition x y
//@hide
private let ( * ) (x:nat) (y:nat): nat = Mul.op_Star x y

#push-options "--z3rlimit 30 --z3rlimit_factor 4"
instance amem_adom {|l:adom 'a|}: adom (amem 'a) = { c = mem' l.c
  ; adom_lat=solve; meet_law=(fun _ _->()); top_law=(fun _->()); bot_law=(fun _->())
  ; gamma = withbot_gamma (fun mⵌ m -> fold (/\) (mapi (fun v x -> m v ∈ gamma x) mⵌ))
  ; widen = (fun x y -> match x, y with
    | Val x, Val y -> Val (map2 widen x y) | m,Bot | _,m -> m)
  ; order_measure = let {max; f} = l.order_measure in
    { f = (function | Bot -> 0 | Val mⵌ -> 1 + fold (+) (map1 f mⵌ))
    ; max = 1 + max * 4 }}
#pop-options


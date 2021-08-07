module WithBottom
open Order

type withbot (a: Type) = | Val: v:a -> withbot a | Bot
//@hide
let option_of_withbot = function | Val x -> Some x
                                 | Bot   -> None
//@hide
let bind x f = match x with | Val x -> f x | Bot -> Bot

//@regexp=unfold |
//@let-as-val
unfold let withbot_ord #a (o: order a): order (withbot a)
  = let f x y = match x, y with
                | Bot, _ -> true | _, Bot -> false
                | Val x, Val y -> o x y
    in assert_norm (trans o ==> trans f);
       f

open Set

//@regexp=unfold |
//@let-as-val
unfold let withbot_gamma #a #c (gamma: a -> set c): (withbot a -> set c)
    = function | Bot -> (fun _ -> False)
               | Val x -> gamma x





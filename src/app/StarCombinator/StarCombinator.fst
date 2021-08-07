module StarCombinator

open FStar.String
open FStar.Char

module M = FStar.Mul
module L = FStar.List.Tot.Base
module T = FStar.Tactics

include StarCombinator.Core
include StarCombinator.Operators
include StarCombinator.Base

(* delayMe makes a parser act "lazy", then you can define recursive parsers (hopefully!) *)
//let delayMe #a (p: unit -> parser a): parser a = fun a b -> (p ()) a b

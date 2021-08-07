module Interval.Extra

open Interval
open PrettyPrint
open StarCombinator
open LangDef
open LangDef.Extra
open WithBottom
open ADom

open HasDefault
//@hide
instance itv_has_default: has_default itv = { def = mk 0 0 }

let string_of_itv' (i: itv'): string =
  let (|l,r|) = i in "[" ^ string_of_int l ^ "," ^ string_of_int r ^ "]"

let string_of_itv = function | Bot -> "Bot" | Val i -> string_of_itv' i
instance itv_pp: prettyprintable itv = {print = string_of_itv}
instance itv'_pp: prettyprintable itv' = {print = string_of_itv'}

open MachineIntegers
let itv'_parser: parser itv'
  = (   flatten_option
    (   ((fun (x, y) -> option_of_withbot (mk x y)) <: int_m*int_m -> _)
    @<< between_kwd "[" "]" (int_m_parser <*> ((keyword "," <|> keyword ";") <*>> int_m_parser))
    )   "Bad itv")
    <|> (fun x -> let i: itv'=(|x, x|) in i) @<< int_m_parser
    <|> (Val?.v top) *<< (keyword "?" <|> keyword "T")


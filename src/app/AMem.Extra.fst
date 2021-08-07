module AMem.Extra

open StarCombinator
open PrettyPrint
open Interval 
open WithBottom
open HasDefault
open LangDef.Extra
open LangDef
open AMem

let map_empty {| has_default 't |}: map 't = ({va=def;vb=def;vc=def;vd=def})
let amem_empty {| has_default 't |}: amem 't = Val map_empty

instance amem_has_default {| has_default 't |}: has_default (amem 't) = {
  def = amem_empty
}

open PrettyPrint
let string_of_amem {| prettyprintable 't |} (m: amem 't): string
  = match m with
  | Bot -> "Bot"
  | Val m -> "{A=" ^ print (get' m VA) ^ ";"
          ^ " B=" ^ print (get' m VB) ^ ";"
          ^ " C=" ^ print (get' m VC) ^ ";"
          ^ " D=" ^ print (get' m VD) ^ "}"

private let map_update (k: varname) (v: 't) (m: map 't): map 't
  = mapi (fun k' v' -> if k'=k then v else v') m

let parse_map #a {|has_default a|} (f: parser a): parser (map a) =
  let tuple_parser: parser (varname&a) = varname_parser <*> ((operator "=" <|> operator ":") <*>> f) in
  List.Tot.fold_left (fun x (v, i) -> map_update v i x) map_empty
  @<< (sepBy tuple_parser (operator "," <|> operator ";"))

let parse_amem #a {|has_default a|} (f: parser a): parser (amem a)
  =   (Bot *<< exact_string "Bot")
  <|> (Val @<< parse_map f)

instance stmt_pp (a: Type) {| prettyprintable a |}: prettyprintable (amem a) = { print = string_of_amem }


module LangDef.Extra

open LangDef
open PrettyPrint
open StarCombinator
open WithBottom
open Doc
open MachineIntegers

let string_of_binop = function | Plus -> "+" | Minus -> "-" | Mult -> "*" | Eq -> "==" | Lt -> "<" | And -> "&&" | Or -> "||"
let string_of_varname = function | VA -> "a" | VB -> "b" | VC -> "c" | VD -> "d"
let rec string_of_expr' e par
  = let lparen = if par then "(" else "" in
    let rparen = if par then ")" else "" in
    match e with
  | Const i -> string_of_int i
  | BinOp op a b -> lparen ^ string_of_expr' a true ^ " " ^ string_of_binop op ^ " " ^ string_of_expr' b true ^ rparen
  | Var v -> string_of_varname v
  | _ -> "?"

let string_of_expr e = string_of_expr' e false

let doc_of_choice (a b: doc unit): doc unit
  = str "choice" <+> space
    <+> lbrace <+> indent (nl <+> a) <+> nl <+> rbrace
    <+> space // <+> str "or" <+> space
    <+> lbrace <+> indent (nl <+> b) <+> nl <+> rbrace

let enable_pretty_print_ifs = false

let rec doc_of_stmt (s: stmt): Tot (doc unit) (decreases s) = match s with
  | Assign v e -> str (string_of_varname v) <+> str " = " <+> str (string_of_expr e)
  | Assume e -> str "assume" <+> space <+> lparen <+> str (string_of_expr e) <+> rparen
  | Choice (Seq (Assume c) a) (Seq (Assume (BinOp Eq c' (Const 0))) b) ->
           if c = c' && enable_pretty_print_ifs
           then str "if" <+> space <+> lparen <+> str (string_of_expr c) <+> rparen
           <+> lbrace <+> indent (nl <+> doc_of_stmt a) <+> nl
           <+> rbrace <+> str " else "
           <+> lbrace <+> indent (nl <+> doc_of_stmt b) <+> nl <+> rbrace
           else doc_of_choice (doc_of_stmt (Seq (Assume c) a)) (doc_of_stmt (Seq (Assume (BinOp Eq c' (Const 0))) b))
  | Choice a b -> doc_of_choice (doc_of_stmt a) (doc_of_stmt b)
  | Seq a b -> doc_of_stmt a <+> str ";" <+> nl <+> doc_of_stmt b
  | Loop a -> str "loop " <+> lbrace <+> indent (nl <+> doc_of_stmt a) <+> nl <+> rbrace <+> nl


let string_of_stmt s = doc_to_string (doc_of_stmt s)

let int_m_parser: parser int_m
  = flatten_option
    ((fun (x: int) -> if inbounds x then Some (x <: int_m) else None) @<< number)
    "This number is not in [-127;127]"

let operator' (l: _ {l <> []}) = spaces <*>> choice (List.Tot.map exact_string l) <<*> spaces

let binop_parser: parser binop
  = (function
    | "+"  -> Plus
    | "-"  -> Minus
    | "*"  -> Mult
    | "==" -> Eq
    | "<"  -> Lt
    | "&&" -> And
    | _ -> Or
    ) @<< operator' ["+";"-";"*";"<";"==";"&&";"||"]
  
let varname_parser: parser varname
  =   VA *<< (exact_string "a")
  <|> VB *<< (exact_string "b")
  <|> VC *<< (exact_string "c")
  <|> VD *<< (exact_string "d")

let between_par = between_kwd "(" ")"
let between_braces = between_kwd "{" "}"

let expr_parser: parser expr =
  let rec no_rec (): parser expr =
          between_par  (admitP (()<<()); delayMe h')
      <|> Const @<< number
      <|> Var @<< varname_parser
  and h' (): parser expr = admitP (() << ()); let h = delayMe h' in
       (function 
       | (e, None) -> e
       | (l, Some (op, r)) -> BinOp op l r
       )@<< (no_rec () <*> maybe (binop_parser <*> h))
  in wrapspace (h' ())

let mkIf (c: expr) (a b: stmt): stmt
  = Choice (Seq (Assume c) a)
           (Seq (Assume (BinOp Eq c (Const 0))) b)

let stmt_parser: parser stmt =
  let rec no_rec (): parser stmt =
           Assume @<< (keyword "assume" <*>> expr_parser)
      <|> (fun (v, n) -> Assign v n) @<< (varname_parser <*> (operator "=" <*>> expr_parser))
  and h' (): parser stmt = admitP (() << ()); let h = delayMe h' in
      begin
        (function
        | (l, Some r) -> Seq l r
        | (l, None) -> l
        ) @<<
        ((    (fun ((c, a), b) -> mkIf c a b) @<< ((keyword "if" <*>> between_par expr_parser) <*> between_braces h <*> (keyword "else" <*>> between_braces h))
          <|> (fun (a, b) -> Choice a b) @<< (keyword "choice" <*>> between_braces h <*> between_braces h)
          <|> Loop @<< (keyword "loop" <*>> between_braces h)
         ) <*> maybe h)
      end
      <|> (function 
          | (e, None) -> e
          | (l, Some r) -> Seq l r
          ) @<< (no_rec () <*> maybe (operator ";" <*>> h))
  in wrapspace (h' ()) <<*> maybe (operator ";")

instance stmt_pp: prettyprintable stmt = { print = string_of_stmt }
instance expr_pp: prettyprintable expr = { print = string_of_expr }
instance binop_pp: prettyprintable binop = { print = string_of_binop }
instance varname_pp: prettyprintable varname = { print = string_of_varname }


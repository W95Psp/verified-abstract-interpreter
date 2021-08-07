module Main
open AbstractSemantic
open LangDef
open LangDef.Extra
open Set
open HasDefault

open Interval
open Interval.Extra
open AMem
open AMem.Extra

open FStar.All
open FStar.IO

open StarCombinator
open StarCombinator.Helpers
let fail s = "\x1B[1m\x1B[41m" ^ s ^ cstENDC

let exact_string (s: string) = exact_string (if s = "" then "bad" else s)

noeq
type options (amType: Type) =
  { //asem: asem_options
    program_fd: option fd_read
  ; initial_memory: amType
  ; final_memory: option amType
  ; widening: bool
  }

// let default_asem_options =
//   { use_backward_fixpoint = true
//   }

instance options_has_default {| has_default 'm |}: has_default (options 'm)
  = { def = { //asem = default_asem_options
              program_fd = None
            ; initial_memory = def
            ; final_memory = None
            ; widening = true
            }; }

open StarCombinator
exception ParseError
let parse_exn (p: parser 'a) (source: string): ML 'a
  = if String.length source = 0
    then raise ParseError
    else match make p source with
    | Inl s -> s
    | Inr e -> print_string ("Parsing a stmt resulted in the following error:  " ^ e);
              print_newline ();
              raise ParseError

open ADom.Mem

type flag m = string & option Char.char & bool 
         & (string -> options m -> ML (options m)) & string
         
let flags #m {| has_default m |} {| mem_adom m |} (parser:parser m): list (flag m)
    = [// "disable-backward-iteration", Some 'd', false
      // , (let f _ o: ML _ = {o with asem = ({o.asem with use_backward_fixpoint = false})} in f)
      // , "Do not look for a fixpoint during backward propagation"
        "initial-memory", Some 'i', true,  (fun s o -> {o with initial_memory = parse_exn (parser <<*> eof) s})
      , "<value> should be a memory (i.e. 'a = [1,5], b = [4,6], c = [3,6], d=[2,9]')"
      ; "final-memory", Some 'f', true,  (fun s o -> {o with final_memory = Some (parse_exn (parser <<*> eof) s)})
      , "If specified, will check if the computed given memory is at least as precise as <value>"
      ; "disable-widening", Some 'd', false,  (fun s o -> {o with widening = false})
      , "Disable widening in loop iterations"
      ]

let rec make_space_n (n: int): string
  = if n <= 0 then "" else make_space_n (n - 1)^" "

let mk_pad_right (n: nat) (s: string)
  = make_space_n (n - String.length s)

let flag_explanations #m {| has_default m |} {| mem_adom m |} (parser:parser m) = 
  let m = List.Tot.fold_left (fun (x y:nat) -> max x y) (0<:nat) (List.Tot.map (fun (full,_,_,_,_) -> String.length full) (flags parser)) in
  String.concat "\n\n" (List.Tot.map (fun (full,abbr,f,_,e) -> 
    "  " ^ bold ("--" ^ full) ^ (mk_pad_right m full) ^ "   " ^ 
    ( match abbr with
    | None -> "  "
    | Some c -> String.string_of_list ['-';c])
    ^ (if f then "<value>" else "") ^ "\n    " ^ e
  ) (flags parser))

let satisfies_flag #m (f: flag m) (l: list string): (options m -> ML (options m)) * list string
  = let full, abbrev, arg, fn, _ = f in
    let full = "--" ^ full in
    let abbrev = match abbrev with | Some a -> Some (String.string_of_list ['-';a]) | None -> None in
    let nothing = id, l in
    let match_arg l =
      match arg, l with
      | true, hd::tl -> ( match String.list_of_string hd with
                      | '-'::_ -> nothing
                      | _     -> fn hd, tl )
      | false, _   -> fn "", l
      | _ -> nothing
    in
    match l with
    | hd::l -> if Some hd = abbrev || hd = full
             then match_arg l else nothing
    | [] -> nothing

let parse_argv_once #m {| has_default m |} {| mem_adom m |} (parser:parser m) (opts: options m) (l: list string)
  : ML (options m & list string)
  = List.fold_left (fun (o, l) flag -> let fn, l = satisfies_flag flag l in fn o, l) (opts, l) (flags parser)

let rec parse_argv #m {| has_default m |} {| mem_adom m |} (parser:parser m) ignore_if_not_matching opts l: ML (options m & list string)
  = let opts, l' = parse_argv_once parser opts l in
    if List.length l' < List.length l
    then parse_argv parser ignore_if_not_matching opts l' 
    else if ignore_if_not_matching && l' <> [] 
         then parse_argv parser ignore_if_not_matching opts (List.Tot.tail l') 
         else opts, l'

let dblquote = '"' // "

let space_separated_parser =
  let p1 = satisfy_char (fun c -> c <> ' ' && c <> '\'' && c <> dblquote) in
  let p2 = satisfy_char (fun c -> c <> '\'' && c <> dblquote) in
  sepBy ( (String.concat "") @<<
          many (   String.string_of_list
               @<< (((fun c -> [c]) @<< p1)
               <|> (exact_char '\'' <*>> many p2 <<*> exact_char '\'')
               <|> (exact_char dblquote <*>> many p2 <<*> exact_char dblquote))
               )
        ) space

let string_of_tup (f: 'a -> string): 'a&'a -> string
  = fun (a,b) -> "(" ^ f a ^ ", " ^ f b ^ ")"

// let options_parser =
//   let flag_parser (full, abbrev, fn)
//     : parser (options -> options)
//     = let pfull = () *<< exact_string ("--" ^ full) in
//       (function | Some _ -> fn | None -> id)
//       @<< maybe (match abbrev with
//       | Some d -> pfull <|> ((exact_char '-' <*>> () *<<exact_char d))
//       | None -> pfull)
//   in List.Tot.fold_left (fun opts f -> f opts) default_options @<< many (choice (List.Tot.map flag_parser flags))

open ADom
open PrettyPrint
let run_a #m {| has_default m |} {| mem_adom m |} {| prettyprintable m |} (parser:parser m) (opts: options m) (s: stmt) (m0: m) (expected_m1: option m)
  = print_string (header "Running the following program:\n");
    print_string (string_of_stmt s);
    if opts.widening then () else print_string "[widening in iteration is disabled]\n";
    print_string (header "\nInitial mem.:  ");
    print_string (print m0);
    print_string (header "\nComputed mem.: ");
    let m1: m = asem_stmt opts.widening s m0 in
    print_string (print m1);
    match expected_m1 with
    | Some em1 ->
      let result = m1 ⊑ em1 in
      let strcmem1 = print m1 in
      let strmem1 = print em1 in
      if result
      then print_string (green ("\n\nThe computed abstract memory respects the given invariant:\n  ") ^ strcmem1 ^ "\n ⊆ " ^ strmem1)
      else print_string ("\n\n" ^ fail ("The computed abstract memory is not contanined in the given invariant:") ^ "\n  " ^ strcmem1 ^ "\n ⊈ " ^ strmem1);
      result
    | None -> true

let usage #m {| has_default m |} {| mem_adom m |} {| prettyprintable m |} (parser:parser m) (name: string) = print_string (
    header 
    "Usage:     " ^ name ^ " <OPTION>* <PROGRAM>\n\n"
  // ^ "\n"
  ^ header 
    "<PROGRAM>  Path to a source file or if '-', read stdin\n\n"
  ^ header 
    "<OPTION>   Any combination of the following\n"
  ^ flag_explanations parser
  ); false


let string_of_tup_int (x, y) = string_of_int x ^ "  " ^ string_of_int y

let read_entire_file (path: string)
  = let f = match path with | "-" -> stdin | path -> IO.open_read_file path in
    let rec l (): ML string = try let ln = read_line f in
                                  if String.length ln = 0 && path = "-"
                                  then ln else ln ^ "\n" ^ l ()
                              with | _ -> ""
    in let r = l () in IO.close_read_file f; r

let stmt_annot_parser
  = let p = exact_string "//" <*>> 
            String.string_of_list @<< many (satisfy_char (fun c -> c <> '\n'))
            <<*> exact_char '\n' in
    many p <*> stmt_parser <<*> eof

let flatten_list = List.Tot.fold_left (@) []

let main' #m {| has_default m |} {| mem_adom m |} {| prettyprintable m |} (parser:parser m) (argv: list string)
  : ML _
  = print_string "COMPILATION_TIMESTAMP\n"; 
  try
  let parse_mem s: ML _ = if String.length s = 0 then def else parse_exn (parser <<*> eof) s in
  let name::argv = match argv with | [] -> ["./run"] | _  -> argv in
  let opts, argv = parse_argv parser false def argv in
  match argv with
  | ["--help"] -> usage parser name
  | [prog] -> 
      let comments, prog = parse_exn stmt_annot_parser (read_entire_file prog) in
      let comments: list string = List.Tot.filter (fun x -> x <> "") (flatten_list (List.map (parse_exn space_separated_parser) comments)) in
      let opts, _ = parse_argv parser true opts comments in
      run_a parser opts prog opts.initial_memory opts.final_memory
  | _ -> usage parser name
  with | ParseError -> false
       | e -> print_string "Unknown exception (some file was probably not found)";
             raise e;
             false


open WithBottom
open AMem.ADom
let run_simple (prog: string): ML bool
  = let comments, prog = parse_exn stmt_annot_parser prog in
    let comments: list string = List.Tot.filter (fun x -> x <> "") (flatten_list (List.map (parse_exn space_separated_parser) comments)) in
    let parser = parse_amem (Val @<< itv'_parser) in
    let opts, _ = parse_argv parser true def comments in
    run_a parser opts prog opts.initial_memory opts.final_memory

let main (argv: list string) 
  = main' (parse_amem (Val @<< itv'_parser)) argv


module PrettyPrint

open FStar.Tactics.Typeclasses
open FStar.String

class prettyprintable (a: Type u#n)
  = { print: a -> string
    }

instance int_pp: prettyprintable int = { print = string_of_int }
instance nat_pp: prettyprintable nat = { print = string_of_int }
instance bool_pp: prettyprintable bool = { print = string_of_bool }
instance char_pp: prettyprintable char = { print = (fun c -> string_of_list [c]) }
instance unit_pp: prettyprintable char = { print = (fun _ -> "()") }

open FStar.List.Tot

instance list_pp {| prettyprintable 'a |}: prettyprintable (list 'a)
  = { print = (fun l -> "[" ^ concat ";" (map print l) ^ "]" ) }
instance tuple2_pp {| prettyprintable 'a |} {| prettyprintable 'b |}: prettyprintable ('a*'b)
  = { print = (fun (a,b) -> "(" ^ print a ^ ", " ^ print b ^")" ) }
instance tuple3_pp {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |}: prettyprintable ('a*'b*'c)
  = { print = (fun (a,b,c) -> "(" ^ print a ^ ", " ^ print b ^ ", " ^ print c ^ ")" ) }
instance tuple4_pp {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |} {| prettyprintable 'd |}: prettyprintable ('a*'b*'c*'d)
  = { print = (fun (a,b,c,d) -> "(" ^ print a ^ ", " ^ print b ^ ", " ^ ", " ^ print c ^ print d ^")" ) }
instance tuple5_pp {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |} {| prettyprintable 'd |} {| prettyprintable 'e |}: prettyprintable ('a*'b*'c*'d*'e)
  = { print = (fun (a,b,c,d,e) -> "(" ^ print a ^ ", " ^ print b ^ ", " ^ ", " ^ print c ^ print d ^ ", " ^ print e ^")" ) }


open FStar.IO
class traceable (a: Type u#n)
  = { trace: string -> (i:a -> o:a{i == o}) }

instance pp_trace {| prettyprintable 'a |}: traceable 'a = {trace = (fun s v -> let _ = debug_print_string (s ^ print v) in v)}

private
let print_as_fun_call (s: string) args outcome = 
  debug_print_string (s ^ concat " " (map (fun x -> "("^x^")") args) ^ " => " ^ outcome ^ "\n")

instance fun1_trace {| prettyprintable 'a |} {| prettyprintable 'b |}: traceable ('a -> 'b)
  = { trace = (fun s f x -> let r = f x in
                       let _ = print_as_fun_call s [print x] (print r) in 
                       r
              )
    }
    
instance fun2_trace {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |}: traceable ('a -> 'b -> 'c)
  = { trace = (fun s f x y -> let r = f x y in
                         let _ = print_as_fun_call s [print x;print y] (print r) in 
                         r
              )
    }
    
instance fun3_trace {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |} {| prettyprintable 'd |}: traceable ('a -> 'b -> 'c -> 'd)
  = { trace = (fun s f x y z -> let r = f x y z in
                             let _ = print_as_fun_call s [print x;print y;print z] (print r) in 
                             r
              )
    }
    
instance fun4_trace {| prettyprintable 'a |} {| prettyprintable 'b |} {| prettyprintable 'c |} {| prettyprintable 'd |} {| prettyprintable 'e |}: traceable ('a -> 'b -> 'c -> 'd -> 'e)
  = { trace = (fun s f x y z a -> let r = f x y z a in
                       let _ = print_as_fun_call s [print x;print y;print z;print a] (print r) in 
                       r
              )
    }

let trace' {| traceable 'a |} (x: 'a) = trace "" x

// let lemma_equality (s: string) {| traceable 'a |} (x:'a) (): Lemma (x == trace s x) = ()

// module T = FStar.Tactics
// let lhs (): T.Tac T.term =
//     match T.cur_formula () with
//     | T.Comp (T.Eq _) lhs _ -> lhs
//     | _ -> T.fail "not an eq"

// unfold let trace_this msg = (fun _ -> 
//   let t = quote lemma_equality msg in
//   T.apply_lemma (T.mk_e_app t [lhs ()])
// )

// // let _ = fun n ->
// //   PrettyPrint.trace (Prims.op_Hat ""
// //         (Prims.op_Hat " (" (Prims.op_Hat (FStar.Tactics.Builtins.print n) ")")))
// //     (n + 3)

// let add_trace_call (msg: string) (t: T.term): T.Tac T.term = 
//   let args, body = T.collect_abs t in
//   let (^^) x y = T.mk_e_app (`(^)) [x;y] in
//   let args_str = fold_left (fun str arg -> str ^^ (`" (") ^^ T.mk_e_app (`print) [arg] ^^ (`")")) (`"") (T.map T.binder_to_term args) in
//   let t = mk_abs args (
//     T.mk_e_app (`trace) [args_str; body]
//   ) in
//   t

// [@@FStar.Tactics.preprocess_with (add_trace_call "backward_asem")]
// let f n = n + 3



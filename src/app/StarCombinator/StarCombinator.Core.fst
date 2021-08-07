module StarCombinator.Core

module LP = FStar.List.Pure.Base
module L = FStar.List.Tot.Base
module S = FStar.String

open StarCombinator.Helpers

private
let remove_dups (#a:eqtype) (l:list a) =
    let rec h l already: Tot (list a) (decreases l) = match l with
    | [] -> []
    | hd::tl -> if lst_contains hd already then h tl already else hd::(h tl (hd::already))
    in h l []

type map key value = list (key * list value)
let get (#tk:eqtype) #tv (map:map tk tv) (key: tk): list tv =
  let rec h l = match l with | [] -> [] | (hd, lvals)::tl -> (if hd = key then lvals else h tl) in
  h map

let set (#tk:eqtype) (#tv:eqtype) (map:map tk tv) (key: tk) (value: tv) =
  let rec h l = match l with
                | [] -> [(key, [value])]
                | (hd, lvals)::tl -> (if hd = key
                                    then ((hd, (if lst_contains value lvals then lvals else value::lvals))::tl)
                                    else ((hd, lvals)::(h tl))
                                    )
  //let rec h l = match l with | [] -> [] | (hd, lvals)::tl -> (hd, (if hd = key then value::lvals else lvals))::tl
  in h map

let merge (#tk:eqtype) (#tv:eqtype) (map0:map tk tv) (map1:map tk tv) =
  let rec h l = match l with | [] -> map0 | (k,vl)::tl -> let map2 = h tl in L.fold_left (fun m v -> set m k v) map2 vl
  in h map1

// a parserState whose position is exactly the length of the source is okay: it means that we're done
// maximum_position keeps track of the most advanced position any parser have reached yet
type parserState = {
    errors: map (nat * nat) string
  ; source: string
  ; maximum_position: n : nat{n <= String.length source}
  ; position: n : nat{n <= maximum_position}
  ; nest_level: nat
}

let (+++) (s1: parserState) (s2: parserState{s1.source = s2.source})
          (f: (a:nat) -> (b:nat) -> (r: nat {a = r \/ b = r}))
          = { position = f s1.position s2.position
            ; maximum_position = max s1.maximum_position s2.maximum_position
            ; errors = merge s1.errors s2.errors
            ; source = s1.source
            ; nest_level = s1.nest_level
            }


noeq
type continuation i o = | Continuation : (nat -> continuation i o) -> continuation i o
                        | ContinuationResult : (i ->  o) -> continuation i o

private
let lift_to_continuation #i #o (f: i -> o) = ContinuationResult f

private
let ask_n #i #o (n': nat) (f: (l: list nat {L.length l == n'}) -> continuation i o): continuation i o =
  let rec h (n: nat {n <> 0}) (acc: list nat {L.length acc == n' - n})
    = Continuation (
      fun r -> if n = 1
            then f (r::acc)
            else h (n - 1) (r::acc)
      )
  in if n' = 0 then f [] else h n' []

private
let lask_n n f = ask_n n (fun l -> f l |> lift_to_continuation)

private
let cmp_cont #i #o0 #o9 (f0: continuation i o0) (f3: continuation o0 o9) =
  let rec h (f0: continuation i o0)
      = Continuation (fun seed -> match f0 with
                     | Continuation f1 -> h (admitP (seed << seed); f1 seed)
                     | ContinuationResult f2 ->
                       let rec k (f3: continuation o0 o9) = (match f3 with
                         | Continuation f4 -> Continuation #i #o9 (fun seed -> (admitP (seed << seed); k (f4 seed)))
                         | ContinuationResult f5 -> ContinuationResult #i #o9 (f5 @@ f2)
                         ) in k f3
                     ) in h f0

let cmp_cont_par #a #i #j (f: continuation a i) (g: continuation a j): continuation a (i*j) =
  let rec h (f0: continuation a i) = match f0 with
                 | Continuation f1 -> Continuation (fun seed -> h (admit (); f1 seed))
                 | ContinuationResult fr ->
                   let h' (f1: continuation a j) = (match f1 with
                   | Continuation f2 -> Continuation (fun seed -> h (admit (); f2 seed))
                   | ContinuationResult fr' -> ContinuationResult (fun v -> (fr v, fr' v))
                   ) in h' g
  in h f

type parserDescription = {
    message: string
}

noeq
type parser a = {
    description: unit -> parserDescription
  ; random_generator: continuation unit string
  ; parser_fun: string -> s : parserState -> ((l : parserState{l.source == s.source}) * option a)
}

private
let rec mkIdent (n: nat) =
  if n = 0 then "" else "  " ^ mkIdent (n - 1)

let add_error s0 p0 p1 message = {s0 with errors = set s0.errors (p0, p1) message}

val add_error_same_source : s0: parserState -> p0: nat -> p1: nat -> m: string -> Lemma (s0.source = (add_error s0 p0 p1 m).source)
let add_error_same_source s0 p0 p1 m = ()

val p2fun (#a : Type) : p : parser a -> s : parserState -> ((t : parserState{t.source == s.source}) * option a)
let p2fun #a (p: parser a) x =
    let d = (p.description ()).message in
    //let t = mi_unsafe_now () in
    //let _ = mi_debug_print_string ("\n"^mkIdent x.nest_level^"Start "^d^" at "^(S.substring x.source x.position 1)) in
    let (s1, r) = p.parser_fun d x in
    //let t = mi_unsafe_now () - t in
    //let _ = mi_debug_print_string ("\n"^mkIdent x.nest_level^"End "^d^". Time(ms)= "^string_of_int t) in
    let s2 = {s1 with nest_level = s1.nest_level + 1} in
    let s3 = if None? r then add_error s2 x.position s2.position (p.description ()).message else s2 in
    (s3, r)

//let p2fun a = fun x -> let x = mi_debug_print_string "Start" a.parser_fun (a.description ()) x

let mktup2 a b = (a, b)

let fp #a #b (f: a -> b) (p:parser a): parser b
  = { description = p.description
    ; random_generator = p.random_generator
    ; parser_fun = fun sd s0 -> let s1, r = p.parser_fun sd s0 in s1, f <$> r
    }

let mk_d msg = fun _ -> {message = msg}
let cat_d a b = fun _ -> {message = (a ()).message ^ (b ()).message}

#set-options "--z3rlimit 80"

let mk_seq #a #b (parser1: parser a) (parser2: parser b): parser (a * b) = {
    description = (mk_d "sequence")//(fun _ -> "( " ^ parser2.description () ^ " . " ^ parser1.description () ^ " )")
  ; random_generator = cmp_cont_par parser1.random_generator parser2.random_generator `cmp_cont` lift_to_continuation (fun (a, b) -> a ^ "; " ^ b)
  ; parser_fun  = (let run sd (s0: parserState): (parserState*option (a * b)) = (
                     let (s1, r1) = p2fun parser1 s0 in
                     match r1 with
                     | None -> add_error s1 s0.position s1.position sd, None
                     | Some r1 ->
                       let (s2, r2) = p2fun parser2 s1 in
                       (let s3 = s1 +++ s2 <| (fun _ p2 -> p2) in (match r2 with
                       | None -> add_error s3 s0.position s2.position sd, None
                       | Some r2 -> s3, Some (r1, r2)
                       ))
                      // (s1 +++ s2) (fun _ p2 -> p2), mktup2 r1 <$> r2
                  ) in (admit (); run))
}

let flatten_option #a (p: parser (option a)) (msg: string): parser a = {
    description = (mk_d msg)
  ; random_generator = p.random_generator
  ; parser_fun  = (let run sd (s0: parserState): ((s1: parserState {s1.source == s0.source})*option a) = (
                     let s1, r1 = p2fun p s0 in
                     match r1 with
                     | Some None | None -> add_error s1 s0.position s1.position sd, None #a
                     | Some (Some r1) -> s1, Some r1
                  ) in run)
}

let choice_two #a #b (parser1: parser a) (parser2: parser b): parser (either a b) = {
    description = mk_d "or"//"( " ^ parser2.description () ^ " | " ^ parser1.description () ^ " )")
  ; random_generator = (
        ask_n 1 (fun [n] -> if n % 2 = 0
        then parser1.random_generator
        else parser2.random_generator))
  ; parser_fun  = (let run _ (s0: parserState): (parserState * option (either a b)) = (
                     let (s1, r1) = p2fun parser1 s0 in
                     match r1 with
                     | None -> if s1.position <> s0.position
                              then s0 +++ s1 <| (fun a b -> max a b), None
                              else let s2, r2 = p2fun parser2 s0 in
                                   // s1 +++ s2 <| (fun _ p2 -> p2), (Inr <$> r2)
                                   s2 +++ s1 <| (fun p2 _ -> p2), (Inr <$> r2)
                     | Some r1 -> s1, (Some <| Inl r1)
                  ) in (admit (); run))
}

let choice_two_same p1 p2 = fp (fun x -> match x with | Inl y -> y | Inr y -> y) <| choice_two p1 p2


let empty parser unit = {
    description = (mk_d "empty")
  ; random_generator = lift_to_continuation (fun _ -> "")
  ; parser_fun = fun _sd s0 -> s0, Some ()
}

let choice #a (lp: list (parser a) {~(lp == [])}): parser a = match lp with
                 | hd::lp -> L.fold_left (fun acc p -> choice_two_same acc p) hd lp


let maybe' #a (p: parser a): parser (option a) = {
    description = mk_d "?" `cat_d` p.description
  ; random_generator = (
        ask_n 1 (fun [n] -> if n % 2 = 0
        then p.random_generator
        else lift_to_continuation (fun _ -> "")))
  ; parser_fun  = fun _ s0 ->
                     let s1, r1 = p2fun p s0 in
                     match r1 with
                     | Some _ -> s1, Some r1
                     | None   -> s0, Some None
}


let maybe #a (p: parser a): parser (option a) = {
    description = mk_d "?" `cat_d` p.description
  ; random_generator = (
        ask_n 1 (fun [n] -> if n % 2 = 0
        then p.random_generator
        else lift_to_continuation (fun _ -> "")))
  ; parser_fun  = fun _ s0 ->
                     let s1, r1 = p2fun p s0 in s1, Some r1
}

let map_error #a (p: parser a) (msg: string): parser a = {
   description = mk_d msg
 ; random_generator = p.random_generator
 ; parser_fun = p.parser_fun
}

let delayMe #a (p: unit -> parser a): parser a
  = { description = (fun () -> (p ()).description ())
    ; random_generator = Continuation (fun _ -> (p ()).random_generator)
    ; parser_fun = fun sd st0 -> let x = p () in x.parser_fun sd st0
    }


// F* doesn't support precise smt inlining of recursive inner lets

let rec h #a (p: parser a) (n: nat)
        = if n = 0 then lift_to_continuation (fun _ -> "")
          else p.random_generator `cmp_cont_par` (h #a p (n-1)) `cmp_cont` lift_to_continuation (fun (x, l) -> x ^ l)

let rec run #a (p: parser a) (sd : string) (s0: parserState): (r:((l : parserState{l.source == s0.source}) * option (list a)) {Some? (snd r)}) = (
                     let s1, r1 = p2fun p s0 in
                     match r1 with
                     | None -> (s1, Some [])
                     | Some r1 -> let (s2, Some r2) = admitP (s1 << s0); run #a p sd s1 in (s2, Some <| r1::r2)
                  )


let many #a (p: parser a): parser (list a) = {
    description = (mk_d "[" `cat_d` p.description `cat_d` mk_d "]")
  ; random_generator = (
        ask_n 1 (fun [n] -> let n = n % 8 in
                         h #a p n))
  ; parser_fun  = (fun sd s0 -> run #a p sd s0 )
}

let many1 #a (p: parser a) = (fun (a, b) -> a::b) `fp` (p `mk_seq` many p)

let eof: (parser unit) = {
    description = (mk_d "EOF")
  ; random_generator = lift_to_continuation (fun _ -> "")
  ; parser_fun  = fun sd (s0: parserState) ->
                     if s0.position = S.length s0.source
                     then s0, Some ()
                     else add_error s0 s0.position s0.position sd, None
}

let notFollowedBy #a (p:parser a): parser unit = {
    description = p.description `cat_d` mk_d " was not expected (notFollowedBy)"
  ; random_generator = lift_to_continuation (fun _ -> " ") (* this is wrong *)
  ; parser_fun  = fun sd s0  ->
                  let s1, res = p2fun p s0 in
                  match res with
                  | None   -> s0, Some ()
                  | Some _ -> add_error s0 s0.position s1.position sd, None
}

(* TODO : figure out why <| makes the verifier mad *)
let lookAhead #a (p:parser a): parser a = {
    description = mk_d "lookAhead(" `cat_d` p.description `cat_d` mk_d ")"
  ; random_generator = lift_to_continuation (fun _ -> "")
  ; parser_fun  = fun sd s0 ->
                  let s1, res = p2fun p s0 in
                  match res with
                  | Some v -> s0, Some v
                  | None   -> (s0 +++ s1) (fun a b -> b), None
}

let ptry #a (p:parser a): parser a = {
    description = mk_d "try(" `cat_d` p.description `cat_d` mk_d ")"
  ; random_generator = p.random_generator
  ; parser_fun  = fun sd s0 ->
                  let s1, res = p2fun p s0 in
                  match res with
                  | Some v -> s1, Some v // when everything goes well, "ptry p == p"
                  | None   -> (s0 +++ s1) (fun a b -> a), None // in case of failure, we aknowledge the error, but place the cursor at s0.position (then no tokens were consumed)
}

let satisfy_char' (f: String.char -> bool) (g: nat -> String.char) =
  let d = "satisfy_char(some function)" in
  { description      = mk_d d
  ; random_generator = lask_n 1 (fun [x] -> fun () -> S.string_of_list [g x])
  ; parser_fun       = fun sd s0 -> if s0.position >= S.length s0.source
                                 then add_error s0 (max 0 (s0.position - 1)) s0.position "satisfy_char: hit end of line", None
                                 else (let ch = S.index s0.source s0.position in
                                       if f ch
                                       then let p = s0.position + 1 in
                                         {s0 with position = p; maximum_position = max p s0.maximum_position}, Some ch
                                       else add_error s0 s0.position (s0.position + 1) d, None
                                      )
  }

let satisfy_char (f: String.char -> bool) = satisfy_char' f (fun _ -> '?')

let exact_char ch = satisfy_char' (fun ch' -> ch = ch') (fun _ -> ch)
let neg_satisfy_char f = satisfy_char (fun ch -> not (f ch))

private
let get_errors_tup3 (errors: map (nat * nat) string): list (nat * nat * string) =
  let rec h errors = match errors with
    | [] -> []
    | ((p0, p1), msgs)::tl -> let rec i msgs = (match msgs with
              | [] -> []
              | msg::tl -> (p0, p1, msg)::i tl
              ) in i msgs @ h tl
  in h errors

let gt_errors ((p0, p1, _): (nat * nat * _)) ((p0', p1', _): (nat * nat * _)): bool = not (
  if      p1 > p1' then true
  else if p1 = p1' then p0 > p0'
  else                  false)

let sort_errors: list (nat * nat * string) -> list (nat * nat * string)
  = L.sortWith <| L.compare_of_bool gt_errors

private
let count_in_list (#a:eqtype) (x: a) (l: list a):nat = L.fold_left (fun (acc:nat) h -> acc + (if h = x then 0 else 1)) 0 l

private
let count_in_str ch (str: string) =
    let rec h (p:nat{p <= S.length str}) = if p = 0
                      then 0
                      else let p = p - 1 in
                           (if S.index str p = ch then 1 else 0) + h p
    in h <| S.length str

let replaceCharStr all ch str = S.concat "" <| L.map (fun c -> if c = ch then str else S.string_of_list [c]) (S.list_of_string all)

let identLines str ident = S.concat "" <| L.map (fun c -> if c = '\n' then "\n" ^ ident else S.string_of_list [c]) (S.list_of_string str)

let make p = fun (source: string) ->
  let s0 = { position = 0
           ; maximum_position = 0
           ; errors = []
           ; source = source
           ; nest_level = 0
           } in let (s1, res) = (p2fun p) s0 in
           match res with
           | Some res -> Inl res
           | None -> Inr (
             let l = sort_errors <| get_errors_tup3 s1.errors in
             let show ((p0, p1, msg):(nat*nat*string)): string =
               let src = s1.source in
               let err_len: nat = admit(); p1 - p0 in
               let err_len = if err_len = 0 then 1 else err_len in
               let s_before = S.sub src 0 p0 in
               let s_middle = S.sub src p0 err_len in
               let s_after  = S.sub src <| p0+err_len <| S.length src - p0 - err_len in
               let errStyle = underline @@ fail in
               let ident = "" in
               let line_num = count_in_str '\n' s_before in
               "\n" ^ ident ^ fail "Parser error " ^ " on line "^ (underline <| string_of_int line_num) ^ " [pos:"^string_of_int p0^"-"^string_of_int p1^"]:" ^
               "\n" ^ ident ^ identLines (s_before ^ errStyle s_middle ^ s_after) ident ^
               "\n" ^ ident ^ "Reason: " ^ msg

             in
             S.concat "\n" (L.map show l)
           )


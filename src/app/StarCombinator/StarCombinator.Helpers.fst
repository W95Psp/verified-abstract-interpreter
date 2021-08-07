module StarCombinator.Helpers

private
let prefix = '\x1b'

let (<$>) #ta #ra (f: ta -> ra) a: option ra = match a with | Some a -> Some (f a) | None -> None
let (<*>) #ta #ra (f: option (ta -> ra)) (a: option ta): option ra = match f with | Some f -> f <$> a | None -> None
let max x y = if x > y then x else y

let (@@) #a #b #c (f: b -> c) (g: a -> b) (v:a) = f (g v)

let ( |> ) (v:'a) (f: 'a -> 'b): 'b = f v
let ( <| ) (f: 'a -> 'b) (v:'a): 'b = f v

let rec lst_contains (#a:eqtype)  (x: a) (l: list a) = match l with
  | [] -> false | h::t -> x = h || lst_contains x t


let cstHEADER = "\x1b[95m"
let cstOKBLUE = "\x1b[94m"
let cstOKGREEN = "\x1b[92m"
let cstWARNING = "\x1b[93m"
let cstFAIL = "\x1b[91m"
let cstENDC = "\x1b[0m"
let cstBOLD = "\x1b[1m"
let cstUNDERLINE = "\x1b[4m"

let cstGREEN = "\x1b[32m"

let header str          = cstHEADER	^ str ^ cstENDC
let okblue str          = cstOKBLUE	^ str ^ cstENDC
let okgreen str         = cstOKGREEN	^ str ^ cstENDC
let green str           = cstGREEN	^ str ^ cstENDC
let warning str         = cstWARNING	^ str ^ cstENDC
let fail str            = cstFAIL	^ str ^ cstENDC
let bold str            = cstBOLD	^ str ^ cstENDC
let underline str       = cstUNDERLINE	^ str ^ cstENDC
let line str            = str ^ "\n"

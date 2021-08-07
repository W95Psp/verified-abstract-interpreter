module StarCombinator.Operators

open StarCombinator.Core

let (<*>) = mk_seq
let (<?>) = map_error
let (</>) = choice_two
let (<|>) = choice_two_same

let (<*>>) a b = fp (fun (_, b) -> b) (a <*> b)
let (<<*>) a b = fp (fun (a, _) -> a) (a <*> b)

let ( @<< ) = fp
let ( *<< ) cst = fp (fun _ -> cst)

module NumTC

//@hide
class num (a: Type) = { n_add: a->a->a; n_sub: a->a->a; n_mul: a->a->a;
          n_eq:  a->a->a; n_lt:  a->a->a; n_and:a->a->a; n_or: a->a->a }

//@hide
instance int_arith: num int = let h f x y = if f x y then 1 else 0 in
  { n_add=(+); n_sub=op_Subtraction; n_mul=Mul.op_Star; n_eq=h (=)
  ; n_and=h (fun x y -> x<>0 && y<>0); n_lt = h (<); n_or = h (fun x y -> x<>0 || y<>0)}

//@hide
let ( + ) {|c:num 'a|} #p #q ($x:'a{p x}) ($y:'a{q x y}): 'a = c.n_add x y
//@hide
let ( * ) {|c:num 'a|} #p #q ($x:'a{p x}) ($y:'a{q x y}): 'a = c.n_mul x y
//@hide
let op_Subtraction {|c:num 'a|} #p #q ($x:'a{p x}) ($y:'a{q x y}): 'a = c.n_sub x y


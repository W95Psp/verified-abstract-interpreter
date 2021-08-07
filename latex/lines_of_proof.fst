  = assert_norm(∀s0 s1 (m0 mf:mem). osem_stmt (Seq s0 s1) m0 mf
     == (exists(m1:mem). m1 ∈ osem_stmt s0 m0 /\ mf ∈ osem_stmt s1 m1));
    assert_norm(∀a b c (m0 mf:mem). osem_stmt (If c a b) m0 mf
     == (mf ∈ ( osem_stmt (Assume c `Seq` a) m0 
              ∪ osem_stmt (Assume (neg_expr c) `Seq` b) m0)));
///////
let top_lemma (i: adom 'a)
  : Lemma (forall (x: i.c). x ∈ i.gamma i.adom_lat.top)
          [SMTPat (i.gamma i.adom_lat.top)] = i.top_law ()
let bottom_lemma (i: adom 'a)
  : Lemma (forall (x: i.c). ~(x ∈ i.gamma i.adom_lat.bottom))
          [SMTPat (i.gamma i.adom_lat.bottom)]
  = i.bot_law ()
let meet_lemma (i: adom 'a) (x y: 'a)
  : Lemma ((i.gamma x ∩ i.gamma y) ⊆ i.gamma (i.adom_lat.meet x y))
          [SMTPat (i.adom_lat.meet x y)]
  = meet_law x y
let join_lemma (i: adom 'a) (x y: 'a)
  : Lemma ((i.gamma x ∪ i.gamma y) ⊆ i.gamma (i.adom_lat.join x y))
          [SMTPat (i.adom_lat.join x y)]
  = let r = i.adom_lat.join x y in assert (gamma x ⊆ gamma r /\ gamma y ⊆ gamma r)
///////
assert_norm (forall (m: mem) (v: int_m). v ∈ osem_expr m e
        <==> (exists (x y:int_m). x ∈ osem_expr m ex /\ y ∈ osem_expr m ey
                         /\ v == concrete_binop op x y));

  = assert ((a-b) ⊆ (a+set_inverse b)) by (  compute ();
      let _= forall_intro () in let p0 = implies_intro () in
      let witX,p1 = elim_exists (binder_to_term p0) in
      let witY,p1 = elim_exists (binder_to_term p1) in
      let y: int = unquote (binder_to_term witY) in
      witness witX; witness (quote (-y)))
///////
let lemma_min (a b c d: int) (x: int{a<=x /\ x<=b}) (y: int{c<=y /\ y<=d})
  : Lemma (x*y>=a*c \/ x*y>=a*d \/ x*y>=b*c \/ x*y>=b*d) = ()
let lemma_mul (a b c d x y: int)
  : Lemma (requires in_btw x a b /\ in_btw y c d)
    (ensures x*y >= (a*c) `min` (a*d) `min` (b*c) `min` (b*d)
           /\ x*y <= (a*c) `max` (a*d) `max` (b*c) `max` (b*d))
    [SMTPat (x*y); SMTPat (a*c); SMTPat (b * d)]
  = lemma_min a b c d x y; lemma_min (-b) (-a) c d (-x) y
//////
    in assert_norm (trans o ==> trans f);





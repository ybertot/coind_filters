 
Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.
 
Section str_def.

Variable A : Set.

CoInductive str : Set :=
  SCons: A -> str ->  str .
 
Definition hd (s : str) : A :=
   match s with SCons x s' => x end.
 
Definition tl (s : str) : str :=
   match s with SCons x s' => s' end.
 
Definition str_decompose (s : str) : str :=
   match s with SCons x s' => SCons x s' end.
 
Theorem st_dec_eq: forall (s : str),  s = str_decompose s.
intros s; case s; auto.
Qed.
 
Section def_filter.
Variables (P : A ->  Prop) (P_dec : forall x,  ({ P x }) + ({ ~ P x })).
 
Inductive eventually : str ->  Prop :=
  ev_b: forall x s, P x ->  eventually (SCons x s)
 | ev_r: forall x s, eventually s ->  eventually (SCons x s) .
 
CoInductive F_infinite : str ->  Prop :=
  al_cons:
    forall x s,
    eventually (SCons x s) -> F_infinite s ->  F_infinite (SCons x s) .
 
Definition eventually_inv:
 forall (s : str),
 eventually s -> forall x s', s = SCons x s' -> ~ P x ->  eventually s'.
intros s h; case h.
intros x s0 H x0 s' H0 H1; elim H1; injection H0; intros; subst x0; auto.
intros x s0 H x0 s' H0 H1; injection H0; intros; subst s'; assumption.
Defined.
 
Fixpoint pre_filter_i (s : str) (h : eventually s) {struct h} : A :=
 match s as b return s = b ->  A with
    SCons x s' =>
      fun heq =>
         match P_dec x with
           left _ => x
          | right hn => pre_filter_i s' (eventually_inv s h x s' heq hn)
         end
 end (refl_equal s).
 
Theorem next_always_hyp: forall x s', F_infinite (SCons x s') ->  F_infinite s'.
intros x s' H; change (F_infinite (tl (SCons x s'))); case H; intros; assumption.
Qed.
 
Theorem always_eventually: forall s', F_infinite s' ->  eventually s'.
intros s' H; case H; intros; assumption.
Qed.
 
Definition next_always_sig (x : A) (s' : str) (h : F_infinite (SCons x s')) :
  {s' : str | F_infinite s'} :=
   exist (fun s' => F_infinite s') s' (next_always_hyp x s' h).
 

Fixpoint filter_i (s : str) (h : eventually s) {struct h} :
 F_infinite s ->  ({n : A | P n}) * ({s' : str | F_infinite s'}) :=
 match s as b
 return
 s = b -> F_infinite b ->  ({n : A | P n}) * ({s' : str | F_infinite s'}) with
    SCons x s' =>
      fun heq =>
         match P_dec x with
           left hp =>
             fun halways =>
             (exist (fun n => P n) x hp, next_always_sig x s' halways)
          | right hn =>
              fun halways =>
              filter_i
               s' (eventually_inv s h x s' heq hn)
               (next_always_hyp x s' halways)
         end
 end (refl_equal s).

   
CoFixpoint filter (s : str) (h : F_infinite s): str :=
   let (a, b) := filter_i s (always_eventually s h) h in
   let (n, hn) := a in let (s', hs') := b in SCons n (filter s' hs').
 
CoInductive always : str ->  Prop :=
  as_cons: forall x s', P x -> always s' ->  always (SCons x s') .
 
Theorem filter_always:
 forall (s : str) (h : F_infinite s),  always (filter s h).
cofix.
intros s h; rewrite (st_dec_eq (filter s h)).
simpl; case (filter_i s (always_eventually s h) h); intros [n hn] [s' hs'].
apply as_cons.
assumption.
apply filter_always.
Qed.
 
CoInductive connected (R : A -> A ->  Prop) : A -> str ->  Prop :=
  connected_cons:
    forall k x s, R k x -> connected R x s ->  connected R k (SCons x s) .
 
Scheme
eventually_ind2 := Induction for eventually Sort Prop.
 
Theorem filter_i_connected:
 forall (R1 R2 : A -> A ->  Prop),
 (forall x y z, R1 x y -> ~ P y -> R2 y z ->  R2 x z) ->
 (forall x y, P y -> R1 x y ->  R2 x y) ->
 forall s (hev : eventually s) (h : F_infinite s) x y hy s' hs',
 filter_i s hev h =
 (exist (fun x => P x) y hy, exist (fun s => F_infinite s) s' hs') ->
 connected R1 x s ->  R2 x y /\ connected R1 y s'.
intros R1 R2 Rt Rs.
intros s hev; elim hev  using eventually_ind2; clear hev s.
intros y s Hpy hf x y' hy' s' hs'.
simpl.
case (P_dec y).
unfold next_always_sig; intros HPy_2 Heq; injection Heq; intros H1 H2 Hc.
subst y s; inversion Hc; auto.
intros b; elim b; trivial.
intros y s hev hind hf x z hz s' hs'.
simpl.
case (P_dec y).
unfold next_always_sig; intros Hpy Heq; injection Heq; intros H1 H2 Hc.
subst y s; inversion Hc; auto.
intros Hrejy Heq Hc.
inversion Hc.
assert (Hinterm: R2 y z /\ connected R1 z s').
apply hind with ( 1 := Heq ); trivial.
split.
apply Rt with y; auto.
intuition.
intuition.
Qed.
 
Theorem filter_connected:
 forall (R1 R2 : A -> A ->  Prop),
 (forall x y z, R1 x y -> ~ P y -> R2 y z ->  R2 x z) ->
 (forall x y, P y -> R1 x y ->  R2 x y) ->
 forall s (h : F_infinite s) x, connected R1 x s ->  connected R2 x (filter s h).
intros R1 R2 Rs Rt.
cofix.
intros s Hf; case Hf; clear Hf s.
intros y s hev hf x Hc;
 rewrite (st_dec_eq (filter (SCons y s) (al_cons y s hev hf))); simpl.
caseEq (filter_i
         (SCons y s) (always_eventually (SCons y s) (al_cons y s hev hf))
         (al_cons y s hev hf)).
intros [z hz] [s' hs'] Heq.
elim filter_i_connected with ( R1 := R1 ) ( R2 := R2 ) ( 3 := Heq ) ( x := x );
 trivial.
intros HR2xz Hczs'.
constructor; trivial.
apply filter_connected; trivial.
Qed.
 
End def_filter.
 
Section filter_keep_sect.

Theorem filter_i_keep:
 forall (P Q : A ->  Prop) (P_dec : forall x,  ({ P x }) + ({ ~ P x }))
        (s : str) (h : eventually P s) (ha : F_infinite P s),
 always Q s ->
 forall x hx s' hs',
 filter_i P P_dec s h ha =
 (exist (fun n => P n) x hx, exist (fun s => F_infinite P s) s' hs') ->
  Q x /\ always Q s'.
intros P Q P_dec s h; elim h  using eventually_ind2.
simpl.
intros x s0 p ha hq x' hp s' hs'; elim (P_dec x).
simpl; intros hpx Heq; injection Heq; intros; subst x' s'; inversion hq; auto.
intros b; elim b; assumption.
simpl; intros x s0 he hind hf hq x' hx' s' hs'; elim (P_dec x).
simpl; intros hpx Heq; injection Heq; intros; subst x' s'; inversion hq; auto.
intros hrejx heq; apply hind with ( 2 := heq ).
inversion hq; auto.
Qed.
 
Theorem filter_keep:
 forall (P Q : A ->  Prop) (P_dec : forall x,  ({ P x }) + ({ ~ P x }))
        (s : str) (h : F_infinite P s),
 always Q s ->  always Q (filter P P_dec s h).
intros P Q P_dec; cofix.
intros s h hq.
rewrite (st_dec_eq (filter P P_dec s h)).
simpl.
caseEq (filter_i P P_dec s (always_eventually P s h) h).
intros [x hx] [s' hs'] Heq.
assert (Q x /\ always Q s').
apply filter_i_keep with ( Q := Q ) ( 2 := Heq ).
exact hq.
apply as_cons.
intuition.
apply filter_keep.
intuition.
Qed.

End filter_keep_sect.

End str_def.
Implicit Arguments SCons [A].
Implicit Arguments hd [A].
Implicit Arguments tl [A].
Implicit Arguments connected [A].
Implicit Arguments filter [A].
Implicit Arguments F_infinite [A].
Implicit Arguments st_dec_eq [A].
Implicit Arguments always [A].
Implicit Arguments eventually [A].

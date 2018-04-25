Require Export Omega.
Require Export ArithRing.
Require Export sieve_arith_complements.
Require Export List.
Require Export filter.
 
Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.
 
Definition step_all (P:nat->Prop) (x y:nat) :=
   x < y /\ (forall k, x < k < y -> not(P k)) /\ P y.

Definition step_partial_prime m :=
   step_all (partial_prime m).
 
Theorem partial_primes_to_F_infinite:
 forall m,
 1 < m ->
 forall k s, connected (step_partial_prime m) k s ->  F_infinite (not_mult m) s.
intros m H1ltm.
cofix.
intros k s; case s; intros n s' Hpprs; apply al_cons.
2:apply (partial_primes_to_F_infinite n); inversion Hpprs; assumption.
destruct (infinite_primes (n + (m + 1))) as [x [hle hpr]].
cut (n <= x).
generalize s' k Hpprs; clear partial_primes_to_F_infinite Hpprs k s' s.
rewrite <- (minus_minus n x).
2:omega.
elim (x - n)  using (well_founded_ind Wf_nat.lt_wf).
intros d Hind s' k Hpprs _; destruct (mult_dec m (x - d)) as [Hnm|Hm].
apply ev_b; trivial.
inversion Hpprs; apply ev_r; destruct s' as [n1 s'].
assert (Hdpos: 0 < d).
apply pre_prime_multiple_diff with m x0 x; trivial; omega.
assert (hc: connected (step_partial_prime m) (x - d) (SCons n1 s')); trivial.
inversion hc.
assert (hspp: step_partial_prime m (x - d) n1); trivial.
destruct hspp as [hlt [hn hp]].
assert (Hn1lex: n1 <= x).
elim (le_or_lt n1 x); trivial.
intros Hlt; elim (hn x).
apply simpl_int_prop with m n; trivial.
intros p Hint; apply hpr.
apply simpl_int_prop2 with m n; trivial.
rewrite <- (minus_minus n1 x); trivial.
apply Hind with (x - d).
apply simpl_int_prop3 with m n; trivial.
rewrite minus_minus; trivial.
apply simpl_int_prop4; trivial.
omega.
Qed.
 
Theorem inv1:
 forall (m x y z : nat),
 1 < m ->
 step_partial_prime m x y ->
 ~ not_mult m y -> step_partial_prime (S m) y z ->  step_partial_prime (S m) x z.
intros m x y z hltm [hlt [hn hp]] HP [hlt' [hn' hp']].
split.
apply lt_trans with y; trivial.
split; trivial.
intros k Hint.
elim (le_or_lt k y).
intros hle; elim (le_lt_or_eq k y hle).
intros hlt'' hprk; apply (hn k).
omega.
apply partial_prime_le with ( 2 := hprk ); auto with arith.
intros heq hprk; subst y; elim HP.
apply hprk; trivial.
omega.
intros hlt''; apply hn'; omega.
Qed.
 
Theorem inv2:
 forall (m x y : nat),
 1 < m ->
 not_mult m y -> step_partial_prime m x y ->  step_partial_prime (S m) x y.
intros m x y hltm HP [hlt [hn hp]].
split; trivial.
split.
intros k Hint Hprk.
apply (hn k); trivial.
apply partial_prime_le with (S m); trivial; omega.
apply partial_prime_step; trivial.
Qed.
 
Theorem connect_invariant:
 forall m,
 1 < m ->
 forall s k (Hf : F_infinite (not_mult m) s),
 connected (step_partial_prime m) k s ->
  connected (step_partial_prime (S m)) k (filter (not_mult m) (mult_dec m) s Hf).
Proof.
intros; apply filter_connected with ( R1 := step_partial_prime m ).
intros x y z; apply (inv1 m); trivial.
intros x y; apply (inv2 m); trivial.
trivial.
Qed.
 
Theorem connect_partial_prime_next:
 forall m m',
 m <= m' ->
 (forall p, ( m <= p < m' ) ->  ~ pre_prime p) ->
 forall x s,
 connected (step_partial_prime m) x s ->  connected (step_partial_prime m') x s.
intros m m' hltm hnpr; cofix.
intros x s Hc; inversion Hc.
destruct H as [hlt [hn hp]].
constructor.
split; trivial.
split.
intros k' Hint' hprk'; apply (hn k'); trivial.
apply partial_prime_le with m'; trivial.
apply partial_prime_next with m; trivial.
apply connect_partial_prime_next; trivial.
Qed.
CoFixpoint nums (n : nat): str nat :=
   SCons n (nums (n + 1)).
 
Theorem pprs2:
 forall k, 2 <= k ->  connected (step_partial_prime 2) k (nums (k + 1)).
Proof.
 cofix.
 intros k; rewrite (st_dec_eq (nums (k + 1))).
 simpl.
 intros Hle; apply connected_cons.
 split.
 omega.
 split.
 intros p Hint; assert False; [omega | elim H].
 intros p Hint; assert False; [omega | elim H].
 apply pprs2.
 omega.
Qed.
 
Theorem pre_prime_connect_partial_prime:
 forall m s, connected (step_partial_prime (S m)) m s ->  pre_prime (hd s).
intros m s Hc.
inversion Hc.
unfold pre_prime.
assert (hspp: step_partial_prime (S m) m x); trivial.
destruct hspp as [hlt [hn hp]].
simpl.
apply partial_prime_next with (S m); trivial.
intros p Hint Hprp; elim (hn p).
omega.
apply partial_prime_le with p.
omega.
exact Hprp.
Qed.
 
Definition start_partial_primes s :=
   1 < hd s /\ connected (step_partial_prime (hd s)) (hd s) (tl s).
 
Theorem start_partial_primes_invariant:
 forall p rest (Ha : F_infinite (not_mult p) rest),
 1 < p ->
 connected (step_partial_prime p) p rest ->
  start_partial_primes (filter (not_mult p) (mult_dec p) rest Ha).
intros p rest Ha Hm Hpprs.
assert (Hc'':
 connected
  (step_partial_prime (S p)) p (filter (not_mult p) (mult_dec p) rest Ha)).
apply connect_invariant; trivial.
inversion Hc''.
simpl; assert (hspp: step_partial_prime (S p) p x); trivial.
destruct hspp as [hlt [hn hp]].
assert (Hc': connected (step_partial_prime x) p (SCons x s)).
apply connect_partial_prime_next with ( m := S p ); trivial.
intros k' Hint' Hprk; apply (hn k'); trivial.
apply partial_prime_le with k'; trivial.
omega.
rewrite H; trivial.
split.
simpl; omega.
simpl; inversion Hc'; trivial.
Qed.

CoFixpoint sieve s  : start_partial_primes s ->  str nat :=
   match s return start_partial_primes s ->  str nat with
      SCons p rest =>
        fun H =>
        let (Hm, Hpprs) := H in
        let Ha := partial_primes_to_F_infinite p Hm p rest Hpprs in
          SCons
           p
           (sieve
             (filter (not_mult p) (mult_dec p) rest Ha)
             (start_partial_primes_invariant p rest Ha Hm Hpprs))
   end.
 
Definition step_prime x y :=
   x < y /\ ((forall k, ( x < k < y ) ->  ~ pre_prime k) /\ pre_prime y).
 
Theorem sieve_primes:
 forall s (Hs : start_partial_primes s) m,
 m < hd s ->
 (forall p, ( m < p < hd s ) ->  ~ pre_prime p) ->
 pre_prime (hd s) ->  connected step_prime m (sieve s Hs).
cofix.
intros [x s] [Hk H] m Hmk Hnp Hpr.
rewrite (st_dec_eq (sieve (SCons x s) (conj Hk H))).
simpl; fold sieve.
apply connected_cons.
split; [trivial | split; trivial].
simpl in H |-.
assert (Hc:
 connected
  (step_partial_prime (S x)) x
  (filter (not_mult x) (mult_dec x) s (partial_primes_to_F_infinite x Hk x s H))).
apply connect_invariant; trivial.
inversion Hc.
assert (hspp: step_partial_prime (S x) x x0); trivial.
destruct hspp as [hlt [hn hp]].
apply sieve_primes.
rewrite <- H0; simpl; trivial.
rewrite <- H0; simpl.
intros p Hint Hprp.
elim (hn p).
exact Hint.
apply partial_prime_le with p.
omega.
exact Hprp.
apply pre_prime_connect_partial_prime with x; trivial.
Qed.
 
Definition primes := (sieve (nums 2) (conj (lt_n_Sn 1)(pprs2 2 (le_n 2)))).

Theorem pre_primes: connected step_prime 1 primes.
unfold primes; apply sieve_primes.
simpl; omega.
simpl; unfold not; intros; omega.
exact pre_prime2.
Qed.

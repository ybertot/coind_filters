Require Export Omega.
Require Export ZArithRing.
Require Export ZArith.
Require Export filter.
Require Export sieve_arith_complements2.
Require Export List.
Open Scope Z_scope.

Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.
 
Definition step_all (P:Z->Prop) (x y:Z) :=
   x < y /\ (forall k, x < k < y -> not(P k)) /\ P y.

Definition step_partial_prime m :=
   step_all (partial_prime m).
 
Theorem partial_primes_to_F_infinite:
 forall m,
 1 < m ->
 forall k s, 1 < k -> connected (step_partial_prime m) k s ->
  F_infinite (not_mult m) s.
intros m H1ltm.
cofix.
intros k s; case s; intros n s' Hkpos Hpprs; apply al_cons.
2:apply (partial_primes_to_F_infinite n); inversion Hpprs; try assumption.
destruct (infinite_primes (n + (m + 1))) as [x [hle hpr]].
assert (Hnltx:1<n<=x).
inversion_clear Hpprs.
unfold step_partial_prime, step_all in H.
omega.
cut (1 < n <= x);[idtac|assumption].
generalize s' k Hkpos Hpprs;
 clear partial_primes_to_F_infinite Hpprs Hkpos k s' s.
replace n with (x - (x -n));[idtac|ring].
elim (x - n)  using (well_founded_ind (Zwf_well_founded 0)).
intros d Hind s' k Hkpos Hpprs Hdpos; destruct (fun h => mult_dec m h (x - d)) as [Hnm|Hm].
omega.
apply ev_b; trivial.
inversion Hpprs; apply ev_r; destruct s' as [n1 s'].
assert (Hdpos': 0 < d).
apply pre_prime_multiple_diff with m x0 x; trivial.
assert (hc: connected (step_partial_prime m) (x - d) (SCons n1 s')); trivial.
inversion hc.
assert (hspp: step_partial_prime m (x - d) n1); trivial.
destruct hspp as [hlt [hn hp]].
assert (Hn1lex: n1 <= x).
elim (Zle_or_lt n1 x); trivial.
intros Hlt; elim (hn x).
split.
case (Z_eq_dec d 0).
intros Hq; elim Hm;rewrite Hq.
replace (x-0) with x;[idtac|ring];apply hpr.
intros; omega.
intros; omega.
auto.
intros p Hint; apply hpr.
omega.
omega.
omega.
inversion H3.
elim H7.
intros.
assert (0 < n1 <= x).
split.
omega.
elim (Zle_or_lt n1 x);trivial.
intros Hxltn1.
elim H10; intros H11 _; elim (H11 x).
omega.
apply partial_prime_le with x.
omega.
exact hpr.
replace n1 with (x - (x - n1));[idtac | ring].
apply Hind with (x - d).
split;omega.
replace (x - ( x - n1)) with n1;[trivial|ring].
omega.
replace (x-(x-n1)) with n1;[assumption|ring].
omega.
destruct H2 as [H4 _];omega.
Qed.
 
Theorem inv1:
 forall (m x y z : Z),
 1 < m ->
 step_partial_prime m x y ->
 ~ not_mult m y -> step_partial_prime (m + 1) y z ->  step_partial_prime (m + 1) x z.
intros m x y z hltm [hlt [hn hp]] HP [hlt' [hn' hp']].
split.
omega.
split;trivial.
intros k Hint.
elim (Zle_or_lt k y).
intros hle; elim (Zle_lt_or_eq k y hle).
intros hlt'' hprk; apply (hn k).
omega.
apply partial_prime_le with ( 2 := hprk ); try omega.
intros heq hprk; subst y; elim HP.
apply hprk; trivial.
omega.
intros hlt''; apply hn'; omega.
Qed.
 
Theorem inv2:
 forall (m x y : Z),
 1 < m ->
 not_mult m y -> step_partial_prime m x y ->  step_partial_prime (m + 1) x y.
intros m x y hltm HP [hlt [hn hp]].
split; trivial.
split.
intros k Hint Hprk.
apply (hn k); trivial.
apply partial_prime_le with (m + 1); trivial; omega.
apply partial_prime_step; trivial.
Qed.
 
Lemma lt1_gt0 : forall m, 1 < m -> m > 0.
intros; omega.
Qed.

Theorem connect_invariant:
 forall m
 (h1ltm:1 < m),
 forall s k (Hf : F_infinite (not_mult m) s),
 connected (step_partial_prime m) k s ->
  connected (step_partial_prime (m + 1)) k (filter (not_mult m) 
                (mult_dec m (lt1_gt0 _ h1ltm)) s Hf).
Proof.
intros; apply filter_connected with ( R1 := step_partial_prime m ).
intros x y z; apply (inv1 m); trivial.
intros x y; apply (inv2 m); trivial.
trivial.
Qed.
 
Theorem connect_partial_prime_next:
 forall m m',
 0 <= m <= m' ->
 (forall p, ( m <= p < m' ) ->  ~ pre_prime p) ->
 forall x s,
 connected (step_partial_prime m) x s ->
 connected (step_partial_prime m') x s.
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

CoFixpoint nums (n : Z) : str Z :=
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
 forall m s, 0 <= m ->
  connected (step_partial_prime (m + 1)) m s ->  pre_prime (hd s).
intros m s Hmpos Hc.
inversion Hc.
unfold pre_prime.
assert (hspp: step_partial_prime (m + 1) m x); trivial.
destruct hspp as [hlt [hn hp]].
simpl.
apply partial_prime_next with (m + 1); trivial.
intros p Hint Hprp; elim (hn p).
omega.
apply partial_prime_le with p.
omega.
exact Hprp.
Qed.
 
Definition start_partial_primes s :=
   1 < hd s /\ connected (step_partial_prime (hd s)) (hd s) (tl s).
 
Theorem start_partial_primes_invariant:
 forall p rest (Ha : F_infinite (not_mult p) rest)
 (h1ltp: 1 < p),
 connected (step_partial_prime p) p rest ->
  start_partial_primes (filter (not_mult p) 
  (mult_dec p (lt1_gt0 _ h1ltp)) rest Ha).
intros p rest Ha h1ltp Hpprs.
assert (Hc'':
 connected
  (step_partial_prime (p + 1)) p
     (filter (not_mult p)
           (mult_dec p (lt1_gt0 _ h1ltp)) rest Ha)).
apply connect_invariant; trivial.
inversion Hc''.
simpl; assert (hspp: step_partial_prime (p + 1) p x); trivial.
destruct hspp as [hlt [hn hp]].
assert (Hc': connected (step_partial_prime x) p (SCons x s)).
apply connect_partial_prime_next with ( m := (p+1) ); trivial.
omega.
intros k' Hint' Hprk; apply (hn k'); trivial.
omega.
apply partial_prime_le with k'; trivial.
omega.
rewrite H; trivial.
split.
simpl; omega.
simpl; inversion Hc'; trivial.
Qed.

CoFixpoint sieve s  : start_partial_primes s ->  str Z :=
   match s return start_partial_primes s ->  str Z with
      SCons p rest =>
        fun H : start_partial_primes (SCons p rest) =>
        let (Hm, Hpprs) := H in
        let Ha := partial_primes_to_F_infinite p Hm p rest Hm Hpprs in
          SCons
           p
           (sieve
             (filter (not_mult p)
                (mult_dec p (lt1_gt0 _ Hm)) rest Ha)
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
  (step_partial_prime (x + 1)) x
  (filter (not_mult x) 
    (mult_dec x (lt1_gt0 _ Hk)) s
    (partial_primes_to_F_infinite x Hk x s Hk H))).
apply connect_invariant; trivial.
inversion Hc.
assert (hspp: step_partial_prime (x + 1) x x0); trivial.
destruct hspp as [hlt [hn hp]].
apply sieve_primes.
rewrite <- H0; simpl; trivial.
rewrite <- H0; simpl.
intros p Hint Hprp.
elim (hn p).
exact Hint.
apply partial_prime_le with p.
simpl in Hk; omega.
exact Hprp.
apply pre_prime_connect_partial_prime with x; trivial.
simpl in Hk; omega.
Qed.
 
Lemma lt12 : 1 < 2.
omega.
Qed.

Lemma le22 : 2 <= 2.
omega.
Qed.

Definition primes := (sieve (nums 2) (conj lt12 (pprs2 2 le22))).

Theorem pre_primes: connected step_prime 1 primes.
unfold primes; apply sieve_primes.
simpl; omega.
simpl; unfold not; intros; omega.
exact pre_prime2.
Qed.

Theorem step_all_always : forall P k s, connected (step_all P) k s ->
  always P s.
cofix.
intros P k s H; case H; clear k s H; intros k v s [H1 [H2 H3]] H4.
apply as_cons.
trivial.
apply (step_all_always P v);trivial.
Qed.

Theorem step_all_present: forall P k s, connected (step_all P) k s ->
  forall x, k < x -> P x -> eventually (fun y => y = x) s.
intros P k s Hc x;generalize s Hc; clear s Hc;
 replace k with (x - (x-k));[idtac|ring].
elim (x-k) using (well_founded_ind (Zwf_well_founded 0)).
clear k.
intros d Hrec s Hc; generalize (refl_equal (x-d)); 
pattern (x-d) at -1, s; case Hc.
clear Hc s.
intros k v s Hsp Hc Heq Hlt Hpr.
subst k.
case (Z_eq_dec x v).
intros Heqxv; subst v.
apply ev_b.
auto.
intros Hneq.
assert (Hvltx : v < x).
destruct Hsp as [H1 [H2 H3]].
destruct (Zle_or_lt x v) as [Hxlev | Hxltv];trivial.
assert (Hxltv : x < v).
omega.
elim (H2 x);auto;omega.
apply ev_r.
apply (Hrec (x-v)).
destruct Hsp as [H1 _].
unfold Zwf; omega.
replace (x-(x-v)) with v.
auto.
ring.
omega.
auto.
Qed.
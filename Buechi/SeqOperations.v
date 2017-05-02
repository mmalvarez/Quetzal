Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import BA.External.
Require Import BA.FinTypes.
Require Import BasicDefs.
Require Import Seqs.
Require Import StrictlyMonotoneSeqs.
Require Import Utils.

(** * Operations on Sequences *)

(** ** Finding the next position at which a predicate holds in a sequence *)
Section FindNextPosition.
  (** Given a sequence w on a type X, a decidable predicate on X, a number n  and a proof that P holds at some m, [n <= m],
      we can construct the smallest greater equal n, at which P holds. We use recursion trees. *)

  Context{X: Type}.
  Variable P : X -> Prop.
  Variable decP: forall a, dec (P a).
  Variable w: Seq X.

  Inductive rec_find_next_position : nat -> nat -> Type :=
       | found_pos n m : (P (w n)) -> m >= n -> rec_find_next_position  n m
       | pos_step n m : rec_find_next_position (S n) m -> ~(P (w n)) -> rec_find_next_position n m.

  Lemma there_is_rec_find_next_position n m: P (w m) -> rec_find_next_position (m-n) m.
  Proof.
   intros Fm. induction n.
   - rewrite_eq (m-0 = m).  apply found_pos; oauto. 
   - decide (P (w (m - (S n)))).
     + apply found_pos; oauto.
     + decide (n < m).
       * apply pos_step.
         -- now rewrite_eq (S (m - S n) = m - n).
         -- assumption.
       * now rewrite_eq (m - S n = m - n).
  Qed.

  Fixpoint find_next_position n m (T: rec_find_next_position  n m):= match T with
     | found_pos _ _ => n
     | pos_step  T' _ => find_next_position T'
  end.

  Lemma find_next_position_correct n m (T:rec_find_next_position  n m):
        let k := find_next_position T in
         n <= k <= m /\ P (w k) /\ forall m, n <=m <k ->  ~(P (w m)).
  Proof.
    intros k. subst k. (split;split); try (induction T; simpl; oauto); intros k L.
    - exfalso. omega. 
    - decide (n = k) as [H|H].
      + now rewrite <-H.
      + apply IHT. omega.
  Qed.

  Lemma can_find_next_position n m : n <= m -> P (w m) -> (Sigma k, n <=k<=m /\ (P (w k)) /\ forall m', n <= m' < k -> ~(P (w m'))).
  Proof.
    intros L F.
    pose (T := (there_is_rec_find_next_position (m-n) F)).
    rewrite_eq (m - (m -n) = n) in T.
    exists (find_next_position T).
    apply (find_next_position_correct T).
  Qed.

End FindNextPosition.

(** ** Infinite Filter *)
Section InfiniteFilter.
  (** Given a sequence w on a type X, a decidable predicate P on X and a proof that there are infinitely many
      positions in w at which P holds, there is function [infinite_filter : Seq nat] which has the following
      properties:
      - [infinite_filter] gives a strictly monotone sequence
      - P holds at all positions in w given by [infinite_filter]
      - [infinite_filter] gives all positions in w, at which P holds *)

  Context {X:Type}.
  Variable (w: Seq X).
  Variable (P : X -> Prop).
  Variable (decP: forall x, dec (P x)).
  Variable (infP: (forall n, exists m, m>=n /\ P (w m))).

  Lemma ge_to_le n m : m >= n -> n <= m. Proof. omega. Qed.

  Arguments cc_nat [p] [p_dec] _.
  Arguments can_find_next_position [X] [P] [decP] [w] [n] [m] _ _.

  Fixpoint infinite_filter  n :=
      match n with 
      | 0 => match cc_nat (infP 0) with
            exist _ m (conj Gm Pm) => projT1 (can_find_next_position (P:=P) (ge_to_le Gm) Pm)
             end
      | S n => match cc_nat (infP (S(infinite_filter n))) with
            exist _ m (conj Gm Pm) => projT1 (can_find_next_position (P:=P) (ge_to_le Gm) Pm)
             end
     end.

  Lemma infinite_filter_s_monotone : s_monotone infinite_filter.
  Proof.
    intros n. simpl.
    destruct cc_nat as [? [? ?]]. destruct can_find_next_position  as [? [? ?]].
    simpl. omega.
  Qed.

  Lemma infinite_filter_correct : (forall n, P ( w (infinite_filter n))).
  Proof.
    intros n. destruct n; simpl; destruct cc_nat  as [? [? ?]]; now destruct can_find_next_position.
  Qed.

  Lemma infinite_filter_all n: forall k, infinite_filter n < k < infinite_filter (S n) -> ~ P (w k).
  Proof.
    simpl. intros k L.
    destruct cc_nat as [l [Q1 Q2]]. destruct can_find_next_position as [l' [Q1' [Q2' Q3']]].
    simpl in L. apply Q3'. omega.
  Qed.

  Lemma infinite_filter_zero: P (w 0) -> infinite_filter 0 = 0.
  Proof.
    intros P0. simpl.
    destruct cc_nat as [k [Q1 Q2]]. destruct can_find_next_position as [k' [Q'1 [Q'2 Q'3]]].
    simpl. decide (k' = 0).
    - assumption.
    - exfalso. apply (Q'3 0); oauto.
  Qed.

End InfiniteFilter.

(** ** History Filter *)
Section HistoryFilter.

  (** Given a sequence w over a type X and a decidable and extensional predicate on strings over X, we want to find
      a function [history_filter] with the following properties
      - [history_filter] is strictly monotone
      - P holds for all prefixes of the induced subsequence of $w$.
      - [history_filter 0 = 0] (this is rather special for our application)

      To build this function, we require the following two things
      - P holds for the prefix of length 1 of w
      - If we have a strictly monotone string and P holds for the induced substring, we can find a next index which
        can be appended two this string. *)

  Arguments cc_nat [p] [p_dec] _.

  Context {X:Type}.
  Variable (w:Seq X).
  Variable (P: StringLang X).
  Variable (decP: forall w, dec (P w)).
  Variable (extP : StringLang_Extensional P).
  Arguments extP _ [w'] _ _.
        
  Variable (baseP: P (mkstring w 0)).

  Definition substring (g: String nat) : String X := mkstring (fun n => w (g [n])) (|g|).

  Variable (stepP: (forall g, g [0] = 0 -> P  (substring g) -> exists m, m>(g [|g|]) /\ P (substring (g++ (mkstring (fun n => m) 0))))).

  (** Because we need to keep the proofs that P holds to apply [stepP], [history_filter] is defined recursively on
      dependent pairs. The base and inductive case are established with lemmata. It is easier to work with sequences 
      than with strings and keep the bound as an extra argument *)

  Lemma history_filter_base: {g : Seq nat | g 0 = 0 /\ forall m, m <= 0 -> P (substring (mkstring g m))}.
  Proof.
    exists (fun i => 0). split.
    - reflexivity.
    - intros m L. rewrite_eq (m = 0). unfold substring. simpl.
      apply (extP (mkstring w 0)) ; auto.  split; auto; simpl.
      intros n O. now rewrite_eq (n = 0).
  Qed.
  
  Lemma history_filter_step  n:
     forall g : Seq  nat , g 0 = 0 -> (forall m, m <= n -> P (substring (mkstring g m)))->
          { k | k > g (n) /\  ((prepend_path  n g (fun i => k)) 0 = 0 /\ forall m, m <= S n -> P (substring (mkstring (prepend_path  n g (fun i => k))  m)))}.
  Proof.
    intros g' Z Q.
    assert ((mkstring g' n) [0] = 0) as Z' by apply Z.
    destruct (cc_nat (stepP  Z' (Q n (le_refl n)))) as [k [Q1 Q2]].
    exists k. repeat split.
    - now simpl in Q1. 
    - rewrite prepend_path_begin_correct; oauto. 
    - intros m L. unfold substring in *. simpl in *.
      decide (m = n + 1) as [D |D].
      + now subst m.
      + apply (extP (substring (mkstring g' m))).
        * apply Q. simpl. omega. 
        * split; simpl.
          -- reflexivity.
          -- intros l lL. rewrite prepend_path_begin_correct; oauto.
  Qed.

  Fixpoint history_filter_proof  n :  {g : Seq nat | g 0 = 0 /\ forall m, m <= n -> P (substring  (mkstring g m))} := match n with 
    | 0 => history_filter_base
    | S n => match (history_filter_proof n) with
                exist _ g (conj Q Q') => match (history_filter_step Q Q') with 
                   exist _ k (conj  _ Q2) =>  exist (fun g => g 0 = 0/\ forall m, m <= S n -> P (substring  (mkstring g m)))((prepend_path  n g (fun i => k))) Q2
                end
              end
    end .
    
  (** Then we can obtain [history_filter] by taking the n-th positiong of the function. *)
  Definition history_filter n := proj1_sig (history_filter_proof n) n.

  
  Lemma history_filter_s_monotone: s_monotone history_filter.
  Proof.
    intros n.  unfold history_filter. simpl.
    destruct history_filter_proof as [? [? ?]]; destruct history_filter_step as [? [? ?]]. simpl.
    rewrite_eq (S n = S n + 0). rewrite prepend_path_rest_correct. omega.
  Qed.

  Lemma history_filter_zero: history_filter 0 = 0.
  Proof.
    unfold history_filter. simpl. now destruct history_filter_base as [? [? ?]].
  Qed. 

  (** Before we can show that P holds for all prefixes of the induced substring, we need to show that [history_filter_proof]
      does not change the functions before the valid index but only appends stuff *)

  Lemma history_filter_proof_only_append_step m : forall k, k <= m -> (proj1_sig (history_filter_proof m)) k = (proj1_sig (history_filter_proof (S m))) k.
  Proof.
    destruct m; intros k L.
    - rewrite_eq (k = 0). simpl.
      destruct history_filter_base as [? [? ?]]. now destruct history_filter_step.
    - remember (S m) as M. simpl.
      destruct (history_filter_proof M) as [? [? ?]]. destruct history_filter_step as [? [_ ?]]. simpl.
      rewrite prepend_path_begin_correct; oauto.
  Qed.

  Lemma history_filter_proof_only_append m n : m <= n -> forall k, k <= m -> (proj1_sig (history_filter_proof m)) k = (proj1_sig (history_filter_proof n)) k.
  Proof.
    intros L. induction L; intros k Lk. 
    - reflexivity.
    - rewrite <-history_filter_proof_only_append_step by omega.
      apply IHL; omega.
  Qed.

  Lemma history_filter_correct: forall n, P (substring (mkstring history_filter n)).
  Proof.
    intros n. unfold substring, history_filter. induction n; simpl.
    - destruct history_filter_base as [g [? Q]] eqn:H.
      apply (extP (substring (mkstring g 0 ) )).
      + now apply Q. 
      + split; simpl.
        * reflexivity.
        * intros n L. rewrite_eq (n = 0). simpl. now rewrite H.
    - destruct (history_filter_proof (S n)) as [g Q] eqn:H.
      apply (extP (substring (mkstring g (S n)))).
      + now apply Q.
      + split; simpl.
        * reflexivity.
        * intros m L. destruct (history_filter_proof m) as [g' Q'] eqn: H'. f_equal. 
          (* This is not so nice ... *)
          change ((proj1_sig (exist (fun g : Seq nat => g 0 = 0 /\ forall m : nat, m <= S n -> P (substring (mkstring g m))) g Q)) m
                     = (proj1_sig (exist (fun g : Seq nat => g 0 = 0 /\ forall m0 : nat, m0 <= m -> P (substring (mkstring g m0))) g' Q')) m).
          rewrite  <-H, <-H'. symmetry.
          apply history_filter_proof_only_append; omega.
  Qed.

End HistoryFilter.

(** ** Infinite Concattenation
    Concattenating infinitely many strings (a sequence of strings) to a sequence *)
Section InfiniteConcat.

  Context {A:Type}.

  (** Helper function which translates the indices: it returns a tuple [(w, i)] such that
     [(f w) [i]] is the desired character at index n *)
  Fixpoint concat_inf_indices (f: Seq (String A)) n := match n with
    | 0 => (0,0)
    | S n => match (concat_inf_indices f n) with (w, i) =>
                if (decision (i = |f w|))
                  then (S w, 0)
                  else (w , S i) end end.

  Definition concat_inf (f: Seq ( String A)) : Seq A := fun n => 
      (f (fst (concat_inf_indices f n )))[snd (concat_inf_indices f n)].


  (** Calculates the begin index of [(f n)] in [(concat_inf f)] *)
  Fixpoint begin_in (f: Seq (String A)) n := match n with
     |0 => 0
     |S n => (begin_in f n) +  S (| f n|) end.

  Lemma s_monotone_begin_in f: s_monotone (begin_in f).
  Proof.
    intros n. simpl. omega.
  Qed.

  (** Various correctness lemmata *)

  Lemma concat_inf_index_in_string f i n : concat_inf_indices f n = (i, 0) ->
        forall k, k <= |f i| -> concat_inf_indices f (n + k) = (i , k).
  Proof.
    intros C.
    apply (complete_induction (P:= fun k => (k <= |f i| -> concat_inf_indices f (n + k) = (i, k)))).
    - intros _. now rewrite_eq (n + 0 = n).
    - intros k IHk L. 
      rewrite_eq (n + S k = S (n + k)). simpl.
      assert (concat_inf_indices f (n + k) = (i, k)) as H. { apply IHk; omega. }
      rewrite H.
      decide (k = |f i|).
      + exfalso. omega.
      + reflexivity.
  Qed.
      
  Lemma concat_inf_index_begin f i:  concat_inf_indices f (begin_in f i) = (i, 0).
  Proof.
    induction i ; simpl.
    - reflexivity.
    - rewrite_eq (begin_in f i + S (| f i |) = S(begin_in f i + |f i|)).
      simpl. rewrite concat_inf_index_in_string with (i:=i) by auto.
      decide (|f i| = |f i|); oauto.
  Qed.

  Lemma concat_inf_index_correct f i k: k <= |f i| -> concat_inf_indices f (begin_in f i + k) = (i, k).
  Proof.
    intros L.
    apply concat_inf_index_in_string ; auto.
    now apply concat_inf_index_begin.
  Qed.

  Lemma concat_inf_index_in_bounds f n i k : concat_inf_indices f n = (i , k) -> k <= |f i|.
  Proof.
    revert i; revert k.
    induction n; intros k i; intros C.
    - simpl in C. assert (k = 0) as H by congruence.
      rewrite H. omega.
    - simpl in C.
      destruct (concat_inf_indices f n) as [i' k'] eqn:H.
      decide (k' = |f i'|).
      + assert (k = 0) as H' by congruence.
        rewrite H'. omega.
      + assert (i' = i) as H' by congruence.
        subst i'.
        specialize (IHn k' i).
        assert (S k' = k) by congruence.
        assert (k' <= |f i|) by now apply IHn.
        omega.
  Qed.

  Lemma concat_inf_index_step_correct f n i k: concat_inf_indices f n = (i, k) ->
    concat_inf_indices f (S n) = (i, (S k)) \/
    (concat_inf_indices f (S n) = (S i, 0) /\ k = |f i|).
  Proof.
    intros L. simpl. rewrite L.
    decide (k = |f i|).
    - right. auto.
    - now left.
  Qed.


  (** To show that [concat_inf_indices] is injective, we define the natural order on pairs of natural numbers
     and show that [concat_inf_indices] is strictly s_monotone *)
  Definition nat_pair_le (x y : nat * nat) := (fst x < fst y) \/ (fst x = fst y /\ (snd x < snd y)).

  Lemma nat_pair_le_not_equal (x y: nat * nat):nat_pair_le x y -> x <> y.
  Proof.
    intros E. unfold nat_pair_le in E. destruct x, y.
    simpl in E. destruct E.
    - assert (n <> n1) by omega. congruence.
    - assert (n0 <> n2) by omega. congruence.
  Qed.   

  Lemma concat_inf_index_le f n m: n < m -> nat_pair_le (concat_inf_indices f n) (concat_inf_indices f m) .
  Proof.
   intros L. induction L. 
   - simpl.
     destruct (concat_inf_indices f n). decide (n1 = |f n0|).
     + left. simpl. omega.
     + right. simpl. omega.
   - simpl.
     destruct (concat_inf_indices f n)as [w i]; destruct (concat_inf_indices f m)as [w' i'].
     decide (i' = |f w'|); unfold nat_pair_le in IHL; simpl in IHL; unfold nat_pair_le; simpl; omega.
  Qed.

  Lemma concat_inf_index_injective f n n' : concat_inf_indices f n = concat_inf_indices f n' -> n = n'.
  Proof.
    decide (n = n').
    - auto.
    - intros H. exfalso. decide (n < n') as [D|D].
      + now apply (nat_pair_le_not_equal (concat_inf_index_le f D)).
      + assert (n' < n) as D' by omega.
        now apply (nat_pair_le_not_equal (concat_inf_index_le f D')).
  Qed.

  Lemma concat_inf_index_to_begin f n i k : concat_inf_indices f n = (i, k) -> n = (begin_in f i) + k /\ (n < begin_in f (S i)).
  Proof.
    intros C.
    assert ( k <= |f i|) by apply (concat_inf_index_in_bounds C).
    rewrite <- (concat_inf_index_correct (f:=f)) in C by now apply concat_inf_index_in_bounds with (n:=n).
    apply concat_inf_index_injective with (n:=n) in C.
    split; simpl; oauto.
  Qed.

  Lemma concat_inf_correct f i k : k <= |f i| -> concat_inf f ((begin_in f i) + k) = (f i) [k].
  Proof.
    unfold concat_inf. intros L.
    now rewrite concat_inf_index_correct.
  Qed.

End InfiniteConcat.

Lemma concat_inf_index_equal (A A': Type) (f:Seq (String A)) (f':Seq (String A')): (forall n , |f n| = |f' n|) -> (forall n,  concat_inf_indices f n = concat_inf_indices f' n).
Proof.
  intros EL n.
  induction n.
  - reflexivity.
  - simpl. rewrite <-IHn.
    destruct (concat_inf_indices f n) as [wi i].
    rewrite <-(EL wi).
    now decide (i = | f wi |).
Qed.


(** Define the omega iteration of a string using [concat_inf]*)

Definition omega_iteration (A: Type) (w:String A) := concat_inf (fun n => w).

Notation " w 'to_omega'" := (omega_iteration w) (at level 50).

Lemma omega_iteration_infinite (A:Type) (w:String A): forall n, n <= |w| -> infinite (w [n]) (w to_omega) .
Proof.
  intros n L m.
  unfold omega_iteration, concat_inf.
  destruct (concat_inf_indices (fun _ : nat => w) m) as [wi i] eqn:H.
  destruct (concat_inf_index_to_begin H).
  exists ((begin_in (fun _ : nat => w) (S wi)) + n). split.
  - omega.
  - now rewrite concat_inf_index_correct.
Qed.
 
(** ** Composing String and Sequence Languages *)

(** *** String Language#<sup>&omega;*)

(** Two Definitions for an #&omega;#-iteration of a string language*)
Definition lang_o_iter (A:Type) (l : StringLang A) : SeqLang A:= fun w =>
     exists f, s_monotone f /\ (f 0 = 0) /\ (forall n,l (extract (f n) (f (S n)) w)  ).

Definition lang_o_iter2 (A:Type) (l : StringLang A) : SeqLang A := fun w =>
     exists (f: Seq (String A)), (forall n, l ( f n)) /\ (w === concat_inf f).

Notation "l ^00" := (lang_o_iter l) (at level 20). 
Notation "l ^002"  := (lang_o_iter2 l) (at level 20).

Section OmegaIteration.

  Context{A:Type}.
  Variable l: StringLang A.

  (* Imagine the omega of the two 00, but I cannot use letters, otherwise coq doc pretty printing
     does not like the ^ in front !*)
 
  (** The second definition is weaker. If the string language is extensional, both definitions are 
      equivalent. *)

  Lemma o_iter_implies_o_iter2 w: l^00 w -> l^002 w.
  Proof.
    intros [f [Inc [B L]]].
    pose (f' := fun n => (extract (f n) (f (S n)) w)).
    assert (forall n, f n = begin_in f' n) as Bf. {
       induction n.
       - now simpl.
       - simpl. rewrite IHn.
         specialize (Inc n). omega. }
    exists f'. split.
    - exact L.
    - intros n. unfold concat_inf.
      destruct concat_inf_indices eqn:H. simpl. rewrite Bf. 
      destruct (concat_inf_index_to_begin H) as [H1 H2].
      rewrite H1. now rewrite drop_correct.
  Qed.

  Lemma extensional_o_iter2_implies_iter1 w: StringLang_Extensional l -> l^002 w -> l^00 w.
  Proof.
    intros E [f [L C]].
    exists (begin_in f).
    repeat split.
    - apply s_monotone_begin_in.
    - intros n. unfold extract.
      apply E with (w := (f n)).
      + apply L.
      + split.
        * simpl. omega.
        * intros k B. simpl. rewrite drop_correct. rewrite C. now rewrite concat_inf_correct.
  Qed.
End OmegaIteration.

(** *** Prepending a String on a Sequence Language *)

Definition lang_prepend (A:Type) (lf : StringLang A) (ls: SeqLang A) : (SeqLang A) := fun w =>
     exists n, lf (mkstring w  n) /\ ls (drop (S n) w).

Notation "l1 'o' l2" := (lang_prepend l1 l2) (at level 50).


Lemma prepend_on_omega_iteration (A:Type) (f1 f2 : StringLang A) w :  (f1 o f2^00) w
     -> exists v fw, f1 v /\ (forall k, f2 (fw k)) /\  w === (v +++ (concat_inf fw )) .
Proof.
  intros [n [v W]].
  apply o_iter_implies_o_iter2 in W.
  destruct W as [fw [P Q]].
  exists (mkstring w n).
  exists fw.
  repeat split; auto.
  intros i.
  decide (i <= n).
  - rewrite prepend_path_begin_correct; auto.
  - rewrite_eq (i = S n + (i - S n)).
    rewrite prepend_path_rest_correct.
    rewrite <-Q.
    now rewrite drop_correct.
Qed.
    
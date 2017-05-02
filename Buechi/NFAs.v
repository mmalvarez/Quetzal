Set Implicit Arguments.
Require Import BA.External.
Require Import Coq.Init.Nat.
Require Import Seqs.
Require Import SeqOperations.
Require Import BasicDefs.
Require Import BA.FinTypes.
Require Import Utils.

Open Scope string_scope.

(** * Nondeterminisic Finite Automata *)
 
Structure NFA (A:finType) := mknfa
   { state: finType;
     transition : state -> A -> state -> Prop;
     transition_dec : forall s1 a s2, dec(transition s1 a s2);
     initial_state : state  -> Prop;
     initial_state_dec : forall s, dec(initial_state s);
     final_state: state  -> Prop;
     final_state_dec: forall s, dec(final_state s)
   }.


Arguments transition [A] [aut] _ _ _ : rename.
Arguments initial_state [A] [aut] _ : rename.
Arguments final_state [A] [aut] _ : rename.
Arguments transition_dec [A] [aut] _ _ _ : rename.
Arguments initial_state_dec [A] [aut] _ : rename.
Arguments final_state_dec [A] [aut] _ : rename.

Hint Resolve final_state_dec.
Hint Resolve initial_state_dec.
Hint Resolve transition_dec.
Hint Resolve finType_exists_dec.

(* Dont ask me why Coq sometimes needs this *)
Instance transition_dec_public (A:finType)(aut:NFA A): forall s a s', dec (transition (aut:=aut) s a s').
Proof. auto. Defined.
Instance initial_dec_public (A:finType)(aut:NFA A): forall s, dec (initial_state (aut:=aut) s).
Proof. auto. Defined.
Instance final_dec_public (A:finType)(aut:NFA A): forall s, dec (final_state (aut:=aut) s).
Proof. auto. Defined.

(** ** Facts for valid Strings and Sequences of NFAs *)
Section TransitionGraph.
  Context {A : finType}.
  Context {aut: NFA A}.

  (** Definitions of valid runs and paths. We use sequences as runs for strings,
      because the length of the run is determined by the length of the string and
      so the length of the run is redundant. *)
  Definition Run := Seq (state aut).

  Definition valid_run  (r : Run) (w : Seq A):=
     forall n, transition (r n) (w n) (r (S n)).
  Definition valid_path  (r: Run) (w: String A) :=
        forall n, n <= |w| -> transition (r n) (w [n]) (r (S n)).

  Definition string_valid w := exists r, valid_path  r w .
  Definition path r w s s' := valid_path r w /\ r 0 = s /\ r (S (|w|)) = s'.  
  Definition cyclic_path r w s:= path r w s s.
  Definition connected (s s': state aut) : Prop := exists r w, path r w s s'.
  Definition cyclic s := connected s s.


  (** *** Extensionality facts *)
  Lemma valid_path_extensional r w w': valid_path r w ->  w == w' -> valid_path r w'.
  Proof.
    intros V [LE WE] n L. rewrite <-LE in L. rewrite <-WE by auto. now apply V.
  Qed.

  Lemma valid_run_extensional (r r' : Run ) w w':
       valid_run r w -> r === r' -> w === w' -> valid_run r' w'.
  Proof.
    intros V R W n.
    rewrite <- W.
    repeat rewrite <- R.
    apply V.
  Qed.

  Lemma path_extensional (r:Run ) (w w':String A) s s': path r w s s' -> w == w' -> path r w' s s'.
  Proof.
    intros [V [B E]] [EL EW].
    repeat split; auto.
    - now apply valid_path_extensional with (w:=w).
    - now rewrite <-EL.
  Qed. 

  (** *** Manipulations of valid paths and runs *)

  Lemma valid_run_is_path_everywhere r w: valid_run r w -> forall n m, valid_path (drop n r) (extract n m w).
  Proof.
    intros V n m k L. unfold extract. simpl.
    repeat rewrite drop_correct. 
    rewrite_eq (n + S k = S (n + k)).
    apply V.
  Qed.

  Lemma valid_run_is_path_from_begin r w: valid_run r w -> forall n, valid_path r (mkstring w n).
  Proof.
    intros V n m L. auto.
  Qed.

  Lemma  valid_path_decrease r w : valid_path r w -> forall k', k' <= |w| -> valid_path r (drop_string_end  k' w).
  Proof.
    intros p k' L  m Lm.
    apply p. simpl in Lm.
    omega.
  Qed.
  
  Lemma valid_run_drop (r: Run) w: forall n, valid_run r w -> valid_run (drop n r) (drop n w).
  Proof.
    intros n V m.
    repeat rewrite drop_correct.
    rewrite <-plus_n_Sm.
    now apply V.
  Qed.

  Lemma valid_path_drop r w k': valid_path r w -> k' <= |w| -> valid_path (drop k' r) (drop_string_begin k' w).
  Proof.
    intros V L n Lk. unfold drop_string_begin. simpl. simpl in Lk.
    repeat rewrite drop_correct.
    rewrite_eq (k' + S n = S (k' + n) ).
    remember (k' + n) as k''.
    apply V. omega.
  Qed.

  Lemma valid_path_cut r w k1 k2: valid_path r w -> S k1 < k2 <= |w| -> r (S k1) = r k2 -> valid_path (cut k1 k2 r) (mkstring (cut k1 k2 w) (S (|w|) - k2 + k1)).
  Proof.
    intros V L E n Lk. simpl. simpl in Lk.
    decide (n < k1).
    - repeat rewrite cut_front_correct by omega. apply V. omega.
    - decide (n = k1).
      + repeat rewrite cut_front_correct by omega.
        rewrite_eq (S n = S k1 + 0).
        rewrite cut_rest_correct. 
        rewrite_eq (k2 + 0 = k2). rewrite <-E. subst n.
        apply V. omega.
      + rewrite_eq (n = S k1 + (n - S k1)).
        rewrite_eq ((S (S k1 + (n - S k1))) = S k1 +  (n - k1)).
        repeat rewrite cut_rest_correct.
        rewrite_eq (k2 + (n - k1) = S (k2 + (n - S k1))).
        apply V. 
        destruct k2 eqn:K.
        * exfalso. omega.
        * omega.
  Qed.

  Lemma prepend_valid_run (s:state aut) (a: A) (r:Run) (w:Seq A) :
    valid_run r w -> transition s a (r 0) -> valid_run (prepend s r) (prepend a w).
  Proof.
  intros V T n.
  destruct n.
  - repeat rewrite prepend_first_correct.
    rewrite prepend_rest_correct.
    exact T.
  - repeat rewrite prepend_rest_correct.
    apply V.
  Qed.
    
  Lemma prepending_path_is_valid r w : valid_path r w ->
        forall r' w', (r' 0) = (r (S (|w|))) -> (valid_run r' w') ->
                      valid_run (prepend_path (|w|) r r') (w +++ w').
  Proof.
  revert r. destruct w as [w k]. revert w.
  induction k;intros r w p r' w' R0 V; simpl in R0.
  - simpl. 
    apply prepend_valid_run; auto.
    rewrite R0. now apply p.
  - simpl.
    apply prepend_valid_run.
    + apply IHk; auto.
      intros n L. simpl in L. apply p. simpl. omega.
    + rewrite prepend_path_begin_correct.
      * apply p. omega.
      * omega.
  Qed.

  Lemma prepend_valid_path s a r w :
    valid_path r w -> transition s a (r 0) -> valid_path (prepend s r) (mkstring (prepend a (seq w)) (S(|w|))).
  Proof.
  intros V T n L.
  destruct n.
  - repeat rewrite prepend_first_correct.
    rewrite prepend_rest_correct.
    exact T.
  - repeat rewrite prepend_rest_correct.
    apply V. simpl in L. omega.
  Qed.

  Lemma prepending_path_on_path_is_valid r w : valid_path r w -> 
        forall r' w', (r' 0) = (r (S (|w|))) -> (valid_path r' w') ->
                      valid_path (prepend_path (|w|) r r') (w ++ w').
  Proof.
  revert r. destruct w as [w k]. revert w.
  induction k;intros r w p r' w' R0 V; simpl in R0.
  - simpl. 
    apply prepend_valid_path; auto.
    rewrite R0. now apply p.
  - simpl. unfold concat_strings. simpl.
    apply prepend_valid_path with (w:= (mkstring (prepend_path k (fun n : nat => r (S n)) w')  (k + S (| w' |)))).
    + apply IHk; auto.
      intros n L. simpl in L. apply p. simpl. omega.
    + rewrite prepend_path_begin_correct.
      * apply p. omega.
      * omega.
  Qed.

  Lemma non_empty_cycle_is_valid r w s: cyclic_path r w s -> valid_run ((mkstring r (|w|)) to_omega) (w to_omega).
  Proof.
    intros p n.
    unfold omega_iteration, concat_inf.
    destruct p as [V [R0 RSk]].
    rewrite (concat_inf_index_equal (f:=(fun _ : nat => w)) (f':=(fun _ : nat => mkstring r (| w |)))) by auto. 
    simpl.
    destruct ((concat_inf_indices (fun _ : nat => mkstring r (| w |)) n)) as [wi i] eqn:H.
    destruct (concat_inf_index_step_correct H) as [J|J]; simpl in J; rewrite H in J.
    - simpl. rewrite J. simpl. apply V. apply (concat_inf_index_in_bounds H).
    - simpl. decide (i = | w |).
      + destruct J as [J1 J2]. simpl. repeat rewrite J2. rewrite R0, <-RSk. now apply V.
      + simpl. apply V. apply (concat_inf_index_in_bounds H).
  Qed.

  (** *** Facts about Connectivity *)
  
  Lemma valid_run_connects r w: valid_run r w -> forall n m, n < m -> connected (r n) (r m).
  Proof.
    intros V n m L.
    exists (drop n r); exists (extract n m w). repeat split.
    - now apply  valid_run_is_path_everywhere.
    - rewrite drop_correct. f_equal. omega.
    - rewrite drop_correct. f_equal. simpl. omega.
  Qed.  
  
  Lemma cyclic_path_connects_on_path r w s: cyclic_path r w s -> forall i j, i  < j <=  S(|w|) -> connected (r i) (r j).
  Proof.
   intros [V [B E]] i j [Li Lj].
   exists (prepend_path (|w| - i) (drop i r) r). exists ( (drop_string_begin i w) ++ (drop_string_end (|w| - (pred j)) w)).
   repeat split.
   - apply prepending_path_on_path_is_valid.
     + apply valid_path_drop; oauto. 
     + simpl. rewrite drop_correct. rewrite_eq (i+ S((|w|) - i) = S(|w|)). now rewrite B, E.
     + apply valid_path_decrease; oauto.
   - rewrite prepend_path_begin_correct by omega. rewrite drop_correct. f_equal. omega.
   - simpl.
     rewrite_eq ((S ((| w |) - i + S ((| w |) - ((| w |) - pred j)))) = S ((| w |) - i)  + j).
     now rewrite prepend_path_rest_correct by omega. 
  Qed.

  (* Would follow from the Lemma before, but this is just easier *)
  Lemma cyclic_path_connects r w s: cyclic_path r w s -> connected s s.
  Proof.
   intros C.
   exists r; exists w. apply C.
  Qed.

  (** *** Concatting and Splitting of Paths *)
  Lemma concat_paths r r' (w w': String A) (s s'' s': state aut): path r w s s'' -> path r' w' s'' s' -> path (prepend_path (|w|) r r') (w ++ w') s s'.
  Proof.
    intros [V [B E]] [V'[B' E']].
    repeat split.
    - apply prepending_path_on_path_is_valid;auto. now rewrite E,B'.
    - rewrite <-B. rewrite prepend_path_begin_correct; oauto.
    - rewrite <-E'. rewrite prepend_path_rest_correct2 with (n:= S(|w'|)); simpl; oauto.
  Qed.

  Lemma adjacent_paths_agree (r1 r2:Run) (w1 w2: String A) (s s' s'':state aut): path r1 w1 s s'' -> path r2 w2 s'' s' -> r1 (S(|w1|)) = r2 0.
  Proof.
    intros [_ [_ E]] [_ [B _]].
    now rewrite E ,B.
  Qed.

  Lemma split_path (r:Run) (u w:String A) (s s':state aut):path r (u ++ w) s s' -> exists s'', path r u s s'' /\ path (drop (S(|u|)) r) w s'' s'.
  Proof.
    intros [V [B E]].
    exists (r (S(|u|))). repeat split;auto.
    - apply (valid_path_extensional (w:= drop_string_end (S(|w|)) (u++w))).
      + apply valid_path_decrease; simpl;oauto.
      + apply string_equal_symmetric. apply revert_concat_first.  
    - apply (valid_path_extensional (w:= drop_string_begin (S(|u|)) (u++w))).
      + apply valid_path_drop; simpl; oauto.
      + apply string_equal_symmetric. apply revert_concat_second.
    - rewrite drop_correct. f_equal. omega.
    - rewrite drop_correct. now rewrite <-E.
  Qed.

End TransitionGraph.


Arguments Run [A] _.

(** ** String Language of an NFA *)
Section NFAStringLanguage.

  Context{ A: finType}.
  Context (aut: NFA A).

  Definition svalid r w:= valid_path (aut:=aut)  r w.
  Definition sinitial (r: Run aut) := initial_state (r 0).
  Definition sfinal (r: Run aut)  (w:String A) := final_state  (r (S(|w|))).
  Definition saccepting r w := svalid r w /\ sinitial r /\ sfinal r w.

  Definition slanguage := fun w => exists r, saccepting r w.

  Lemma slanguage_extensional:StringLang_Extensional (slanguage).
  Proof.
    intros w w' [ r [V [I F]]] E.
    exists r. repeat split.
    - unfold svalid. now apply (valid_path_extensional (w:=w)).
    - auto.
    - unfold sfinal. destruct E as [E ]. now rewrite <-E.
  Qed. 
End NFAStringLanguage.

Notation "'L_S'" := slanguage.

Hint Unfold svalid.
Hint Unfold sinitial.
Hint Unfold sfinal.

(** ** Decidability of Connectivity in NFAs 
    I do not claim that this is the nicest possibility (no, I am sure, it is not), but this is a well
    known fact and so not so interessting per se. *)
Section DecConnected.
  
  Context {A : finType}.
  Context {aut : NFA A}.

  (** Show that the maximum path length needed to connect two states is bounded *)

  Definition remove_circle k (r: Run aut) (w: Seq A): nat * (Run aut) * (Seq A) := match (can_find_duplicate k r) with
      | inleft (existT _ n1 (existT _ n2 _)) => match n1 with 
              | 0  => (k - n2, drop n2 r, drop n2 w)
              | S n1' => (k - n2 + n1,  cut  (pred n1) (n2) r, cut   (pred n1) (n2) w)
               end
      | _ => (k,r, w)
   end.

  Definition minimize_path k r w := iter k (fun z => match z with
         (k',r', w') => remove_circle k' r' w' end ) (k, r, w).

  Lemma remove_circle_correct r w: valid_path r w -> match  remove_circle (|w|) r w 
       with (k',r', w')  => valid_path  r' (mkstring w' k' ) end.
  Proof.
    destruct w as [w k].
    intros V.
    unfold remove_circle. simpl.
    destruct (can_find_duplicate k r).
    - destruct s as [n1 [n2 [O E]]].
      destruct n1 eqn:En1.
      + change (valid_path (drop n2 r) (drop_string_begin (X:=A) n2 (mkstring w k)) ).
        now apply valid_path_drop.
      + rewrite_eq (pred (S n) = n).
        rewrite_eq (k - n2 + S n = S k - n2 + n).
        now apply (valid_path_cut (w:=mkstring w  k)).
     - assumption.
  Qed.

  Lemma remove_circle_decrease k r w: match remove_circle k r w with (k',r',w') => (k' < k) \/ (k' <= Cardinality (state aut)) end.
  Proof.
   unfold remove_circle.
   destruct (can_find_duplicate k r) as [D|D].
   - destruct D as [n1 [n2[L _]]].
     destruct n1.
     + left. omega.
     + left. omega.
   - now right.
  Qed.

  Lemma remove_circle_preserves_first_state k r w: snd (fst (remove_circle k r w)) 0 = r 0.
  Proof.
    unfold remove_circle.
    destruct (can_find_duplicate k r) as [D|D].
    - destruct D as [n1 [ n2 [ L E]]].
      destruct n1.
      + simpl. rewrite drop_correct. now  rewrite_eq (n2 + 0= n2).
      + simpl. now rewrite cut_front_correct by oauto.
    - reflexivity.
  Qed.

  Lemma remove_circle_preserves_last_state k r w: (snd (fst (remove_circle k r w))) (S (fst (fst (remove_circle k r w)))) = r (S k) .
  Proof.
    unfold remove_circle.
    destruct (can_find_duplicate k r) as [D|D].
    - destruct D as [n1 [ n2 [ L E]]].
      destruct n1.
      + simpl. rewrite drop_correct. f_equal. omega.
      + simpl. 
        rewrite_eq (S(k - n2 + S n1) = S n1 + (S k - n2)).
        rewrite cut_rest_correct. f_equal. omega.
    - reflexivity.
  Qed. 

  Lemma minimize_path_correct r w : valid_path r w -> match (minimize_path (|w|) r w) with
          (k', r', w') => valid_path r' (mkstring w' k') /\ k' <= Cardinality(state aut ) /\ r' 0 = r 0 /\ r' (S k') = r (S (|w|)) end.
  Proof.
    revert r. destruct w as [w k]. revert w.   
    unfold minimize_path.

    enough (forall l r w, valid_path r (mkstring w k) -> match (iter l (fun z => match z with
         (k',r', w') => remove_circle k' r' w' end ) (k, r, w)) with (k',r',w') => valid_path  r' (mkstring w' k')  /\ k' <= max (k -l) (Cardinality (state aut)) /\ r' 0 = r 0 /\ r' (S k') = r (S k) end).
   
    - intros w r V.
      specialize (H k r w V). simpl.
      destruct iter  as [[k' r'] w'].
      now rewrite_eq (k-k = 0) in H.

    - induction l; intros r w V.
      + simpl. repeat split.
        *  assumption.
        *  rewrite_eq (k - 0 = k). apply Nat.le_max_l.
      + simpl. destruct iter as [[k' r'] w']  eqn:E';
        destruct remove_circle  as [[k'' r''] w''] eqn:E''.
        specialize (IHl r w V).
        rewrite E' in IHl.
        destruct IHl as [V' [L' [ r0 rk]]]. simpl in V'.
        repeat split.
        * pose (Z:= (remove_circle_correct V')). simpl in Z.
          now rewrite E'' in Z.
        * pose (Z:= remove_circle_decrease k' r' w').
          rewrite E'' in Z.
          destruct Z as [Z|Z].
          -- destruct (Nat.max_dec (k - l) (Cardinality (state aut))) as [Z'|Z'].
             ++ apply max_le_left. omega.
             ++ apply max_le_right. omega.
          -- now apply max_le_right.
        * change (snd (fst (k'',r'',w'')) 0 = r 0).
          rewrite <-E''.
          now rewrite remove_circle_preserves_first_state.
        * change ((snd (fst (k'',r'',w''))) (S(fst (fst (k'', r'',w'')))) = r (S k)).
          rewrite <-E''.
          now rewrite remove_circle_preserves_last_state.
  Qed.
      

  Lemma path_length_bounded s t: connected s t <-> exists r w,  |w| <  S(Cardinality (state aut)) /\ path (aut:=aut) r w s t.
  Proof.
    split.
    - intros [r [w [V [B E]]]].
      destruct (minimize_path (|w|) r w) as [[k'' r''] w''] eqn:M.
      pose (minimize_path_correct V) as C.
      rewrite M in C.
      destruct C as [VC [LC [BC EC]]]. 
      exists r''; exists (mkstring w'' k''). split.
      + simpl. omega.
      + repeat split; simpl.
        * assumption.
        * now rewrite BC, B.
        * now rewrite EC, E.
    - intros [r [w [_ Q]]]. exists r; exists w. assumption.
  Qed.


  (* Instance transition_dec s a s' : dec(transition (a:= aut) s a s'). Proof. apply transition_dec. Qed.*)
  Instance dec_valid_path r w: dec(valid_path (aut:= aut)  r w).
  Proof.
    destruct w as [w k].
    induction k.
    - decide ( transition (r 0) (w 0) (r 1)).
      + left. intros n L. simpl. simpl in L.
        now rewrite_eq (n = 0) .
      + right. auto.
    - destruct IHk as [D|D].
      + decide (transition (r (S k)) (w (S k)) (r (S (S k)))).
        * left. intros n L. decide (n = S k).
          -- now rewrite e.
          -- apply D. simpl. simpl in L. omega.
        * right. auto.
      + right. intros V. apply D.
        rewrite_eq (k = (S k) - 1). apply (valid_path_decrease V).
        simpl. omega.
  Defined.

  (** Now show that we can decide connectivity for the bounded paths *)

  Definition m := S(Cardinality (state aut)). 
  Definition M := (finType_Le_K m).
  Definition BoundedPath := (state aut) ^ M.
  Definition BoundedString := (A) ^ M.

  Lemma dec_bounded_path  s t : dec (exists n, n < m /\ exists (b : BoundedPath) (w:BoundedString), path (to_seq b) (mkstring (to_seq w) n) s t).
  Proof.
    auto.
  Qed.

  Lemma bounded_run_is_valid_path (r: Run aut) w m : m >= S (|w|) ->
    valid_path  r w -> valid_path (to_seq(to_bounded (m:= m) r)) w.
  Proof.
    intros M V.
    unfold valid_path.
    intros n L.
    repeat rewrite bounded_unchanged by omega.
    now apply V.
  Qed.

  Lemma bounded_string_is_valid_path (r: Run aut) w m : m >=  |w| ->
    valid_path r w -> valid_path r (mkstring (to_seq(to_bounded (m:= m) w)) (|w|)).
  Proof.
    intros M V.
    unfold valid_path.
    intros n L. simpl. simpl in L.
    repeat rewrite bounded_unchanged by omega.
    now apply V.
  Qed.

  Lemma bounded_path_to_path s t :
    (exists k, k < m /\ exists (r : BoundedPath) (w:BoundedString), path (to_seq r) (mkstring (to_seq w) k) s t)
 <-> (exists r w,  |w| <  m /\ path (aut:=aut) r w s t).
  Proof.
   split.
   - intros [k [L [r [w P]]]].
     exists (to_seq r); exists (mkstring (to_seq w) k). split; auto.
   - intros [r [w [L  [V [I E]]]]]. simpl in L.
     exists (|w|). split; auto.
     exists (to_bounded r); exists(to_bounded w). repeat split.
     + apply bounded_run_is_valid_path. { simpl. omega. }
       apply bounded_string_is_valid_path. { omega. }
       assumption.
     + now rewrite bounded_unchanged by omega.
     + now rewrite bounded_unchanged by auto.
  Qed.    

  Lemma dec_connected s t : dec (connected (aut:=aut) s t).
  Proof.
    pose (X:= (exists r w,  |w| <  m /\ path (aut:=aut) r w s t)).
    apply (dec_prop_iff (X:=X)).
    - unfold X. symmetry.  apply path_length_bounded.
    - pose (Y:=(exists k, k < m /\ exists (r : BoundedPath) (w:BoundedString), path (to_seq r) (mkstring (to_seq w) k) s t)
).
      apply (dec_prop_iff (X:=Y)).
      + unfold X,Y. apply bounded_path_to_path.
      + unfold Y. apply dec_bounded_path.
  Qed.
  
 
End DecConnected.

(* I do not know why Hint Resolve is not sufficient. *)
Instance dec_valid_path_public A aut  r w: dec (valid_path (A:=A)(aut:=aut) r w).
Proof. apply dec_valid_path. Defined.
Instance dec_connected_public A aut s t: dec (connected (A:=A)(aut:=aut) s t).
Proof. apply dec_connected. Defined.

Instance dec_svalid A (aut:NFA A) r w : dec (svalid (aut:=aut) r w).
Proof. auto. Defined.
Instance dec_sinitial A (aut:NFA A) r : dec (sinitial (aut:=aut) r ).
Proof. auto. Defined.
Instance dec_sfinal A (aut:NFA A) r  w: dec (sfinal (aut:=aut) r w).
Proof. auto. Defined.
Instance dec_saccepting A (aut:NFA A) r w: dec (saccepting (aut:=aut) r w).
Proof. auto. Defined.
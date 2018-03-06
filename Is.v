Require Import Bauer.
Require Import List. 
Require Import MSets Arith.
Require Import Coq.omega.Omega.
Require Import synth.

Import ListNotations.


(* We can make a set out of an ordered type *)

Definition instance := Graph.
Definition solution := S.t.

Definition metric := nat.
Definition eval := S.cardinal.
Definition better (m1 m2 : metric) := negb (m1 <? m2).

Definition verifier (I : instance) (S : solution) := 
S.For_all (fun v1 => S.For_all (fun v2 => ~ is_some (I v1 v2)) S) S.

Definition checker (I : instance) (S : solution) := 
S.for_all (fun v1 => S.for_all (fun v2 => negb (is_someb (E I v1 v2))) S) S.

Definition gen_space := fun I => all_subset (V I).

Definition max_Is_brute_force := synthesize instance solution metric checker eval better gen_space.

Compute S.elements (match max_Is_brute_force (K 10) with | None => S.empty | Some s => s end).

Definition algorithm f := forall (I : instance) (Sol Cand : solution), 
  (f I = Some Sol -> verifier I Sol /\ ((verifier I Cand) -> better Sol Cand))
/\
  (f I = None -> ~exists Cand', verifier I Cand').

Check SF.for_all_1.
Print Proper.

Lemma vc_reflect : forall I Sol, reflect (verifier I Sol) (checker I Sol).
Proof. 
intros. 
apply iff_reflect. split. 
- intros. unfold verifier in H. unfold checker. 
Admitted.

Search reflect.

Lemma list_max_aux : forall {X : Type} f l (d : X),  In (list_max f (d::l) d) (d::l).
Proof.
intros. induction l.
- simpl. left. destruct (f d d). reflexivity. reflexivity.
- simpl. inversion IHl. destruct (f d d) eqn:h.
  + destruct (f d a) eqn:e. 
    * right. left. simpl in H. rewrite h in H.   
Qed.
 

Lemma list_max_aux2 : forall {X : Type} f l (d a m : X), f d a = true -> list_max f l a = m -> 
list_max f l d = m.
Proof.
induction l. 
- intros. simpl. simpl in H0. rewrite <- H0. 
Qed. 

Check equivalence.
 
Search (Set -> Prop).

Definition f_refl {X : Type} f := forall x : X, f x x = true.
Definition f_trans {X : Type} f := forall x y z : X, f x y = true -> f y z = true -> f x z = true.

Definition f_preorder {X : Type} (f : X -> X -> bool) := (f_refl f) /\ (f_trans f).

Lemma list_max_In : forall {X : Type} f l (d : X), 
In (list_max f l d) (d::l).
Proof.
intros. generalize dependent d. induction l.
- simpl. left. reflexivity.
- intros. simpl. destruct (f d a) eqn:e. 
  + simpl in IHl. pose (IHl a). inversion o. 
    * right. left. exact H.
    * right. right. exact H. 
  + simpl in IHl. pose (IHl d). inversion o.
    * left. exact H.
    * right. right. exact H.   
Qed.

Lemma list_max_max : forall {X : Type} f l (d a : X), In a (d::l) -> 
f a (list_max f l d) = true.
Proof.
Admitted.

Lemma all_subset_In : forall (I : instance) (S : solution), verifier I S -> In S (all_subset I).
Proof.
Admitted.

Check Nat.ltb_lt.

Theorem correct : algorithm brute_force. 
Proof.
unfold algorithm.
split. 
- intros. split. 
  + unfold brute_force in H.  
    destruct (map (fun iset : S.t => (metric iset, iset))
           (filter (checker I)
              (all_subset I))) eqn:e.
    * inversion H.
    * inversion H. assert (forall rs, In rs
    (map (fun iset : S.t => (metric iset, iset))
      (filter (checker I )
         (all_subset I))) -> verifier I (snd rs)). 
    { intros. apply in_map_iff in H0. inversion H0. inversion H2. inversion H3. 
      apply filter_In in H4. inversion H4. destruct (vc_reflect I x).
      - simpl. exact v.
      - inversion H7.
    }  
    pose (list_max
          (fun e1 e2 : nat * S.t =>
           let (s1, _) := e1 in let (s2, _) := e2 in s1 <? s2) l p).
    apply (H0 p0). rewrite e. apply list_max_In.
  + unfold brute_force in H. 
     destruct (map (fun iset : S.t => (metric iset, iset))
           (filter (checker I)
              (all_subset I))) eqn:e. 
    * inversion H.
    * inversion H. unfold better. intros. remember (list_max
          (fun e1 e2 : nat * S.t =>
           let (s1, _) := e1 in let (s2, _) := e2 in s1 <? s2) l p) as m.
      assert (In (metric Cand, Cand) (p::l)). 
      { pose (all_subset_In I Cand H0). Check iff. pose (filter_In (checker I) Cand (all_subset I)). 
        inversion i0. destruct (vc_reflect I Cand). 
        + assert (In Cand (all_subset I) /\ true = true). { split. exact i. reflexivity. }
          apply H3 in H4. pose (in_map_iff (fun iset : S.t => (metric iset, iset)) (filter (checker I) (all_subset I)) (metric Cand, Cand)).
          inversion i1. rewrite e in H6. apply H6. exists Cand. split.
          - reflexivity.
          - exact H4.
        + exfalso. unfold not in n. apply n. apply H0. }
      pose (list_max_max (fun e1 e2 : nat * S.t =>
          let (s1, _) := e1 in let (s2, _) := e2 in s1 <? s2) l p (metric Cand, Cand)).
      apply e0 in H2. rewrite <- Heqm in H2. 
      destruct m. apply Nat.ltb_lt in H2.
      assert (n = metric t). { pose (list_max_In  (fun e1 e2 : nat * S.t =>
          let (s1, _) := e1 in let (s2, _) := e2 in s1 <? s2) l p). rewrite <- Heqm in i.
      pose (in_map_iff (fun iset : S.t => (metric iset, iset)) (filter (checker I) (all_subset I)) (n,t)). inversion i0.
      rewrite e in H3. apply H3 in i. inversion i. inversion H5. inversion H6. reflexivity. }
      simpl. rewrite <- H3. unfold ge. omega.
- admit.
Qed.
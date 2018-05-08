Require Import List.
Require Import MSets Arith.
Require Import Coq.Numbers.NaryFunctions.
From Template Require Import All.
Import ListNotations MonadNotation.
Require Import Coq.Strings.String.
Require Import Ascii.
Extraction Language Haskell.
Require Import FMaps.

Require Import DepList.

Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

Run TemplateProgram (t <- tmQuoteInductive "nat";; tmPrint t).
Run TemplateProgram (r <- tmQuote nat;; tmPrint r).


Definition split_i {X : Type} (i : nat) (l : list X) := (firstn i l, skipn i l).

Fixpoint tabulate_list {X : Type} (f : nat -> X) n : List.list X := 
match n with 
| 0 => []
| S n => List.cons (f n) (tabulate_list f n)
end.


Inductive prod3 (A B C : Type) : Type := 
pair3 : A -> B -> prod3 A B C
| pair3' : B -> prod3 A B C
| pair3'' : C -> prod3 A B C.

Print sum.
Definition rec (F : Type -> Type -> Type) (A : Type) : Type := forall X, (F X A -> X) -> X.

Definition snat := rec (fun X _ => sum unit X) unit.

Definition szero : snat := fun x f => f (inl tt).
Definition sone : snat := fun x f => f (inr (szero x f)).

Definition twice (sn : snat) : snat := fun x f => 
sn x (fun body => 
match body with
| inl tt => f (inl tt)
| inr n' => f (inr (f (inr (n'))))
end).

Definition ss (sn : snat) : snat := fun x f => f (inr (sn x f)).

Definition list' := rec (fun X A => sum unit (prod A X)).

Definition var1 := fun _ : Type -> Type => unit.

Definition Id := fun X : Type => X.

Inductive tlist : list Type -> Type :=
| Hnil : tlist nil
| Hcons : forall (T : Type) {TS}, list T -> tlist TS -> tlist (T :: TS).

Notation "<<>>" := Hnil.
Infix ":+:" := Hcons (right associativity, at level 60).

Check Hcons nat [1;2;3] Hnil.

Check HFirst.

Check sigT.
Check sigT list.
Check existT list nat [1;2].

Definition tget' T TS : member T TS  -> Type := fun _ => T.
Fixpoint tget {TS : list Type} {T} (hs : tlist TS)
: member T TS ->  list T :=
  match hs in tlist TS return member T TS -> list T with
    | Hnil =>
      fun x => match x in member _ Z return match Z with
                                           | nil => list T
                                           | _ :: _ => Type * list unit
                                         end
               with
                 | HFirst => (unit, [tt])
                 | HNext _ _ _ => (unit, [tt])
               end
    | Hcons T' x hs =>
      fun m => match m in member _ Z
                     return match Z with
                              | nil => list T
                              | x :: y => list x -> (member T y -> list T) -> list T
                            end
               with
                 | HFirst => fun x' _ => x'
                 | HNext _ _ m' => fun _ f => f m'
               end x (@tget _ T hs)
  end.

Definition h1 := Hcons string ["a";"b";"c"] (Hcons nat [1;2;3] Hnil).
Definition i1 : member string [string;nat] := HFirst.
Check i1.
Compute tget h1 i1.

Definition Nfunctor := list Type -> Type.

Definition nrec (F : Type -> Type): Type := forall X, (F X-> X) -> X.

Definition rfold F  : forall X, (F X -> X) -> (nrec F) -> X := 
fun X k t => t X k.

Class Functor (F : Type -> Type) : Type := 
{
   liftF : forall {X Y}, (X -> Y) -> (F X -> F Y)
}.

Instance Maybe : Functor (fun X => sum unit X) :=
{
  liftF := fun X Y => fun f => fun x => 
  match x with 
  | inl tt => inl tt
  | inr y => inr (f y)
  end
}.

Definition rin F `{Functor (F)} : F (nrec F) -> nrec F :=
fun s => fun X k => k ((liftF (rfold F X k)) s). 

Definition rout F `{Functor (F)} : nrec F -> F (nrec F) :=
rfold F (F (nrec F)) (liftF (rin F )).

Fixpoint arrTy' A (l : list Type) : Type :=
match l with 
| [] => A
| x::xs => x -> (arrTy' A xs)
end.

Compute arrTy' (list nat) [nat;list nat].
 
Definition arr' A := fun l : list Type => arrTy' A l.
Check arr'.
Definition constructor (A : Type) : Type := sigT (arr' A).
Compute constructor.
Definition inductive (A : Type) := 
list (constructor A).

Fixpoint computeS {A} (l : inductive A) : list (list Type) := 
match l with 
| [] => []
| x::xs => 
  let argT := projT1 x in 
  argT :: computeS xs
end.

Section s.
 Variable ts : list Type.

 Inductive Species : list Type -> Type -> Type := 
| zero : forall C, Species C (Empty_set)
| one :  forall C {x} (m : member x ts), Species C ( unit)
| singleton :  forall C {x} (m : member x ts), Species C ( tget' _ ts m)
| cprod : forall C {F G}, Species C F -> Species C G -> Species C ( prod F G)
| pprod : forall C {F G}, Species C F -> Species C G -> Species C ( prod F G)
| ssum : forall C {F G}, Species C F -> Species C G -> Species C (sum F G)
| srec : forall C F `{Functor (F)}, Species ((nrec F)::C) (F (nrec F)) -> 
  Species C (nrec F) 
| svar : forall C F, member F C -> Species C F
| sind : forall C A (l : inductive A), 
  hlist (fun c => prod (arr' A (projT1 c)) (hlist (Species (A::C)) (projT1 c : list Type))) l -> Species C A. 
End s.

Check existT (fun x => x) nat 4.
Notation "{{ x }}" := (@cons Type (x : Type) nil) : list_scope.
Notation "{{ x ; y ; .. ; z }}" := (@cons Type (x : Type) (@cons Type (y : Type) .. (@cons Type (z : Type) nil) ..)) : list_scope.



Fixpoint insertAt A (t : A) (G : list A) (n : nat) {struct n} : list A :=
match n with
| O => t :: G
| S n' => match G with
| nil => t :: G 
| t' :: G' => t' :: insertAt A t G' n'
end
end.

Fixpoint liftVar A t G (x : member t G) t' n : member t (insertAt A t' G n) :=
match x with
| HFirst => match n return member t (insertAt A t' (t :: _) n) with
| O => HNext t' (t::_) HFirst
| _ => HFirst
end
| HNext t'' G'' x' => 
match n return member t (insertAt A t' (t''::G'') n) with
| O => HNext _ _ (HNext _ _ x')
| S n' => HNext _ _ (liftVar A _ _ x' t' n')
end
end.

Print ilist.

Check ICons "a" (ICons "b" (ICons "c" INil)).

Definition f := fun t => list t.
Check hmap.
Fixpoint lift' k C t' n t (s : Species k C t) : Species k (insertAt _ t' C n) t := 
match s with 
| zero _ C => zero _ (insertAt _ t' C n)
| one _ C i => one _ (insertAt _ t' C n) i
| singleton _ C _ => singleton _ (insertAt _ t' C n) _
| cprod _ C S1 S2 => cprod _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| pprod _ C S1 S2 => pprod _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| ssum _ C S1 S2 => ssum _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| srec _ C F S' => srec _ (insertAt _ t' C n) F (lift' k _ t' (S n) _ S')
| svar _ C F x => svar _ _ _ (liftVar _ _ _ x t' n)
| sind _ C tA indA hll => sind _ (insertAt _ t' C n) tA indA 
  (hmap (fun l '(c, hl) => (c, hmap (fun x s => lift' k _ t' (S n )x s) hl)) hll )
end.

Definition lift k C t' t (e : Species k C t) : Species k (t' :: C) t := lift' k C t' O t e.


Fixpoint subst {k} C t (s : Species k C t) C' : hlist (Species k C') C -> Species k C' t :=
match s with 
| zero _ C => fun _ => zero _ _
| one _ C i => fun _ => one _ _ i
| singleton _ C _ => fun _ => singleton _ _ _
| cprod _ C S1 S2 => fun s =>  cprod _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| pprod _ C S1 S2 => fun s =>  pprod _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| ssum _ C S1 S2 => fun s => ssum _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| srec _ _ F S' => fun s => srec _ _ F (subst _ _ S' _ (svar _ (_::C') _ (HFirst) ::: hmap (fun f =>  lift k C' _ f) s))
| svar _ C F x => fun s => hget s x
| sind _ C tA indA hll => fun s => sind _ _ tA indA 
  (hmap (fun l '(c,hl) => (c,hmap (fun x s' => subst _ _ s' _ (svar _ _ _ HFirst ::: hmap (lift k C' _) s) ) hl)) hll)
end.

(*fun tls h => 
  let C'' := nrec ts F :: C' in 
  let s'' := subst C'' _ s' C' (HCons s h) in 
  enum s'' tls*)

Fixpoint part {T} (ls : list T) :=
match ls with
| [] => [([],[])]
| x::xs => 
  let r := part xs in 
  let add_l := fun p => match p with (l,r) => (x::l,r) end in
  let add_r := fun p => match p with (l,r) => (l,x::r) end in
  List.app (map add_l r) (map add_r r)
end.


Fixpoint partition {ts} (tls : tlist ts) : list (tlist ts * tlist ts) :=
match tls with 
| Hnil => [(Hnil,Hnil)]
| Hcons T ls tls' => 
  let tlspart := partition tls' in 
  let lpart := part ls in 
  concat (map (fun tlp => match tlp with 
  (l,r) => map (fun p => match p with (l',r') => (Hcons T l' l, Hcons T r' r) end) lpart 
  end) tlspart)
end.

Fixpoint mapo {A B} (f : A -> list A -> B) (ls : list A) := 
let mapo := fix k {A B} (f : A -> list A -> B) (l : list A) (r : list A) : list B :=
match r with
| [] => []
| x::xs => 
  f x (List.app l xs) :: k f (List.app l [x]) xs
end in
mapo f [] ls.

Fixpoint npartition (n : nat) {ts} (tls : tlist ts) : list (list (tlist ts)) := 
match n with
| 0 => [[tls]]
| 1 => [[tls]]
| S n' => 
  let r := npartition n' tls in 
  concat (map (fun p => concat (
    mapo (fun t p' => 
    let part := partition t in 
    map (fun '(l,r) => l::r::p') part
    ) p)
  ) r)
end.

(*
Lemma in_concat_app : forall {A} (x : A) l r, In x (l ++ r) -> (In x l \/ In x r).
Proof.
induction l.
- intros. right. simpl in H. exact H.
- intros. simpl in H. inversion H.
  + left. rewrite H0. simpl. left. reflexivity.
  + pose (IHl _ H0).  inversion o.
    * left. simpl. right. exact H1.
    * right.  exact H1.
Qed.

Theorem in_concat : forall {A} (x : A) ll, In x (concat ll) -> exists l', In l' ll /\ In x l'.
Proof.
induction ll.
- intros. inversion H.
- intros. simpl in H. pose (in_concat_app _ a (concat ll) H).
inversion o.
  + exists a. split. simpl. left. reflexivity. exact H0.
  + pose (IHll H0). inversion e. exists x0. inversion H1. split.
    * simpl. right. exact H2.
    * exact H3. 
Qed.

Theorem is_n_part : forall (n : nat) {ts} (tls : tlist ts), forall x, In x (npartition n tls) -> List.length x = n.
Proof.
intros. generalize dependent x. induction n. 
- intros. inversion H. 
- intros. remember (S n). destruct n eqn:E. 
  + rewrite Heqn0 in H. simpl in H. inversion H. 
    * rewrite <- H0, Heqn0. reflexivity.
    * inversion H0.
  + rewrite Heqn0 in H. simpl npartition in H. remember (match n1 with
            | 0 => [[tls]]
            | S _ =>
                concat
                  (map
                     (fun p : list (tlist ts0) =>
                      concat
                        (mapo
                           (fun (t : tlist ts0) (p' : list (tlist ts0)) =>
                            map (fun '(l, r) => l :: r :: p') (partition t)) p)) (npartition n1 tls))
            end).
  remember (concat
         (map
            (fun p : list (tlist ts0) =>
             concat
               (mapo (fun (t : tlist ts0) (p' : list (tlist ts0)) => map (fun '(l, r) => l :: r :: p') (partition t))
                  p)) l)).
  induction l0.
  * inversion H.
  * inversion H. remember (map
             (fun p : list (tlist ts0) =>
              concat
                (mapo (fun (t : tlist ts0) (p' : list (tlist ts0)) => map (fun '(l, r) => l :: r :: p') (partition t))
                   p)) l).
    rewrite Heql0 in H.
    pose (in_concat x l1 H). inversion e. inversion H1. rewrite Heql1 in H2. Check in_map_iff.
    pose (in_map_iff ((fun p : list (tlist ts0) =>
           concat
             (mapo (fun (t : tlist ts0) (p' : list (tlist ts0)) => map (fun '(l, r) => l :: r :: p') (partition t)) p))) l x0).
    inversion i. pose (H4 H2). clear H5.
    inversion e0. inversion H5.
    simpl npartition in IHn. rewrite <- Heql in IHn. pose (IHn _ H7).
admit.
admit.
Admitted.*)
Compute npartition 3 (Hcons string ["a";"b"] Hnil).

(* (x,y) = [x,y) *)
Definition interval := prod nat nat.

Definition inside '(i,n) :=
match i with 
| (x,y) => 
 (x <=? n) && (n <? y)
end.

Definition intersection (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (max x1 x2, min y1 y2)
end.

Definition iadd (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (x1 + x2, y1 + y2)
end.

Definition union (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (min x1 x2, max y1 y2)
end.

Fixpoint make_list {A l X} {x : A} (m : member x l) (t : X) (e : X) : list _ := 
match m with 
| HFirst => t :: tabulate_list (fun _ => e) ((List.length l) - 1) : list X
| HNext x l' m' => e :: (make_list m' t e)
end.

Check HNext.
Definition H : member 3 [1;2;3] := HNext 1 [2;3] (HNext 2 [3] (HFirst )).
Compute make_list (H) 5 0.

 Fixpoint zip {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : list C :=
      match l,l' with
        | x::tl, y::tl' => (f x y)::(zip f tl tl')
        | _, _ => nil
      end.
Definition int_max := 10000.
Print fold_right.
Fixpoint bound {ts K F} (s : Species ts K F) : list interval := 
match s with 
| zero _ _ => tabulate_list (fun _ => (0,0)) (List.length ts)
| one _ _ m => make_list m (0,1) (0,int_max)
| singleton  _ _ m => make_list m (1,2) (0, int_max)
| cprod _ _ s1 s2 => zip intersection (bound s1) (bound s2)
| pprod _ _ s1 s2 => zip iadd (bound s1) (bound s2)
| ssum _ _ s1 s2 => zip union (bound s1) (bound s2)
| srec _ _ _  s' => bound s'
| svar _ _ _ _ => tabulate_list (fun _ => (int_max,int_max)) (List.length ts)
| sind _ _ _ _ hll => 
  let add_unit := tabulate_list (fun _ => (0,0)) (List.length ts) in
  let union_unit :=  tabulate_list (fun _ => (int_max,0)) (List.length ts) in
  fold_right (zip union) union_unit
  (hmap1 (fun l '(c,hl) => fold_right (zip iadd) add_unit (hmap1 (fun x s => bound s) hl)) hll)
end.

Fixpoint tempty {ts} (tls : tlist ts) :=
match tls with 
| Hnil => true
| Hcons _ l tlss => false
end.

Fixpoint lengths {ts} (tls : tlist ts) :=
match tls with 
| Hnil => []
| Hcons _ l tlss => (List.length l) :: lengths tlss
end.

Check tlist.
Fixpoint empty ts : tlist ts :=
match ts with 
| nil => Hnil
| x::xs => Hcons x [] (empty xs)
end.

  Fixpoint fromList' {A ts} (ls : list A) (l : list (tlist ts)) : hlist (fun _ => tlist ts) ls := 
    match ls with 
    | nil => HNil
    | _::ys =>  
      match l with 
      | nil => HCons (empty ts) (fromList' ys nil)
      | x::xs => HCons x (fromList' ys xs)
    end
    end.

Fixpoint lmerge {ls} (hl : hlist list ls) : list (hlist (fun x => x) ls) :=
match hl with
| HNil => [HNil]
| HCons x xs => 
  let r := lmerge xs in 
  concat (map (fun e => map (fun h => e ::: h) r) x)
end.

Compute (lmerge (HCons [1;2] (HCons ["a";"b";"c"] HNil))).

Fixpoint napply {A} (args : list Type) (c : arr' A args) (hl : hlist (fun x => x) args) : A.
destruct args eqn:e.
- simpl in c.  exact c.
- simpl in c. inversion hl. 
  pose (c X). exact (napply A l a X0).
Defined.

Fixpoint collapse {A: Type} {ls} (hl : hlist (fun _ : {x : list Type & arr' A x} => list (list A)) ls) : list A := 
match hl with 
| HNil => []
| HCons x xs => concat x ++ collapse xs
end.

Definition enumerate (n : nat) {ts : list Type} {F} {K} (s : Species ts K F) : 
forall tls : tlist ts, hlist (Species ts K) K -> list (F). 
refine(
(fix enum n {ts : list Type} {F} {K} (s : Species ts K F) : forall tls : tlist ts, hlist (Species ts K) K -> list (F) := 
match n with 
| 0 => fun _ _ => []
| S n' => 
match s in Species _ KK F return forall (s : Species _ KK F) (tls : tlist ts), hlist (Species ts KK) KK -> list (F) with
| zero _ C => fun _ tls _ => []
| one _ _ m => fun _ tls _ => 
  match tget tls m with [] => [tt] | _ => [] end
| singleton _ _ m => fun _ tls _ => 
  match tget' _ ts m with 
  | T => match tget tls m in list _ return list T with 
      | ls => match ls with [x] => [x] | _ => [] end
      end
  end
| pprod _ C' s1 s2 => fun _ tls _ => 
  let sizes := lengths tls in 
  let bounds := bound s in 
  let sb := combine bounds sizes in 
  if forallb inside sb then
  let parts : list (tlist ts * tlist ts) := partition tls in 
   concat (map (fun part => match part with (l,r) => list_prod (enum n' s1 l _) (enum n' s2 r _) end) parts)
  else []
| cprod _ _ s1 s2 => fun _ tls _ => list_prod (enum n' s1 tls _) (enum n' s2 tls _)
| ssum _ _ s1 s2 => fun _ tls  _ => app (map inl (enum n' s1 tls _)) (map inr (enum n' s2 tls _))
| srec _ C' F s' => fun _ tls _ => 
  let sizes := lengths tls in 
  let bounds := bound s in 
  let sb := combine bounds sizes in 
  if forallb inside sb then _
  else []
| svar _ _ F v => fun _ tls _ => []
| sind _ C' tA indA hll =>  fun s'' tls h => 
  let C'' := tA :: C' in
  let hll' :=  hmap (fun l '(c,hl) => (c,hmap (fun _ s' => subst C'' _ s' C' (HCons s'' h)) hl)) hll in 
  let As := hmap (fun args '(c,hl) => 
    let l := projT1 args in
    let cstr := projT2 args in 
    let parts := npartition (List.length l) tls in 
    let As := map (fun part => 
      let hpart := fromList' l part in 
      let all := zipH (fun _ s' p => enum n' s' p h) hl hpart in 
      let merged := lmerge all in 
      let finals := map (fun hl => napply _ cstr hl) merged in 
      finals
    ) parts in 
    As
  ) hll' in
  _
end s
end) n ts F K s).
- exact h.
- exact h.
- exact h.
- exact h.
- exact h. 
- exact h.  
- intros.
  pose ( C'' := nrec F :: C').
  pose (s'' := subst C'' _ s' C' (HCons s1 h)).
  pose (r := enum n' _ _ _  s'' tls h).
  exact (map (rin _  ) r).
- exact (collapse As). 
Defined.

Extraction Language Ocaml.

Definition re_listnat : inductive (list nat ):= [
  existT (arr' (list nat)) [] (nil);
  existT (arr' (list nat)) {{nat; list nat}} (cons)
].

Definition ts : list Type := [nat : Type].
Definition C : list Type := [list nat : Type].
Definition AA := list nat : Type.

Compute arr' AA (projT1 (existT (arr' (list nat)) {{nat; list nat}} (cons))).

Definition a1 := 
  (cons : arr' AA (projT1 (existT (arr' (list nat)) {{nat; list nat}} (cons))), HCons (singleton ts C HFirst) (HCons (svar ts C _ HFirst) HNil)).
Definition a2 := (nil, HNil) : (arr' AA (projT1 (existT (arr' (list nat)) [] (nil)))) * hlist (Species ts C) [].

Definition a3  := a2 ::: a1 ::: HNil :  
  hlist (fun c => prod (arr' AA (projT1 c)) (hlist (Species ts ({{AA}})) (projT1 c : list Type))) 
  re_listnat.
Check a3.

Definition natlist_s  := 
sind ts [] (list nat) re_listnat a3.
Definition tls0 : tlist ts := Hcons nat [1;2;3;4] Hnil.

Definition hll' :=  hmap (fun l '(c,hl) => (c,hmap (fun _ s' => subst C _ s' [] (HCons natlist_s HNil)) hl)) a3.
Compute a3.
Compute hll'.
Definition part1 := nth 1 (npartition 0 tls0) [].
Definition hpart := fromList' ([] : list Type) part1.
Definition ctx : hlist (Species ts C) C := HCons (svar ts C  _ HFirst) HNil.
Definition all := zipH (fun _ s' p => enumerate 30 s' p ctx) (snd a2) hpart.
Definition merged := lmerge all.
Definition finals := map (fun hl => napply _ (nil : arr' AA (projT1 (existT (arr' (list nat)) [] (nil)))) hl) merged.
Compute part1.
Compute hpart.
Compute all.
Compute merged.
Compute finals.

Compute enumerate 20 natlist_s tls0 HNil.


(* lists *)

Definition ts0 : list Type := [nat : Type].
Definition F1 := (fun X => sum unit (prod (tget' _ ts HFirst) X)).
Instance F1F : Functor F1 := 
{
  liftF := fun X Y f x => 
  match x with 
  | inl tt => inl tt
  | inr (a,x') => inr (a, f x')
  end
}.
Definition C1 := [nrec F1].
Definition s := srec ts []  F1 (ssum ts C1 (one ts C1 HFirst) (pprod ts C1 (singleton ts C1 HFirst) (svar ts C1 (nrec F1) (HFirst)))).
Definition tls : tlist ts := Hcons nat [1;2;3] Hnil.
Definition C0 : hlist (Species ts []) [] := HNil.

Definition e := enumerate 20 s tls C0.
Compute e.

Compute npartition 2 (Hcons string ["a";"b"] tls).
Compute bound s.
Compute e.

Extraction "enum.ml" e.


(* multi-sorted product *)
Definition ts2 : list Type := [nat : Type; string : Type].
Definition tls2 : tlist ts2 := Hcons nat [1;2] (Hcons string ["a";"b";"c"] Hnil).
Definition s2 := pprod ts2 [] (ssum ts2 [] (singleton ts2 [] HFirst) (singleton ts2 [] (HNext nat [string] HFirst))) (singleton ts2 [] HFirst).
Definition C2 : hlist (Species ts2 []) [] := HNil.
Compute enumerate 100 s2 tls2 C2.
Compute (List.length (enumerate 3 s2 tls2 C2)).

(* rose trees *)
Definition rlistF A := (fun X => sum unit (prod A X)).
Instance rlistFF : forall A, Functor (rlistF A) :=
{
  liftF := fun X Y f m => 
   match m with 
   | inl tt => inl tt
   | inr (a,x) => inr (a, f x)
   end
}.
Definition rlist A := nrec (rlistF A).
Check @liftF.
Definition sizet {A} (m : A) := 0.
Definition rnil {A} : rlist A := fun X f => f (inl tt).
Definition rcons {A} (a : A) (l : rlist A) : rlist A := fun X f => f (inr (a, l X f)).
Definition l1 := rcons nat (rcons string rnil).
Fixpoint k  {X Y : Type} (f : X -> Y) (m : rlist X) (d : nat)  : rlist Y :=
  match d with 
  | 0 => rnil
  | S d' => 
  let out := rout (rlistF X) m in
  match out with
  | inl tt => rin (rlistF Y) (inl tt)
  | inr (a, x) => rin (rlistF Y) (inr (f a, k f x d'))
  end
  end.

Compute k (fun X => sum unit X) l1 100.

Instance ListF : Functor (rlist) := 
{
  liftF := fun X Y f m => 
  let out := rout (rlistF X) m in
  match out with
  | inl tt => rin (rlistF Y) (inl tt)
  | inr (a, x) => rin (rlistF Y) (inr (f a, k f x 1000))
  end
}.

Definition F3 := (fun X => sum unit (prod (tget' _ ts HFirst) (rlist X))).
Instance F3F : Functor F3 := 
{
  liftF := fun X Y f x => 
  match x with 
  | inl tt => inl tt
  | inr (a, xl) => inr (a, liftF f xl)
  end
}.
Definition C3 := [nrec F3].
Definition C3' := [rlist (nrec F3) ;nrec F3].
Definition ts3 : list Type := [nat : Type].
Definition tls3 : tlist ts3 := Hcons nat [1;2] Hnil.
Definition t : member (nrec F3) C3' := HNext _ _ HFirst.
Definition s3 := srec ts3 []  F3 (ssum ts3 C3 (one ts3 C3 (HFirst)) 
  (pprod ts3 C3 (singleton ts3 C3 HFirst) 
    (srec ts3 C3 (rlistF (nrec F3)) (ssum ts3 C3' (one ts3 C3' HFirst) (pprod ts3 C3' ((svar ts3 C3' (nrec F3) (t))) ((svar ts3 C3' (rlist (nrec F3)) HFirst)) ) ) )
  )).


Definition Empty : hlist (Species ts3 []) [] := HNil.

Compute enumerate 20 s3 tls3 Empty. 

Extraction "enum.ml" e.

Fixpoint all_perm {X : Type} (l : list X) :=
match l with 
| [] => [[]]
| [x] => [[x]]
| x::xs => 
  let perms := all_perm xs in 
  fold_left (fun ps perm => 
    let perms' :=  
      tabulate_list (fun i => 
       let (a,b) := split_i i perm in List.app (List.app a  [x])  b
      ) (1 + List.length perm)
    in List.app ps perms') perms []
end.

Compute all_perm [1;2;3;4;5;6;7].

(* end; ignore below *)
Run TemplateProgram (t <- tmQuoteRec (list nat);; r <- tmEval all t;; tmPrint r).

Check tmQuote (list).
Run TemplateProgram (t<- (tmQuote (nat -> nat));; t <- tmUnquoteTyped Set t;; tmPrint t).

Definition str_eq s1 s2 := match string_dec s1 s2 with left _ => true | _ => false end. 
Definition ascii_eq c1 c2 := match ascii_dec c1 c2 with left _ => true | _ => false end. 

Fixpoint map_ {A B} (f : A -> TemplateMonad B) (l : list A) : TemplateMonad (list B) :=
match l with 
| [] => tmReturn []
| x::xs => r <- f x ;; rs <- map_ f xs ;; tmReturn (r::rs)
end.

Fixpoint split_until (f : ascii -> bool) s :=
match s with 
| EmptyString => (EmptyString, EmptyString)
| String c xs => 
  if f c then (String c EmptyString, xs)
  else
  let (a,b) := split_until f xs in 
  (String c a,b)
end.

Compute split_until (ascii_eq ".") "fd.a".
Fixpoint strip s dummy {struct dummy} := 
let (a,b) := split_until (ascii_eq ".") s in
match b with 
| EmptyString => s
| _ => match dummy with 
  | 0 => EmptyString
  | S n' => strip b n'
  end
end.

Compute strip "Coq.Init.Datatypes.nat" 100.
 
Check fold_left.

Print prod.



Fixpoint enumerate (ind : Type) (n : nat) : TemplateMonad (list ind) := 
tm <- tmQuote ind;; match tm with 
| tInd ind' _ => 
let qualified := inductive_mind ind' in
let indName := strip qualified (length qualified) in
decl <- tmQuoteInductive indName ;;
indBody <- 
  match find (fun body => str_eq (ind_name body) indName) (ind_bodies decl) with 
  | Some e => tmReturn e
  | _ => tmFail (append "fail" indName)
  end;;
let find_base := (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => true | _ => false end) cstrs)
in
let find_ind := 
  (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => false | _ => true end) cstrs)
in 
(match n with 
| 0 => map_ (fun cstr => match cstr with (tn,_,_) => tmUnquoteTyped ind (tConstruct (mkInd indName 0) 0 [])  end) 
    (find_base indBody)
| S n' => 
  let cstrs := find_ind indBody in 
  let flatten := fix f tm' := 
    match tm' with 
    | tRel _ => [tm]
    | tInd ind _ => tm'
    | tProd _ tm1 tm2 => f tm1 ++ f tm2
    end
  in
  let get_args l := removelast (flatten l) in
  map_ (fun acc cstr => match cstr with 
    | (name, tm, arity) => 
      all_args <- map_ (fun arg => ty <- tmUnquote arg;; enumerate (projT2 ty) n') (get_args tm);;
      let combined := map (fun args => 
          
    end) cstrs 
end)
| _ => tmFail "non inductive type"
end.
  
Check enumerate.
Run TemplateProgram (r <- enumerate nat 0;; tmPrint r).

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Class Ord A `{Eq A} : Type :=
  {
    le : A -> A -> bool
  }.

Module S := Make Nat_as_OT.

Module SP := WPropertiesOn Nat_as_OT S.

Module SF := WFactsOn Nat_as_OT S.

Fixpoint tabulate f n := 
match n with 
| 0 => S.empty
| S n => S.add (f n) (tabulate f n)
end.

Definition list_max {X : Type} (f : X -> X -> bool) l d := fold_left (fun acc e => if f acc e then acc else e) l d.

Fixpoint all_subset (s : S.t) := 
S.fold (fun e subsets => subsets ++ (map (fun s => S.add e s) subsets)) s [S.empty].





Definition algorithm (instance solution metric : Type) f 
 (verifier : instance -> solution -> Prop)
 (eval : solution -> metric) 
 (better : metric -> metric -> Prop) := 
forall (I : instance) (Sol Cand : solution), 
  (f I = Some Sol -> verifier I Sol /\ ((verifier I Cand) -> better (eval Sol) (eval Cand)))
/\
  (f I = None -> ~exists Cand', verifier I Cand').

Definition synthesize (instance : Type) (solution : Type) (metric : Type)
(checker : instance -> solution -> bool) 
(eval : solution -> metric) 
(better : metric -> metric -> bool) 
(gen_space : instance -> list solution) 
: instance -> option solution := 
fun I => 
let candidates := filter (checker I) (gen_space I) in 
let ranks := map (fun cand => (eval cand, cand)) candidates in 
match ranks with 
| [] => None
| x::xs => Some (snd (list_max (fun e1 e2 => match e1, e2 with | (s1,_), (s2,_) => better s1 s2 end) xs x))
end.

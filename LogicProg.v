(* Exercises from the Logic Programming chapter of CPDT. *)

Require Import List Omega.
Require Import CpdtEx.CpdtTactics.

(* Operational type classes *)

Class GProd (T : Type) := prod : T -> T -> T.
Class GId (T : Type) := id : T.
Class GInv (T : Type) := inv : T -> T.

Notation "a ∗ b" := (prod a b) (at level 50, left associativity).

Class Group (T : Type) (prod : GProd T) (id : GId T) (inv : GInv T) :=
  MkGroup {
      assoc (a b c : T) : (a ∗ b) ∗ c = a ∗ (b ∗ c);

      right_id (a : T) : a ∗ id = a;

      right_inverse (a : T) : a ∗ (inv a) = id;                
    }.


Section group_laws.
  Variable (T : Type).
  Context `{Group T}.

  (* Hint given in the book *)

  Lemma mult_both a b c d1 d2:
      a ∗ c = d1 ->
      b ∗ c = d2 ->
      a = b ->
      d1 = d2.
  Proof. crush. Qed.
  
  Hint Extern 100 (_ = _) =>
    match goal with
    | [_ : True |- _ ] => fail 1
    | _ => assert True by constructor; eapply mult_both
    end : core.

  (* Additional hints *)

  Hint Resolve assoc : core.
  Hint Resolve right_id : core.
  Hint Resolve right_inverse : core.

  (* Characterizing identity *)
  Lemma equals_id a b :
    b = inv a ->
    a ∗ b = id.
  Proof. crush. Qed.

  Hint Resolve equals_id : core.

  Lemma simpl_inv a b :
    a ∗ id = a ->
    b ∗ inv b = id ->
    a ∗ b ∗ inv b = a ∗ (b ∗ inv b) ->
    a ∗ b ∗ inv b = a.
  Proof. crush. Qed.

  Hint Resolve simpl_inv : core.
  
  Lemma chr_id a : (a ∗ a = a) -> (a = id).
  Proof. eauto 7. Qed.

  Hint Resolve chr_id : core.
  
  (* Left inverse *)

  Lemma left_inv a : (inv a) ∗ a = id.
  Proof. eauto 8. Qed.

  Hint Resolve left_inv : core.

  (* Left identity *)

  Lemma left_id_hint a :
    a ∗ id = a ->
    inv a ∗ a = id ->
    (a ∗ inv a) ∗ a = a ∗ (inv a ∗ a) ->
    id = (a ∗ inv a) -> 
    id ∗ a = a.
  Proof. crush. Qed.

  Hint Resolve left_id_hint : core.
  
  Lemma left_id a : id ∗ a = a.
  Proof. eauto 6. Qed.

  Hint Resolve left_id : core.

  (* Uniqueness of left identity *)

  Lemma uniq_left_id p a :
    p ∗ a = a ->
    p = id.
  Proof. eauto 7. Qed. 

  Hint Resolve uniq_left_id : core.

  (* Uniqueness of right inverse *)

  Lemma uniq_right_inv_hint a b c :
    c ∗ (a ∗ b) = b ->
    c ∗ id = inv a ->
    a ∗ b = id ->
    b = inv a.
  Proof. crush. Qed.

  Hint Resolve uniq_right_inv_hint : core.
  
  Lemma uniq_right_inv a b :
    a ∗ b = id ->
    b = inv a.
  Proof. eauto. Qed.
 
  
End group_laws.


    
                                                     
    


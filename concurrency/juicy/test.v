From iris.heap_lang Require Import lang notation spawn par.
From iris.heap_lang Require Import lang proofmode notation par.
From iris.base_logic.lib Require Export invariants token.
From iris.algebra Require Import excl.
From iris.heap_lang Require Import lang proofmode notation.

Section heaplang.
Context `{!heapGS Σ}.
Context `{!tokenG Σ}.

Definition mk_lock : val :=
  λ: <>, ref #false.

Definition locked γ : iProp Σ := token γ.

Definition lock_inv γ l P : iProp Σ :=
  ∃ b : bool, l ↦ #b ∗
  if b then True
  else locked γ ∗ P. 

(* Gradescope review:　
This is a good start. The actual invariant probably needs to have ghost state to 
track what each thread knows about the state of the lock, so we can say that, 
e.g., when `A` sets `fst flags` to `true` then it will stay true until we call `P_rls_A`.*)

Definition Boolean_Allocated l := 
  (l ↦ #false ∨ l ↦ #true)%I.  

Inductive Step : Set :=
  step_0 | step_1 | step_2 | step_3 | step_4. 

Definition steps_to_assignments (step_A step_B : Step)(f1 f2 v: bool) : Prop :=
  match step_A, step_B with
  | step_0, step_0 => True
  | step_0, step_1 => f2 = true
  | step_0, step_2 => f2 = true /\ v = true
  | step_0, step_3 => False
  | step_0, step_4 => true /\ v = true

  | step_1, step_0 => True
  | step_1, step_1 => f1 = true /\ f2 = true
  | step_1, step_2 => f1 = true /\ f2 = true /\ v = true
  | step_1, step_3 => f1 = true /\ f2 = true /\ v = true
  | step_1, step_4 => f1 = true /\ f2 = true /\ v = true

  (* | step_2, step_0 => (flags.1 ↦ #true) ∗ (Boolean_Allocated flags.2) ∗
              (victim ↦ #false) ∗ C ∗ token γ
  | step_2, step_1 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (victim ↦ #false) ∗ C ∗ token γ
  | step_2, step_2 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (Boolean_Allocated victim) ∗ C ∗ token γ
  | step_2, step_3 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗ 
              (∃ v , victim ↦ v) ∗ C ∗ token γ
  | step_2, step_4 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (∃ v , victim ↦ v) 

  | step_3, step_0 => False
  | step_3, step_1 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (victim ↦ #false) ∗ C ∗ token γ
  | step_3, step_2 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (Boolean_Allocated victim) ∗ C ∗ token γ
  | step_3, step_3 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗
              (Boolean_Allocated victim) ∗ C ∗ token γ
  | step_3, step_4 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗ 
              (Boolean_Allocated victim)

  | step_4, step_0 => (flags.1 ↦ #true) ∗ (Boolean_Allocated flags.2) ∗ (victim ↦ #false) 
  | step_4, step_1 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗ (victim ↦ #false) 
  | step_4, step_2 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗ (Boolean_Allocated victim) 
  | step_4, step_3 => (flags.1 ↦ #true) ∗ (flags.2 ↦ #true) ∗ (Boolean_Allocated victim)   *)
  (* >>> This is the most interesting result, but I just admitted it?! <<< *)
  | step_4, step_4 => False 
  | _, _ => False
  end.   

(* >>> Assuming each thread run aquire at most once. <<< *)
(* Definition P_lock_inv (flags : loc * loc) (victim : loc)
  (γ : gname) (C : iProp Σ) : iProp Σ :=
  ∃ (f1 f2 v : bool) (step_A step_B : Step),
    (flags.1 ↦ #f1 ∗ flags.2 ↦ #f2 ∗ victim ↦ #v) ∗
      ⌜steps_to_assignments step_A step_B f1 f2 v⌝ ∗
      match step_A, step_B with
      | step_4, _ => True
      | _, step_4 => True
      | _, _ => token γ ∗ C
      end.
*)

Definition P_lock_inv (flags : loc * loc) (victim locked : loc)
  (γ : gname) (C : iProp Σ) : iProp Σ :=
  ∃ (f1 f2 v : bool) (step_A step_B : Step) (b : bool),
    (flags.1 ↦ #f1 ∗ flags.2 ↦ #f2 ∗ victim ↦ #v ∗ locked ↦ #b) ∗
      ⌜steps_to_assignments step_A step_B f1 f2 v⌝ ∗
      (if b then True else token γ ∗ C).


Definition P_loop_A (flags : loc * loc)(victim : loc) : expr :=
  (rec: "loop" <> := 
(* state 2 *)
    if: (!#(snd flags) = #true) 
(* state 3 *)
    && (!#victim = #false) then
(* state 2 *)
      "loop" #()
(* state 4 *)
    else #()) #().

Definition P_loop_B (flags : loc * loc)(victim : loc) : expr :=
  (rec: "loop" <> := 
(* state 2 *)
    if: (!#(fst flags) = #true) 
(* state 3 *)
    && (!#victim = #true) then
      "loop" #()
(* state 4 *)
    else #()) #().

(* >> How to guarantee that flags and victim are different locations? << *)
(* >> This can be assured in the invariant, where they are different locations. <<*)
Definition P_acq_A (flags : loc * loc)(victim : loc) : expr := 
(* state 0 *)
  #(fst flags) <- #true ;; 
(* state 1 *)
  #victim <- #false ;;
(* state 2 *)
  P_loop_A flags victim.
(* state 4 *)

Definition P_acq_B (flags : loc * loc)(victim : loc) : expr := 
(* state 0 *)
  #(snd flags) <- #true ;; 
(* state 1 *)
  #victim <- #true ;;
(* state 2 *)
  P_loop_B flags victim.
(* state 5 *)

Definition P_rls_A (flags : loc * loc) : expr :=   
  #(fst flags) <- #false.  
Definition P_rls_B (flags : loc * loc) : expr :=   
  #(snd flags) <- #false.

(* Definition P_rls_A (flags : loc * loc)(victim : loc) : val :=   
  λ: <>,
  #(fst flags) <- #false. *)
(* Definition P_rls_B (flags : loc * loc)(victim : loc) : val := 
  λ: <>,
  #(snd flags) <- #false. *)

Let N := nroot .@ "lock".

(*If flags and victim are allocated, then after acquring a lock, 
the thread should hold the lock and the critical zone C. *)

Theorem P_acq_A_spec (flags : loc * loc)(victim locked: loc) γ C locked1 :
  {{{ inv N (P_lock_inv flags victim locked1 γ C) }}} P_acq_A flags victim {{{ RET #(); token γ ∗ C}}}.
Proof.
  intros. 
  iIntros "#Precondition Postcondition".   
  rewrite /P_acq_A.
  rewrite /P_lock_inv. 
  wp_bind (#flags.1 <- #true)%E.
  
  Search "later".
  Check bi.later_exist_except_0.
  iInv N as (f1 f2 v) "H" "Hclose".
  rewrite bi.later_exist_except_0.
  iMod "H" as "[%s1 Pre]".
  rewrite bi.later_exist_except_0.
  iMod "Pre" as "[%s2 Pre]".
  iDestruct "Pre" as (?) "((Pre & ? & ? &?) & ? & ?)".
  wp_store.
  Locate "◇".
  iDestruct "H" as (step_A step_B b) "H".
  iDestruct "H" as (?) "?". 
  wp_store.
  
  wp_store.
  iModIntro. 
  destruct lckd  eqn: lckd_case.
  - (* lckd = true *) 
  iSplitL "Hf1 Hf2 Hv Hlocked". 
  (* Closing the inv *)
  { iModIntro. iFrame. }
  wp_seq.      
  wp_bind (#victim <- #0)%E. 
  iInv "Precondition" as (f1' f2' lckd' vic') "(Hf1' & Hf2' & Hv' & Hlocked' & HC')". 
  wp_store. 
  iModIntro. 
  iSplitL "Hf1' Hf2' Hv' Hlocked'". 
  (* Closing the inv *)
  { iFrame. iExists 0. iModIntro. iFrame.
  (* >>> Cannot proceed, bc we need info about locked from another thread. <<< *)
  admit.
  }
  wp_seq.
  clear f1 f2 f1' f2' vic vic'. 
  
  (* Finally we get the while loop. *)
  (* wp_apply (P_loop_A_spec flags victim).  *)
  (* Closing the inv *)
  (* { done. }
  iApply "Postcondition". *)
Admitted.  *)

(* Definition test_prog (flags : loc * loc)(victim : loc) : expr :=
  let: "x" := ref #0 in
  #flags.1 <- #false ;;
  #flags.2 <- #false ;;
  #victim <- #0 ;;
  Fork (
    P_acq_A flags victim ;;
    "x" <- #17;;
    "x" <- !"x" - #6;;
    P_rls_A flags victim #()
  );;
    P_acq_B flags victim ;;
    "x" <- #97;;
    "x" <- !"x" - #6;;
    P_rls_B flags victim #();;
    !"x".  *)

(* Since two threads cannot intervene, x cannot be deducted twice. *)
(* Lemma test_spec (flags : loc * loc)(victim : loc) : 
  {{{inv N (P_lock_inv flags victim)}}} test_prog flags victim {{{x, RET x; ⌜x = # 11 ∨ x = #91⌝ }}}. 
Proof.
  unfold test_prog.
Admitted. 
 *)

End heaplang. 

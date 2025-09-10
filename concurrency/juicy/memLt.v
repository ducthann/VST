(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SequentialClight.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.canon.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
(*Require Import VST.concurrency.juicy.juicy_machine.*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
(*Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.*)
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

  (*
    Hlt : permMapLt max (getMaxPerm m)

    m1 = (getCurPerm m) 
    m2 = (getCurPerm (restrPermMap Hlt))

   *)
  Definition memLt m1 m2 := permMapLt (getCurPerm m1) (getCurPerm m2) /\
                              Mem.mem_contents m1 = Mem.mem_contents m2 /\
                              Mem.nextblock m1 = Mem.nextblock m2.

  Lemma memPerm_permMapLt m1 m2:
    permMapLt (getCurPerm m1) (getCurPerm m2) ->
    ∀ (b0 : block) (ofs : Z) (p : permission),
      Mem.perm m1 b0 ofs Cur p → Mem.perm m2 b0 ofs Cur p.
  Proof.
    intros HpermLt b???.
    rewrite /Mem.perm /Mem.perm_order' in H |-*.
    rewrite /permMapLt /Mem.perm_order'' /getCurPerm in HpermLt.
    specialize (HpermLt b ofs).
    rewrite ! Maps.PMap.gmap in HpermLt.
    destruct ((Mem.mem_access m2) # b ofs Cur);
    destruct ((Mem.mem_access m1) # b ofs Cur); try contradiction.
    eapply perm_order_trans; eauto.
  Qed.
  
  Lemma memLt_valid_pointer:
    forall m1 m2 b z, 
      memLt m1 m2 ->
      Mem.valid_pointer m1 b z = true ->
      Mem.valid_pointer m2 b z = true.
  Proof.
    intros.
    destruct H as [? [? ?]].
    unfold Mem.valid_pointer in *.
    destruct (Mem.perm_dec m1 b z Cur Nonempty); inv H0.
    destruct (Mem.perm_dec m2 b z Cur Nonempty); try reflexivity.
    contradiction n. clear n.
    eapply memPerm_permMapLt; eauto.
  Qed.

  Lemma memLt_weak_valid_pointer:
    forall m1 m2 b z,
      memLt m1 m2 -> Mem.weak_valid_pointer m1 b z = true -> Mem.weak_valid_pointer m2 b z = true.
  Proof.
    intros; unfold Mem.weak_valid_pointer in *.
    rewrite -> orb_true_iff in *.
    destruct H0; [left|right]; eapply memLt_valid_pointer; eauto.
  Qed.

  (*
  Lemma unaryop_mem_lessdef {op u t m v m2}
    (V: Cop.sem_unary_operation op u t m = Some v)
    (M : memLt m m2):
    Cop.sem_unary_operation op u t m2 = Some v.
  Proof. destruct op; simpl; inv V; try econstructor.
         unfold sem_notbool, bool_val in *.
         remember (classify_bool t) as c.
         destruct c; trivial.
         destruct u; trivial.
         simple_if_tac; trivial.
         destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H0.
         rewrite (mem_lessdef_weak_valid_pointer _ _ _ _ M); trivial.
  Qed.
*)

  Lemma unaryop_memLt {op u t m v m2}
    (V : Cop.sem_unary_operation op u t m = Some v)
    (M : memLt m m2):
    Cop.sem_unary_operation op u t m2 = Some v.
  Proof.
    rewrite /Cop.sem_unary_operation in V |-*.
    destruct op; simpl; inv V; try econstructor.
    rewrite /Cop.sem_notbool /Cop.bool_val in H0 |-*.
    remember (Cop.classify_bool t) as c.
    destruct c; auto.
    destruct u; auto.
    simple_if_tac; auto.
    destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H0.
    rewrite (memLt_weak_valid_pointer _ _ _ _ M); auto.
  Qed.
  
  Lemma sem_cast_memLt {v t d m m2 v'} (M : memLt m m2):
    Cop.sem_cast v t d m = Some v' -> Cop.sem_cast v t d m2 = Some v'.
  Proof.
    unfold Cop.sem_cast; intros.
    destruct (Cop.classify_cast t d); trivial.
    destruct v; trivial.
    simple_if_tac; trivial.
    destruct (Mem.weak_valid_pointer m _ _) eqn: Hm; inv H.
    rewrite (memLt_weak_valid_pointer _ _ _ _ M); trivial.
  Qed.
  
  Lemma sem_binarith_memLt {f1 f2 f3 f4 v1 t1 v2 t2 v' m m2} (M : memLt m m2):
    Cop.sem_binarith f1 f2 f3 f4 v1 t1 v2 t2 m = Some v' ->
    Cop.sem_binarith f1 f2 f3 f4 v1 t1 v2 t2 m2 = Some v'.
  Proof.
    unfold Cop.sem_binarith; intros.
    destruct (Cop.sem_cast v1 t1 _ m) eqn: Hcast1; inv H.
    destruct (Cop.sem_cast v2 t2 _ m) eqn: Hcast2; inv H1.
    erewrite !(sem_cast_memLt  M); eauto.
  Qed.

  Lemma cmplu_bool_memLt {v1 v2 f b m m2} (M : memLt m m2):
    Val.cmplu_bool (Mem.valid_pointer m) f v1 v2 = Some b ->
    Val.cmplu_bool (Mem.valid_pointer m2) f v1 v2 = Some b.
  Proof.
    unfold Val.cmplu_bool; intros. forget Archi.ptr64 as ptr64.
    destruct v1, v2; trivial; simple_if_tac; inv H;
    repeat match goal with H:
        context[if ?b then _ else _] |- _ =>
            destruct b eqn: ?Hb; inv H;
            try apply andb_true_iff in Hb as [-> Hp];
            try (rewrite orb_true_iff in Hp; destruct Hp as [Hp | Hp];
                 rewrite (memLt_valid_pointer _ _ _ _ M Hp); rewrite ?orb_true_r; auto) end.
    * apply andb_true_iff in Hb0 as [Hp1 Hp2].
      apply orb_true_iff in Hp1 as [Hp1 | Hp1]; apply orb_true_iff in Hp2 as [Hp2 | Hp2];
        rewrite (memLt_valid_pointer _ _ _ _ M Hp1);
        rewrite (memLt_valid_pointer _ _ _ _ M Hp2);
        rewrite ?orb_true_r; auto.
    * apply andb_true_iff in Hb0 as [Hp1 Hp2].
      rewrite (memLt_valid_pointer _ _ _ _ M Hp1);
      rewrite (memLt_valid_pointer _ _ _ _ M Hp2); auto.
   Qed.
  
  Lemma cmp_ptr_lessdef {v1 v2 f b m m2} (M : memLt m m2):
    Cop.cmp_ptr m f v1 v2 = Some b ->
    Cop.cmp_ptr m2 f v1 v2 = Some b.
  Proof.
  Admitted.
  
  Lemma sem_cmp_mem_lessdef {f v1 t1 v2 t2 b m m2} (M : memLt m m2):
    Cop.sem_cmp f v1 t1 v2 t2 m = Some b -> Cop.sem_cmp f v1 t1 v2 t2 m2 = Some b.
  Proof.
    unfold Cop.sem_cmp; intros.
    destruct (Cop.classify_cmp t1 t2).
    destruct v1; inv H.
  Admitted.

  Lemma binaryop_memLt {ge op v1 t1 v2 t2 m v m2}
    (V: Cop.sem_binary_operation ge op v1 t1 v2 t2 m = Some v)
    (M: memLt m m2):
    Cop.sem_binary_operation ge op v1 t1 v2 t2 m2 = Some v.
  Proof.
    destruct op; simpl; inv V; try econstructor.
    + rewrite /Cop.sem_add in H0 |-*.
      remember (Cop.classify_add t1 t2) as c.
      destruct c.
      destruct v1; auto. destruct v1; auto. destruct v1; auto. destruct v1; auto.
      simpl.
      erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_sub in *.
      remember (Cop.classify_sub t1 t2) as c.
      destruct c.
      destruct v1; trivial. destruct v1; trivial. destruct v1; trivial.
      erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_mul in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_div in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_mod in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_and in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_or  in *. erewrite sem_binarith_memLt; eauto.
    + unfold Cop.sem_xor in *. erewrite sem_binarith_memLt; eauto.
    + erewrite sem_binarith_memLt; eauto.
      
+ erewrite sem_cmp_mem_lessdef; eauto.
+ erewrite sem_cmp_mem_lessdef; eauto.
+ erewrite sem_cmp_mem_lessdef; eauto.
+ erewrite sem_cmp_mem_lessdef; eauto.
+ erewrite sem_cmp_mem_lessdef; eauto.
+ erewrite sem_cmp_mem_lessdef; eauto.
Qed.
*)
    

  Lemma memLt_loadbytes : forall m1 m2 b ofs len v,
      memLt m1 m2 ->
      Mem.loadbytes m1 b ofs len = Some v -> Mem.loadbytes m2 b ofs len = Some v.
  Proof.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes; intros.
    if_tac in H0; inv H0.
    destruct H as (HpermLt & ? & ?).
    assert ( ∀ (b0 : block) (ofs : Z) (p : permission),
               Mem.perm m1 b0 ofs Cur p → Mem.perm m2 b0 ofs Cur p) as Hmem.
    { eapply memPerm_permMapLt; auto. }
    rewrite if_true; auto.
    2 :{ intros ??; auto. }
    do 2 f_equal.
    rewrite H; auto.
  Qed.

  Lemma eval_expr_eval_lvalue_memLt ge ve te m:
     (forall (e : expr) (v : val),
        eval_expr ge ve te m e v ->
        forall m2 : mem, memLt m m2 -> eval_expr ge ve te m2 e v) /\
     (forall (e : expr) (b : block) (i : ptrofs) (bf: bitfield),
        eval_lvalue ge ve te m e b i bf ->
        forall m2 : mem, memLt m m2 -> eval_lvalue ge ve te m2 e b i bf).
Proof.
  apply eval_expr_lvalue_ind; intros; try solve [econstructor; eauto].
  + econstructor; eauto.
    eapply unaryop_memLt; eauto.
  + econstructor; eauto. (* eapply binaryop_mem_lessaloc; eauto. *) admit.
  + econstructor; eauto. rewrite <- H1. symmetry. 
    (* apply sem_cast_mem_lessaloc; trivial. *) admit.
  + econstructor; eauto.
    destruct H2 as [M1 [M2 M3]].
    inv H1; simpl in *.
  - eapply deref_loc_value; eauto.
    simpl.
    destruct (Mem.load_loadbytes _ _ _ _ _ H3) as [vals [X Y]]; subst.
    apply Mem.load_valid_access in H3.
    destruct H3.
    eapply Mem.loadbytes_load; trivial.
    eapply memLt_loadbytes; eauto.
    repeat split; auto.
  - apply deref_loc_reference; trivial.
  - apply deref_loc_copy; trivial.
  - apply deref_loc_bitfield; auto.
     inv H2. econstructor; eauto.
    destruct (Mem.load_loadbytes _ _ _ _ _ H7) as [vals [X Y]]; subst.
    apply Mem.load_valid_access in H7. destruct H7.
    unfold Mem.loadv.
    rewrite Y.
    eapply Mem.loadbytes_load; trivial.
    eapply memLt_loadbytes; eauto.
    repeat split; auto.
  Admitted.

 
  
  Lemma cl_step_step m1 m2 (c c': CC_core):
    forall m1', memLt m1 m2 ->
           cl_step ge c m1 c' m1' -> exists m2', cl_step ge c m2 c' m2' /\ memLt m1' m2'.
  Proof.
    intros.
    inv H0.
    eexists; esplit.
    eapply step_assign; eauto.
    eapply eval_expr_eval_lvalue_memLt; eauto.
    


    
    Search cl_step.
    econstructor.
    eapply Clight_mem_lessdef.eval_expr_eval_lvalue_mem_lessalloc; eauto.
    rewrite /mem_lessdef.mem_lessalloc.
    {
      rewrite /memLt in H.
      destruct H as (Hperm & Hcontent & Hnextblock).
      repeat split.
      - Transparent Mem.loadbytes.
        rewrite /Mem.loadbytes.
        extensionality b1 ofs1 n1.
        admit.
      - Transparent Mem.perm.
        rewrite /Mem.perm.
        extensionality b1 ofs1 n1.
        f_equal.
        Search Mem.mem_access. 
        

  Admitted.

  Lemma permMapLt_cur: forall p m (Hlt : permMapLt (getCurPerm p) (getCurPerm m)),
      permMapLt (getCurPerm p) (getMaxPerm m).
  Proof.
    rewrite /permMapLt.
    intros.
    specialize (Hlt b ofs).
    eapply mem_lemmas.po_trans; eauto.
    rewrite /getMaxPerm /getCurPerm.
    repeat (rewrite Maps.PMap.gmap).
    apply Mem.access_max.
  Qed.
  
  Lemma jsafe_jsafe_perm : forall `{!VSTGS unit Σ} max E z c p, p = max ->
    jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c ⊢ jsafe_perm max E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    subst; pose proof (partial_order_antisym mem_equiv.permMapLt_order _ _ Hlt Hmax) as Heq.
(*    iDestruct "S" as "((% & (% & %Hlock) & Hm) & Hz)". *)
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      iIntros "!>".
      eapply (cl_step_step _ _) in H.
      destruct H as (? & ?).
      iExists _, x.
      iSplit.
      {
        destruct H.
        iPureIntro.
        simpl. done.
      }
      destruct H as (Hcl & HmemLt).
      rewrite /memLt in HmemLt.
      destruct HmemLt as (Hperm & Hcontent & Hnext).
      iSplitL "S".
      { iExists (getCurPerm m').
        assert (permMapLt (getCurPerm m') (getMaxPerm x)) as Hltm'.
        { apply permMapLt_cur; auto. }
        iExists Hltm'.
        
        Check restrPermMap_idem.

          Search permMapLt getCurPerm.
          Check restr_Max_eq.
          Search permMapLt .



          


            Hperm : permMapLt (getCurPerm m') (getCurPerm x)

                      permMapLt (getCurPerm m') (getMaxPerm x)
                 
          rewrite /permMapLt.

          rewrite restr_Max_eq; apply cur_lt_max. }

        
        rewrite /state_interp.
        
        rewrite /memLt in HmemLt.
        Search restrPermMap.
      
      iIntros "!>"; iExists _, _; iSplit; first done.
      iSplitL "S".

      
      admit.
      Search permMapLt.
      Check mem_equiv.useful_permMapLt_trans.
      Search mem_equiv.access_map_equiv.
      Search getCurPerm restrPermMap.
      Check  mem_equiv.permMapLt_equiv.
      assert (permMapLt p1 (getMaxPerm m)) as Hlt1.
      { eapply mem_equiv.permMapLt_equiv; done. }
      rewrite /getCurPerm /=.
      extensionality.
      
        
        
        instantiate (1 := x).
      simpl in *.
      Check mem_sub.
      iIntros "!>"; iExists _, _; iSplit; first done.
      
      (* do we need to bring back mem_sub for this? *)
      assert (exists m'', corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'' /\ exists p' (Hlt' : permMapLt p' (getMaxPerm m')), m'' = restrPermMap Hlt') as (? & ? & ? & Hlt' & ->).
   (*   {
        assert (Hlt1:= mem_max_lt_max m').
        eexists.
        split; eauto.
        rewrite /mem_equiv.access_map_equiv in Heq.
        assert (Hlt2:= mem_max_lt_max m).
        apply (@restrPermMap_ext max (getMaxPerm m) m Hlt Hlt2) in Heq.
        induction H.
        assert (restrPermMap Hlt = m).
        {
          Check  restrPermMap_eq.
          Search restrPermMap.
          
        rewrite Heq.
        rewrite /cl_step in H |- *.
        try done.
        inversion H; subst; eauto.
        
        assert (mem_max_lt_max
        eapply (@restrPermMap_ext max (getMaxPerm m) m) in Heq.
        eapply restrPermMap_ext in Heq.
        Locate "#".
        Search permMapLt.
        Search mem_equiv.access_map_equiv.
        Search restrPermMap .
        Check (@restrPermMap_eq m).
        Search mem_equiv.access_map_equiv.
        eapply mem_equiv.Cur_equiv_restr in Heq; eauto.
        simpl in Heq.
        Check mem_equiv.cur_equiv_restr_mem_equiv.
        Search cl_step.
        instantiate (1:= Hmax). *)

      by admit.
      iIntros "!>"; iExists _, _; iSplit; first done.
      iSplitL "S".
      + assert (permMapLt (getCurPerm m') (getMaxPerm (restrPermMap Hlt'))) as Hltm'.
        { rewrite restr_Max_eq; apply cur_lt_max. }
        iExists _, Hltm'; rewrite restrPermMap_idem restrPermMap_eq //.
      + iNext; iApply ("IH" with "[%] Hsafe").
        admit. (* something about how perms being maxxed carries forward *)
    - iRight; iRight.
      iDestruct "H" as (??? (? & ?)) "H".
      assert (ext_spec_pre (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
       (sig_args (ef_sig e)) args z (restrPermMap Hlt)) by admit.
      iExists _, _, _; iSplit; first done.
      iIntros "!>" (?????).
      iMod ("H" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done.
      iFrame; iApply ("IH" with "[%] Hsafe").
      simpl in H, H4.
  Admitted.

  Definition thread_safe `{!VSTGS unit Σ} max (tp : dtp) i :=
    ∃ cnti : containsThread tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c => jsafe_perm max ⊤ tt c (getThreadR cnti).1
    | Kresume c v =>
      ∀ c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        ⌜cl_after_external None c = Some c'⌝ →
        jsafe_perm max ⊤ tt c' (getThreadR cnti).1
    | Kinit v1 v2 =>
      ∃ q_new,
      ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm max ⊤ tt q_new (getThreadR cnti).1
    end%I.

  Definition threads_safe `{!VSTGS unit Σ} max (tp : dtp) : mpred :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), thread_safe max tp i.

  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Definition locks_coherent `{!heapGS Σ} (tp : dtp) (m : mem) (ls : gmap address unit) :=
    forall l, (l ∈ dom ls -> lockRes tp l <> None /\ (Mem.load Mptr m l.1 l.2 = Some (Vptrofs Ptrofs.zero) <-> lockRes tp l = Some (empty_map, empty_map))).

  Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

  Definition other_threads_safe `{!VSTGS unit Σ} max tp i : mpred :=
    ∀ Ψ, □ (∀ k j, ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some j⌝ → ⌜k ≠ i⌝ →
        thread_safe max tp j -∗ Ψ k j) -∗
      Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.

  Definition post_safe `{!VSTGS unit Σ} max sig x c args k : mpred :=
    ∀ (ret : option val) (m' : mem) z',
      ⌜Val.has_type_list args (sig_args sig) ∧ Builtins0.val_opt_has_rettype ret (sig_res sig)⌝ →
      ⌜ext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res sig) ret z' m'⌝ →
      |={⊤}=> ∃ c' : CC_core, ⌜after_external (cl_core_sem ge) ret (Callstate c args k) m' = Some c'⌝ ∧
        state_interp m' z' ∗ jsafe_perm max ⊤ z' c' (getCurPerm m').
  
(*
 (* these lemmas could be split off again into semax_acquire_safety, etc. *)
  Lemma acquire_safe `{!VSTGS unit Σ} tp m ls i
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp) (Hcompat : HybridMachineSig.mem_compatible tp m)
    (cnti : containsThread tp i) argsty retty cc k args
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    p (Hmax : permMapLt p (getMaxPerm m)) (Hlt0 : permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax)))
    x (Hpre : ext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args () (restrPermMap Hlt0)) :
    ⊢ other_threads_safe (getMaxPerm m) tp i -∗
      ▷ post_safe (getMaxPerm m) (ef_sig LOCK) x (Ctypes.External LOCK argsty retty cc) args k -∗
      (* lock_set ls -∗ *)
      |={⊤}[∅]▷=> ∃ (tp' : t) (m' : mem) (ev : Events.sync_event),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧ locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
        threads_safe (getMaxPerm m') tp' ∗ (∃ (p0 : access_map) (Hlt : permMapLt p0 (getMaxPerm m')), state_interp (restrPermMap Hlt) ()) (* ∗ lock_set ls *).
  Proof.
    iIntros "Hsafe Hpost".
    apply CEspec_acquire_pre in Hpre as (x' & Heqx & Hpre).
    destruct x' as ((n, phi), ((l, sh), R)); simpl in Hpre.
    destruct Hpre as (Hvphi & Hty & Hpre).
    set (c := Callstate (Ctypes.External LOCK argsty retty cc) args k).
    destruct args as [|arg args]; simpl in Hty; first done.
    destruct Hty as (Hty & Htys); destruct args; last done.
    clear Htys.
    assert (readable_share sh /\ val_lemmas.isptr arg) as (Hsh & Hisptr).
    { revert Hpre; rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx; monPred.unseal; ouPred.unseal.
      intros (? & ? & ? & _ & (? & _) & [=] & _ & ? & ? & ? & Hlock & _).
      pose proof (lockinv_isptr sh l R) as [Heq].
      apply Heq in Hlock.
      revert Hlock; ouPred.unseal; intros (? & _); subst; done.
      { eapply cmra_validN_op_l, ora_validN_orderN; last done.
        eapply cmra_validN_op_r, ora_validN_orderN; done. } }
    destruct arg as [| | | | | b ofs]; try done.
    clear Hty Hisptr.
    (* Does the ls ghost state actually work? We don't have that phi is true in the current state. *)
    assert (ext_step cnti Hcompat (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) (b, Ptrofs.intval ofs) (empty_map, empty_map)) m' (Events.acquire (b, Ptrofs.intval ofs) (Some (build_delta_content virtueThread.1 m')))) as Hstep.

    iMod ("Hpost" with "[%] [%]").
  Admitted. *)

  Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)} sch n : exists b c_init,
    Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
    cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
    HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init) (proj1_sig init_mem) n.
  Proof.
    eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
    simpl; intros; iIntros "_".
    iMod (@init_VST _ _ VSTGpreS0) as "H".
    iDestruct ("H" $! Hinv) as (?? HE) "(H & ?)".
    iMod (own_alloc(A := gmap_view.gmap_viewR address unit) (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γl) "locks".
    { apply gmap_view.gmap_view_auth_valid. }
    set (HH := Build_VSTGS _ _ (HeapGS _ _ _ _) HE).
    destruct (spr HH) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "H") as "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
         (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
       (sch, [],
        DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
          q) (proj1_sig init_mem) n⌝) with "[S Hsafe locks]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done. }
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    set (tp := initial_machine _ _).
    assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
    assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat by apply ThreadPoolWF.initial_mem_compatible.
    assert (threads_wellformed tp) as Htp_wf by done.
    iAssert (threads_safe(VSTGS0 := HH) (getMaxPerm (`init_mem)) tp) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      unshelve iExists _; first done.
      iApply (jsafe_jsafe_perm with "Hsafe").
      admit. (* should be provable, but is this what we need? *) }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    clearbody tp.
    set (ls := ∅) in Hlocks |- *.
(*     iAssert (lock_set ls) with "locks" as "locks". *)
    clearbody ls.
    clear dependent b x q.
    (* the machine semantics clobber the curPerm with the most recent thread's curPerm *)
    iAssert (∃ p (Hlt : permMapLt p (getMaxPerm m)), state_interp (restrPermMap Hlt) tt) with "[S]" as "S".
    { iExists _, (cur_lt_max m); rewrite restrPermMap_eq //. }
    iLöb as "IH" forall (sch tr tp m n ls Htp_wf Hinvariant Hcompat Hlocks).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: {
      iApply step_fupd_intro; first done; iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
         { rewrite step_fupdN_plain_forall //.
           iIntros.
           iApply ("IH" with "[%] [%] [%] [%] locks Hsafe S"); try done.
         }
      iApply (step_fupdN_mono with "H"); iPureIntro.
      intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
           with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.schedfail; eauto.
      rewrite /containsThread /= /OrdinalPool.containsThread.
      intros ?.
      pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle;
           [lia | congruence]. }
    rewrite {2}/threads_safe.
    iPoseProof (big_sepL_lookup_acc_impl with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto.
          hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe (getMaxPerm m) tp) with "[Hsafei Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "H"; iApply "H".
          * iExists cnti; rewrite Hi //. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] [%] locks Hsafe S"); done. }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.halted_step; eauto.
      + (* HybridMachineSig.suspend_step *)
        assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
        { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] [%] locks [Hsafe Hsafei]").
          (*
          
          iIntros; iApply ("IH" with "[%] [%] [%] [%] locks S [Hsafei Hsafe]"). *)
          + intros j cntj.
            destruct (eq_dec j i).
            * subst; rewrite gssThreadCC Hat_ext //.
            * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
              rewrite -gsoThreadCC //; apply Htp_wf.
          + by apply ThreadPoolWF.updThreadC_invariant.
          + by apply StepLemmas.updThreadC_compatible.
          + intros ?; rewrite gsoThreadCLPool; apply Hlocks.
          + iApply "Hsafe".
            * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
              iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
            * iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
              by iApply "Hsafei".
          + iFrame.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        rewrite jsafe_perm_unfold /jsafe_perm_pre.
        iDestruct "S" as (? Hmax) "S".
        assert (permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax))) as Hlt0.
        { rewrite restr_Max_eq. by apply compat_th. }
        iMod ("Hsafei" $! _ Hlt0 with "[%] S") as "[Hhalt | [Hstep | Hext]]".
        { rewrite restr_Max_eq //. }
        { iDestruct "Hhalt" as %(? & Hhalt' & ?); done. }
        2: { iDestruct "Hext" as (??? (Hext & ?)) "?".
             simpl in Hext; congruence. }
        iMod "Hstep" as (?? Hstep) "(S & Hsafei)".
        rewrite restrPermMap_idem in Hstep.
        assert (corestep (cl_core_sem ge) s (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { by erewrite restrPermMap_irr. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) with "[%] [%] [%] [%] locks [Hsafe Hsafei] ").
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
          by eapply ev_step_ax1.
        * by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        * intros ?; rewrite gsoThreadLPool. (*eapply Hlocks. need to know that coresteps don't mess with locks *) admit.
        * iApply "Hsafe".
          -- iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
             iExists (cntUpdate _ _ cnti cnti0).
             rewrite gsoThreadCode // gsoThreadRes //.
             admit. (* need to know that any changes to getMaxPerm don't invalidate other threads! *)
          -- iExists (cntUpdate _ _ cnti cnti).
             rewrite gssThreadCode gssThreadRes.
             simpl in *.
             iApply jsafe_perm_mono; eauto.
             (* Need to know permMapLt (getMaxPerm m') (getMaxPerm m) *)
             simpl in Hlt0.
             apply Clight_evsem.CLC_evstep_ax1 in Hstep'.
             rewrite /= in Hstep'.
             Search decay.
             admit.
        * (* Work from here *)
          iApply (step_fupdN_mono with "[IH]").
          iIntros "_".
          iPureIntro;
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          eapply step_dry.
          simpl. repeat try done. done. done.
          simpl in *. eauto. done. simpl in *.

          (*
          
          iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe, Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          by eapply step_dry. *) admit. admit.
    - (* Kblocked: HybridMachineSig.sync_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      rewrite jsafe_perm_unfold /jsafe_perm_pre.
      iDestruct "S" as (? Hmax) "S".
      assert (permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax))) as Hlt0.
      { rewrite restr_Max_eq. by apply compat_th. }
      iMod ("Hsafei" $! _ Hlt0 with "[%] S") as "[Hhalt | [Hstep | Hext]]".
      { rewrite restr_Max_eq //. }
      { iDestruct "Hhalt" as %(? & Hhalt' & ?).
        destruct s; done. }
      { iMod "Hstep" as (?? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done. }
      iDestruct "Hext" as (??? (Hat_ext & Hpre)) "Hpost".
      iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev, ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
        locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
        threads_safe (getMaxPerm m') tp' ∗ (∃ p (Hlt : permMapLt p (getMaxPerm m')), state_interp (restrPermMap Hlt) tt) ∗ lock_set ls) with "[-]" as "Hsafe".
      2: { iMod "Hsafe"; iIntros "!> !>"; iMod "Hsafe" as (??? (? & ? & ? & ? & ?)) "(Hsafe & S & locks)".
           iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
           { rewrite step_fupdN_plain_forall //.
             iIntros; iApply ("IH" with "[%] [%] [%] [%] Hsafe locks S"); done. }
           iApply (step_fupdN_mono with "H"); iPureIntro.
           intros Hsafe.
           eapply HybridMachineSig.HybridCoarseMachine.AngelSafe; simpl; last apply Hsafe.
           eapply HybridMachineSig.sync_step; eauto. }
      (* consider each of the concurrency functions *)
      clear Hwfi.
      destruct s as [|f ? k|]; try done; simpl in Hat_ext.
      destruct f as [|ext argsty retty cc]; try done.
      destruct (ef_inline ext); inv Hat_ext.
      destruct (CEspec_cases _ x) as [-> | [-> | [-> | [-> | ->]]]].
      + (* acquire *)
        iApply (acquire_safe with "Hsafe Hpost locks").
      + (* release *)
      + (* makelock *)
      + (* freelock *)
      + (* spawn *)
    - (* Kresume: HybridMachineSig.resume_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c))) with "[%] [%] [%] [Hsafei Hsafe] S").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
        * iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
          by iApply "Hsafei".
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        eapply HybridMachineSig.resume_step; eauto.
    - (* Kinit: HybridMachineSig.start_step *)
      iDestruct "Hsafei" as (? Hinit) "Hsafei".
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [Hsafei Hsafe] [S]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + eapply InternalSteps.start_compatible; try done.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdate _ _ cnti cnti0); rewrite gsoThreadCode // gsoThreadRes //.
          subst m'; rewrite restr_Max_eq //.
        * iExists (cntUpdate _ _ cnti cnti); rewrite gssThreadCode gssThreadRes.
          rewrite restr_Max_eq /=.
          iApply (jsafe_perm_equiv with "Hsafei").
          symmetry; apply mem_equiv.getCur_restr.
      + iDestruct "S" as (??) "S".
        iExists _, (mem_equiv.useful_permMapLt_trans _ Hlt).
        rewrite restrPermMap_idem. erewrite restrPermMap_irr; done.
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m').
        eapply HybridMachineSig.start_step; eauto.
  Admitted.

End Safety.

Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Section value.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Program Definition value (ot : Ctypes.type) (v : val) : type := {|
    ty_has_op_type ot' mt := (ot' = ot ∧ type_is_by_value ot = true)%type;
    ty_own β l := (<affine>⌜l `has_layout_loc` ot⌝ ∗
                   <affine>⌜(valinject ot v) `has_layout_val` ot⌝ ∗
                   l ↦[β]|ot| (valinject ot v))%I;
    ty_own_val cty v' := (<affine> ⌜cty = ot⌝ ∗
                          <affine> ⌜v' = valinject cty v⌝ ∗
                          <affine> ⌜v' `has_layout_val` cty⌝)%I;
  |}.
  Next Obligation. iIntros (?????) "[$ [$ ?]]". by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (ot v ot' mt l [-> ?]) "[% [% ?]]". done. Qed.
  Next Obligation. intros ot v ot' mt l [-> ?].
                   iIntros "[% [% ?]]". done. Qed.
  Next Obligation. intros ot v ot' mt l [-> ?].
                   iIntros "[% [% ?]]". eauto with iFrame. Qed.
  Next Obligation. iIntros (ot v ot' mt l ? [-> ?]) "% Hl (% & -> & %)".
                   by iFrame. Qed.
(*  Next Obligation. iIntros (ot v v' ot' mt st ?). apply: mem_cast_compat_id. iPureIntro.
    move => [?[? ->]]. by destruct ot' => //; simplify_eq/=.
  Qed.*)

  Lemma valinject_inj cty v1 v2: type_is_by_value cty = true →
    valinject cty v1 = valinject cty v2 → v1 = v2.
  Proof. by destruct cty. Qed.

  Global Instance value_defined ot v `{!TCDone (type_is_by_value (val_type ot) = true)} `{!TCDone (v ≠ Vundef)}: DefinedTy ot (value ot v).
  Proof.
    iIntros (? (_ & ? & _)).
    by apply valinject_inj in H as ->.
  Qed.

  Lemma value_simplify ot v p T:
    (<affine> ⌜v = valinject ot p⌝ -∗ <affine>⌜v `has_layout_val` ot⌝ -∗ ⟦v ◁ᵥ|ot| value ot p⟧ -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ|ot| value ot p) T.
  Proof. iIntros "HT [% [% %]]". rewrite do_not_simplify_eq /=. by iApply "HT". Qed.
  Definition value_simplify_inst := [instance value_simplify with 0%N].
  Global Existing Instance value_simplify_inst.

  Lemma value_simplify' ot v p (T : assert):
    (<affine> ⌜v = valinject ot p⌝ -∗ <affine>⌜v `has_layout_val` ot⌝ -∗ ⟦⎡v ◁ᵥ|ot| value ot p⎤⟧ -∗ T)
    ⊢ simplify_hyp ⎡v ◁ᵥ|ot| value ot p⎤ T.
  Proof. iIntros "HT [% [% %]]". rewrite do_not_simplify_eq /=. by iApply "HT". Qed.
  Definition value_simplify'_inst := [instance value_simplify' with 0%N].
  Global Existing Instance value_simplify'_inst.

  Lemma value_simplify_goal ot v p T:
    (<affine> ⌜v = valinject ot p⌝ ∗ <affine> ⌜v `has_layout_val` ot⌝ ∗ T)
    ⊢ simplify_goal (v ◁ᵥ|ot| value ot p) T.
  Proof. iIntros "(% & % & $)". done. Qed.
  Definition value_simplify_goal_inst := [instance value_simplify_goal with 0%N].
  Global Existing Instance value_simplify_goal_inst.

  Lemma value_simplify_goal' ot v p (T : assert):
    (<affine> ⌜v = valinject ot p⌝ ∗ <affine> ⌜v `has_layout_val` ot⌝ ∗ T)
    ⊢ simplify_goal ⎡v ◁ᵥ|ot| value ot p⎤ T.
  Proof. iIntros "(% & % & $)". done. Qed.
  Definition value_simplify_goal'_inst := [instance value_simplify_goal' with 0%N].
  Global Existing Instance value_simplify_goal'_inst.

  (* might restore this if we find an analogue to memcast *)
(*   Lemma value_subsume_goal A v v' ly ty T:
    (<affine> ⌜ty.(ty_has_op_type) ly MCId⌝ ∗ (v ◁ᵥ ty -∗ ∃ x, <affine> ⌜v = v' x⌝ ∗ T x))
    ⊢ subsume (v ◁ᵥ ty) (λ x : A, v ◁ᵥ value ly (v' x)) T.
  Proof.
    iIntros "[% HT] Hty". (* iDestruct (ty_size_eq with "Hty") as %Hly; [done|]. *)
(*     iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|]. *)
    iDestruct ("HT" with "Hty") as (? ->) "?". iExists _. by iFrame.
  Qed. *)
  Lemma value_subsume_goal A cty v v' ty T:
    (<affine> ⌜v `has_layout_val` cty⌝ ∗ (v ◁ᵥ|cty| ty -∗ ∃ x, <affine> ⌜v = valinject cty (v' x)⌝ ∗ T x))
    ⊢ subsume (v ◁ᵥ|cty| ty) (λ x : A, v ◁ᵥ|cty| value cty (v' x)) T.
  Proof.
    iIntros "[% HT] Hty". (* iDestruct (ty_size_eq with "Hty") as %Hly; [done|]. *)
(*     iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|]. *)
    iDestruct ("HT" with "Hty") as (? ->) "?". iExists _. by iFrame.
  Qed.
  Definition value_subsume_goal_inst := [instance value_subsume_goal].
  Global Existing Instance value_subsume_goal_inst.

  Lemma value_subsume_goal' A cty v v' ty (T : A → assert):
    (<affine> ⌜v `has_layout_val` cty⌝ ∗ (⎡v ◁ᵥ|cty| ty⎤ -∗ ∃ x, <affine> ⌜v = valinject cty (v' x)⌝ ∗ T x))
    ⊢ subsume ⎡v ◁ᵥ|cty| ty⎤ (λ x : A, ⎡v ◁ᵥ|cty| value cty (v' x)⎤) T.
  Proof.
    iIntros "[% HT] Hty". (* iDestruct (ty_size_eq with "Hty") as %Hly; [done|]. *)
(*     iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|]. *)
    iDestruct ("HT" with "Hty") as (? ->) "?". iExists _. by iFrame.
  Qed.
  Definition value_subsume_goal'_inst := [instance value_subsume_goal'].
  Global Existing Instance value_subsume_goal'_inst.

  (*   Lemma value_subsume_goal_loc A l v' ot ty T:
    (<affine> ⌜ty.(ty_has_op_type) ot MCId⌝ ∗ ∀ v, v ◁ᵥ ty -∗ ∃ x, <affine> ⌜v = (v' x)⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ ty) (λ x : A, l ◁ₗ value ot (v' x)) T.
  Proof.
    iIntros "[% HT] Hty".
    iDestruct (ty_aligned with "Hty") as %Hal; [done|].
    iDestruct (ty_deref with "Hty") as (v) "[Hmt Hty]"; [done|].
(*     iDestruct (ty_size_eq with "Hty") as %Hly; [done|].
    iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|]. *)
    iDestruct ("HT" with "Hty") as (? ->) "?". iExists _. by iFrame.
  Qed.
  Definition value_subsume_goal_loc_inst := [instance value_subsume_goal_loc].
  Global Existing Instance value_subsume_goal_loc_inst. *)

  Lemma value_subsume_own_ptrop A l β (v' : A → val) ty T:
    (l ◁ₗ{β} ty -∗ ∃ x, <affine> ⌜v' x = l⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ty) (λ x : A, l ◁ᵥ|tptr tvoid| value (tptr tvoid) (v' x)) T.
  Proof.
    iIntros "HT Hty". iDestruct ("HT" with "Hty") as (? Heq) "?". iExists _. iFrame.
    rewrite Heq. iPureIntro. split_and!; done.
  Qed.
  Definition value_subsume_own_ptrop_inst := [instance value_subsume_own_ptrop].
  Global Existing Instance value_subsume_own_ptrop_inst.

  Lemma value_subsume_own_ptrop' A l β (v' : A → val) ty (T : A → assert):
    (⎡l ◁ₗ{β} ty⎤ -∗ ∃ x, <affine> ⌜v' x = l⌝ ∗ T x)
    ⊢ subsume ⎡l ◁ₗ{β} ty⎤ (λ x : A, ⎡l ◁ᵥ|tptr tvoid| value (tptr tvoid) (v' x)⎤) T.
  Proof.
    iIntros "HT Hty". iDestruct ("HT" with "Hty") as (? Heq) "?". iExists _. iFrame.
    rewrite Heq. iPureIntro. split_and!; done.
  Qed.
  Definition value_subsume_own_ptrop'_inst := [instance value_subsume_own_ptrop'].
  Global Existing Instance value_subsume_own_ptrop'_inst.

(*   Lemma value_merge v l ot T:
    find_in_context (FindVal v) (λ ty:type, ⌜ty.(ty_has_op_type) (UntypedOp (ot_layout ot)) MCNone⌝ ∗ (l ◁ₗ ty -∗ T))
    ⊢ simplify_hyp (l ◁ₗ value ot v) T.
  Proof.
    iDestruct 1 as (ty) "[Hv [% HT]]".
    iIntros "[% [% [% Hl]]]". iApply "HT". by iApply (ty_ref with "[] Hl Hv").
  Qed.
  Definition value_merge_inst := [instance value_merge with 50%N].
  Global Existing Instance value_merge_inst | 20. *)

Lemma type_read_move l ty ot a E `{!TCDone (ty.(ty_has_op_type) ot MCId)} `{!DefinedTy ot ty}
  `{!TCDone (type_is_by_value ot = true)} T:
    (∀ v, T v (value ot v) ty)
    ⊢ typed_read_end a E l Own ty ot T.
  Proof.
    unfold TCDone, typed_read_end in *. intros. iIntros "HT Hl".
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hclose".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    (* iDestruct (ty_memcast_compat_id with "Hv") as %Hid; [done|]. *)
    iDestruct (defined_ty (repinject ot v) with "[Hv]") as %?.
    { rewrite /val_type TCDone1 valinject_repinject //. }
    iExists _, (repinject ot v), _. rewrite /val_type TCDone1 valinject_repinject //.
    iFrame. do 3 iSplit => //=.
    { iPureIntro. apply readable_share_top. }
    iSplit => //.
    iIntros "? ?". iMod "Hclose". iModIntro.
    iFrame.
    iSpecialize ("HT" $! (repinject ot v)).
    iFrame.
    rewrite /ty_own /= valinject_repinject //.
    do 2 iSplit => //=.
  Qed.
  Definition type_read_move_inst := [instance type_read_move].
  Global Existing Instance type_read_move_inst | 50.

  (* TODO: this constraint on the layout is too strong, we only need
  that the length is the same and the alignment is lower. Adapt when necessary. *)
  Lemma type_write_own a ty E l2 ty2 ot v T:
    typed_write_end a E ot v ty l2 Own ty2 T where
    `{!TCDone (ty.(ty_has_op_type) (val_type ot) MCId ∧
               ty2.(ty_has_op_type) (val_type ot) MCNone)} :-
      ∀ v', inhale ⎡v ◁ᵥₐₗ|ot| ty⎤; inhale ⎡v' ◁ᵥ|val_type ot| ty2⎤; return T (value (val_type ot) v).
  Proof.
    unfold TCDone, typed_write_end => -[??]. iIntros "HT Hl Hv".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iDestruct (ty_size_eq with "Hv'") as %?; [done|].
    (*iDestruct (ty_memcast_compat_id with "Hv") as %Hid; [done|].*)
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hmask".
    iSplit; [done|]. iSplitL "Hl". { iExists _. by iFrame. }
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iExists _. iDestruct ("HT" with "Hv Hv'") as "$". by iFrame.
  Qed.
  Definition type_write_own_inst := [instance type_write_own].
  Global Existing Instance type_write_own_inst | 50.

End value.
Global Typeclasses Opaque value.
Notation "value< ot , v >" := (value ot v) (only printing, format "'value<' ot ',' v '>'") : printing_sugar.

Section at_value.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* up *)
  Lemma field_compatible_tptr : forall p a b, field_compatible (Tpointer a b) [] p ↔ field_compatible (tptr tvoid) [] p.
  Proof.
    intros.
    split; intros (? & ? & ? & Ha & ?); split3; auto; split3; auto;
      destruct p; try done; simpl in *;
      inv Ha; econstructor; eauto.
  Qed.

  Lemma has_layout_loc_tptr : forall p a b, p `has_layout_loc` (Tpointer a b) ↔ p `has_layout_loc` (tptr tvoid).
  Proof.
    intros.
    rewrite /has_layout_loc field_compatible_tptr //.
  Qed.

  Lemma mem_block_mapsto_tptr:
    forall sh t1 t2, mapsto_memory_block.mapsto sh (tptr t1) = mapsto_memory_block.mapsto sh (tptr t2).
  Proof.
    intros.
    unfold mapsto_memory_block.mapsto.
    extensionality v1 v2.
    unfold tc_val', tc_val. simpl.
    rewrite !andb_false_r //.
  Qed.

  Lemma mapsto_tptr:
    forall l sh t1 t2, mapsto l sh (tptr t1) = mapsto l sh (tptr t2).
  Proof.
    intros.
    unfold mapsto.
    extensionality v.
    rewrite /data_at_rec /=.
    by erewrite mem_block_mapsto_tptr.
  Qed.

  (* The type of the pointer really doesn't matter; maybe this means we're using the wrong level of type here. *)
  (* Lemma value_tptr l t1 t2 v' : l ◁ₗ value (tptr t1) v' ⊣⊢ l ◁ₗ value (tptr t2) v'.
  Proof.
    rewrite /ty_own /=.
    rewrite /has_layout_val /has_layout_loc /=.
    rewrite !field_compatible_tptr.
    rewrite /heap_mapsto_own_state. rewrite (mapsto_tptr _ _ t1 t2).
    rewrite /value_fits /tc_val' /=.

  Qed. *)

  (* Lemma value_tptr_val v t1 t2 v' : v ◁ᵥ|tptr t1| value (tptr t1) v' = v ◁ᵥ|tptr t2| value (tptr t2) v'.
  Proof.
    rewrite /ty_own_val_at /ty_own_val /=.
    rewrite /has_layout_val.
    rewrite /value_fits /=.

    rewrite !andb_false_r //.
  Qed. *)

  (* TODO: At the moment this is hard-coded for PtrOp. Generalize it to other layouts as well. *)
  Program Definition at_value (cty: Ctypes.type) (v : val) (ty : type) : type := {|
    ty_has_op_type ot mt := (ot = tptr cty ∧ type_is_by_value cty = true)%type;
    ty_own β l := (if β is Own then l ◁ₗ value (tptr cty) v ∗ v ◁ᵥₐₗ|cty| ty else True)%I;
    ty_own_val ot v' := (<affine> ⌜ot = tptr cty⌝ ∗ v' ◁ᵥ|ot| value (tptr cty) v ∗ v ◁ᵥₐₗ|cty| ty)%I;
  |}.
  Next Obligation. by iIntros (??????) "?". Qed.
  Next Obligation. iIntros (cty v ty ot mt l (-> & ?)) "(Hv & ?)". iDestruct (ty_aligned _ _ MCId with "Hv") as %?; done. Qed.
  Next Obligation. iIntros (cty v ty ot mt l (-> & ?)) "[% [Hl Hv]]".
    iPoseProof (ty_size_eq _ _ mt with "Hl") as "%Hl"; try done.
  Qed.
  Next Obligation. iIntros (cty v ty ot mt l (-> & ?)) "(Hl & Hv)".
    rewrite /ty_own_val_at /=.
    iDestruct (ty_deref _ _ MCId with "Hl") as "(% & ↦ & own_vrep)"; try done.
     iFrame. done.
    Qed.
  Next Obligation. iIntros (cty v ty ot mt l ? ?) "% Hl (% & Hv & $)".
    iApply (ty_ref _ _ MCId with "[] Hl Hv"); done. Qed.
(*   Next Obligation.
    iIntros (v ty v' ot mt st ?) "[Hv ?]".
    iDestruct (ty_memcast_compat with "Hv") as "?"; [done|]. destruct mt => //. iFrame.
  Qed. *)


  Lemma at_value_simplify_hyp_val v v' t ty T:
    (v ◁ᵥₐₗ|t| value (tptr t) v' -∗ v' ◁ᵥₐₗ|t| ty -∗ T)
    ⊢ simplify_hyp (v ◁ᵥₐₗ|t| at_value t v' ty) T.
  Proof. iIntros "HT (% & [??])". by iApply ("HT" with "[$] [$]"). Qed.
  Definition at_value_simplify_hyp_val_inst := [instance at_value_simplify_hyp_val with 0%N].
  Global Existing Instance at_value_simplify_hyp_val_inst.

  Lemma at_value_simplify_goal_val v v' t ty T:
    v ◁ᵥₐₗ|tptr t| value (tptr t) v' ∗ v' ◁ᵥₐₗ|t| ty ∗ T
    ⊢ simplify_goal (v ◁ᵥₐₗ|tptr t| at_value t v' ty) T.
  Proof. iIntros "[$ [$ $]]". done. Qed.
  Definition at_value_simplify_goal_val_inst := [instance at_value_simplify_goal_val with 0%N].
  Global Existing Instance at_value_simplify_goal_val_inst.

  Lemma at_value_simplify_hyp_loc l v' t ty T:
    (l ◁ₗ value (tptr t) v' -∗ v' ◁ᵥₐₗ|t| ty -∗ T)
    ⊢ simplify_hyp (l ◁ₗ at_value t v' ty) T.
  Proof. iIntros "HT [? ?]". by iApply ("HT" with "[$] [$]"). Qed.
  Definition at_value_simplify_hyp_loc_inst := [instance at_value_simplify_hyp_loc with 0%N].
  Global Existing Instance at_value_simplify_hyp_loc_inst.

  Lemma at_value_simplify_goal_loc l v' t ty T:
    l ◁ₗ value (tptr t) v' ∗ v' ◁ᵥₐₗ|t| ty ∗ T
    ⊢ simplify_goal (l ◁ₗ at_value t v' ty) T.
  Proof. iIntros "[$ [$ $]]". Qed.
  Definition at_value_simplify_goal_loc_inst := [instance at_value_simplify_goal_loc with 0%N].
  Global Existing Instance at_value_simplify_goal_loc_inst.

End at_value.
Global Typeclasses Opaque at_value.
Notation "at_value< cty , v , ty >" := (at_value cty v ty) (only printing, format "'at_value<' cty ',' v ',' ty '>'") : printing_sugar.

Section place.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Program Definition place (l : address) : type := {|
    ty_own β l' := (<affine> ⌜l = l'⌝)%I;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ _ := emp;
  |}.
  Solve Obligations with try done.
  Next Obligation. by iIntros (????) "$". Qed.

  Lemma place_simplify l β p T:
    (<affine> ⌜l = p⌝ -∗ T)
    ⊢ simplify_hyp (l◁ₗ{β} place p) T.
  Proof. iIntros "HT ->". by iApply "HT". Qed.
  Definition place_simplify_inst := [instance place_simplify with 0%N].
  Global Existing Instance place_simplify_inst.

  Lemma place_simplify_goal l β p T:
    <affine> ⌜l = p⌝ ∗ T
    ⊢ simplify_goal (l◁ₗ{β} place p) T.
  Proof. by iIntros "[-> $]". Qed.
  Definition place_simplify_goal_inst := [instance place_simplify_goal with 0%N].
  Global Existing Instance place_simplify_goal_inst.

  Lemma simplify_goal_ex_place l β ty T:
    simplify_goal (l ◁ₗ{β} ty) T :- exhale (<affine> ⌜ty = place l⌝); return T.
  Proof. iIntros "[-> $]". done. Qed.
  (* This is applied with Hint Extern for better performance. *)
  Definition simplify_goal_ex_place_inst := [instance simplify_goal_ex_place with 99%N].

  Lemma place_simplify' l β p (T : assert):
    (<affine> ⌜l = p⌝ -∗ T)
    ⊢ simplify_hyp ⎡l◁ₗ{β} place p⎤ T.
  Proof. iIntros "HT ->". by iApply "HT". Qed.
  Definition place_simplify'_inst := [instance place_simplify' with 0%N].
  Global Existing Instance place_simplify'_inst.

  Lemma place_simplify_goal' l β p (T : assert):
    <affine> ⌜l = p⌝ ∗ T
    ⊢ simplify_goal ⎡l◁ₗ{β} place p⎤ T.
  Proof. by iIntros "[-> $]". Qed.
  Definition place_simplify_goal'_inst := [instance place_simplify_goal' with 0%N].
  Global Existing Instance place_simplify_goal'_inst.

  Lemma simplify_goal_ex_place' l β ty (T : assert):
    simplify_goal ⎡l ◁ₗ{β} ty⎤ T :- exhale (<affine> ⌜ty = place l⌝); return T.
  Proof. iIntros "[-> $]". done. Qed.
  (* This is applied with Hint Extern for better performance. *)
  Definition simplify_goal_ex_place'_inst := [instance simplify_goal_ex_place' with 99%N].

  Lemma type_addr_of_singleton l β ty T:
    T β ty (place l)
    ⊢ typed_addr_of_end l β ty T.
  Proof. iIntros "HT Hl !#". iExists _, _, _. iFrame "HT". by iFrame. Qed.
  Definition type_addr_of_singleton_inst := [instance type_addr_of_singleton].
  Global Existing Instance type_addr_of_singleton_inst.

  Lemma typed_place_simpl ge P l ty1 β1 n {SH:SimplifyHyp ⎡l ◁ₗ{β1} ty1⎤ (Some n)} T:
    (SH (find_in_context (FindLoc l) (λ '(β2, ty2),
        typed_place ge P l β2 ty2 (λ l3 β3 ty3 typ R,
           T l3 β3 ty3 (λ _, place l) (λ ty', ⎡l ◁ₗ{β2} typ ty'⎤ ∗ R ty' ))))).(i2p_P)
    ⊢ typed_place ge P l β1 ty1 T.
  Proof.
    iIntros "SH" (Φ) "Hl HΦ".
    iDestruct (i2p_proof with "SH Hl") as ([β2 ty2]) "[Hl HP]".
    iApply ("HP" with "Hl").
    iIntros (l3 β3 ty3 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [Hc] HT").
    iIntros (ty') "Hl3". by iMod ("Hc" with "Hl3") as "[$ $]".
  Qed.
  Definition typed_place_simpl_inst := [instance typed_place_simpl].
  Global Existing Instance typed_place_simpl_inst | 1000.

  Lemma typed_read_end_simpl E l β ty ly n {SH:SimplifyHyp ⎡l ◁ₗ{β} ty⎤ (Some n)} a T:
    (SH (find_in_context (FindLoc l) (λ '(β2, ty2),
        typed_read_end a E l β2 ty2 ly (λ v ty' ty3, ⎡l ◁ₗ{β2} ty'⎤ -∗ T v (place l) ty3)))).(i2p_P)
    ⊢ typed_read_end a E l β ty ly T.
  Proof.
    iIntros "SH". iApply typed_read_end_mono_strong; [done|]. iIntros "Hl !>".
    iDestruct (i2p_proof with "SH Hl") as ([β2 ty2]) "[Hl HP]" => /=.
    iExists _, _, emp%I. iFrame "Hl". iSplit; [done|].
    iApply (typed_read_end_wand with "HP"). iIntros (v ty1 ty2') "HT _ Hl Hv !>".
    iExists (place l), _. iFrame. iSplit; [done|]. by iApply "HT".
  Qed.
  Definition typed_read_end_simpl_inst := [instance typed_read_end_simpl].
  Global Existing Instance typed_read_end_simpl_inst | 1000.

  Lemma typed_write_end_simpl b E ot v ty1 l β ty2 n {SH:SimplifyHyp ⎡l ◁ₗ{β} ty2⎤ (Some n)} T:
    (SH (find_in_context (FindLoc l) (λ '(β3, ty3),
        typed_write_end b E ot v ty1 l β3 ty3 (λ ty', ⎡l ◁ₗ{β3} ty'⎤ -∗ T (place l))))).(i2p_P)
    ⊢ typed_write_end b E ot v ty1 l β ty2 T.
  Proof.
    iIntros "SH". iApply typed_write_end_mono_strong; [done|]. iIntros "Hv Hl !>".
    iDestruct (i2p_proof with "SH Hl") as ([β2' ty2']) "[Hl HP]" => /=.
    iExists _, _, _, emp%I. iFrame "Hv Hl". iSplit; [done|].
    iApply (typed_write_end_wand with "HP"). iIntros (ty3) "HT _ Hl !>".
    iExists (place l). iSplit; [done|]. by iApply "HT".
  Qed.
  Definition typed_write_end_simpl_inst := [instance typed_write_end_simpl].
  Global Existing Instance typed_write_end_simpl_inst | 1000.

End place.
Global Typeclasses Opaque place.
Notation "place< l >" := (place l) (only printing, format "'place<' l '>'") : printing_sugar.

Global Hint Extern 99 (SimplifyGoal (_ ◁ₗ{_} _.1ₗ) _) =>
  (class_apply simplify_goal_ex_place_inst) : typeclass_instances.
Global Hint Extern 99 (SimplifyGoal (_ ◁ₗ{_} _.1ₗ) _) =>
  (class_apply simplify_goal_ex_place'_inst) : typeclass_instances.

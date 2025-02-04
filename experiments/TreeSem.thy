theory TreeSem
  imports "../Soundness" "HOL-Cardinals.Bounded_Set" "HOL-Library.BNF_Corec"
begin

lemma bmember_bmap_iff:
  \<open>bmember y (map_bset f B) \<longleftrightarrow> (\<exists>x. bmember x B \<and> y = f x)\<close>
  by transfer (force simp add: image_def)

lemma bCollect_eq_bempty_iff:
  \<open>bCollect p = bempty \<longleftrightarrow> (\<nexists>x. p x)\<close>
  by (metis Collect_empty_eq bCollect.rep_eq bempty.rep_eq set_bset_inject)


datatype 'a label = Env | Local \<open>'a act\<close>

type_synonym ('s, 'a) config = \<open>('s + unit) \<times> ('s, 'a) comm\<close>

datatype ('s, 'a) sem_tree =
  Branch
    (config_sem_tree: \<open>('s, 'a) config\<close>)
    (branches_sem_tree: \<open>('a label \<times> ('s, 'a) sem_tree) set[('a label \<times> ('s, 'a) config) set]\<close>)

lemma sem_tree_induct:
  \<open>(\<And>ty.
      (\<And>tx. tx \<in> snd ` set_bset (branches_sem_tree ty) \<Longrightarrow> P tx) \<Longrightarrow>
      P ty) \<Longrightarrow>
    P t\<close>
  apply (rule sem_tree.induct)
  apply (clarsimp simp add: image_def Bex_def)
  apply (metis sem_tree.sel(2))
  done

function pred_sem_tree :: \<open>(('s, 'a) config \<Rightarrow> bool) \<Rightarrow> ('s, 'a) sem_tree \<Rightarrow> bool\<close> where
  \<open>pred_sem_tree p (Branch s bs) = (p s \<and> pred_bset (pred_sem_tree p \<circ> snd) bs)\<close>
  by pat_completeness auto
termination
  apply (relation \<open>{((x,a),(y,b)). x = y \<and> a \<in> snd ` set_bset (branches_sem_tree b)}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply simp
  done

function step_rel_sem_tree
  :: \<open>('a label \<Rightarrow> ('s, 'a) config \<Rightarrow> ('s, 'a) config \<Rightarrow> bool) \<Rightarrow> ('s, 'a) sem_tree \<Rightarrow> bool\<close>
  where
  \<open>step_rel_sem_tree r (Branch s bs) =
    pred_bset (\<lambda>(l,t). r l s (config_sem_tree t) \<and> step_rel_sem_tree r t) bs\<close>
  by pat_completeness auto
termination
  apply (relation \<open>{((x,a),(y,b)). x = y \<and> a \<in> snd ` set_bset (branches_sem_tree b)}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply (clarsimp simp add: rev_image_eqI)
  done

(*

definition
  \<open>sem_tree_contains t1 t2 \<equiv>
    (t1, t2) \<in> {(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<^sup>+\<close>

lemmas sem_tree_contains_baseI =
  r_into_trancl[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_contains_stepI =
  trancl_into_trancl[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_contains_induct =
  trancl.induct[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemmas sem_tree_containsE[elim] =
  trancl.cases[
    of _ _ \<open>{(t1,t2). t1 \<in> snd ` set_bset (branches_sem_tree t2)}\<close>,
    simplified,
    simplified sem_tree_contains_def[symmetric]]

lemma sem_tree_contains_branches_no_loop:
  \<open>sem_tree_contains a b \<Longrightarrow>
    b \<notin> snd ` set_bset (branches_sem_tree a)\<close>
  by (induct b arbitrary: a rule: sem_tree_induct)
    (meson sem_tree_containsE sem_tree_contains_baseI trancl_trans
      sem_tree_contains_def)

lemma sem_tree_contains_no_loop:
  \<open>sem_tree_contains a b \<Longrightarrow> \<not> sem_tree_contains b a\<close>
  by (erule sem_tree_contains_induct)
    (meson sem_tree_contains_branches_no_loop sem_tree_contains_def trancl_trans)+
*)



fun bounded_treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) config \<Rightarrow>
      nat \<Rightarrow>
      ('l \<times> 's, unit) sem_tree\<close>
  where
  \<open>bounded_treesem r s 0 = Branch s bempty\<close>
| \<open>bounded_treesem r (Inr (), c) n = Branch (Inr (), c) bempty\<close>
| \<open>bounded_treesem r (Inl (hl, hs), c) (Suc n) =
    Branch (Inl (hl, hs), c)
      (map_bset
        (\<lambda>(l, s'). (l, bounded_treesem r s' n))
        (bCollect (\<lambda>(l, (s', c')).
          (\<exists>\<alpha>. l = Local \<alpha> \<and> ((hl, hs), c) \<midarrow>\<alpha>\<rightarrow> (s', c')) \<or>
          (\<exists>hs'. l = Env \<and> c' = c \<and> s' = Inl (hl, hs') \<and> r hs hs'))))\<close>

definition treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) comm \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) sem_tree set\<close> where
  \<open>treesem r c p \<equiv> {bounded_treesem r (Inl s,c) n|s n. p s}\<close>


definition
  \<open>sem_tree_nocrash = pred_sem_tree (\<lambda>(s,c). \<exists>sx. s = Inl sx)\<close>

definition
  \<open>sem_tree_post q = pred_sem_tree (\<lambda>(s,c). \<forall>sx. c = Skip \<longrightarrow> s = Inl sx \<longrightarrow> q sx)\<close>

definition
  \<open>sem_tree_guar g =
    step_rel_sem_tree (\<lambda>l (s,c) (s',c').
      \<forall>\<alpha> h h'. l = Local \<alpha> \<longrightarrow> s = Inl h \<longrightarrow> s' = Inl h' \<longrightarrow> g (snd h) (snd h'))\<close>

definition
  \<open>sem_tree_frame_cond F =
    step_rel_sem_tree (\<lambda>l (s,c) (s',c').
      \<forall>\<alpha> hl hs hl' hs'. l = Local \<alpha> \<longrightarrow> s = Inl (hl,hs) \<longrightarrow> s' = Inl (hl',hs') \<longrightarrow>
        (\<forall>hlf.
          F (hlf, hs) \<longrightarrow>
          hlf
          True
        ))\<close>
\<comment> \<open> TODO! \<close>


inductive safe
  :: \<open>nat \<Rightarrow>
      ('l::pre_perm_alg \<times> 's, unit) comm \<Rightarrow>
      'l \<times> 's + unit \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      bool\<close>
  where
  safe_nil[intro!]: \<open>safe 0 c (Inl (hl, hs)) r g q S F\<close>
| safe_suc[intro]:
  \<open>\<comment> \<open> if the command is Skip, the postcondition is established \<close>
    \<comment> \<open> TODO: This requires termination is represented as infinite stuttering past the end.
               We may want a different model, but that would be more complicated. \<close>
    (c = Skip \<longrightarrow> q (hl, hs)) \<Longrightarrow>
    \<comment> \<open> the current state is in the stateset \<close>
    S (hl, hs) \<Longrightarrow>
    \<comment> \<open> rely steps are safe \<close>
    (\<And>hs'. r hs hs' \<Longrightarrow> safe n c (Inl (hl, hs')) r g q S F) \<Longrightarrow>
    \<comment> \<open> closed under opsteps \<close>
    (\<And>\<alpha> c' hl' hs'.
        ((hl,hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hl',hs'), c') \<Longrightarrow>
        safe n c' (Inl (hl', hs')) r g q S F \<and>
        (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<Longrightarrow>
    \<comment> \<open> closed under framed opsteps \<close>
    (\<And>\<alpha> c' hlf hlhlf' hs'.
        hl ## hlf \<Longrightarrow>
        ((hl + hlf, hs), c) \<midarrow>\<alpha>\<rightarrow> (Inl (hlhlf', hs'), c') \<Longrightarrow>
        F (hlf, hs) \<Longrightarrow>
        (\<exists>hl'.
          hl' ## hlf \<and>
          hlhlf' = hl' + hlf \<and>
          (\<alpha> = Tau \<longrightarrow> hl' = hl) \<and>
          safe n c' (Inl (hl', hs')) r g q S F) \<and>
        (\<alpha> \<noteq> Tau \<longrightarrow> g hs hs')) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    safe (Suc n) c (Inl (hl, hs)) r g q S F\<close>

end
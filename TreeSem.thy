theory TreeSem
  imports Soundness "HOL-Cardinals.Bounded_Set"
begin

section \<open> Bounded Set Utils \<close>

lemma bmember_bmap_iff:
  \<open>bmember y (map_bset f B) \<longleftrightarrow> (\<exists>x. bmember x B \<and> y = f x)\<close>
  by transfer (force simp add: image_def)

lemma bCollect_eq_bempty_iff:
  \<open>bCollect p = bempty \<longleftrightarrow> (\<nexists>x. p x)\<close>
  by (metis Collect_empty_eq bCollect.rep_eq bempty.rep_eq set_bset_inject)

lemma pred_bset_bempty[simp]:
  \<open>pred_bset p bempty\<close>
  by (simp add: bset.pred_rel)

lemma pred_bCollect_eq[simp]:
  \<open>pred_bset p (bCollect q) = (q \<le> p)\<close>
  by (simp add: bCollect.rep_eq bset.pred_set le_fun_def)

section \<open> Semantic Trees \<close>

datatype 'a label = Env | Local \<open>'a act\<close>

datatype ('c, 's, 'l) sem_tree =
  Branch
    (config_sem_tree: \<open>'s \<times> 'c\<close>)
    (branches_sem_tree:
      \<open>('l \<times> (('c, 's, 'l) sem_tree + unit)) set[('l \<times> (('s + unit) \<times> 'c)) set]\<close>)

lemma sem_tree_induct:
  \<open>(\<And>ty.
      (\<And>l tx.
        (l, Inl tx) \<in> set_bset (branches_sem_tree ty) \<Longrightarrow>
        P tx) \<Longrightarrow>
      P ty) \<Longrightarrow>
    P t\<close>
  apply (rule sem_tree.induct)
  apply (clarsimp simp add: image_def Bex_def)
  apply (metis sem_tree.sel(2) setl.intros)
  done

function pred_sem_tree
  :: \<open>('s \<times> 'c \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
  \<open>pred_sem_tree p (Branch sc S) =
    (p sc \<and> pred_bset (\<lambda>v. case v of (l,mt') \<Rightarrow> case_sum (pred_sem_tree p) (\<lambda>_. False) mt') S)\<close>
  by pat_completeness auto
termination
  apply (relation
      \<open>{((xa,ta),(xb,tb)). xa = xb \<and> (\<exists>l. (l, Inl ta) \<in> set_bset (branches_sem_tree tb))}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply force
  done

function step_rel_sem_tree
  :: \<open>('l \<Rightarrow> 's \<Rightarrow> 's + unit \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
  \<open>step_rel_sem_tree r (Branch (s, c) S) =
      pred_bset
        (\<lambda>(l,mt'). r l s (map_sum (fst \<circ> config_sem_tree) id mt') \<and>
                   (\<forall>t'. mt' = Inl t' \<longrightarrow> step_rel_sem_tree r t'))
        S\<close>
  by pat_completeness auto
termination
  apply (relation
      \<open>{((xa,ta),(xb,tb)). xa = xb \<and> (\<exists>l. (l, Inl ta) \<in> set_bset (branches_sem_tree tb))}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply force
  done


function steps_pred_sem_tree
  :: \<open>(('s \<times> 'l \<times> ('s + unit)) set \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
  \<open>steps_pred_sem_tree p (Branch (s,c) S) =
    (p (set_bset (map_bset (\<lambda>(l, mt'). (s, l, map_sum (fst \<circ> config_sem_tree) id mt')) S)) \<and>
      pred_bset (\<lambda>v. \<forall>l t'. v = (l, Inl t') \<longrightarrow> steps_pred_sem_tree p t') S)\<close>
  by pat_completeness auto
termination
  apply (relation
      \<open>{((xa,ta),(xb,tb)). xa = xb \<and> (\<exists>l. (l, Inl ta) \<in> set_bset (branches_sem_tree tb))}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply force
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
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l::pre_perm_alg \<times> 's) \<times> ('l \<times> 's, unit) comm \<Rightarrow>
      nat \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree\<close>
  where
  \<open>bounded_treesem r F sc 0 = Branch sc bempty\<close>
| \<open>bounded_treesem r F (s, c) (Suc n) =
    Branch (s, c)
      (map_bset (apsnd
        (\<lambda>(z', c').
          case z' of
            Inl s' \<Rightarrow> Inl (bounded_treesem r F (s', c') n)
          | Inr () \<Rightarrow> Inr ()))
        (bCollect
          (\<lambda>(l, (z', c')).
              (\<exists>\<alpha>. l = Local \<alpha> \<and> (s, c) \<midarrow>\<alpha>\<rightarrow> (z', c')) \<or>
              (\<exists>hs'. l = Env \<and> r (snd s) hs' \<and> z' = Inl (fst s, hs') \<and> c' = c))))\<close>

(* TODO: precondition limitations *)

(*
definition treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's, unit) comm \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree set\<close> where
  \<open>treesem r c \<equiv> range (bounded_treesem r c)\<close>
*)


definition sem_tree_nocrash
  :: \<open>(('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
  \<open>sem_tree_nocrash \<equiv> step_rel_sem_tree (\<lambda>_ _ z'. z' \<noteq> Inr ())\<close>

definition sem_tree_post
  :: \<open>('s \<Rightarrow> bool) \<Rightarrow>
      (('s, unit) comm, 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_post q \<equiv> pred_sem_tree (\<lambda>(s,c). c = Skip \<longrightarrow> q s)\<close>

definition sem_tree_guar
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_guar g \<equiv>
    step_rel_sem_tree (\<lambda>l s z'. \<forall>\<alpha> s'. l = Local \<alpha> \<longrightarrow> z' = Inl s' \<longrightarrow> g (snd s) (snd s'))\<close>

definition sem_tree_states
  :: \<open>('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_states S \<equiv> pred_sem_tree (S \<circ> fst)\<close>

definition sem_tree_frame_cond
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_frame_cond F \<equiv>
    steps_pred_sem_tree (\<lambda>S.
      \<forall>\<alpha> hl hs hl' hs'.
        ((hl, hs), Local \<alpha>, (Inl (hl', hs'))) \<in> S \<longrightarrow>
        (\<forall>hlf hlhlf'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow>
          ((hl + hlf, hs), Local \<alpha>, (Inl (hlhlf', hs'))) \<in> S \<longrightarrow>
          (\<exists>hl'. hl' ## hlf \<and> hlhlf' = hl' + hlf)))\<close>


definition sem_tree_safe
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's, unit) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_safe q g S \<equiv>
    sem_tree_nocrash \<sqinter>
    sem_tree_post q \<sqinter>
    sem_tree_guar g \<sqinter>
    sem_tree_states S\<close>


lemma safe_then_sem_tree_safe:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    sem_tree_safe q g S (bounded_treesem r F (s, c) n)\<close>
  apply (induct arbitrary: s rule: safe.inducts)
  sorry

lemma sem_tree_safe_then_safe:
  \<open>sem_tree_safe q g S (bounded_treesem r F (s, c) n) \<Longrightarrow>
    safe n c (Inl s) r g q S F\<close>
  apply (induct n arbitrary: s c)
  sorry

theorem safe_iff_sem_tree_safe:
  \<open>safe n c (Inl s) r g q S F \<longleftrightarrow> sem_tree_safe q g S (bounded_treesem r F (s, c) n)\<close>
  using safe_then_sem_tree_safe sem_tree_safe_then_safe
  by fast


end
theory TreeSem
  imports Soundness "HOL-Cardinals.Bounded_Set"
begin

section \<open> utils \<close>

lemma disjCE:
  \<open>P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not> P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
  by blast

lemma map_sum_rev_iff[simp]:
  \<open>map_sum f g s = Inl a' \<longleftrightarrow> (\<exists>a. s = Inl a \<and> a' = f a)\<close>
  \<open>map_sum f g s = Inr b' \<longleftrightarrow> (\<exists>b. s = Inr b \<and> b' = g b)\<close>
  by (metis Inl_Inr_False isl_def isl_map_sum map_sum_sel sum.exhaust_sel sum.sel)+

section \<open> Bounded Set Utils \<close>

lemma bmember_bmap_iff:
  \<open>bmember y (map_bset f B) \<longleftrightarrow> (\<exists>x. bmember x B \<and> y = f x)\<close>
  by transfer (force simp add: image_def)

lemma bCollect_eq_bempty_iff[simp]:
  \<open>bCollect p = bempty \<longleftrightarrow> (\<nexists>x. p x)\<close>
  by (metis Collect_empty_eq bCollect.rep_eq bempty.rep_eq set_bset_inject)

lemma pred_bset_bempty[simp]:
  \<open>pred_bset p bempty\<close>
  by (simp add: bset.pred_rel)

lemma pred_bCollect_eq[simp]:
  \<open>pred_bset p (bCollect q) = (q \<le> p)\<close>
  by (simp add: bCollect.rep_eq bset.pred_set le_fun_def)

declare bempty.rep_eq[simp]
declare map_bset.rep_eq[simp]
declare bCollect.rep_eq[simp]

thm bset.pred_map


section \<open> Semantic Trees \<close>

datatype 'a label = Env | Local \<open>'a act\<close>

datatype ('c, 's, 'l) sem_tree =
  Branch
    (config_sem_tree: \<open>'s \<times> 'c\<close>)
    \<comment> \<open> This stores every framed state greater than some base state. \<close>
    (branches_sem_tree:
      \<open>('s \<times> 'l \<times> (('s \<times> ('c, 's, 'l) sem_tree) + unit)) set[('s \<times> 'l \<times> (('s + unit) \<times> 'c)) set]\<close>)

lemma sem_tree_induct:
  \<open>(\<And>ty.
      (\<And>s l s' tx.
        (s, l, Inl (s', tx)) \<in> set_bset (branches_sem_tree ty) \<Longrightarrow>
        P tx) \<Longrightarrow>
      P ty) \<Longrightarrow>
    P t\<close>
  apply (rule sem_tree.induct)
  apply (clarsimp simp add: image_def Bex_def)
  apply fastforce
  done

function pred_sem_tree
  :: \<open>('s \<times> 'c \<Rightarrow>
        ('s \<times> 'l \<times> (('s \<times> ('c, 's, 'l) sem_tree) + unit)) set[('s \<times> 'l \<times> (('s + unit) \<times> 'c)) set] \<Rightarrow>
        bool) \<Rightarrow>
      ('c, 's, 'l) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>pred_sem_tree p (Branch sc S) =
    (p sc S \<and>
      pred_bset
        (\<lambda>(s,l,mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> pred_sem_tree p t')
        S)\<close>
  by pat_completeness auto
termination
  apply (relation
      \<open>{((xa,ta),(xb,tb)).
          xa = xb \<and> (\<exists>s l s'. (s, l, Inl (s', ta)) \<in> set_bset (branches_sem_tree tb))}\<close>)
   apply (clarsimp simp add: wf_def, rule sem_tree_induct, blast)
  apply force
  done


definition config_pred_sem_tree
  :: \<open>('s \<times> 'c \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>config_pred_sem_tree p t \<equiv> pred_sem_tree (\<lambda>sc S. S \<noteq> bempty \<longrightarrow> p sc) t\<close>

definition precond_pred_sem_tree
  :: \<open>('s set \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>precond_pred_sem_tree P t \<equiv> pred_sem_tree (\<lambda>_ S. P (fst ` set_bset S)) t\<close>

definition step_rel_sem_tree :: \<open>('l \<Rightarrow> 's \<Rightarrow> 's + unit \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>step_rel_sem_tree r t =
      pred_sem_tree (\<lambda>c S. \<forall>s l mst'. (s,l,mst') \<in> set_bset S \<longrightarrow> r l s (map_sum fst id mst')) t\<close>

definition steps_pred_sem_tree
  :: \<open>('s \<Rightarrow> ('s \<times> 'l \<times> ('s + unit)) set \<Rightarrow> bool) \<Rightarrow> ('c, 's, 'l) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>steps_pred_sem_tree P t \<equiv>
      pred_sem_tree
        (\<lambda>sc S. P (fst sc) (set_bset (map_bset (\<lambda>(sb, l, mst'). (sb, l, map_sum fst id mst')) S)))
        t\<close>

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
      ('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) \<times> ('l \<times> 's) comm \<Rightarrow>
      nat \<Rightarrow>
      (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree\<close>
  where
  \<open>bounded_treesem r F sc 0 = Branch sc bempty\<close>
| \<open>bounded_treesem r F ((hl,hs), c) (Suc n) =
    Branch ((hl,hs), c)
      (map_bset
        (apsnd (apsnd (\<lambda>(z', c').
          (map_sum (\<lambda>s'. (s', bounded_treesem r F (s',c') n)) id z'))))
        (bCollect
          (\<lambda>((hlx,hsx), l, (z', c')).
              hsx = hs \<and> (
                (hlx = hl \<or> (\<exists>hlf. F (hlf, hsx) \<and> hl ## hlf \<and> hlx = hl + hlf)) \<and>
                  (\<exists>\<alpha>. l = Local \<alpha> \<and> ((hlx,hsx), c) \<midarrow>\<alpha>\<rightarrow> (z', c')) \<or>
                (hlx = hl \<and> c' = c \<and> (\<exists>hsx'. l = Env \<and> r hsx hsx' \<and>
                  z' = Inl (hlx, hsx')))))))\<close>

lemma precond_pred_sem_tree_mono:
  \<open>p \<le> q \<Longrightarrow> pred_sem_tree p t \<Longrightarrow> pred_sem_tree q t\<close>
  apply (induct t)
  apply (clarsimp split: prod.splits)
  apply (rule conjI, blast)
  apply (rule bset.pred_mono_strong, assumption)
  apply (clarsimp split: sum.splits)
  done

lemmas precond_pred_sem_tree_monoD = precond_pred_sem_tree_mono[rotated]

lemma bounded_treesem_least_state:
  \<open>pred_sem_tree
    (\<lambda>(s,c) S.
        set_bset S \<noteq> {} \<longrightarrow> (\<forall>hlx hsx l mzt'.
          ((hlx,hsx), l, mzt') \<in> set_bset S \<longrightarrow> fst s \<preceq> hlx))
    (bounded_treesem r F sc n)\<close>
  apply (induct n arbitrary: sc)
   apply force
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (metis less_eq_sepadd_def)
  apply (clarsimp simp add: bset.pred_map map_sum_def split: sum.splits)
  done

(*
definition treesem
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's) comm \<Rightarrow>
      (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree set\<close> where
  \<open>treesem r c \<equiv> range (bounded_treesem r c)\<close>
*)


definition sem_tree_nocrash
  :: \<open>(('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_nocrash \<equiv> step_rel_sem_tree (\<lambda>_ _ z'. z' \<noteq> Inr ())\<close>

definition sem_tree_postcond
  :: \<open>('s \<Rightarrow> bool) \<Rightarrow> ('s comm, 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_postcond q \<equiv> config_pred_sem_tree (\<lambda>(s,c). c = Skip \<longrightarrow> q s)\<close>

definition sem_tree_guar
  :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_guar g \<equiv>
      step_rel_sem_tree (\<lambda>l s z'. \<forall>\<alpha> s'. l = Local \<alpha> \<longrightarrow> z' = Inl s' \<longrightarrow> g (snd s) (snd s'))\<close>

definition sem_tree_states
  :: \<open>('l \<times> 's \<Rightarrow> bool) \<Rightarrow> (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow> bool\<close>
  where
    \<open>sem_tree_states S \<equiv> config_pred_sem_tree (S \<circ> fst)\<close>

definition sem_tree_frame_cond
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_frame_cond F \<equiv>
    steps_pred_sem_tree (\<lambda>(hl,hs) B.
      \<forall>\<alpha> hl' hs'.
        ((hl, hs), Local \<alpha>, Inl (hl', hs')) \<in> B \<longrightarrow>
        (\<forall>hlf hlhlf'.
          F (hlf, hs) \<longrightarrow>
          hl ## hlf \<longrightarrow> 
          ((hl + hlf, hs), Local \<alpha>, Inl (hlhlf', hs')) \<in> B \<longrightarrow>
          (\<exists>hl'. hl' ## hlf \<and> hlhlf' = hl' + hlf)))\<close>

definition sem_tree_safe
  :: \<open>('l::pre_perm_alg \<times> 's \<Rightarrow> bool) \<Rightarrow>
      ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
      ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> 's) comm, 'l \<times> 's, unit label) sem_tree \<Rightarrow>
      bool\<close>
  where
  \<open>sem_tree_safe q g S \<equiv>
    sem_tree_nocrash \<sqinter>
    sem_tree_postcond q \<sqinter>
    sem_tree_guar g \<sqinter>
    sem_tree_states S\<close>

paragraph \<open> defined tree predicate simp thms \<close>

lemma config_pred_sem_tree_simps[simp]:
  \<open>config_pred_sem_tree p (Branch sc S) =
    ((S \<noteq> bempty \<longrightarrow> p sc) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> config_pred_sem_tree p t')
        S)\<close>
  unfolding config_pred_sem_tree_def
  by simp

lemma step_rel_sem_tree_simps[simp]:
  \<open>step_rel_sem_tree r (Branch sc S) =
    ((\<forall>s l mst'. (s, l, mst') \<in> set_bset S \<longrightarrow> r l s (map_sum fst id mst')) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> step_rel_sem_tree r t')
        S)\<close>
  unfolding step_rel_sem_tree_def
  by simp

lemma sem_tree_nocrash_simps[simp]:
  \<open>sem_tree_nocrash (Branch sc S) =
    ((\<forall>s l mst'. (s, l, mst') \<in> set_bset S \<longrightarrow> mst' \<noteq> Inr ()) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> sem_tree_nocrash t')
      S)\<close>
  unfolding sem_tree_nocrash_def
  by simp

lemma sem_tree_postcond_simps[simp]:
  \<open>sem_tree_postcond q (Branch sc S) =
    ((S \<noteq> bempty \<longrightarrow> snd sc = Skip \<longrightarrow> q (fst sc)) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> sem_tree_postcond q t')
      S)\<close>
  unfolding sem_tree_postcond_def
  by force

lemma sem_tree_guar_simps[simp]:
  \<open>sem_tree_guar g (Branch sc S) =
    ((\<forall>s \<alpha> s' t'. (s, Local \<alpha>, Inl (s', t')) \<in> set_bset S \<longrightarrow> g (snd s) (snd s')) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> sem_tree_guar g t')
      S)\<close>
  unfolding sem_tree_guar_def
  by force

lemma sem_tree_states_simps[simp]:
  \<open>sem_tree_states ss (Branch sc S) =
    ((S \<noteq> bempty \<longrightarrow> ss (fst sc)) \<and>
      pred_bset
        (\<lambda>(s, l, mst'). \<forall>s' t'. mst' = Inl (s', t') \<longrightarrow> sem_tree_states ss t')
      S)\<close>
  unfolding sem_tree_states_def
  by force


subsection \<open> equivalence with safe \<close>

lemma safe_then_sem_tree_safe:
  \<open>safe n c z r g q S F \<Longrightarrow>
    z = Inl s \<Longrightarrow>
    sem_tree_safe q g S (bounded_treesem r F (s, c) n)\<close>
  unfolding sem_tree_safe_def sem_tree_nocrash_def sem_tree_postcond_def sem_tree_guar_def
    sem_tree_states_def step_rel_sem_tree_def config_pred_sem_tree_def
  apply (induct arbitrary: s rule: safe.inducts)
   apply force
  apply (clarsimp simp add: bset.pred_map split: prod.splits)
  apply (intro conjI allI impI)
       apply (clarsimp simp add: image_def)
       apply blast
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
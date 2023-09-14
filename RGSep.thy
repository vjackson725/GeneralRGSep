theory RGSep
  imports Stabilisation
begin

definition \<open>rel_liftL p \<equiv> \<lambda>a b. p a\<close>
definition \<open>rel_liftR p \<equiv> \<lambda>a b. p b\<close>

lemma rel_liftL_unfold[simp]:
  \<open>rel_liftL p a b = p a\<close>
  by (simp add: rel_liftL_def)

lemma rel_liftR_unfold[simp]:
  \<open>rel_liftR p a b = p b\<close>
  by (simp add: rel_liftR_def)

lemma liftL_le_liftL[simp]:
  \<open>rel_liftL p \<le> rel_liftL q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: rel_liftL_def le_fun_def)

lemma liftR_le_liftR[simp]:
  \<open>rel_liftR p \<le> rel_liftR q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: rel_liftR_def)

section \<open> Language Definition \<close>

datatype 'h comm =
  Done (\<open>\<checkmark>\<close>)
  | Seq \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Ndet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>+\<close> 65)
(*
  | ExtNdet \<open>'h comm\<close> \<open>'h comm\<close> (infixr \<open>\<^bold>\<box>\<close> 65)
*)
  | Iter \<open>'h comm\<close> \<open>'h \<Rightarrow> bool\<close> (\<open>_\<^sup>\<star>\<^bsub>_\<^esub>\<close> [80,0] 80)
  | Basic \<open>'h \<Rightarrow> 'h \<Rightarrow> bool\<close>

datatype 'h act =
    Tau
  | Env 'h 'h

lemma act_neq_iff[simp]:
  \<open>a \<noteq> Tau \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  \<open>Tau \<noteq> a \<longleftrightarrow> (\<exists>x y. a = Env x y)\<close>
  by (metis act.distinct(1) act.exhaust)+


paragraph \<open> Predicate to ensure that loop invariants have a given property \<close>

inductive all_loop_inv :: \<open>(('h \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_loop_inv p Done\<close>
| seq[intro!]: \<open>all_loop_inv p c1 \<Longrightarrow> all_loop_inv p c2 \<Longrightarrow> all_loop_inv p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_loop_inv p c1 \<Longrightarrow> all_loop_inv p c2 \<Longrightarrow> all_loop_inv p (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>all_loop_inv p c1 \<Longrightarrow> all_loop_inv p c2 \<Longrightarrow> all_loop_inv p (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>all_loop_inv p c \<Longrightarrow> p i \<Longrightarrow> all_loop_inv p (c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
| basic[intro!]: \<open>all_loop_inv p (Basic b)\<close>

inductive_cases all_loop_inv_doneE[elim!]: \<open>all_loop_inv p Done\<close>
inductive_cases all_loop_inv_seqE[elim!]: \<open>all_loop_inv p (c1 ;; c2)\<close>
inductive_cases all_loop_inv_ndetE[elim!]: \<open>all_loop_inv p (c1 \<^bold>+ c2)\<close>
inductive_cases all_loop_inv_parE[elim!]: \<open>all_loop_inv p (c1 \<parallel> c2)\<close>
inductive_cases all_loop_inv_iterE[elim!]: \<open>all_loop_inv p (c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
inductive_cases all_loop_inv_basicE[elim!]: \<open>all_loop_inv p (Basic b)\<close>

lemma all_loop_inv_simps[simp]:
  \<open>all_loop_inv p Done \<longleftrightarrow> True\<close>
  \<open>all_loop_inv p (c1 ;; c2) \<longleftrightarrow> all_loop_inv p c1 \<and> all_loop_inv p c2\<close>
  \<open>all_loop_inv p (c1 \<^bold>+ c2) \<longleftrightarrow> all_loop_inv p c1 \<and> all_loop_inv p c2\<close>
  \<open>all_loop_inv p (c1 \<parallel> c2) \<longleftrightarrow> all_loop_inv p c1 \<and> all_loop_inv p c2\<close>
  \<open>all_loop_inv p (c\<^sup>\<star>\<^bsub>i\<^esub>) \<longleftrightarrow> p i \<and> all_loop_inv p c\<close>
  \<open>all_loop_inv p (Basic b) \<longleftrightarrow> True\<close>
  by fastforce+


paragraph \<open> Predicate to ensure basic actions have a given property \<close>

inductive all_basic_comm :: \<open>(('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'h comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_basic_comm p Done\<close>
| seq[intro!]: \<open>all_basic_comm p c1 \<Longrightarrow> all_basic_comm p c2 \<Longrightarrow> all_basic_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_basic_comm p c1 \<Longrightarrow> all_basic_comm p c2 \<Longrightarrow> all_basic_comm p (c1 \<parallel> c2)\<close>
| ndet[intro!]: \<open>all_basic_comm p c1 \<Longrightarrow> all_basic_comm p c2 \<Longrightarrow> all_basic_comm p (c1 \<^bold>+ c2)\<close>
| iter[intro!]: \<open>all_basic_comm p c \<Longrightarrow> all_basic_comm p (c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
| basic[intro!]: \<open>p b \<Longrightarrow> all_basic_comm p (Basic b)\<close>

inductive_cases all_basic_comm_doneE[elim!]: \<open>all_basic_comm p Done\<close>
inductive_cases all_basic_comm_seqE[elim!]: \<open>all_basic_comm p (c1 ;; c2)\<close>
inductive_cases all_basic_comm_ndetE[elim!]: \<open>all_basic_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_basic_comm_parE[elim!]: \<open>all_basic_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_basic_comm_iterE[elim!]: \<open>all_basic_comm p (c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
inductive_cases all_basic_comm_basicE[elim!]: \<open>all_basic_comm p (Basic b)\<close>

lemma all_basic_comm_simps[simp]:
  \<open>all_basic_comm p Done \<longleftrightarrow> True\<close>
  \<open>all_basic_comm p (c1 ;; c2) \<longleftrightarrow> all_basic_comm p c1 \<and> all_basic_comm p c2\<close>
  \<open>all_basic_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_basic_comm p c1 \<and> all_basic_comm p c2\<close>
  \<open>all_basic_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_basic_comm p c1 \<and> all_basic_comm p c2\<close>
  \<open>all_basic_comm p (c\<^sup>\<star>\<^bsub>i\<^esub>) \<longleftrightarrow> all_basic_comm p c\<close>
  \<open>all_basic_comm p (Basic b) \<longleftrightarrow> p b\<close>
  by fastforce+

abbreviation \<open>basics_guarantee g \<equiv> all_basic_comm ((\<le>) g)\<close>

subsection \<open> For the variable restriction \<close>

definition
  \<open>basic_frame_pred p c \<equiv>
    all_basic_comm
      (\<lambda>b. \<forall>h1 hf h'. p hf \<longrightarrow> b (h1 + hf) h' \<longrightarrow> (\<exists>h2. b h1 h2 \<and> h2 ## hf \<and> h' = h2 + hf))
      c\<close>

lemma basic_frame_pred_simps[simp]:
  \<open>basic_frame_pred p Done \<longleftrightarrow> True\<close>
  \<open>basic_frame_pred p (c1 ;; c2) \<longleftrightarrow> basic_frame_pred p c1 \<and> basic_frame_pred p c2\<close>
  \<open>basic_frame_pred p (c1 \<^bold>+ c2) \<longleftrightarrow> basic_frame_pred p c1 \<and> basic_frame_pred p c2\<close>
  \<open>basic_frame_pred p (c1 \<parallel> c2) \<longleftrightarrow> basic_frame_pred p c1 \<and> basic_frame_pred p c2\<close>
  \<open>basic_frame_pred p (c\<^sup>\<star>\<^bsub>i\<^esub>) \<longleftrightarrow> basic_frame_pred p c\<close>
  \<open>basic_frame_pred p (Basic b) \<longleftrightarrow>
    (\<forall>h1 hf h'. p hf \<longrightarrow> b (h1 + hf) h' \<longrightarrow> (\<exists>h2. b h1 h2 \<and> h2 ## hf \<and> h' = h2 + hf))\<close>
  by (fastforce simp add: basic_frame_pred_def)+

lemma basic_frame_pred_antimono:
  \<open>p \<le> q \<Longrightarrow> basic_frame_pred q c \<Longrightarrow> basic_frame_pred p c\<close>
  by (induct c arbitrary: p q)
    (fastforce simp add: basic_frame_pred_def)+

section \<open> Operational Semantics \<close>

inductive opsem :: \<open>('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> 'h act \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> 'h \<times> 'h comm \<Rightarrow> bool\<close> where
  seq_left[intro!]: \<open>opsem r a (h,c1) (h',c1') \<Longrightarrow> opsem r a (h, c1 ;; c2) (h', c1' ;; c2)\<close>
| seq_right[intro!]: \<open>opsem r Tau (h, Done ;; c2) (h, c2)\<close>
| ndet_left[intro!]: \<open>opsem r Tau (h, s \<^bold>+ t) (h, s)\<close>
| ndet_right[intro!]: \<open>opsem r Tau (h, s \<^bold>+ t) (h, t)\<close>
(*
| extndet_resolve_left[intro]:
  \<open>opsem r a (h, c1) (h', c1') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem r a (h, c1 \<^bold>\<box> c2) (h', c1')\<close>
| extndet_resolve_right[intro]:
  \<open>opsem r a (h, c2) (h', c2') \<Longrightarrow> a \<noteq> Tau \<Longrightarrow> opsem r a (h, c1 \<^bold>\<box> c2) (h', c2')\<close>
| extndet_step_left[intro]:
  \<open>opsem r Tau (h, c1) (h', c1') \<Longrightarrow> opsem r Tau (h, c1 \<^bold>\<box> c2) (h', c1' \<^bold>\<box> c2)\<close>
| extndet_step_right[intro]:
  \<open>opsem r Tau (h, c2) (h', c2') \<Longrightarrow> opsem r Tau (h, c1 \<^bold>\<box> c2) (h', c1 \<^bold>\<box> c2')\<close>
*)
| par_step_left[intro]: \<open>opsem r a (h, s) (h', s') \<Longrightarrow> opsem r a (h, s \<parallel> t) (h', s' \<parallel> t)\<close>
| par_step_right[intro]: \<open>opsem r a (h, t) (h', t') \<Longrightarrow> opsem r a (h, s \<parallel> t) (h', s \<parallel> t')\<close>
| par_left[intro!]: \<open>opsem r Tau (h, Done \<parallel> t) (h, t)\<close>
| par_right[intro!]: \<open>opsem r Tau (h, s \<parallel> Done) (h, s)\<close>
| iter[intro]: \<open>opsem r Tau (h, c\<^sup>\<star>\<^bsub>i\<^esub>) (h, (Done \<^bold>+ c) ;; c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
| basic[intro!]: \<open>g h h' \<Longrightarrow> opsem r Tau (h, Basic g) (h', Done)\<close>
| env[intro!]: \<open>r h h' \<Longrightarrow> opsem r (Env h h') (h, t) (h', t)\<close>

inductive_cases opsem_seqE[elim!]: \<open>opsem r a (h, c1 ;; c2) (h', c')\<close>
inductive_cases opsem_ndetE[elim!]: \<open>opsem r a (h, c1 \<^bold>+ c2) (h', c')\<close>
inductive_cases opsem_parE[elim!]: \<open>opsem r a (h, c1 \<parallel>  c2) (h', c')\<close>
inductive_cases opsem_iterE[elim!]: \<open>opsem r a (h, c\<^sup>\<star>\<^bsub>i\<^esub>) (h', c')\<close>
inductive_cases opsem_basicE[elim!]: \<open>opsem r a (h, Basic g) (h', c')\<close>
inductive_cases opsem_skipE[elim!]: \<open>opsem r a (h, Done) (h', c')\<close>
inductive_cases opsem_envE[elim]: \<open>opsem r (Env x y) s s'\<close>

lemma opsem_tau_iff:
  \<open>opsem r Tau (h, c1 ;; c2) s' \<longleftrightarrow>
    c1 = Done \<and> s' = (h, c2) \<or> (\<exists>h' c1'. opsem r Tau (h,c1) (h',c1') \<and> s' = (h', c1' ;; c2))\<close>
  \<open>opsem r Tau (h, c1 \<parallel> c2) s' \<longleftrightarrow>
    c1 = Done \<and> s' = (h, c2) \<or>
    c2 = Done \<and> s' = (h, c1) \<or>
    (\<exists>h' c1'. opsem r Tau (h,c1) (h',c1') \<and> s' = (h', c1' \<parallel> c2) \<or>
    (\<exists>h' c2'. opsem r Tau (h,c2) (h',c2') \<and> s' = (h', c1 \<parallel> c2')))\<close>
  \<open>opsem r Tau (h, c1 \<^bold>+ c2) s' \<longleftrightarrow> s' = (h, c2) \<or> s' = (h, c1)\<close>
  \<open>opsem r Tau (h, c\<^sup>\<star>\<^bsub>i\<^esub>) s' \<longleftrightarrow> s' = (h, (Done \<^bold>+ c) ;; c\<^sup>\<star>\<^bsub>i\<^esub>)\<close>
  \<open>opsem r Tau (h, Basic g) s' \<longleftrightarrow> (\<exists>h'. g h h' \<and> s' = (h', Done))\<close>
  by (cases s', force)+

lemma opsem_envD:
  \<open>opsem r a s s' \<Longrightarrow> a = Env x y \<Longrightarrow> fst s = x \<and> fst s' = y \<and> snd s' = snd s \<and> r x y\<close>
  by (induct arbitrary: x y rule: opsem.induct) simp+

lemma opsem_env_iff:
  \<open>opsem r (Env x y) s s' \<longleftrightarrow> fst s = x \<and> fst s' = y \<and> snd s' = snd s \<and> r x y\<close>
  by (metis env opsem_envD prod.collapse)

subsubsection \<open>sugared atomic programs\<close>

definition \<open>passert p \<equiv> \<lambda>a b. p a \<and> a = b\<close>

abbreviation \<open>Assert p \<equiv> Basic (passert p)\<close>
abbreviation \<open>Assume p \<equiv> Basic (rel_liftR p)\<close>
abbreviation \<open>Skip \<equiv> Basic (passert \<top>)\<close>

lemma passert_simps[simp]:
  \<open>passert p a b \<longleftrightarrow> p a \<and> b = a\<close>
  by (force simp add: passert_def)

lemma opsem_assert[intro!]: \<open>p h \<Longrightarrow> opsem r Tau (h, Assert p) (h, Done)\<close>
  by (simp add: opsem.basic passert_def)

lemma opsem_assume[intro!]: \<open>q h' \<Longrightarrow> opsem r Tau (h, Assume q) (h', Done)\<close>
  by (simp add: opsem.basic rel_liftR_def)

lemma opsem_skip[intro!]: \<open>opsem r Tau (h, Skip) (h, Done)\<close>
  by (simp add: opsem.basic passert_def)

subsubsection \<open> Sugared programs \<close>

abbreviation \<open>IfThenElse p ct cf \<equiv> Assert p ;; ct \<^bold>+ Assert (-p) ;; cf\<close>
abbreviation \<open>WhileLoop p c \<equiv> (Assert p ;; c)\<^sup>\<star>\<^bsub>i\<^esub> ;; Assert (-p)\<close>

paragraph \<open> Pretty operational semantics \<close>

abbreviation(input) pretty_opsem :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow> _\<close> [60,0,60] 60) where
  \<open>hs \<midarrow>r, a\<rightarrow> ht \<equiv> opsem r a hs ht\<close>

lemma opsem_rely_monoD:
  \<open>s \<midarrow>r, a\<rightarrow> s' \<Longrightarrow> r \<le> r' \<Longrightarrow> s \<midarrow>r', a\<rightarrow> s'\<close>
  by (induct rule: opsem.induct) force+

lemmas opsem_rely_mono = opsem_rely_monoD[rotated]

subsection \<open> Operational semantics transitive closure \<close>

(* TODO: infinite behaviour *)
(* TODO: actions *)
inductive opsem_rtrancl
  :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a act list \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> 'a \<times> 'a comm \<Rightarrow> bool\<close>
  where
  base[intro!]: \<open>opsem_rtrancl r [] s s\<close>
| step[intro!]: \<open>s \<midarrow>r, a\<rightarrow> s' \<Longrightarrow> opsem_rtrancl r as s' s'' \<Longrightarrow> opsem_rtrancl r (a # as) s s''\<close>

inductive_cases opsem_rtrancl_NilE[elim!]: \<open>opsem_rtrancl r [] s s'\<close>
inductive_cases opsem_rtrancl_ConsE[elim!]: \<open>opsem_rtrancl r (a # as) s s'\<close>

lemma opsem_rtrancl_iff[simp]:
  \<open>opsem_rtrancl r [] s s' \<longleftrightarrow> s' = s\<close>
  \<open>opsem_rtrancl r (a # as) s s'' \<longleftrightarrow> (\<exists>s'. (s \<midarrow>r, a\<rightarrow> s') \<and> opsem_rtrancl r as s' s'')\<close>
  by force+

paragraph \<open> pretty opsem transitive closure \<close>

abbreviation(input) pretty_opsem_rtrancl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_, _)\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> _\<close> [60,0,0,60] 60) where
  \<open>hs \<midarrow>r, as\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> ht \<equiv> opsem_rtrancl r as hs ht\<close>

subsection \<open> Theorems about the operational semantics \<close>

paragraph \<open> Reverse-cons transitive closure rules \<close>

lemma opsem_rtrancl_step_rev:
  \<open>opsem_rtrancl r as s s' \<Longrightarrow> s' \<midarrow>r, a\<rightarrow> s'' \<Longrightarrow> opsem_rtrancl r (as @ [a]) s s''\<close>
  apply (induct rule: opsem_rtrancl.induct)
   apply (metis append_self_conv2 opsem_rtrancl.simps)
  apply force
  done

lemma opsem_rtrancl_step_revE:
  \<open>opsem_rtrancl r (as @ [a]) s s'' \<Longrightarrow> (\<And>s'. opsem_rtrancl r as s s' \<Longrightarrow> opsem r a s' s'' \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (induct as arbitrary: r a s s'') force+

lemma opsem_rtrancl_rev_cons_iff[simp]:
  \<open>opsem_rtrancl r (as @ [a]) s s'' \<longleftrightarrow> (\<exists>s'. opsem_rtrancl r as s s' \<and> (s' \<midarrow>r, a\<rightarrow> s''))\<close>
  by (meson opsem_rtrancl_step_rev opsem_rtrancl_step_revE)


lemma opsem_rtrancl_rely_monoD:
  \<open>s \<midarrow>r, as\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s' \<Longrightarrow> r \<le> r' \<Longrightarrow> s \<midarrow>r', as\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s'\<close>
  by (induct rule: opsem_rtrancl.induct)
    (fastforce dest: opsem_rely_monoD[where r'=r'])+

lemmas opsem_rtrancl_rely_mono = opsem_rtrancl_rely_monoD[rotated]

lemma opsem_rtrancl_stepI:
  \<open>s \<midarrow>r, a\<rightarrow> s' \<Longrightarrow> s \<midarrow>r, [a]\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s'\<close>
  by blast

lemma opsem_rtrancl_trans:
  \<open>s \<midarrow>r1, as1\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s' \<Longrightarrow> s' \<midarrow>r2, as2\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s'' \<Longrightarrow> s \<midarrow>r1 \<squnion> r2, as1 @ as2\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s''\<close>
  by (induct arbitrary: r2 as2 s'' rule: opsem_rtrancl.induct)
    (force intro: opsem_rely_mono opsem_rtrancl_rely_mono)+

lemma opsem_rtrancl_rev_induct[consumes 1, case_names Nil Snoc]:
  \<open>opsem_rtrancl r as s s' \<Longrightarrow>
    (\<And>r s. P r [] s s) \<Longrightarrow>
    (\<And>s r a s' as s''.
      opsem_rtrancl r as s s' \<Longrightarrow>
      opsem r a s' s'' \<Longrightarrow>
      P r as s s' \<Longrightarrow>
      P r (as @ [a]) s s'') \<Longrightarrow>
    P r as s s'\<close>
  by (induct as arbitrary: s s' rule: rev_induct) force+

lemma done_stuck:
  \<open>\<nexists>s'. (h, Done)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by force

lemma blocked_basic_stuck:
  \<open>\<nexists>h'. g h h' \<Longrightarrow> \<nexists>s'. (h, Basic g)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by force

lemma nondone_nonstuck:
  \<open>c \<noteq> Done \<Longrightarrow> \<forall>x. \<exists>y. g x y \<Longrightarrow> basics_guarantee g c \<Longrightarrow> \<exists>s'. (h, c)  \<midarrow>r, Tau\<rightarrow> s'\<close>
  by (induct c arbitrary: h)
    (fastforce simp add: opsem_tau_iff)+

lemma opsem_samecD:
  \<open>opsem r a s s' \<Longrightarrow> snd s' = snd s \<Longrightarrow> r (fst s) (fst s') \<and> a = Env (fst s) (fst s')\<close>
  by (induct rule: opsem.induct) force+

lemma opsem_samec:
  \<open>opsem r a (h, c) (h', c) \<longleftrightarrow> r h h' \<and> a = Env h h'\<close>
  by (force dest: opsem_samecD)

lemma opsem_env_step:
  \<open>opsem r (Env h h') (ha, ca) (hb, cb) \<longleftrightarrow> ha = h \<and> hb = h' \<and> r h h' \<and> cb = ca\<close>
  using opsem_envD by fastforce

paragraph \<open> relation for reasoning about the effect if several environment steps \<close>

inductive env_chain :: \<open>'h act list \<Rightarrow> 'h \<Rightarrow> 'h \<Rightarrow> bool\<close> where
  \<open>env_chain [] x x\<close>
| \<open>env_chain as x z \<Longrightarrow> env_chain (Env y x # as) y z\<close>

inductive_cases env_chain_NilE[elim!]: \<open>env_chain [] x z\<close>
inductive_cases env_chain_ConsE[elim!]: \<open>env_chain (a # as) x z\<close>

lemma env_chain_iff[simp]:
  \<open>env_chain [] x x \<longleftrightarrow> True\<close>
  \<open>env_chain (a # as) x z \<longleftrightarrow> (\<exists>y. a = Env x y \<and> env_chain as y z)\<close>
  by (force intro: env_chain.intros)+


lemma opsem_rtrancl_start_done_all_env:
  assumes \<open>opsem_rtrancl r as (h, Done) s'\<close>
  shows \<open>env_chain as h (fst s')\<close>
proof -
  { fix s
    have \<open>opsem_rtrancl r as s s' \<Longrightarrow> snd s = Done \<Longrightarrow> env_chain as (fst s) (fst s')\<close>
      by (induct rule: opsem_rtrancl.induct) force+
  } then show ?thesis
    using assms
    by force
qed

lemma opsem_rtrancl_start_done_in_rely:
  assumes
    \<open>opsem_rtrancl r as (h, Done) s'\<close>
    \<open>reflp r\<close>
    \<open>transp r\<close>
  shows \<open>snd s' = Done \<and> r h (fst s')\<close>
proof -
  { fix s
    have \<open>opsem_rtrancl r as s s' \<Longrightarrow> snd s = Done \<Longrightarrow> snd s' = Done \<and> r (fst s) (fst s')\<close>
      using assms
      by (induct arbitrary: s' rule: opsem_rtrancl_rev_induct)
        (force dest: reflpD transpD)+
  } then show ?thesis
    using assms
    by force
qed

section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat
  :: \<open>('h::perm_alg) comm \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> ('h \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
  rgsat_done: \<open>\<lceil> p \<rceil>\<^bsub>r\<^esub> \<le> q \<Longrightarrow> rgsat Done r g p q\<close>
| rgsat_iter:
  \<open>rgsat c r g p' q' \<Longrightarrow>
      p \<le> i \<Longrightarrow> i \<le> p' \<Longrightarrow>
      q' \<le> i \<Longrightarrow> i \<le> q \<Longrightarrow>
      rgsat (c\<^sup>\<star>\<^bsub>i\<^esub>) r g p q\<close>
| rgsat_ndet:
  \<open>rgsat s1 r g1 p q1 \<Longrightarrow>
    rgsat s2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<^bold>+ s2) r g p q\<close>
| rgsat_parallel:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<Longrightarrow> p \<le> p2 \<Longrightarrow>
    q1 \<sqinter> q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q\<close>
| rgsat_basic:
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR q \<Longrightarrow>
    b \<le> g \<Longrightarrow>
    rgsat (Basic b) r g p q\<close>
inductive_cases rgsep_doneE[elim]: \<open>rgsat Done r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (c\<^sup>\<star>\<^bsub>i\<^esub>) r g p q\<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_basicE[elim]: \<open>rgsat (Basic c) r g p q\<close>


lemma rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
  apply (induct arbitrary: p r g q rule: rgsat.induct)
      apply (rule rgsat_done, metis le_supE sup.absorb_iff2 wsstable_disj_distrib wsstable_rely_mono)
     apply (rule_tac i=i in rgsat_iter)
         apply assumption
        apply (simp; fail)
       apply (simp; fail)
      apply blast
     apply blast
    apply (meson order.eq_iff order.trans rgsat_ndet; fail)
   apply (meson order.eq_iff order.trans sup_mono rgsat_parallel; fail)
  apply (fastforce intro!: rgsat_basic)
  done

lemma rgsat_iter':
  \<open>rgsat c r g i i \<Longrightarrow> rgsat (c\<^sup>\<star>\<^bsub>i\<^esub>) r g i i\<close>
  using rgsat_iter[OF _ order.refl order.refl order.refl order.refl]
  by blast
  

lemma frame_conj_helper:
  fixes p1 :: \<open>'a::cancel_perm_alg \<Rightarrow> bool\<close>
  assumes precise_f: \<open>\<And>h h'. (\<lceil> f \<rceil>\<^bsub>r1\<^esub>) h \<Longrightarrow> (\<lceil> f \<rceil>\<^bsub>r2\<^esub>) h' \<Longrightarrow> h' = h\<close>
  shows \<open>p1 \<^emph> \<lceil> f \<rceil>\<^bsub>r1\<^esub> \<sqinter> p2 \<^emph> \<lceil> f \<rceil>\<^bsub>r2\<^esub> \<le> (p1 \<sqinter> p2) \<^emph> \<lceil> f \<rceil>\<^bsub>r1 \<squnion> r2\<^esub>\<close>
  apply (clarsimp simp add: sepconj_def)
  apply (rename_tac h1a h1b h2a h2b)
  apply (frule(1) precise_f)
  apply simp
  apply (metis precise_f predicate1D wsstable_def wsstable_stronger)
  done

lemma ex_inv:
  \<open>
      p \<^emph> f \<le> i' \<and>
      i' \<le> p' \<^emph> f \<and>
      q' \<^emph> \<lceil> f \<rceil>\<^bsub>r\<^esub> \<le> i' \<and>
      i' \<le> q \<^emph> \<lceil> f \<rceil>\<^bsub>r\<^esub> \<Longrightarrow>
      \<lceil> f \<rceil>\<^bsub>r\<^esub> \<le> f\<close>
  nitpick
  oops

lemma rgsat_frame:
  assumes
    \<open>rgsat c r g p q\<close>
    \<open>rel_add_preserve (r\<^sup>*\<^sup>*)\<close>
    \<comment> \<open> the variable restriction \<close>
    \<open>basic_frame_pred f c\<close>
    \<open>all_loop_inv (\<lambda>i. i \<^emph> \<lceil> f \<rceil>\<^bsub>r\<^esub> \<le> i \<^emph> f) c\<close>
(*
   and frame_stable:
   \<open>f \<le> \<lfloor> f \<rfloor>\<^bsub>r\<^esub>\<close> (* I note this is my addition, varying from Wickerson; It is needed for the basic step. *)
*)
  shows
    \<open>rgsat c r g (p \<^emph> f) (q \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g\<^esub>)\<close>
  using assms
proof (induct arbitrary: f rule: rgsat.induct)
  case (rgsat_done p r q g)
  then show ?case
    apply (intro rgsat.rgsat_done[OF order.trans])
     apply (rule wsstable_sepconj_semidistrib; force)
    apply (meson sepconj_mono sup_ge1 wsstable_rely_mono; fail)
    done
next
  case (rgsat_iter c r g p' q' p i q)
  then show ?case
    apply (rule_tac rgsat.rgsat_iter)
        apply fastforce
    apply simp
      apply clarsimp

    thm basic_frame_pred_antimono swstable_weaker wsstable_stronger
    sorry
(*
      apply (metis (no_types, lifting) order.refl wsstable_absorb2 rgsat_iter.hyps(2))
     apply (meson sepconj_mono wsstable_stronger; fail)
    apply (meson sepconj_left_mono wsstable_stronger; fail)
    done
*)
next
  case (rgsat_ndet s1 r g1 p q1 s2 g2 q2 g q)
  then show ?case
    apply (intro rgsat.rgsat_ndet[where
          ?g1.0=g1 and ?g2.0=g2 and ?q1.0=\<open>q1 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g1\<^esub>\<close> and ?q2.0=\<open>q2 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g2\<^esub>\<close>])
    sorry
next
  case (rgsat_parallel s1 r g2 g1 p1 q1 s2 p2 q2 g p q)
  then show ?case
    apply -
    apply (rule rgsat.rgsat_parallel[where
          g=g and ?g1.0=g1 and ?g2.0=g2 and
            ?p1.0=\<open>p1 \<^emph> f\<close> and
            ?q1.0=\<open>q1 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g2\<^esub>\<close> and
            ?p2.0=\<open>p2 \<^emph> f\<close> and
            ?q2.0=\<open>q2 \<^emph> \<lceil> f \<rceil>\<^bsub>r \<squnion> g1\<^esub>\<close>])
          defer
          defer
          apply blast
         apply blast
        apply (meson sepconj_left_mono; fail)
       apply (meson sepconj_left_mono; fail)
    sorry
next
  case (rgsat_basic p b q g r f)
  then show ?case
    apply -
    apply (rule rgsat.rgsat_basic)
     apply (rule order.trans[where b=\<open>rel_liftR (q \<^emph> f)\<close>])
      apply (clarsimp simp add: sepconj_def le_fun_def, metis)
     apply (clarsimp simp add: sepconj_monoR wsstable_stronger)
    apply blast
    done
qed

lemma backwards_frame:
  \<open>rgsat c r g p q \<Longrightarrow> rel_add_preserve (r\<^sup>*\<^sup>*) \<Longrightarrow> rgsat c r g (p \<^emph> \<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>) (q \<^emph> f)\<close>
  oops
  by (rule rgsat_weaken[OF rgsat_frame[where f=\<open>\<lfloor> f \<rfloor>\<^bsub>r \<squnion> g\<^esub>\<close>] _ _ order.refl order.refl])
    (force simp add: wsstable_def swstable_def le_fun_def)+

lemma backwards_done:
  \<open>rgsat Done r g (\<lfloor> p \<rfloor>\<^bsub>r\<^esub>) p\<close>
  by (rule rgsat_weaken[OF rgsat_done _ _ order.refl order.refl, where p'=\<open>\<lfloor> p \<rfloor>\<^bsub>r\<^esub>\<close> and q'=p])
    (clarsimp simp add: wsstable_def swstable_def le_fun_def)+


lemma pre_soundness:
  assumes opsem:
    \<open>s \<midarrow>r, as\<rightarrow>\<^sup>\<star>\<^bsub>i\<^esub> s'\<close>
    \<open>s = (h, c)\<close>
    \<open>s' = (h', Done)\<close>
    and rgsat: \<open>rgsat c r g p q\<close>
    and rtrans_r:
    \<open>reflp r\<close>
    \<open>transp r\<close>
    and r_mono_p: \<open>\<And>h h'. r h h' \<Longrightarrow> p h \<Longrightarrow> (\<lceil> p \<rceil>\<^bsub>r\<^esub>) h'\<close>
    and c_maintains_g: \<open>basics_guarantee g c\<close>
    and pre: \<open>p h\<close>
  shows \<open>q h'\<close>
  using assms
proof (induct r as s s' arbitrary: g p q h c h' rule: opsem_rtrancl.induct)
  case (base r s)
  then show ?case
    apply clarsimp
    apply (erule rgsep_doneE)
      apply clarsimp
    apply (metis reflpE)
    sorry
next
  case (step s r a s' as s'')
  then show ?case
    sorry
qed

end
 theory Security
  imports Soundness
begin


section \<open> RGSep-Security State Types \<close>

type_synonym ('a,'b) rgstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>

type_synonym ('a,'b) secstate = \<open>(('a \<times> 'b) \<times> ('a \<times> 'b))\<close>


section \<open> Double-state lifting \<close>

subsection \<open> exchange \<close>

definition
  \<open>exch4 abcd \<equiv> ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>

lemma exch4_four_apply[simp]:
  \<open>exch4 ((a,b),(c,d)) = ((a,c),(b,d))\<close>
  by (simp add: exch4_def)

lemma exch4_two_apply:
  \<open>exch4 (sx, sy) = ((fst sx, fst sy), (snd sx, snd sy))\<close>
  by (simp add: exch4_def)

lemma exch4_apply:
  \<open>exch4 abcd = ((fst (fst abcd), fst (snd abcd)), (snd (fst abcd), snd (snd abcd)))\<close>
  by (simp add: exch4_def)

lemma exch4_idem[simp]:
  \<open>exch4 (exch4 x) = x\<close>
  by (simp add: exch4_def split: prod.splits)

lemma exch4_switch:
  \<open>exch4 x = y \<longleftrightarrow> x = exch4 y\<close>
  by (force simp add: exch4_def split: prod.splits)

lemma exch4_comp_idem[simp]:
  \<open>exch4 \<circ> exch4 = id\<close>
  by (force simp add: exch4_def)

lemma inv_exch4_eq[simp]:
  \<open>inv exch4 = exch4\<close>
  by (simp add: inv_unique_comp)

lemma exch4_eq_iff[simp]:
  \<open>exch4 a = exch4 b \<longleftrightarrow> a = b\<close>
  by (cases a, cases b, force simp add: exch4_def)

lemma comp_exch4_eq_iff[simp]:
  \<open>f \<circ> exch4 = g \<circ> exch4 \<longleftrightarrow> f = g\<close>
  by (simp add: fun_eq_iff, blast)

lemma rel_comp_exch4_eq_iff[simp]:
  \<open>ra \<circ>\<^sub>2 exch4 = rb \<circ>\<^sub>2 exch4 \<longleftrightarrow> ra = rb\<close>
  by (force simp add: fun_eq_iff)

lemma prod_destruct_exch4_eq[simp]:
  \<open>fst (fst (exch4 x)) = fst (fst x)\<close>
  \<open>fst (snd (exch4 x)) = snd (fst x)\<close>
  \<open>snd (fst (exch4 x)) = fst (snd x)\<close>
  \<open>snd (snd (exch4 x)) = snd (snd x)\<close>
  by (clarsimp simp add: exch4_def)+

lemma prod_part_destruct_exch4_eq[simp]:
  \<open>fst (exch4 (ab, cd)) = (fst ab, fst cd)\<close>
  \<open>snd (exch4 (ab, cd)) = (snd ab, snd cd)\<close>
  by (simp add: exch4_def)+

lemma leq_exch4_shunt:
  \<open>p \<le> q \<circ> exch4 \<longleftrightarrow> p \<circ> exch4 \<le> q\<close>
  by (metis comp_def exch4_idem le_fun_def)

lemma eq_exch4_iff[simp]:
  \<open>((ax, bx), (ay, by)) = exch4 ab \<longleftrightarrow> fst ab = (ax, ay) \<and> snd ab = (bx, by)\<close>
  by (force simp add: exch4_def split: prod.splits)


subsection \<open> Relational Predicate Lifting \<close>

syntax
  "_twoPredLiftBasic"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("\<lblot> _ \<rblot>" [0] 999)
  "_twoPredLiftDouble"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar> _ \<rblot>" [0,0] 998)
  "_twoPredLiftL"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar>" [0] 997)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 997)

translations
  "_twoPredLiftBasic p" \<rightharpoonup> "(CONST pred_times) p p"
  "_twoPredLiftDouble p q" \<rightleftharpoons> "(CONST pred_times) p q"
  "_twoPredLiftL p" \<rightharpoonup> "(CONST pred_times) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST pred_times) \<top> q"


subsubsection \<open> Predicate Lifting Lemmas \<close>

lemma twoPredLift_sup_semidistrib:
  \<open>\<lblot>p\<rblot> \<squnion> \<lblot>q\<rblot> \<le> \<lblot>p \<squnion> q\<rblot>\<close>
  by (simp add: le_fun_def)

lemma pred_list_disj_eq:
  \<open>\<lblot> p \<squnion> q \<rblot> = \<lblot> p \<rblot> \<squnion> \<lblot> p \<bar> q \<rblot> \<squnion> \<lblot> q \<bar> p \<rblot> \<squnion> \<lblot> q \<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma twoPredLift_Sup_semidistrib:
  \<open>(\<Squnion>p\<in>P. \<lblot>p\<rblot>) \<le> \<lblot>\<Squnion>P\<rblot>\<close>
  by (force simp add: le_fun_def)

lemma twoPredLift_inf_distrib:
  \<open>\<lblot>p \<sqinter> q\<rblot> = \<lblot>p\<rblot> \<sqinter> \<lblot>q\<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma twoPredLift_Inf_distrib:
  \<open>\<lblot>\<Sqinter>P\<rblot> = (\<Sqinter>p\<in>P. \<lblot>p\<rblot>)\<close>
  by (force simp add: fun_eq_iff)

lemma twoPredLift_not_semidistrib:
  \<open>\<lblot>- p\<rblot> \<le> - \<lblot>p\<rblot>\<close>
  by (force simp add: fun_eq_iff)

lemma twoPredLift_sepconj_distrib:
  \<open>\<lblot>p \<^emph> q\<rblot> = \<lblot>p\<rblot> \<^emph> \<lblot>q\<rblot>\<close>
  by (force simp add: fun_eq_iff sepconj_def)

lemma twoPredLift_emp_distrib[simp]:
  \<open>\<lblot>emp\<rblot> = emp\<close>
  by (force simp add: fun_eq_iff emp_def)

thm top_pred_times_top_eq
thm bot_pred_times_eq pred_times_bot_eq


subsubsection \<open> Exchanged Predicate Lifting \<close>

definition pred_lift_exch4 (\<open>\<lblot> _ \<rblot>\<^sub>\<ddagger>\<close> [0]) where
  \<open>pred_lift_exch4 p \<equiv> \<lblot> p \<rblot> \<circ> exch4\<close>

lemma pred_lift_exch4_mono:
  \<open>p \<le> q \<Longrightarrow> \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> q \<rblot>\<^sub>\<ddagger>\<close>
  by (simp add: pred_lift_exch4_def le_fun_def)

lemma pred_lift_exch4_mono_exch4:
  \<open>\<lblot> p \<rblot> \<le> \<lblot> q \<rblot> \<Longrightarrow> \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> q \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: pred_lift_exch4_def le_fun_def)

lemma pred_lift_exch4_sepconj_conj_distrib:
  \<open>\<lblot>p \<^emph>\<and> q\<rblot>\<^sub>\<ddagger> = \<lblot>p\<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot>q\<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: pred_lift_exch4_def fun_eq_iff sepconj_conj_apply)

lemma pred_lift_exch4_disj_semidistrib:
  \<open>\<lblot> p \<rblot>\<^sub>\<ddagger> \<squnion> \<lblot> q \<rblot>\<^sub>\<ddagger> \<le> \<lblot> p \<squnion> q \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: pred_lift_exch4_def fun_eq_iff)

lemma pred_lift_exch4_localpred_distrib:
  \<open>\<lblot> \<L> p \<rblot>\<^sub>\<ddagger> = \<L> (\<lblot>p\<rblot>)\<close>
  by (force simp add: pred_lift_exch4_def)

lemma pred_lift_exch4_sharedpred_distrib:
  \<open>\<lblot> \<S> p \<rblot>\<^sub>\<ddagger> = \<S> (\<lblot>p\<rblot>)\<close>
  by (force simp add: pred_lift_exch4_def)

lemma Sup_pred_lift_exch4_semidistrib:
  \<open>\<Squnion>(pred_lift_exch4 ` P) \<le> \<lblot> \<Squnion>P \<rblot>\<^sub>\<ddagger>\<close>
  by (force simp add: pred_lift_exch4_def)

lemma pred_lift_exch4_Inf_distrib:
  \<open>\<lblot> \<Sqinter>P \<rblot>\<^sub>\<ddagger> = \<Sqinter>(pred_lift_exch4 ` P)\<close>
  by (force simp add: pred_lift_exch4_def)


subsection \<open> Agreement \<close>

definition sec_agree :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>) where
  \<open>\<bbbA> vf \<equiv> (\<lambda>(x,y). vf x = vf y)\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)


definition sec_agree_exch4 :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool\<close> (\<open>\<bbbA>\<^sub>\<ddagger>\<close>) where
  \<open>\<bbbA>\<^sub>\<ddagger> h \<equiv> \<bbbA> h \<circ> exch4\<close>

lemmas sec_agree_exch4_def' = sec_agree_exch4_def sec_agree_def


subsection \<open> Command Times \<close>

function(sequential) comm_Times :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> ('a \<times> 'b) comm\<close> (infixr \<open>\<times>\<^sub>C\<close> 80) where
  \<open>Skip \<times>\<^sub>C Skip = Skip\<close>
| \<open>(cax;;cay) \<times>\<^sub>C (cbx;;cby) = (cax \<times>\<^sub>C cbx) ;; (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<parallel> cay) \<times>\<^sub>C (cbx \<parallel> cby) = (cax \<times>\<^sub>C cbx) \<parallel> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<sqinter> cay) \<times>\<^sub>C (cbx \<^bold>\<sqinter> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<sqinter> (cay \<times>\<^sub>C cby)\<close>
| \<open>(cax \<^bold>\<box> cay) \<times>\<^sub>C (cbx \<^bold>\<box> cby) = (cax \<times>\<^sub>C cbx) \<^bold>\<box> (cay \<times>\<^sub>C cby)\<close>
| \<open>(DO ca OD) \<times>\<^sub>C (DO cb OD) = DO (ca \<times>\<^sub>C cb) OD\<close>
| \<open>\<langle>ra\<rangle> \<times>\<^sub>C \<langle>rb\<rangle> = \<langle>ra \<times>\<^sub>R rb\<rangle>\<close>
| \<open>_ \<times>\<^sub>C _ = undefined\<close>
  by pat_completeness auto (* slow *)

termination
  by (relation \<open>measure (\<lambda>(ca,cb). size ca + size cb)\<close>) simp+

lemma comm_Times_rev[simp]:
  \<open>c \<times>\<^sub>C c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>c \<times>\<^sub>C c = ca' ;; cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca ;; cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<parallel> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<parallel> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<sqinter> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<sqinter> cb)\<close>
  \<open>c \<times>\<^sub>C c = ca' \<^bold>\<box> cb' \<longleftrightarrow>
    (\<exists>ca cb. ca' = ca \<times>\<^sub>C ca \<and> cb' = cb \<times>\<^sub>C cb \<and> c = ca \<^bold>\<box> cb)\<close>
  \<open>c \<times>\<^sub>C c = DO c' OD \<longleftrightarrow> (\<exists>ca cb. c' = ca \<times>\<^sub>C ca \<and> c = DO ca OD)\<close>
  \<open>c \<times>\<^sub>C c = \<langle>r'\<rangle> \<longleftrightarrow> (\<exists>r. r' = r \<times>\<^sub>R r \<and> c = \<langle>r\<rangle>)\<close>
  by (induct c; clarsimp; argo)+


subsection \<open> Double-state Lifting \<close>

abbreviation(input) \<open>liftP p \<equiv> p \<times>\<^sub>P p\<close>
abbreviation(input) \<open>liftR r \<equiv> r \<times>\<^sub>R r\<close>


subsubsection \<open> lift command to double command \<close>

definition liftC'
  :: \<open>('lx \<times> 'sx) comm \<Rightarrow> ('ly \<times> 'sy) comm \<Rightarrow> (('lx \<times> 'ly) \<times> ('sx \<times> 'sy)) comm\<close>
  where
    \<open>liftC' ca cb \<equiv> map_atom (\<lambda>ar. ar \<circ>\<^sub>2 exch4) (ca \<times>\<^sub>C cb)\<close>

abbreviation liftC :: \<open>('l \<times> 's) comm \<Rightarrow> (('l \<times> 'l) \<times> ('s \<times> 's)) comm\<close> where
  \<open>liftC c \<equiv> liftC' c c\<close>

lemmas liftC_def = liftC'_def

lemma liftC_def':
  \<open>liftC c = map_atom (\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4) c\<close>
  unfolding liftC_def
  by (induct c) simp+

lemmas liftC_simps[simp] =
  map_atom.simps[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric]]

lemmas liftC_rev_iff[simp] =
  map_atom_rev_iff[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric]]
  map_atom_rev_iff[of \<open>(\<lambda>ar. liftR ar \<circ>\<^sub>2 exch4)\<close>,
    simplified liftC_def'[symmetric], THEN trans[OF eq_commute]]

lemma liftC_eq_iff[simp]:
  \<open>liftC ca = liftC cb \<longleftrightarrow> ca = cb\<close>
  by (induct ca arbitrary: cb) (fastforce simp add: rel_times_def fun_eq_iff)+


subsubsection \<open> control-flow matching \<close>

inductive cfmatchC :: \<open>'a comm \<Rightarrow> 'b comm \<Rightarrow> bool\<close> where
  cfmatch_skip[simp]: \<open>cfmatchC Skip Skip\<close>
| cfmatch_seq[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax ;; cbx) (cay ;; cby)\<close>
| cfmatch_indet[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<^bold>\<sqinter> cbx) (cay \<^bold>\<sqinter> cby)\<close>
| cfmatch_endet[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<^bold>\<box> cbx) (cay \<^bold>\<box> cby)\<close>
| cfmatch_par[intro!]:
  \<open>cfmatchC cax cay \<Longrightarrow> cfmatchC cbx cby \<Longrightarrow> cfmatchC (cax \<parallel> cbx) (cay \<parallel> cby)\<close>
| cfmatch_dood[intro!]:
  \<open>cfmatchC cx cy \<Longrightarrow> cfmatchC (DO cx OD) (DO cy OD)\<close>
| cfmatch_atom[simp]: \<open>cfmatchC (\<langle>arx\<rangle>) (\<langle>ary\<rangle>)\<close>

inductive_cases cfmatchC_Skip_leftE[elim!]: \<open>cfmatchC Skip cy\<close>
inductive_cases cfmatchC_Seq_leftE[elim!]: \<open>cfmatchC (cax ;; cbx) cy\<close>
inductive_cases cfmatchC_INDet_leftE[elim!]: \<open>cfmatchC (cax \<^bold>\<sqinter> cbx) cy\<close>
inductive_cases cfmatchC_ENDet_leftE[elim!]: \<open>cfmatchC (cax \<^bold>\<box> cbx) cy\<close>
inductive_cases cfmatchC_Par_leftE[elim!]: \<open>cfmatchC (cax \<parallel> cbx) cy\<close>
inductive_cases cfmatchC_Iter_leftE[elim!]: \<open>cfmatchC (DO cx OD) cy\<close>
inductive_cases cfmatchC_Atom_leftE[elim!]: \<open>cfmatchC (\<langle>arx\<rangle>) cy\<close>

inductive_cases cfmatchC_Skip_rightE[elim!]: \<open>cfmatchC cx Skip\<close>
inductive_cases cfmatchC_Seq_rightE[elim!]: \<open>cfmatchC cx (cay ;; cby)\<close>
inductive_cases cfmatchC_INDet_rightE[elim!]: \<open>cfmatchC cx (cay \<^bold>\<sqinter> cby)\<close>
inductive_cases cfmatchC_ENDet_rightE[elim!]: \<open>cfmatchC cx (cay \<^bold>\<box> cby)\<close>
inductive_cases cfmatchC_Par_rightE[elim!]: \<open>cfmatchC cx (cay \<parallel> cby)\<close>
inductive_cases cfmatchC_Iter_rightE[elim!]: \<open>cfmatchC cx (DO cy OD)\<close>
inductive_cases cfmatchC_Atom_rightE[elim!]: \<open>cfmatchC cx (\<langle>ary\<rangle>)\<close>

lemma cfmatchC_iff[simp]:
  \<open>cfmatchC Skip cy \<longleftrightarrow> cy = Skip\<close>
  \<open>cfmatchC cx Skip \<longleftrightarrow> cx = Skip\<close>
  \<open>cfmatchC (cax ;; cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay ;; cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay ;; cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax ;; cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<^bold>\<sqinter> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<^bold>\<sqinter> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<^bold>\<sqinter> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<^bold>\<sqinter> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<^bold>\<box> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<^bold>\<box> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<^bold>\<box> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<^bold>\<box> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (cax \<parallel> cbx) cy \<longleftrightarrow> (\<exists>cay cby. cy = cay \<parallel> cby \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC cx (cay \<parallel> cby) \<longleftrightarrow> (\<exists>cax cbx. cx = cax \<parallel> cbx \<and> cfmatchC cax cay \<and> cfmatchC cbx cby)\<close>
  \<open>cfmatchC (DO cx' OD) cy \<longleftrightarrow> (\<exists>cy'. cy = DO cy' OD \<and> cfmatchC cx' cy')\<close>
  \<open>cfmatchC cx (DO cy' OD) \<longleftrightarrow> (\<exists>cx'. cx = DO cx' OD \<and> cfmatchC cx' cy')\<close>
  \<open>cfmatchC \<langle>arx\<rangle> cy \<longleftrightarrow> (\<exists>ary. cy = \<langle>ary\<rangle>)\<close>
  \<open>cfmatchC cx \<langle>ary\<rangle> \<longleftrightarrow> (\<exists>arx. cx = \<langle>arx\<rangle>)\<close>
  by fastforce+


subsubsection \<open> command atoms refl. closure \<close>

definition
  \<open>reflclC \<equiv>
  all_atom_comm (\<lambda>ar.
    (\<forall>sx sy sx' sy'.
      ar (exch4 (sx,sx)) (exch4 (sx',sx')) \<and> ar (exch4 (sy,sy)) (exch4 (sy',sy'))
      \<longleftrightarrow> ar (exch4 (sx,sy)) (exch4 (sx',sy'))))\<close>

lemmas reflclC_simp[simp] =
  all_atom_comm_simps[of \<open>(\<lambda>ar.
    (\<forall>sx sy sx' sy'.
      ar (exch4 (sx,sx)) (exch4 (sx',sx')) \<and> ar (exch4 (sy,sy)) (exch4 (sy',sy')) \<longleftrightarrow>
      ar (exch4 (sx,sy)) (exch4 (sx',sy'))))\<close>,
    simplified reflclC_def[symmetric]]

lemma liftC_is_reflcl[simp]:
  \<open>reflclC (liftC c)\<close>
  by (induct c) clarsimp+


subsubsection \<open> unlift comm \<close>

definition unliftC :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm \<Rightarrow> ('l \<times> 's) comm\<close> where
  \<open>unliftC c \<equiv> map_atom (\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) c\<close>

lemmas unliftC_simps[simp] =
  map_atom.simps[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>, simplified unliftC_def[symmetric]]

lemmas unliftC_rev_iff =
  map_atom_rev_iff[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>, simplified unliftC_def[symmetric]]
  map_atom_rev_iff[of \<open>\<lambda>ar. ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)\<close>, simplified unliftC_def[symmetric],
    THEN trans[OF eq_commute]]

lemma unlift_lift_comm_eq[simp]:
  \<open>unliftC (liftC c) = c\<close>
  by (induct c) (simp add: fun_eq_iff)+


subsection \<open> double atom \<close>

definition doubled_atom
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> ('l \<times> 'l) \<times> ('s \<times> 's) \<Rightarrow> bool) \<Rightarrow> bool\<close>
  where
    \<open>doubled_atom qq \<equiv> (\<exists>q. qq = liftR q \<circ>\<^sub>2 exch4)\<close>

lemma all_doubled_atom_liftC_iff[simp]:
  \<open>all_atom_comm doubled_atom (liftC c)\<close>
  by (induct c)
    (force simp add: doubled_atom_def)+


section \<open> Quasi-reflexive and Symmetric Atomic Relations \<close>

subsection \<open> Quasi-reflexive Atom Relations \<close>

definition
  \<open>quasireflp_steprel ar \<equiv> \<lambda>((lx,ly),(sx,sy)).
    (\<forall>lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((lx,lx),(sx,sx)) ((lx',lx'),(sx',sx')) \<and> ar ((ly,ly),(sy,sy)) ((ly',ly'),(sy',sy')))\<close>

lemma quasireflp_steprel_preserves_quasireflp:
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  assumes
    \<open>p \<le> quasireflp_steprel r\<close>
    \<open>quasireflp (curry (p \<circ> exch4))\<close>
  shows
    \<open>quasireflp (curry (sp r p \<circ> exch4))\<close>
  using assms
  by (clarsimp simp add: reflp_on_def prepost_state_def' quasireflp_steprel_def
      sp_def le_fun_def, metis)

lemma lifted_atom_quasireflp_steprel:
  \<open>\<top> \<le> quasireflp_steprel (liftR r \<circ>\<^sub>2 exch4)\<close>
  by (force simp add: rel_times_def quasireflp_steprel_def split: prod.splits)


definition
  \<open>quasireflp_head_atoms cc \<equiv> \<Sqinter>{quasireflp_steprel ar|ar. ar \<in># head_atoms cc}\<close>

lemma quasireflp_head_atoms_simps[simp]:
  \<open>quasireflp_head_atoms Skip = \<top>\<close>
  \<open>quasireflp_head_atoms (c1 ;; c2) = quasireflp_head_atoms c1\<close>
  \<open>quasireflp_head_atoms (c1 \<^bold>\<sqinter> c2) = \<top>\<close>
  \<open>quasireflp_head_atoms (c1 \<^bold>\<box> c2) = quasireflp_head_atoms c1 \<sqinter> quasireflp_head_atoms c2\<close>
  \<open>quasireflp_head_atoms (c1 \<parallel> c2) = quasireflp_head_atoms c1 \<sqinter> quasireflp_head_atoms c2\<close>
  \<open>quasireflp_head_atoms (DO c OD) = quasireflp_head_atoms c\<close>
  \<open>quasireflp_head_atoms \<langle>ar\<rangle> = quasireflp_steprel ar\<close>
  by (clarsimp simp add: quasireflp_head_atoms_def; blast)+

definition
  \<open>quasireflp_atoms cc \<equiv> \<Sqinter>{quasireflp_steprel ar|ar. ar \<in># all_atoms cc}\<close>

lemma quasireflp_atoms_simps[simp]:
  \<open>quasireflp_atoms Skip = \<top>\<close>
  \<open>quasireflp_atoms (c1 ;; c2) = quasireflp_atoms c1 \<sqinter> quasireflp_atoms c2\<close>
  \<open>quasireflp_atoms (c1 \<^bold>\<sqinter> c2) = quasireflp_atoms c1 \<sqinter> quasireflp_atoms c2\<close>
  \<open>quasireflp_atoms (c1 \<^bold>\<box> c2) = quasireflp_atoms c1 \<sqinter> quasireflp_atoms c2\<close>
  \<open>quasireflp_atoms (c1 \<parallel> c2) = quasireflp_atoms c1 \<sqinter> quasireflp_atoms c2\<close>
  \<open>quasireflp_atoms (DO c OD) = quasireflp_atoms c\<close>
  \<open>quasireflp_atoms \<langle>ar\<rangle> = quasireflp_steprel ar\<close>
  by (clarsimp simp add: quasireflp_atoms_def; blast)+


subsection \<open> Symmetric Atom Relation \<close>

definition
  \<open>symp_steprel ar \<equiv> \<lambda>((lx,ly),(sx,sy)).
    \<forall>lx' sx' ly' sy'.
      ar ((lx,ly),(sx,sy)) ((lx',ly'),(sx',sy')) \<longrightarrow>
      ar ((ly,lx),(sy,sx)) ((ly',lx'),(sy',sx'))\<close>

lemma symp_steprel_preserves_symp:
  fixes p :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and r :: \<open>('l, 's) rgstate \<Rightarrow> ('l, 's) rgstate \<Rightarrow> bool\<close>
  assumes
    \<open>p \<le> symp_steprel r\<close>
    \<open>symp (curry (p \<circ> exch4))\<close>
  shows
    \<open>symp (curry (sp r p \<circ> exch4))\<close>
  using assms
  by (fastforce simp add: symp_steprel_def symp_def sp_def le_fun_def)

lemma lifted_atom_symp_steprel:
  \<open>\<top> \<le> symp_steprel (liftR r \<circ>\<^sub>2 exch4)\<close>
  by (force simp add: rel_times_def symp_steprel_def split: prod.splits)


subsection \<open> Quasi-reflexive Blocking Step Atom Relation \<close>

definition
  \<open>quasirefl_blocking_steprel ar \<equiv>
    (\<lambda>(sx, sy).
      (Ex ((ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) sx) \<or>
        Ex ((ar \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) sy) \<longrightarrow>
      Ex ((ar \<circ>\<^sub>2 exch4) (sx, sy)))) \<circ> exch4\<close>


definition
  \<open>quasirefl_blocking_head_atoms cc \<equiv> \<Sqinter>{quasirefl_blocking_steprel ar|ar. ar \<in># head_atoms cc}\<close>

lemma quasirefl_blocking_head_atoms_simps[simp]:
  \<open>quasirefl_blocking_head_atoms Skip = \<top>\<close>
  \<open>quasirefl_blocking_head_atoms (c1 ;; c2) = quasirefl_blocking_head_atoms c1\<close>
  \<open>quasirefl_blocking_head_atoms (c1 \<^bold>\<sqinter> c2) = \<top>\<close>
  \<open>quasirefl_blocking_head_atoms (c1 \<^bold>\<box> c2) = quasirefl_blocking_head_atoms c1 \<sqinter> quasirefl_blocking_head_atoms c2\<close>
  \<open>quasirefl_blocking_head_atoms (c1 \<parallel> c2) = quasirefl_blocking_head_atoms c1 \<sqinter> quasirefl_blocking_head_atoms c2\<close>
  \<open>quasirefl_blocking_head_atoms (DO c OD) = quasirefl_blocking_head_atoms c\<close>
  \<open>quasirefl_blocking_head_atoms \<langle>ar\<rangle> = quasirefl_blocking_steprel ar\<close>
  by (clarsimp simp add: quasirefl_blocking_head_atoms_def; blast)+

definition
  \<open>quasirefl_blocking_atoms cc \<equiv> \<Sqinter>{quasirefl_blocking_steprel ar|ar. ar \<in># all_atoms cc}\<close>

lemma quasirefl_blocking_atoms_simps[simp]:
  \<open>quasirefl_blocking_atoms Skip = \<top>\<close>
  \<open>quasirefl_blocking_atoms (c1 ;; c2) = quasirefl_blocking_atoms c1 \<sqinter> quasirefl_blocking_atoms c2\<close>
  \<open>quasirefl_blocking_atoms (c1 \<^bold>\<sqinter> c2) = quasirefl_blocking_atoms c1 \<sqinter> quasirefl_blocking_atoms c2\<close>
  \<open>quasirefl_blocking_atoms (c1 \<^bold>\<box> c2) = quasirefl_blocking_atoms c1 \<sqinter> quasirefl_blocking_atoms c2\<close>
  \<open>quasirefl_blocking_atoms (c1 \<parallel> c2) = quasirefl_blocking_atoms c1 \<sqinter> quasirefl_blocking_atoms c2\<close>
  \<open>quasirefl_blocking_atoms (DO c OD) = quasirefl_blocking_atoms c\<close>
  \<open>quasirefl_blocking_atoms \<langle>ar\<rangle> = quasirefl_blocking_steprel ar\<close>
  by (clarsimp simp add: quasirefl_blocking_atoms_def; blast)+


definition
  \<open>quasirefl_blocking_head_doloops_head_atoms cc \<equiv> \<Sqinter>{quasirefl_blocking_head_atoms ca|ca. DO ca OD \<in># head_comms cc}\<close>

lemma quasirefl_blocking_head_doloops_head_atoms_simps[simp]:
  \<open>quasirefl_blocking_head_doloops_head_atoms Skip = \<top>\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms (c1 ;; c2) = quasirefl_blocking_head_doloops_head_atoms c1\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms (c1 \<^bold>\<sqinter> c2) = \<top>\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms (c1 \<^bold>\<box> c2) = quasirefl_blocking_head_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_head_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms (c1 \<parallel> c2) = quasirefl_blocking_head_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_head_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms (DO c OD) = quasirefl_blocking_head_atoms c \<sqinter> quasirefl_blocking_head_doloops_head_atoms c\<close>
  \<open>quasirefl_blocking_head_doloops_head_atoms \<langle>ar\<rangle> = \<top>\<close>
  by (clarsimp simp add: quasirefl_blocking_head_doloops_head_atoms_def; blast)+

definition
  \<open>quasirefl_blocking_doloops_head_atoms cc \<equiv> \<Sqinter>{quasirefl_blocking_head_atoms ca|ca. DO ca OD \<le> cc}\<close>

lemma quasirefl_blocking_doloops_head_atoms_simps[simp]:
  \<open>quasirefl_blocking_doloops_head_atoms Skip = \<top>\<close>
  \<open>quasirefl_blocking_doloops_head_atoms (c1 ;; c2) = quasirefl_blocking_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_doloops_head_atoms (c1 \<^bold>\<sqinter> c2) = quasirefl_blocking_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_doloops_head_atoms (c1 \<^bold>\<box> c2) = quasirefl_blocking_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_doloops_head_atoms (c1 \<parallel> c2) = quasirefl_blocking_doloops_head_atoms c1 \<sqinter> quasirefl_blocking_doloops_head_atoms c2\<close>
  \<open>quasirefl_blocking_doloops_head_atoms (DO c OD) = quasirefl_blocking_head_atoms c \<sqinter> quasirefl_blocking_doloops_head_atoms c\<close>
  \<open>quasirefl_blocking_doloops_head_atoms \<langle>ar\<rangle> = \<top>\<close>
  by (clarsimp simp add: quasirefl_blocking_doloops_head_atoms_def; blast)+


section \<open> GenRGSep Proof Security Lifting \<close>

lemma comp_exch4_mono:
  \<open>p \<le> q \<Longrightarrow> p \<circ> exch4 \<le> q \<circ> exch4\<close>
  by (simp add: le_fun_def)

lemma sswa_pred_lift_exch4_semidistrib:
  \<open>sswa (R \<times>\<^sub>R R) \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> sswa R p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff pred_lift_exch4_def sp_def)
  apply (metis predicate2D rel_times_apply' rel_times_rtranclp_semidistrib)
  done

lemma sswa_sup_rel_pred_lift_exch4_semidistrib:
  \<open>sswa (ra \<times>\<^sub>R ra \<squnion> rb \<times>\<^sub>R rb) \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> sswa (ra \<squnion> rb) p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff pred_lift_exch4_def sp_def)
  apply (metis predicate2D rel_times_apply' rel_times_rtranclp_semidistrib rtranclp_mono
      rel_times_sup_semidistrib)
  done

lemma wssa_pred_lift_exch4_semidistrib:
  \<open>\<lblot> wssa R p \<rblot>\<^sub>\<ddagger> \<le> wssa (R \<times>\<^sub>R R) \<lblot> p \<rblot>\<^sub>\<ddagger>\<close>
  apply (clarsimp simp add: fun_eq_iff pred_lift_exch4_def wlp_def)
  apply (metis fst_conv rel_times_def rtranclp_tuple_rel_semidistrib snd_conv)
  done


section \<open> Proof Lifting to Paired-State Setting \<close>

subsection \<open> Helpers\<close>

lemma atom_unlift_helper:
  \<open>sp (ara \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) p \<le> q \<Longrightarrow>
    All (quasireflp_steprel ara) \<Longrightarrow>
    sp ara \<lblot> p \<rblot>\<^sub>\<ddagger> \<le> \<lblot> q \<rblot>\<^sub>\<ddagger>\<close>
  by (fastforce simp add: le_fun_def fun_eq_iff rel_image_def sp_def imp_ex_conjL
      pred_lift_exch4_def quasireflp_steprel_def)

text \<open> TODO: Note in the writeup that we here again use the 'instantiation to exactly the frame' trick. \<close>
lemma framed_atom_unlift_helper:
  \<open>\<forall>f\<le>F. sp (ara \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)) (p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f \<Longrightarrow>
    All (quasireflp_steprel ara) \<Longrightarrow>
    \<forall>f\<le>\<lblot> F \<rblot>\<^sub>\<ddagger>. sp ara (\<lblot> p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> f) \<le> \<lblot> q \<rblot>\<^sub>\<ddagger> \<^emph>\<and> any_shared f\<close>
  unfolding quasireflp_steprel_def any_shared_def
  apply (clarsimp simp add: sepconj_conj_apply sp_apply le_fun_def)
  apply (rename_tac lfx' lfy' ssx' ssy' ssx ssy lsx lsy fx fy)
  apply (frule_tac x=\<open>(=) (fx, ssx)\<close> in spec, drule mp[of _ \<open>_ ((_ \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)))\<close>])
   apply (simp add: le_fun_def pred_lift_exch4_def; fail)
  apply (drule_tac x=\<open>(=) (fy, ssy)\<close> in spec, drule mp[of _ \<open>_ ((_ \<circ>\<^sub>2 (exch4 \<circ> \<Delta>)))\<close>])
   apply (simp add: le_fun_def pred_lift_exch4_def; fail)
  apply (clarsimp simp add: sp_def le_fun_def sepconj_conj_apply imp_ex_conjL pred_lift_exch4_def
      imp_conjL)
  apply metis
  done

lemma atom_lift_guar_helper:
  \<open>rel_image snd (rel_liftL (p \<squnion> p \<^emph>\<and> F) \<sqinter> (ara \<circ>\<^sub>2 (exch4 \<circ> \<Delta>))) \<le> G \<Longrightarrow>
    All (quasireflp_steprel ara) \<Longrightarrow>
    rel_image snd (rel_liftL (\<lblot> p \<rblot>\<^sub>\<ddagger> \<squnion> \<lblot> p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F \<rblot>\<^sub>\<ddagger>) \<sqinter> ara) \<le> G \<times>\<^sub>R G\<close>
  by (clarsimp simp add: le_fun_def sepconj_conj_apply imp_ex_conjL imp_conjL
      all_conj_distrib pred_lift_exch4_def quasireflp_steprel_def, blast)

lemma cancellative'_lift_helper:
  \<open>cancellative' (\<Squnion> \<I>) (\<Squnion> \<I>) (sswa (\<Squnion> \<G>) F) \<Longrightarrow>
    cancellative' (\<Squnion> (pred_lift_exch4 ` \<I>)) (\<Squnion> (pred_lift_exch4 ` \<I>)) (sswa (\<Squnion>r\<in>\<G>. r \<times>\<^sub>R r) \<lblot> F \<rblot>\<^sub>\<ddagger>)\<close>
  apply (clarsimp simp add: cancellative'_def Bex_def pred_lift_exch4_def)
  apply (subgoal_tac \<open>sswa (\<Squnion>r\<in>\<G>. r \<times>\<^sub>R r) (\<lblot> F \<rblot> \<circ> exch4) \<le> sswa ((\<Squnion>\<G>) \<times>\<^sub>R (\<Squnion>\<G>)) (\<lblot> F \<rblot> \<circ> exch4)\<close>)
   prefer 2
   apply (meson SUP_least Sup_upper rel_times_mono sswa_rel_mono)
  apply (subgoal_tac \<open>sswa ((\<Squnion>\<G>) \<times>\<^sub>R (\<Squnion>\<G>)) (\<lblot> F \<rblot> \<circ> exch4) \<le> (\<lblot> sswa (\<Squnion>\<G>) F \<rblot> \<circ> exch4)\<close>)
   prefer 2
   apply (metis pred_lift_exch4_def sswa_pred_lift_exch4_semidistrib)
  apply (frule predicate1D[of \<open>sswa _ _\<close>, OF order.trans, rotated 2], assumption, assumption)
  apply auto
  done


subsection \<open> Main Lifting Theorem\<close>

(* TODO: Try to tighten up the qrefl side condition. *)
lemma genrgsep_proof_pairedst_lift:
  assumes
    \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
    \<open>c = unliftC cc\<close>
    \<open>All (all_atom_comm (quasireflp_steprel) cc)\<close>
    \<open>\<not> T RGSepDisj\<close>
  shows
    \<open>liftR R, liftR G, \<lblot> I \<rblot>\<^sub>\<ddagger>, \<lblot> F \<rblot>\<^sub>\<ddagger>, T \<squnion> (=) RGSepWeaken \<turnstile> { \<lblot> p \<rblot>\<^sub>\<ddagger> } cc { \<lblot> q \<rblot>\<^sub>\<ddagger> }\<close>
  using assms
proof (induct arbitrary: cc rule: rgsat.induct)
  case (rgsat_skip R p q I T G F)
  then show ?case
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_skip)
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib
        wlp_weaker_iff_sp_stronger; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib
        wlp_weaker_iff_sp_stronger; fail)
    apply force
    done
next
  case (rgsat_iter c R G i I F T p q)
  show ?case
    using rgsat_iter.prems rgsat_iter.hyps(3-)
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_iter[where i=\<open>\<lblot> i \<rblot>\<^sub>\<ddagger>\<close>])
       apply (rule rgsat_weaken[OF rgsat_iter.hyps(2) _ order.refl order.refl order.refl order.refl order.refl])
         apply blast
        apply (simp del: sup_apply; fail)
         apply (simp add: sswa_pred_lift_exch4_semidistrib; fail)
        apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
       apply fast
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_seq ca R G p px Ia F T cb q Ib I)
  show ?case
    using rgsat_seq.prems rgsat_seq.hyps(1,5-)
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_seq[where pp=\<open>\<lblot> px \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
        apply (rule rgsat_seq.hyps(2); force)
       apply (rule rgsat_seq.hyps(4); force)
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_indet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_indet[where qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
            apply (rule rgsat_indet.hyps(2); force)
           apply (rule rgsat_indet.hyps(4); force)
          apply force
         apply force
        apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
       apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_endet ca R Ga p qa Ia F T cb Gb qb Ib G q I)
  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_endet[where qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
            apply (rule rgsat_endet.hyps(2); force)
           apply (rule rgsat_endet.hyps(4); force)
          apply force
         apply force
        apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
       apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
    apply force
    done
next
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F T cb pb qb G p q I)
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (clarsimp simp add: unliftC_rev_iff simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_par[where
          Ga=\<open>Ga \<times>\<^sub>R Ga\<close> and Gb=\<open>Gb \<times>\<^sub>R Gb\<close> and
          pa=\<open>\<lblot> pa \<rblot>\<^sub>\<ddagger>\<close> and pb=\<open>\<lblot> pb \<rblot>\<^sub>\<ddagger>\<close> and qa=\<open>\<lblot> qa \<rblot>\<^sub>\<ddagger>\<close> and qb=\<open>\<lblot> qb \<rblot>\<^sub>\<ddagger>\<close> and Ia=\<open>\<lblot> Ia \<rblot>\<^sub>\<ddagger>\<close> and Ib=\<open>\<lblot> Ib \<rblot>\<^sub>\<ddagger>\<close>])
           apply (rule rgsat_weaken[OF rgsat_par.hyps(2) order.refl order.refl _ order.refl order.refl])
                apply force
               apply force
              apply force
             apply force
           apply (simp add: pred_lift_exch4_sepconj_conj_distrib[symmetric] pred_lift_exch4_mono
        del: top_apply sup_apply; fail)
           apply force
          apply (rule rgsat_weaken[OF rgsat_par.hyps(4) order.refl order.refl _ order.refl order.refl])
               apply force
              apply force
             apply force
            apply force
          apply (simp add: pred_lift_exch4_sepconj_conj_distrib[symmetric] pred_lift_exch4_mono
        del: top_apply sup_apply; fail)
          apply force
         apply (metis rel_times_mono)
        apply (metis rel_times_mono)
       apply (metis pred_lift_exch4_mono pred_lift_exch4_sepconj_conj_distrib)
      apply (rule order.trans[OF _ pred_lift_exch4_mono, rotated], assumption)
      apply (simp add: pred_lift_exch4_sepconj_conj_distrib del: top_apply sup_apply)
      apply (metis sepconj_conj_mono sswa_sup_rel_pred_lift_exch4_semidistrib)
     apply (rule order.trans[OF _ pred_lift_exch4_mono, rotated], assumption)
     apply (simp add: pred_lift_exch4_sepconj_conj_distrib del: top_apply sup_apply)
     apply (metis sepconj_conj_mono sswa_sup_rel_pred_lift_exch4_semidistrib)
    apply force
    done
next
  case (rgsat_atom p' R p q q' ar F G I C)
  then show ?case
    apply (clarsimp simp add: unliftC_rev_iff inj_rel_image_inf_distrib[symmetric]
        simp del: sup_apply top_apply)
    apply (rule rgsat.rgsat_atom[where p=\<open>\<lblot> p \<rblot>\<^sub>\<ddagger>\<close> and  q=\<open>\<lblot> q \<rblot>\<^sub>\<ddagger>\<close>])
           apply (meson order.trans pred_lift_exch4_mono wssa_pred_lift_exch4_semidistrib; fail)
          apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
         apply (simp add: atom_unlift_helper; fail)
        apply (simp add: framed_atom_unlift_helper; fail)
       apply (rule atom_lift_guar_helper; simp; fail)
      apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
     apply (meson order.trans pred_lift_exch4_mono sswa_pred_lift_exch4_semidistrib; fail)
    apply blast
    done
next
  case (rgsat_frame c R G p q I F F' C)
  show ?case
    using rgsat_frame.prems rgsat_frame(3-)
    apply (simp add: pred_lift_exch4_sepconj_conj_distrib del: sup_apply top_apply)
    apply (rule rgsat_weaken[where p'=\<open>\<lblot> p \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F' \<rblot>\<^sub>\<ddagger>\<close> and q'=\<open>\<lblot> q \<rblot>\<^sub>\<ddagger> \<^emph>\<and> \<lblot> F' \<rblot>\<^sub>\<ddagger>\<close>,
          OF _ _ _ order.refl order.refl order.refl order.refl])
       apply (rule rgsat.rgsat_frame)
         apply (rule rgsat_weaken[where F'=\<open> \<lblot> F \<^emph>\<and> F' \<squnion> F' \<rblot>\<^sub>\<ddagger>\<close>,
          OF _order.refl order.refl order.refl order.refl order.refl _])
           apply (cut_tac rgsat_frame.prems(2))
           apply (rule rgsat_frame.hyps(2); blast)
          apply (simp add: pred_lift_exch4_sepconj_conj_distrib[symmetric] pred_lift_exch4_mono
        sup.coboundedI1 del: sup_apply; fail)
         apply force
        apply (metis order_eq_iff sswa_sup_rel_pred_lift_exch4_semidistrib sswa_weaker)
       apply force
      apply force
     apply force
    apply force
    done
next
  case (rgsat_weaken c r' g' p' q' I' F' T p q r g I F)
  show ?case
    using rgsat_weaken.prems rgsat_weaken.hyps(3-)
    apply -
    apply (rule rgsat.rgsat_weaken[OF rgsat_weaken.hyps(2)])
             apply (simp add: pred_lift_exch4_mono; fail)
            apply force
           apply force
          apply (simp add: pred_lift_exch4_mono; fail)
         apply (simp add: pred_lift_exch4_mono; fail)
        apply force
       apply force
      apply (simp add: pred_lift_exch4_mono; fail)
     apply (simp add: pred_lift_exch4_mono; fail)
    apply force
    done
next
  case (rgsat_Disj p' P c R G q I F T)
  then show ?case
    by force \<comment> \<open> excluded \<close>
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  then show ?case
    apply (clarsimp simp add: ball_conj_distrib simp del: top_apply sup_apply)
    apply (rule rgsat.rgsat_Conj[where
          \<I>=\<open>pred_lift_exch4 ` \<I>\<close> and \<G>=\<open>liftR ` \<G>\<close> and Q=\<open>pred_lift_exch4 ` Q\<close>])
            apply (metis pred_lift_exch4_Inf_distrib pred_lift_exch4_mono)
           apply (simp add: Inf_rel_times_distrib rel_times_mono; fail)
          apply (metis pred_lift_exch4_Inf_distrib pred_lift_exch4_mono)
         apply blast
        apply blast
       apply blast
      apply blast
     apply (simp add: cancellative'_lift_helper; fail)
    apply force
    done
qed


section \<open> Aligned Traces \<close>

subsection \<open> Parallel Labels \<close>

datatype plabel = PL plabel | PR plabel | PHere

subsection \<open> Parallel-labelled actions \<close>

text \<open> Extended Actions \<close>

datatype aact =
  TauINdetL |
  TauINdetR |
  TauBasic | \<comment> \<open> Taus other than Taus from INdet \<close>
  AVis

text \<open>
  In an aact, a tau move may be buried under parallel synchronisation labels,
  or divided into an INdet Tau, which are handled separately by the evaluation semantics.
  In programs where sub-programs may take actions (\<box>), we need an
  inductive test for whether an action is internal, as the sub-program may be a parallel.
\<close>
definition \<open>tau_aact \<alpha> \<equiv> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
definition \<open>vis_aact \<alpha> \<equiv> \<alpha> = AVis\<close>

lemma not_aact_iff:
  \<open>\<alpha> \<noteq> AVis \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauBasic \<longleftrightarrow> \<alpha> = AVis \<or> \<alpha> = TauINdetL \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauINdetL \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = AVis \<or> \<alpha> = TauINdetR\<close>
  \<open>\<alpha> \<noteq> TauINdetR \<longleftrightarrow> \<alpha> = TauBasic \<or> \<alpha> = TauINdetL \<or> \<alpha> = AVis\<close>
  using aact.exhaust by blast+

lemma not_tau_aact_iff[simp]:
  \<open>\<not> tau_aact \<pi>\<alpha> \<longleftrightarrow> vis_aact \<pi>\<alpha>\<close>
  by (force simp add: tau_aact_def vis_aact_def not_aact_iff)

lemma not_vis_aact_iff[simp]:
  \<open>\<not> vis_aact \<pi>\<alpha> \<longleftrightarrow> tau_aact \<pi>\<alpha>\<close>
  using not_tau_aact_iff by blast

lemma vis_tau_aact_incompatible:
  \<open>vis_aact \<alpha> \<Longrightarrow> tau_aact \<alpha> = False\<close>
  \<open>tau_aact \<alpha> \<Longrightarrow> vis_aact \<alpha> = False\<close>
  by (simp add: tau_aact_def vis_aact_def not_aact_iff)+

lemma vis_aact_not_TauBasic[simp]:
  \<open>vis_aact \<alpha> \<Longrightarrow> \<alpha> = TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact \<alpha> \<Longrightarrow> TauBasic = \<alpha> \<longleftrightarrow> False\<close>
  \<open>vis_aact (snd \<pi>\<alpha>) \<Longrightarrow> \<pi>\<alpha> = (\<pi>, TauBasic) \<longleftrightarrow> False\<close>
  by (force simp add: tau_aact_def vis_aact_def)+

lemma vis_aact_simps[simp]:
  \<open>vis_aact AVis\<close>
  \<open>vis_aact TauBasic \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetL \<longleftrightarrow> False\<close>
  \<open>vis_aact TauINdetR \<longleftrightarrow> False\<close>
  by (simp add: vis_aact_def)+

lemma tau_aact_simps[simp]:
  \<open>tau_aact TauBasic\<close>
  \<open>tau_aact TauINdetL\<close>
  \<open>tau_aact TauINdetR\<close>
  \<open>tau_aact AVis \<longleftrightarrow> False\<close>
  by (simp add: tau_aact_def)+

lemma all_aact_or_iff[simp]:
  \<open>(\<forall>\<pi>\<alpha>. vis_aact \<pi>\<alpha> \<or> P \<pi>\<alpha>) \<longleftrightarrow> (\<forall>\<pi>\<alpha>. tau_aact \<pi>\<alpha> \<longrightarrow> P \<pi>\<alpha>)\<close>
  \<open>(\<forall>\<pi>\<alpha>. tau_aact \<pi>\<alpha> \<or> P \<pi>\<alpha>) \<longleftrightarrow> (\<forall>\<pi>\<alpha>. vis_aact \<pi>\<alpha> \<longrightarrow> P \<pi>\<alpha>)\<close>
  using not_tau_aact_iff by blast+

lemma all_tau_all_vis_iff:
  \<open>(\<forall>\<alpha>. tau_aact \<alpha> \<longrightarrow> P \<alpha>) \<and>
   (\<forall>\<alpha>. vis_aact \<alpha> \<longrightarrow> P \<alpha>) \<longleftrightarrow>
    All P\<close>
  by force

fun strip_aact where
  \<open>strip_aact AVis = Vis\<close>
| \<open>strip_aact _ = Tau\<close>

lemma strip_aact_rev_iff[simp]:
  \<open>strip_aact \<alpha> = Tau \<longleftrightarrow> tau_aact \<alpha>\<close>
  \<open>Tau = strip_aact \<alpha> \<longleftrightarrow> tau_aact \<alpha>\<close>
  \<open>strip_aact \<alpha> = Vis \<longleftrightarrow> vis_aact \<alpha>\<close>
  \<open>Vis = strip_aact \<alpha> \<longleftrightarrow> vis_aact \<alpha>\<close>
  unfolding tau_aact_def vis_aact_def
  by (metis act.distinct(1) not_aact_iff(4) strip_aact.simps)+


type_synonym 'a ptrace = \<open>(plabel \<times> aact) list\<close>


subsection \<open> Parallel Opstep \<close>

text \<open>
  Unfortunately, because acts are often universally quantified,
  using a general type variable becomes prohibitively unwieldy.
  (Due to \<open>itself\<close> types and schematics type vars in \<open>induct\<close>.)
  Thus we just use unit.
\<close>
fun aopstep :: \<open>plabel \<times> aact \<Rightarrow> 's pconfig \<Rightarrow> 's pconfig \<Rightarrow> bool\<close> where
  \<open>aopstep \<pi>\<alpha> (s, Skip) sc' \<longleftrightarrow> False\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca ;; cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    (\<exists>s' ca'. aopstep \<pi>\<alpha> (s, ca) (s', ca') \<and> sc' = (s', ca' ;; cb))\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<^bold>\<sqinter> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauINdetL) \<and> sc' = (s, ca) \<or>
    \<pi>\<alpha> = (PHere, TauINdetR) \<and> sc' = (s, cb)\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<^bold>\<box> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> sc' = (s, cb) \<or>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> cb = Skip \<and> sc' = (s, ca) \<or>
    tau_aact (snd \<pi>\<alpha>) \<and> (\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb) \<and> aopstep \<pi>\<alpha> (s, ca) (s', ca')) \<or>
    tau_aact (snd \<pi>\<alpha>) \<and> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb') \<and> aopstep \<pi>\<alpha> (s, cb) (s', cb')) \<or>
    vis_aact (snd \<pi>\<alpha>) \<and> aopstep \<pi>\<alpha> (s, ca) sc' \<or>
    vis_aact (snd \<pi>\<alpha>) \<and> aopstep \<pi>\<alpha> (s, cb) sc'\<close>
| \<open>aopstep \<pi>\<alpha> (s, ca \<parallel> cb) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> ca = Skip \<and> cb = Skip \<and> sc' = (s, Skip) \<or>
    (\<exists>\<pi>\<alpha>' s' ca'. \<pi>\<alpha> = apfst PL \<pi>\<alpha>' \<and> aopstep \<pi>\<alpha>' (s, ca) (s', ca') \<and> sc' = (s', ca' \<parallel> cb)) \<or>
    (\<exists>\<pi>\<alpha>' s' cb'. \<pi>\<alpha> = apfst PR \<pi>\<alpha>' \<and> aopstep \<pi>\<alpha>' (s, cb) (s', cb') \<and> sc' = (s', ca \<parallel> cb'))\<close>
| \<open>aopstep \<pi>\<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> (\<forall>\<pi>\<alpha>' sc'. \<not> aopstep \<pi>\<alpha>' (s, c) sc') \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aopstep \<pi>\<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
| \<open>aopstep \<pi>\<alpha> (s, \<langle>ar\<rangle>) sc' \<longleftrightarrow>
    (\<pi>\<alpha> = (PHere, AVis) \<and> ar s (fst sc') \<and> snd sc' = Skip)\<close>

lemmas aopstep_induct = aopstep.induct[case_names Skip Seq Indet Endet Par DoLoop Atom]


paragraph \<open> Pretty parallel operational semantics \<close>

text \<open> \<open>sc\<close> can step to \<open>sc'\<close> \<close>
abbreviation pretty_aopstep :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> (\<open>_ \<midarrow>(_)\<rightarrow>\<^sub>a _\<close> [60,0,60] 60) where
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<equiv> aopstep \<pi>\<alpha> sc sc'\<close>

text \<open> no steps from \<open>sc\<close> can take place \<close>
definition pretty_no_aopstep :: \<open>'s \<times> 's comm \<Rightarrow> bool\<close> (\<open>_ \<midarrow>'/\<rightarrow>\<^sub>a\<close> [60] 60) where
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<equiv> \<forall>\<pi>\<alpha> sc'. \<not> aopstep \<pi>\<alpha> sc sc'\<close>

lemma aopstep_do_loop_iff[simp]:
  \<open>aopstep \<pi>\<alpha> (s, DO c OD) sc' \<longleftrightarrow>
    \<pi>\<alpha> = (PHere, TauBasic) \<and> (s, c) \<midarrow>/\<rightarrow>\<^sub>a \<and> sc' = (s, Skip) \<or>
    (\<exists>s' c'. aopstep \<pi>\<alpha> (s, c) (s', c') \<and> sc' = (s', c' ;; DO c OD))\<close>
  by (simp add: pretty_no_aopstep_def)

declare aopstep.simps(6)[simp del]


lemma pretty_no_aopstep_simps[simp]:
  \<open>(s, Skip) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca ;; cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca \<^bold>\<sqinter> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, ca \<^bold>\<box> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> ca \<noteq> Skip \<and> cb \<noteq> Skip \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, ca \<parallel> cb) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (cb \<noteq> Skip \<or> ca \<noteq> Skip) \<and> (s, ca) \<midarrow>/\<rightarrow>\<^sub>a \<and> (s, cb) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  \<open>(s, DO c OD) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> False\<close>
  \<open>(s, \<langle> ar \<rangle>) \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<nexists>s'. ar s s')\<close>
  by (fastforce simp add: pretty_no_aopstep_def all_conj_distrib)+


subsubsection \<open> aopstep lemmas \<close>

lemma no_aopstep_rgstate_iff:
  \<open>sc \<midarrow>/\<rightarrow>\<^sub>a \<longleftrightarrow> (\<forall>\<alpha> l' s' c'. \<not> aopstep \<alpha> sc ((l', s'), c'))\<close>
  by (clarsimp simp add: pretty_no_aopstep_def)

lemma aopstep_iter_stepD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, DO c OD) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' ;; DO c OD)\<close>
  by fastforce

lemma aopstep_tau_preserves_state:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<Longrightarrow> fst sc' = fst sc\<close>
  by (induct \<pi>\<alpha> sc sc' rule: aopstep_induct)
    (fastforce split: if_splits simp add: tau_aact_def)+

lemma vis_aopstep_impl_atom:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    \<exists>ar.
      ar \<in># head_atoms (snd sc) \<and>
      ar (fst sc) (fst sc')\<close>
  by (induct _ sc sc' rule: aopstep_induct; simp add: vis_aact_def tau_aact_def)
    fastforce+

lemma vis_aopstep_backwards_endet:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    snd sc' = ca' \<^bold>\<box> cb' \<Longrightarrow>
    \<exists>ca cb. snd sc = ca \<^bold>\<box> cb\<close>
  by (induct _ sc sc' arbitrary: ca' cb' rule: aopstep_induct)
    fastforce+

lemma aopstep_then_aopstep_right_seqD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (s, c ;; cx) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' ;; cx)\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct) simp+

lemma aopstep_then_aopstep_right_endetD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, c \<^bold>\<box> cb) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c' \<^bold>\<box> cb))\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_then_aopstep_left_endetD:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    sc = (s, c) \<Longrightarrow>
    sc' = (s', c') \<Longrightarrow>
    (vis_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')) \<and>
    (tau_aact (snd \<pi>\<alpha>) \<longrightarrow> (s, ca \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', ca \<^bold>\<box> c'))\<close>
  by (induct \<pi>\<alpha> sc sc' arbitrary: s c s' c' rule: aopstep_induct)
    (simp add: vis_aact_def tau_aact_def)+

lemma aopstep_aact_cases:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    (sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> vis_aact (snd \<pi>\<alpha>) \<Longrightarrow> P) \<Longrightarrow>
    (sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<Longrightarrow> fst sc' = fst sc \<Longrightarrow> P) \<Longrightarrow>
    P\<close>
  unfolding vis_aact_def tau_aact_def
  using not_vis_aact_iff aopstep_tau_preserves_state tau_aact_def vis_aact_def
  by blast

lemma aopstep_no_new_atoms:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow> set_mset (all_atoms c') \<subseteq> set_mset (all_atoms c)\<close>
  by (induct c arbitrary: \<pi>\<alpha> c' ms')
    (fastforce split: if_splits)+

lemma aopstep_preserves_conj_all_atoms_pred:
  fixes p :: \<open>_ \<Rightarrow> 'l::complete_lattice\<close>
  assumes \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c')\<close>
  shows \<open>\<Sqinter>{p ar|ar. ar \<in># all_atoms c} \<le> \<Sqinter>{p ar|ar. ar \<in># all_atoms c'}\<close>
  using assms aopstep_no_new_atoms[OF assms]
  by (force intro: Inf_superset_mono)


lemma aopstep_liftC_then_output_liftC:
  \<open>sscc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a msscc' \<Longrightarrow>
    sscc = ((ll, ss), liftC c) \<Longrightarrow>
    msscc' = ((ll', ss'), cc') \<Longrightarrow>
    (\<exists>c'. cc' = liftC c')\<close>
  apply (induct _ sscc msscc' arbitrary: ll ss c ll' ss' cc' rule: aopstep_induct)
        apply fastforce
       apply clarsimp
       apply (elim disjE; force)
      apply force
     apply clarsimp
     apply (elim disjE; force)
    apply fastforce
   apply fastforce
  apply force
  done

lemma aopstep_preserves_quasireflp_atoms:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> quasireflp_atoms c \<le> quasireflp_atoms c'\<close>
  by (simp add: quasireflp_atoms_def aopstep_preserves_conj_all_atoms_pred)

lemma aopstep_preserves_quasirefl_blocking_atoms:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> quasirefl_blocking_atoms c \<le> quasirefl_blocking_atoms c'\<close>
  by (simp add: quasirefl_blocking_atoms_def aopstep_preserves_conj_all_atoms_pred)

lemma aopstep_preserves_quasirefl_blocking_doloops_head_atoms:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    quasirefl_blocking_doloops_head_atoms c \<le> quasirefl_blocking_doloops_head_atoms c'\<close>
  unfolding quasirefl_blocking_doloops_head_atoms_def
  apply (induct c arbitrary: \<pi>\<alpha> c')
        apply force
    (* Seq *)
       apply (clarsimp simp add: le_fun_def imp_ex_conjL)
       apply (elim disjE)
        apply blast
       apply (clarsimp, blast)
    (* Par *)
      apply (clarsimp simp add: le_fun_def imp_ex_conjL all_conj_distrib)
      apply (elim disjE)
        apply blast
       apply (metis comm.distinct(29) less_eq_comm_simps_right(3))
      apply (metis comm.distinct(29) less_eq_comm_simps_right(3))
    (* INdet *)
     apply (force simp add: le_fun_def imp_ex_conjL)
    (* ENdet *)
    apply (clarsimp simp add: le_fun_def imp_ex_conjL)
    apply (elim disjE conjE)
         apply blast
        apply blast
       apply (metis comm.distinct(39) less_eq_comm_simps_right(5))
      apply (metis comm.distinct(39) less_eq_comm_simps_right(5))
     apply blast
    apply blast
    (* Atom *)
   apply force
    (* Do Loop *)
  apply (clarsimp simp add: le_fun_def imp_ex_conjL)
  apply (elim disjE conjE)
   apply force
  apply (metis comm.distinct(21) comm.inject(6) less_eq_comm_simps_right(2,7))
  done


subsubsection \<open> aopstep vs. opstep \<close>

lemma no_opstep_then_no_aopstep:
  \<open>(s, c) \<midarrow>/\<rightarrow> \<Longrightarrow> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
proof (induct c)
  case (Endet ca cb)
  then show ?case
    by (simp, metis (full_types) act.distinct(1))
next
  case (Iter ar)
  then show ?case
    by (simp, metis (full_types) act.distinct(1))
qed (clarsimp; blast)+

lemma opstep_then_aopstep:
  \<open>sc \<midarrow>\<alpha>\<rightarrow> sc' \<Longrightarrow> \<exists>\<pi>\<alpha>. \<alpha> = strip_aact (snd \<pi>\<alpha>) \<and> sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
proof (induct \<alpha> sc sc' rule: opstep_induct)
  case (Endet \<alpha> s ca cb sc')
  then show ?case
    by (simp, (elim disjE; clarsimp simp add: tau_aact_def; metis))
next
  case (Par \<alpha> s ca cb sc')
  then show ?case
    by (simp, (elim disjE; clarsimp; metis))
next
  case (DoLoop \<alpha> s c sc')
  then show ?case
    using no_opstep_then_no_aopstep[of s c]
    by (force simp add: pretty_no_aopstep_def)
qed force+

lemma no_aopstep_then_no_opstep:
  \<open>(s, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow> (s, c) \<midarrow>/\<rightarrow>\<close>
  by (meson pretty_no_aopstep_def opstep_then_aopstep)

lemma aopstep_then_opstep:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow> sc \<midarrow>strip_aact (snd \<pi>\<alpha>)\<rightarrow> sc'\<close>
proof (induct rule: aopstep_induct)
  case (Endet \<pi>\<alpha> s ca cb sc')
  then show ?case
    apply (cases \<open>snd \<pi>\<alpha>\<close>; simp)
       apply metis
      apply metis
     apply metis
    apply force
    done
next
  case (DoLoop \<pi>\<alpha> s c sc')
  then show ?case
    using opstep_then_aopstep
    apply (cases \<open>snd \<pi>\<alpha>\<close>; simp)
       apply fastforce
      apply fastforce
     apply (clarsimp simp add: pretty_no_aopstep_def)
     apply (metis prod.exhaust opstep_then_aopstep)
    apply fastforce
    done
qed force+


subsubsection \<open> Self-aopstep Impossible \<close>

lemma comm_self_containment_impossible[simp]:
  \<open>c1 ;; c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 ;; c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<parallel> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<sqinter> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<sqinter> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<box> c2 \<le> c1 \<longleftrightarrow> False\<close>
  \<open>c1 \<^bold>\<box> c2 \<le> c2 \<longleftrightarrow> False\<close>
  \<open>DO c OD \<le> c \<longleftrightarrow> False\<close>
  using less_comm_simps_right
  by (fastforce dest: leD)+

fun eval_focus :: \<open>'a comm \<Rightarrow> 'a comm set\<close> where
  \<open>eval_focus Skip = {Skip}\<close>
| \<open>eval_focus (ca ;; cb) = (if ca = Skip then {ca ;; cb} else eval_focus ca)\<close>
| \<open>eval_focus (ca \<parallel> cb) = (eval_focus ca \<union> eval_focus cb)\<close>
| \<open>eval_focus (ca \<^bold>\<sqinter> cb) = {ca \<^bold>\<sqinter> cb}\<close>
| \<open>eval_focus (ca \<^bold>\<box> cb) = eval_focus ca \<union> eval_focus cb\<close>
| \<open>eval_focus \<langle>ar\<rangle> = {\<langle>ar\<rangle>}\<close>
| \<open>eval_focus (DO c OD) = {c, DO c OD}\<close>

inductive endet_expansion :: \<open>'a comm \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  eexp_reflI[intro!]: \<open>endet_expansion c c\<close>
| eexp_leftI[intro]: \<open>endet_expansion c ca \<Longrightarrow> endet_expansion c (ca \<^bold>\<box> cb)\<close>
| eexp_rightI[intro]: \<open>endet_expansion c cb \<Longrightarrow> endet_expansion c (ca \<^bold>\<box> cb)\<close>

inductive_cases endet_expansion_right_SkipE[elim!]: \<open>endet_expansion c Skip\<close>
inductive_cases endet_expansion_right_SeqE[elim!]: \<open>endet_expansion c (ca ;; cb)\<close>
inductive_cases endet_expansion_right_IndetE[elim!]: \<open>endet_expansion c (ca \<^bold>\<sqinter> cb)\<close>
inductive_cases endet_expansion_right_EndetE[elim]: \<open>endet_expansion c (ca \<^bold>\<box> cb)\<close>
inductive_cases endet_expansion_right_ParE[elim!]: \<open>endet_expansion c (ca \<parallel> cb)\<close>
inductive_cases endet_expansion_right_AtomE[elim!]: \<open>endet_expansion c \<langle>ar\<rangle>\<close>
inductive_cases endet_expansion_right_IterE[elim!]: \<open>endet_expansion c (DO cx OD)\<close>

lemma endet_expansion_subcomm_antisym:
  \<open>endet_expansion ca cb \<Longrightarrow> cb \<le> ca \<Longrightarrow> ca = cb\<close>
  apply (induct cb arbitrary: ca)
        apply force
       apply force
      apply force
     apply force
    apply (metis comm_self_containment_impossible(7,8) less_eq_comm_leftD(7,8)
      endet_expansion_right_EndetE)
   apply force
  apply force
  done

lemma endet_expansion_indet_left[simp]:
  \<open>endet_expansion (c ;; cb) c = False\<close>
  \<open>endet_expansion (ca ;; c) c = False\<close>
  \<open>endet_expansion (c \<parallel> cb) c = False\<close>
  \<open>endet_expansion (ca \<parallel> c) c = False\<close>
  \<open>endet_expansion (c \<^bold>\<sqinter> cb) c = False\<close>
  \<open>endet_expansion (ca \<^bold>\<sqinter> c) c = False\<close>
  \<open>endet_expansion (c \<^bold>\<box> cb) c = False\<close>
  \<open>endet_expansion (ca \<^bold>\<box> c) c = False\<close>
  \<open>endet_expansion (DO c OD) c = False\<close>
  using endet_expansion_subcomm_antisym
  by fastforce+

lemma endet_expansion_endet_leftD:
  \<open>endet_expansion (ca \<^bold>\<box> cb) c' \<Longrightarrow> endet_expansion ca c'\<close>
  \<open>endet_expansion (ca \<^bold>\<box> cb) c' \<Longrightarrow> endet_expansion cb c'\<close>
  by (induct c') blast+

lemma self_aopstep_endet_cluster_then_crash:
  \<open>endet_expansion c c' \<Longrightarrow> (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> False\<close>
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Endet c1 c2)
  then show ?case
    by (clarsimp, metis comm.inject(4) eexp_reflI endet_expansion_right_EndetE
        endet_expansion_endet_leftD(1,2) endet_expansion_indet_left(7,8))
qed force+

lemmas self_aopstep_endet_cluster_then_crashD = 
  self_aopstep_endet_cluster_then_crash[rotated]

lemma self_aopstep_impossible:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) = False\<close>
  \<open>(s, c1) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  \<open>(s, c2) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c1 \<^bold>\<box> c2) = False\<close>
  by (force dest: self_aopstep_endet_cluster_then_crashD)+

lemma aopstep_endet_skip_then:
  \<open>(s, c \<^bold>\<box> Skip) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<and> s' = s\<close>
  \<open>(s, Skip \<^bold>\<box> c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c) \<Longrightarrow> tau_aact (snd \<pi>\<alpha>) \<and> s' = s\<close>
  by (simp add: self_aopstep_impossible,
      metis aopstep_tau_preserves_state split_pairs2 tau_aact_simps(1))+


subsubsection \<open> Aopstep lemmas \<close>

text \<open>
  It would be nice if a tau-move happening did not depend on the state.
  However, this is not the case, as do loops may exit based on whether the subcommand is blocked
  or not. This exit produced a tau-step.
\<close>
lemma tau_aopstep_state_irrelevant:
  \<comment> \<open> False because of do loops \<close>
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    tau_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    (sx, snd sc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx, snd sc')\<close>
proof (induct _ sc sc' arbitrary: sx rule: aopstep_induct)
  case (DoLoop \<pi>\<alpha> s c sc')
  then show ?case
    (* This subgoal fails *)
    oops
(*
qed (clarsimp; metis not_tau_aact_iff)+
*)

lemma basic_tau_aopstep_changes_comm:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    TauBasic = \<alpha> \<Longrightarrow>
    snd sc' \<noteq> snd sc\<close>
  by (induct rule: aopstep_induct) (force simp add: self_aopstep_impossible)+

lemma btau_astep_preserves_nextstep:
  assumes
    \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
    \<open>TauBasic = snd \<pi>\<alpha>\<close>
    \<open>sc \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a scx\<close>
    \<open>\<pi>\<alpha>x \<noteq> \<pi>\<alpha>\<close>
  shows
    \<open>\<exists>cx'. sc' \<midarrow>\<pi>\<alpha>x\<rightarrow>\<^sub>a (fst scx, cx')\<close>
proof -
  have H1: \<open>fst sc = fst sc'\<close>
    using assms(1-2)
    by (simp add: aopstep_tau_preserves_state)
  
  show ?thesis
    using assms H1
  proof (induct _ sc sc' arbitrary: \<pi>\<alpha>x scx rule: aopstep_induct)
    case (Seq \<pi>\<alpha> s ca cb sc')
    then show ?case
      apply clarsimp
      apply (metis aopstep.simps(1) aopstep_then_aopstep_right_seqD fst_conv
          prod.exhaust)
      done
  next
    case (Endet \<pi>\<alpha> s ca cb sc')
    show ?case
      using Endet.prems
      apply (cases scx, rename_tac sx cx)
      apply (clarsimp simp add: vis_tau_aact_incompatible(2))
      apply (elim disjE[of \<open>\<pi>\<alpha> = _ \<and> _\<close>])
        apply fastforce
       apply fastforce
      apply (elim disjE[of \<open>\<pi>\<alpha>x = _ \<and> _\<close>])
        apply (clarsimp, blast)
       apply (clarsimp, blast)
      apply (case_tac \<open>
        ((\<exists>s' ca'. sc' = (s', ca' \<^bold>\<box> cb)) \<or> (\<exists>s' cb'. sc' = (s', ca \<^bold>\<box> cb'))) \<and>
          ((\<exists>ca'. cx = ca' \<^bold>\<box> cb) \<or> (\<exists>cb'. cx = ca \<^bold>\<box> cb'))\<close>)
       apply (elim conjE disjE[of \<open>\<exists>x y. sc' = _ x y\<close>] disjE[of \<open>\<exists>x. _ = _ x\<close>])
          apply (clarsimp, metis Endet.hyps(1) fst_conv)
         apply (clarsimp simp add: self_aopstep_impossible, blast)
        apply (clarsimp simp add: self_aopstep_impossible, blast)
       apply (clarsimp, metis Endet.hyps(2) fst_eqD)
      apply clarsimp
      apply (elim disjE; (simp; fail)?)
         apply (metis Endet.hyps(1) aopstep_then_aopstep_right_endetD fst_conv)
        apply fastforce
       apply fastforce
      apply (metis Endet.hyps(2) aopstep_then_aopstep_left_endetD fst_conv)
      done
  next
    case (Par \<pi>\<alpha> s ca cb sc')
    then show ?case
      apply (cases \<pi>\<alpha>, cases \<pi>\<alpha>x, rename_tac \<pi> \<alpha> \<pi>x \<alpha>x)
      apply clarsimp
      apply (case_tac \<open>\<pi> = PHere\<close>)
       apply (simp, metis aopstep.simps(1))
      apply (case_tac \<open>\<pi>x = PHere\<close>)
       apply (simp; fail)
      apply (case_tac \<open>
        (\<exists>\<pi>'. \<pi> = PL \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PL \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PR \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PR \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PL \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PR \<pi>') \<or>
        (\<exists>\<pi>'. \<pi> = PR \<pi>') \<and> (\<exists>\<pi>'. \<pi>x = PL \<pi>')\<close>)
       apply (elim conjE disjE[of \<open>Ex _ \<and> Ex _\<close>]; clarsimp; blast)
        (* other cases *)
      apply clarsimp
      apply metis
      done
  next
    case (DoLoop \<pi>\<alpha> s c sc')
    show ?case
      using DoLoop.prems
      apply (clarsimp simp add: pretty_no_aopstep_def)
      apply (metis DoLoop.hyps(1) aopstep_then_aopstep_right_seqD split_pairs2)
      done
  qed fastforce+
qed

lemmas btau_astep_preserves_nextstep2 =
  btau_astep_preserves_nextstep[of \<open>(\<pi>, \<alpha>)\<close> for \<pi> \<alpha>, simplified]


subsection \<open> Head Enabled Equivalent States \<close>

definition
  \<open>head_enabled_equiv c sx sy \<equiv> \<forall>a\<in>#head_atoms c. pre_state a sx = pre_state a sy\<close>

lemma head_enabled_equiv_skip_iff[simp]:
  \<open>head_enabled_equiv Skip sx sy\<close>
  \<open>head_enabled_equiv (ca ;; cb) sx sy \<longleftrightarrow> head_enabled_equiv ca sx sy\<close>
  \<open>head_enabled_equiv (ca \<^bold>\<sqinter> cb) sx sy\<close>
  \<open>head_enabled_equiv (ca \<^bold>\<box> cb) sx sy \<longleftrightarrow>
    head_enabled_equiv ca sx sy \<and> head_enabled_equiv cb sx sy\<close>
  \<open>head_enabled_equiv (ca \<parallel> cb) sx sy \<longleftrightarrow>
    head_enabled_equiv ca sx sy \<and> head_enabled_equiv cb sx sy\<close>
  \<open>head_enabled_equiv (DO c OD) sx sy \<longleftrightarrow>
    head_enabled_equiv c sx sy\<close>
  \<open>head_enabled_equiv \<langle>ar\<rangle> sx sy \<longleftrightarrow>
    pre_state ar sx = pre_state ar sy\<close>
  unfolding head_enabled_equiv_def
  by (simp add: Ball_def Bex_def all_conj_distrib image_def imp_ex_conjL split: prod.splits)+

lemma head_enabled_equiv_reflI[intro!]:
  \<open>head_enabled_equiv c s s\<close>
  by (simp add: head_enabled_equiv_def)

lemma head_enabled_equiv_sym:
  \<open>head_enabled_equiv c sx sy \<Longrightarrow> head_enabled_equiv c sy sx\<close>
  by (force simp add: head_enabled_equiv_def)

lemma head_guard_trans_trans[trans]:
  \<open>head_enabled_equiv c sx sy \<Longrightarrow> head_enabled_equiv c sy sz \<Longrightarrow> head_enabled_equiv c sx sz\<close>
  by (force simp add: head_enabled_equiv_def)


subsection \<open> Do Loops \<close>

fun do_loops :: \<open>'s comm \<Rightarrow> 's comm multiset\<close> where
  \<open>do_loops Skip = {#}\<close>
| \<open>do_loops (ca;; cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<parallel> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<^bold>\<sqinter> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops (ca \<^bold>\<box> cb) = do_loops ca \<union># do_loops cb\<close>
| \<open>do_loops \<langle>ar\<rangle> = {#}\<close>
| \<open>do_loops (DO c OD) = add_mset c (do_loops c)\<close>

paragraph \<open> Lemmas \<close>

text \<open> Doing this with multisets is false, as do-loops may duplicate parts of the command. \<close>
lemma aopstep_do_loops_subseteq:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (ms', c') \<Longrightarrow>
    set_mset (do_loops c') \<subseteq> set_mset (do_loops c)\<close>
  by (induct c arbitrary: s ms' c' \<pi>\<alpha>)
    (fastforce simp add: if_bool_eq_disj conj_disj_distribL)+


subsection \<open> Do-Loop Enabled State Equivalence \<close>

abbreviation
  \<open>do_loop_head_enabled_equiv c sx sy \<equiv>
    \<forall>c'\<in>#do_loops c. head_enabled_equiv c' sx sy\<close>

lemma do_loop_head_enabled_equiv_iff[simp]:
  \<open>do_loop_head_enabled_equiv Skip sx sy\<close>
  \<open>do_loop_head_enabled_equiv \<langle>ar\<rangle> sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca ;; cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<^bold>\<sqinter> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<^bold>\<box> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (ca \<parallel> cb) sx sy \<longleftrightarrow>
    do_loop_head_enabled_equiv ca sx sy \<and> do_loop_head_enabled_equiv cb sx sy\<close>
  \<open>do_loop_head_enabled_equiv (DO c OD) sx sy \<longleftrightarrow>
    head_enabled_equiv c sx sy \<and> do_loop_head_enabled_equiv c sx sy\<close>
  by (simp add: Ball_def all_conj_distrib)+

paragraph \<open> Lemmas \<close>

lemma no_aopstep_head_enabled_equiv_state_irrel:
  \<open>(sx, c) \<midarrow>/\<rightarrow>\<^sub>a \<Longrightarrow>
    head_enabled_equiv c sx sy \<Longrightarrow>
    (sy, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
proof (induct c arbitrary: sx sy)
  case (Endet c1 c2)
  then show ?case
    by (clarsimp simp add: pretty_no_aopstep_def split: if_splits, metis not_vis_aact_iff)
next
  case (Atomic x1 x2)
  then show ?case
    by (force simp add: if_bool_eq_disj pre_state_def)
qed (clarsimp simp add: all_conj_distrib; fail)+ (* slow *)


subsection \<open> Head Enabled Unique \<close>

definition
  \<open>head_enabled_unique c s \<equiv>
    \<forall>a\<in>#head_atoms c. \<forall>b\<in>#head_atoms c. pre_state a s = pre_state b s \<longrightarrow> a = b\<close>

subsubsection \<open> Do-guards Determinism \<close>

definition
  \<open>do_loops_determ c s \<equiv>
    (\<forall>c'\<in>#do_loops c.
      (\<forall>a. count (head_atoms c') a \<le> Suc 0) \<and>
      head_enabled_unique c' s)\<close>

lemma do_loops_determ_iff[simp]:
  \<open>do_loops_determ Skip s\<close>
  \<open>do_loops_determ \<langle>ar\<rangle> s\<close>
  \<open>do_loops_determ (ca ;; cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<^bold>\<sqinter> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<^bold>\<box> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (ca \<parallel> cb) s \<longleftrightarrow>
    do_loops_determ ca s \<and> do_loops_determ cb s\<close>
  \<open>do_loops_determ (DO c OD) s \<longleftrightarrow>
    (\<forall>a. count (head_atoms c) a \<le> Suc 0) \<and>
    head_enabled_unique c s \<and>
    do_loops_determ c s\<close>
  unfolding do_loops_determ_def
  by (clarsimp simp add: ball_Un; fail)+

paragraph \<open> Lemmas \<close>

lemma aopstep_tau_determ_doloop_then_state_irrel:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    do_loop_head_enabled_equiv c s sa \<Longrightarrow>
    tau_aact (snd \<pi>\<alpha>) \<Longrightarrow>
    (sa, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sa, c')\<close>
proof (induct c arbitrary: \<pi>\<alpha> s' c')
  case (Endet c1 c2)
  then show ?case by (simp, metis)
next
  case (Iter c)
  then show ?case
    by (simp, metis no_aopstep_head_enabled_equiv_state_irrel)
qed fastforce+

lemma head_atomic_implies_all_steps_vis:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>)\<close>
  by (induct _ sc sc' rule: aopstep_induct) auto


subsection \<open> Security Determinism \<close>

definition
  \<open>head_guards \<equiv> image_mset pre_state \<circ> head_atoms\<close>

fun sec_determ :: \<open>('l \<times> 's) comm \<Rightarrow> ('l, 's) secstate \<Rightarrow> bool\<close> where
  \<open>sec_determ (ca \<^bold>\<box> cb) = (
    (\<lambda>_. head_atomic ca) \<sqinter>
    (\<lambda>_. head_atomic cb) \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards ca)) \<bar> \<Squnion>(set_mset (head_guards cb)) \<rblot> \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards cb)) \<bar> \<Squnion>(set_mset (head_guards ca)) \<rblot>)\<close>
| \<open>sec_determ (DO c OD) = (
    (\<lambda>_. head_atomic c) \<sqinter>
    \<bbbA> (\<Squnion>(set_mset (head_guards c))))\<close>
| \<open>sec_determ c = (\<lambda>_. True)\<close>

lemma
  \<open>pa \<sqinter> pb = \<bottom> \<Longrightarrow>
    - \<lblot> pa \<bar> pb \<rblot> \<sqinter> - \<lblot> pb \<bar> pa \<rblot> \<le> \<bbbA> pa \<sqinter> \<bbbA> pb\<close>
  apply (simp add: sec_agree_def le_fun_def fun_eq_iff)
  nitpick
  oops


lemma sec_determ_symp:
  \<open>symp (curry (sec_determ c))\<close>
  by (induct c) (clarsimp simp add: symp_def sec_agree_exch4_def'; meson)+

lemma head_atom_equivalence_helper:
  \<open>\<not> (pre_state (\<Squnion>(set_mset (head_atoms ca))) sx \<and> pre_state (\<Squnion>(set_mset (head_atoms cb))) sy) \<longleftrightarrow>
    (\<forall>ra \<in># head_atoms ca. \<forall>rb \<in># head_atoms cb. \<not> (pre_state ra sx \<and> pre_state rb sy))\<close>
  by (fastforce simp add: pre_state_def)


definition
  \<open>head_sec_determ c \<equiv> \<Sqinter>{sec_determ c'|c'. c' \<in># head_comms c}\<close>

lemma head_sec_determ_eq[simp]:
  \<open>head_sec_determ Skip = \<top>\<close>
  \<open>head_sec_determ (ca ;; cb) = head_sec_determ ca\<close>
  \<open>head_sec_determ (ca \<^bold>\<sqinter> cb) = \<top>\<close>
  \<open>head_sec_determ \<langle>ra\<rangle> = \<top>\<close>
  \<open>head_sec_determ (ca \<parallel> cb) = head_sec_determ ca \<sqinter> head_sec_determ cb\<close>
  \<open>head_sec_determ (ca \<^bold>\<box> cb) =
    (\<lambda>_. head_atomic ca) \<sqinter>
    (\<lambda>_. head_atomic cb) \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards ca)) \<bar> \<Squnion>(set_mset (head_guards cb)) \<rblot> \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards cb)) \<bar> \<Squnion>(set_mset (head_guards ca)) \<rblot> \<sqinter>
    head_sec_determ ca \<sqinter>
    head_sec_determ cb\<close>
  \<open>head_sec_determ (DO c OD) =
    (\<lambda>_. head_atomic c) \<sqinter>
    \<bbbA> (\<Squnion>(set_mset (head_guards c))) \<sqinter>
    head_sec_determ c\<close>
  by (clarsimp simp add: head_sec_determ_def conj_disj_distribL
      ex_disj_distrib Collect_disj_eq; blast)+

lemma head_sec_determ_implies_sec_determ:
  \<open>head_sec_determ c s \<Longrightarrow> sec_determ c s\<close>
  using heads_refl
  by (force simp add: head_sec_determ_def)


definition
  \<open>all_sec_determ c \<equiv> \<Sqinter>{sec_determ c'|c'. c' \<le> c}\<close>

lemma all_sec_determ_eq[simp]:
  \<open>all_sec_determ Skip = \<top>\<close>
  \<open>all_sec_determ (ca ;; cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ (ca \<^bold>\<sqinter> cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ \<langle>ra\<rangle> = \<top>\<close>
  \<open>all_sec_determ (ca \<parallel> cb) = all_sec_determ ca \<sqinter> all_sec_determ cb\<close>
  \<open>all_sec_determ (ca \<^bold>\<box> cb) =
    (\<lambda>_. head_atomic ca) \<sqinter>
    (\<lambda>_. head_atomic cb) \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards ca)) \<bar> \<Squnion>(set_mset (head_guards cb)) \<rblot> \<sqinter>
    - \<lblot> \<Squnion>(set_mset (head_guards cb)) \<bar> \<Squnion>(set_mset (head_guards ca)) \<rblot> \<sqinter>
    all_sec_determ ca \<sqinter>
    all_sec_determ cb\<close>
  \<open>all_sec_determ (DO c OD) =
    (\<lambda>_. head_atomic c) \<sqinter>
    (\<lambda>_. head_atomic c) \<sqinter>
    \<bbbA> (\<Squnion>(set_mset (head_guards c))) \<sqinter>
    all_sec_determ c\<close>
  by (clarsimp simp add: all_sec_determ_def conj_disj_distribL
      ex_disj_distrib Collect_disj_eq; blast)+

lemma all_sec_determ_implies_head_sec_determ:
  \<open>all_sec_determ c s \<Longrightarrow> head_sec_determ c s\<close>
  by (clarsimp simp add: all_sec_determ_def head_sec_determ_def,
      metis heads_subcomm_original)

lemma all_sec_determ_implies_sec_determ:
  \<open>all_sec_determ c s \<Longrightarrow> sec_determ c s\<close>
  by (clarsimp simp add: all_sec_determ_def, blast)


lemma aopstep_preserves_all_sec_determ:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow> all_sec_determ c \<le> all_sec_determ c'\<close>
proof (induct c arbitrary: \<pi>\<alpha> c')
  case (Endet c1 c2)
  then show ?case
    apply clarsimp
    apply (elim disjE[of \<open>_ \<and> _\<close>])
         apply force
        apply force
       apply (metis head_atomic_implies_all_steps_vis split_pairs tau_aact_simps(4) vis_aact_def)
      apply (metis head_atomic_implies_all_steps_vis split_pairs tau_aact_simps(4) vis_aact_def)
     apply (blast dest: Endet.hyps(1))
    apply (blast dest: Endet.hyps(2))
    done
qed fastforce+


subsubsection \<open> Sec. Determ. Lemmas \<close>

lemma state_in_head_guards_then_aopstep_exists:
  \<open>(\<exists>p\<in>#head_guards c. p s) \<Longrightarrow>
    \<exists>\<pi>\<alpha> sc'. (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<and> vis_aact (snd \<pi>\<alpha>)\<close>
  unfolding head_guards_def
proof (induct c)
  case (Seq c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def, metis)
next
  case (Par c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def image_def, metis)
next
  case (Endet c1 c2)
  then show ?case
    by (clarsimp simp add: pre_state_def image_def, metis)
qed (clarsimp simp add: pre_state_def; blast)+

lemma state_not_in_head_guards_then_no_aopstep:
  \<open>head_atomic c \<Longrightarrow>
    \<forall>p\<in>#head_guards c. \<not> p s \<Longrightarrow>
    (s, c) \<midarrow>/\<rightarrow>\<^sub>a \<close>
proof (induct c)
  case (Seq c1 c2)
  then show ?case
    by (simp add: head_guards_def, metis head_atomic.simps(1))
next
  case (Par c1 c2)
  then show ?case
    by (simp add: head_guards_def ball_Un, metis head_atomic.simps(1))
next
  case (Endet c1 c2)
  then show ?case
    by (simp add: head_guards_def ball_Un, metis head_atomic.simps(1))
next
  case (Iter c)
  then show ?case
    by (metis head_atomic.simps(7))
qed (simp add: head_guards_def pre_state_def)+

lemma state_not_in_head_guards_iff_not_nostep:
  \<open>head_atomic c \<Longrightarrow> (\<exists>p\<in>#head_guards c. p s) \<longleftrightarrow> (\<exists>\<pi>\<alpha> sc'. (s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc')\<close>
  by (metis state_in_head_guards_then_aopstep_exists
      state_not_in_head_guards_then_no_aopstep pretty_no_aopstep_def)

lemma head_atomic_nostep_iff_state_not_in_head_guards:
  \<open>head_atomic c \<Longrightarrow> (\<forall>p\<in>#head_guards c. \<not> p s) \<longleftrightarrow> (s, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  using state_not_in_head_guards_iff_not_nostep pretty_no_aopstep_def
  by metis


subsubsection \<open> The Key Lemmas \<close>

lemma head_atomic_opstep_vis_aact:
  \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc' \<Longrightarrow>
    head_atomic (snd sc) \<Longrightarrow>
    vis_aact (snd \<pi>\<alpha>)\<close>
  by (induct _ sc sc' rule: aopstep_induct) fastforce+

lemma same_initcomm_and_aact_then_same_fincomm:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', cx')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy')\<close>
    \<open>head_sec_determ c (sx, sy)\<close>
  shows
    \<open>cy' = cx'\<close>
proof -
  { fix sc sc'
    assume
      \<open>sc \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a sc'\<close>
      \<open>(sy, snd sc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', cy')\<close>
      \<open>head_sec_determ (snd sc) (fst sc, sy)\<close>
    then have \<open>cy' = snd sc'\<close>
    proof (induct _ sc sc' arbitrary: sy sy' cy' rule: aopstep_induct)
      case (Endet \<pi>\<alpha> sx ca cb sc')
      then show ?case
        apply simp
        apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
         apply (clarsimp simp add: vis_tau_aact_incompatible
            head_atomic_nostep_iff_state_not_in_head_guards)
         apply (metis pretty_no_aopstep_def surj_pair)
        apply (clarsimp simp add: head_atomic_nostep_iff_state_not_in_head_guards)
        apply (metis head_atomic_implies_all_steps_vis snd_eqD tau_aact_def vis_aact_simps(2-4))
        done
    next
      case (DoLoop \<pi>\<alpha> s c sc')
      then show ?case
        apply simp
        apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
        apply (simp, metis snd_conv)
        apply (metis head_atomic_opstep_vis_aact snd_conv)
        done
    qed fastforce+
  }
  then show ?thesis
    using assms
    by fastforce
qed

lemma two_steps_no_aopstep_then_no_double_aopstep:
  assumes
    \<open>head_sec_determ c (sx, sy)\<close>
    \<open>(sx, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>(sy, c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  shows
    \<open>(exch4 (sx, sy), liftC c) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  using assms
proof (induct c arbitrary: sx sy)
  case (Seq ca cb)
  show ?case
    using Seq.prems
    apply (clarsimp simp add: exch4_def split: prod.splits)
    apply (metis Seq.hyps(1) exch4_two_apply)
    done
next
  case (Par ca cb)
  moreover have \<open>ca \<noteq> Skip \<or> cb \<noteq> Skip\<close>
    using Par.prems(2)
    by (clarsimp simp add: all_conj_distrib split_pairs)
  ultimately show ?case
    using Par.hyps(1-2) Par.prems(1)
    by (clarsimp simp add: exch4_def)
next
  case (Endet ca cb)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: all_conj_distrib ball_conj_distrib)
    apply (intro conjI)
     apply (blast dest: Endet.hyps(1))
    apply (blast dest: Endet.hyps(2))
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    by (clarsimp simp add: all_conj_distrib ball_conj_distrib split_pairs)
qed (clarsimp simp add: all_conj_distrib)+


lemma full_sync_double_aopstep_to_aopstep:
  assumes
    \<open>(sx, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', c')\<close>
    \<open>(sy, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', c')\<close>
    \<open>head_sec_determ c (sx, sy)\<close>
  shows
    \<open>(exch4 (sx, sy), liftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (exch4 (sx', sy'), liftC c')\<close>
  using assms
proof (induct c arbitrary: sx sy sx' sy' c' \<pi>\<alpha>)
  case (Endet c1 c2)
  then show ?case
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (simp add: vis_tau_aact_incompatible)
     apply (metis head_atomic_nostep_iff_state_not_in_head_guards pretty_no_aopstep_def)
    apply (simp add: vis_tau_aact_incompatible)
    apply (metis head_atomic.simps(1) head_atomic_opstep_vis_aact not_tau_aact_iff split_pairs)
    done
next
  case (Iter c)
  show ?case
    using Iter.prems
    apply (case_tac \<open>vis_aact (snd \<pi>\<alpha>)\<close>)
     apply (clarsimp simp add: vis_tau_aact_incompatible)
     apply (drule(2) Iter.hyps)
     apply force
    apply (clarsimp simp add: vis_tau_aact_incompatible)
    apply (elim disjE conjE exE; simp)
     apply (metis two_steps_no_aopstep_then_no_double_aopstep)
    apply (metis head_atomic_opstep_vis_aact not_tau_aact_iff snd_conv)
    done
qed fastforce+

definition secure_loop_states
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm \<Rightarrow> ('l \<times> 's) \<times> ('l \<times> 's) \<Rightarrow> bool\<close>
  where
  \<open>secure_loop_states c \<equiv>
    \<Sqinter>{(\<lambda>(sx,sy).
          \<not> pre_state ar (exch4 (sx, sy)) \<longrightarrow>
          \<not> pred_image fst (pre_state (ar \<circ>\<^sub>2 exch4)) sx \<and>
          \<not> pred_image snd (pre_state (ar \<circ>\<^sub>2 exch4)) sy)|ar.
        \<exists>c'. c = DO c' OD \<and> ar \<in># head_atoms c'}\<close>

lemma secure_loop_states_simps[simp]:
  \<open>secure_loop_states (DO c OD) =
    all_head_atoms (\<lambda>ar.
      \<Sqinter>{(\<lambda>(sx,sy).
          \<not> pre_state ar (exch4 (sx, sy)) \<longrightarrow>
          \<not> pred_image fst (pre_state (ar \<circ>\<^sub>2 exch4)) sx \<and>
          \<not> pred_image snd (pre_state (ar \<circ>\<^sub>2 exch4)) sy)}) c\<close>
  \<open>secure_loop_states Skip = \<top>\<close>
  \<open>secure_loop_states (ca \<^bold>\<sqinter> cb) = \<top>\<close>
  \<open>secure_loop_states (ca \<^bold>\<box> cb) = \<top>\<close>
  \<open>secure_loop_states (ca ;; cb) = \<top>\<close>
  \<open>secure_loop_states (ca \<parallel> cb) = \<top>\<close>
  \<open>secure_loop_states \<langle>ar\<rangle> = \<top>\<close>
  by (simp add: secure_loop_states_def all_atom_comm_def all_head_atoms_def)+


abbreviation(input) head_secure_loop_states
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm \<Rightarrow> ('l \<times> 's) \<times> ('l \<times> 's) \<Rightarrow> bool\<close>
  where
    \<open>head_secure_loop_states \<equiv> all_head_comm secure_loop_states\<close>

abbreviation(input) all_secure_loop_states
  :: \<open>(('l \<times> 'l) \<times> ('s \<times> 's)) comm \<Rightarrow> ('l \<times> 's) \<times> ('l \<times> 's) \<Rightarrow> bool\<close>
  where
    \<open>all_secure_loop_states \<equiv> all_subcomm_eq_InfIm secure_loop_states\<close>


lemma all_secure_loop_states_implies_head_secure_loop_states:
  \<open>all_secure_loop_states c s \<Longrightarrow> head_secure_loop_states c s\<close>
  using all_head_comm_le_all_subcomm_eq by blast

lemma aopstep_preserves_all_secure_loop_states:
  \<open>(s, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (s', c') \<Longrightarrow>
    all_secure_loop_states c \<le> all_secure_loop_states c'\<close>
  by (induct c arbitrary: \<pi>\<alpha> c') fastforce+


lemma doublest_nostep_then_some_singlest_unliftC_nostep:
  assumes
    \<open>(sxy, cc) \<midarrow>/\<rightarrow>\<^sub>a\<close>
    \<open>sxy = exch4 (sx, sy)\<close>
    \<open>quasirefl_blocking_head_atoms cc sxy\<close>
  shows
    \<open>(sx, unliftC cc) \<midarrow>/\<rightarrow>\<^sub>a \<and> (sy, unliftC cc) \<midarrow>/\<rightarrow>\<^sub>a\<close>
  using assms
proof (induct cc arbitrary: sxy sx sy)
  case (Seq cc1 cc2)
  show ?case
    using Seq.prems
    by (force simp add: unliftC_rev_iff Seq.hyps(1) dest: Seq.hyps(1))
next
  case (Par cc1 cc2)
  show ?case
    using Par.prems
    by (force simp add: unliftC_rev_iff dest: Par.hyps)
next
  case (Indet cc1 cc2)
  then show ?case
    by force
next
  case (Endet cc1 cc2)
  show ?case
    using Endet.prems
    by (force simp add: unliftC_rev_iff dest: Endet.hyps)
next
  case (Atomic ar)
  then show ?case
    by (clarsimp simp add: exch4_def quasirefl_blocking_steprel_def)
next
  case (Iter cc)
  then show ?case
    by (metis pretty_no_aopstep_simps(6))
qed (force simp add: all_conj_distrib)+

lemma doublest_step_then_singlest_unliftC_step:
  assumes
    \<open>(sxy, cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sxy', cc')\<close>
    \<open>exch4 sxy = (sx, sy)\<close>
    \<open>exch4 sxy' = (sx', sy')\<close>
    \<open>quasireflp_head_atoms cc sxy\<close>
    \<open>quasirefl_blocking_head_doloops_head_atoms cc sxy\<close>
  shows
    \<open>(sx, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sx', unliftC cc') \<and>
     (sy, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sy', unliftC cc')\<close>
  using assms
proof (induct cc arbitrary: \<pi>\<alpha> sxy sx sy sxy' sx' sy' cc')
  case (Seq cc1 cc2)
  show ?case
    using Seq.prems
    apply (clarsimp split: prod.splits)
    apply (elim disjE conjE exE)
     apply force
    apply (clarsimp split: prod.splits)
    apply (simp add: Seq.hyps(1))
    done
next
  case (Par cc1 cc2)
  show ?case
    using Par.prems
    apply (clarsimp split: prod.splits)
    apply (subgoal_tac \<open>(\<exists>\<alpha>. \<pi>\<alpha> = (PHere, \<alpha>)) \<or> (\<exists>\<pi>' \<alpha>. \<pi>\<alpha> = (PL \<pi>', \<alpha>)) \<or> (\<exists>\<pi>' \<alpha>. \<pi>\<alpha> = (PR \<pi>', \<alpha>))\<close>)
     prefer 2
     apply force
    apply (elim disjE[of \<open>Ex _\<close>])
      apply fastforce
     apply (clarsimp simp add: ball_Un)
     apply (frule(1) Par.hyps(1), force, force, force, force)
    apply (clarsimp simp add: ball_Un)
    apply (frule(1) Par.hyps(2), force, force, force, force)
    done
next
  case (Endet cc1 cc2)
  show ?case
    using Endet.prems
    apply (clarsimp simp add: ball_Un split: prod.splits)
    apply (elim disjE conjE exE)
         apply force
        apply force
       apply (clarsimp split: prod.splits)
       apply (metis Endet.hyps(1))
      apply (clarsimp split: prod.splits)
      apply (metis Endet.hyps(2))
     apply (simp add: vis_tau_aact_incompatible)
     apply (frule(3) Endet.hyps(1), force, force)
    apply (simp add: vis_tau_aact_incompatible)
    apply (frule(3) Endet.hyps(2), force, force)
    done
next
  case (Atomic ar)
  then show ?case
    by (clarsimp simp add: exch4_def quasireflp_steprel_def, metis surjective_pairing)
next
  case (Iter cc)
  show ?case
    using Iter.prems
    apply (clarsimp simp add: imp_ex_conjL split: prod.splits)
    apply (elim disjE conjE exE)
     apply clarsimp
     apply (metis doublest_nostep_then_some_singlest_unliftC_nostep exch4_idem)
    apply (metis Iter.hyps surj_pair unliftC_simps(2,7))
    done
qed (fastforce split: prod.splits)+


text \<open>
  Like \<open>safe\<close>, but with an additional secure step condition.
\<close>
inductive secure
  :: \<open>('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      ('s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      (('l, 's) rgstate \<Rightarrow> bool) \<Rightarrow>
      nat \<Rightarrow>
      ('l, 's) rgstate comm \<Rightarrow>
      ('l::pre_perm_alg, 's) rgstate \<Rightarrow>
      bool\<close>
  for R F G I q
  where secureI[intro]:
  \<open>\<comment> \<open> bindings \<close>
    s = (ls, ss) \<Longrightarrow>
    \<comment> \<open> the four safety conditions: \<close>
    \<comment> \<open> Post-condition \<close>
    c = Skip \<longrightarrow> q s \<Longrightarrow>
    \<comment> \<open> State Invariant \<close>
    I s \<Longrightarrow>
    \<comment> \<open> Rely Steps \<close>
    (\<And>n' ss'.
      n = Suc n' \<Longrightarrow>
      R ss ss' \<Longrightarrow>
      secure R F G I q n' c (ls, ss')) \<Longrightarrow>
    \<comment> \<open> Opsteps \<close>
    (\<And>n' \<alpha> ls' ss' c'.
      n = Suc n' \<Longrightarrow>
      (s, c) \<midarrow>\<alpha>\<rightarrow> ((ls', ss'), c') \<Longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
      (\<alpha> = Tau \<longrightarrow> ls' = ls) \<and>
      secure R F G I q n' c' (ls', ss')) \<Longrightarrow>
    \<comment> \<open> Framed opsteps \<close>
    (\<And>n' f \<alpha> lsf' ss' c'.
      n = Suc n' \<Longrightarrow>
      F (f, ss) \<Longrightarrow>
      ls ## f \<Longrightarrow>
      ((ls + f, ss), c) \<midarrow>\<alpha>\<rightarrow> ((lsf', ss'), c') \<Longrightarrow>
      (\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
      (\<exists>ls'.
        ls' ## f \<and> lsf' = ls' + f \<and>
        (\<alpha> = Tau \<longrightarrow> ls' = ls) \<and>
        secure R F G I q n' c' (ls', ss'))) \<Longrightarrow>
    \<comment> \<open> the security conditions: \<close>
    (\<And>n' \<pi>\<alpha> sa sax say.
      n = Suc n' \<Longrightarrow>
      \<comment> \<open> the state may be framed \<close>
      sa = s \<or> (\<exists>f. F (f, ss) \<and> ls ## f \<and> sa = (ls + f, ss)) \<Longrightarrow>
      exch4 sa = (sax, say) \<Longrightarrow>
      \<comment> \<open> a paired-state step has two corresponding single-steps with the commands related
            by unlifting. \<close>
      (\<forall>sa' c' sax' say'.
        (sa, c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sa', c') \<longrightarrow>
        exch4 sa' = (sax', say') \<longrightarrow>
        (sax, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sax', unliftC c') \<and>
        (say, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (say', unliftC c')) \<and>
      \<comment> \<open> any two steps from the related initial states produce the same final command. \<close>
      (\<forall>sax' say' cx' cy'.
        (sax, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sax', cx') \<longrightarrow>
        (say, unliftC c) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (say', cy') \<longrightarrow>
        cx' = cy') ) \<Longrightarrow>
    \<comment> \<open> conclude a step can be made \<close>
    secure R F G I q n c s\<close>


theorem safety_implies_security:
  fixes n :: nat
    and cc :: \<open>('l::pre_perm_alg, 's) rgstate comm\<close>
    and ss :: \<open>('l, 's) rgstate\<close>
    and F I q :: \<open>('l, 's) rgstate \<Rightarrow> bool\<close>
    and R G :: \<open>'s \<times> 's \<Rightarrow> 's \<times> 's \<Rightarrow> bool\<close>
  assumes
    \<open>safe R F G I q n cc s\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> quasireflp_atoms cc\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> quasirefl_blocking_doloops_head_atoms cc\<close>
    \<open>I \<squnion> I \<^emph>\<and> F \<le> all_sec_determ (unliftC cc) \<circ> exch4\<close>
  shows
    \<open>secure R F G I q n cc s\<close>
  using assms
proof (induct rule: safe.induct)
  case (safeI cc s n)

  obtain ls lsx lsy ss ssx ssy where s_eq:
    \<open>s = (ls, ss)\<close>
    \<open>ls = (lsx, lsy)\<close>
    \<open>ss = (ssx, ssy)\<close>
    by (metis surjective_pairing)
  note s_eq' = s_eq(1)[simplified s_eq(2-3)]

  show ?case
  proof (rule secureI[OF s_eq(1) _ _ _ _ _ conjI])
    show \<open>cc = Skip \<longrightarrow> q s\<close>
      using safeI.hyps(1)
      by simp
  next
    show \<open>I s\<close>
      using safeI.hyps(2)
      by simp
  next
    fix n' ss'
    assume
      \<open>n = Suc n'\<close>
      \<open>R ss ss'\<close>
    then show \<open>secure R F G I q n' cc (ls, ss')\<close>
      using safeI.hyps(4) s_eq safeI.prems
      by auto
  next
    fix n' \<alpha> ls' ss' cc'
    assume assms2:
      \<open>n = Suc n'\<close>
      \<open>(s, cc) \<midarrow>\<alpha>\<rightarrow> ((ls', ss'), cc')\<close>

    have quasireflp_atoms_s: \<open>quasireflp_atoms cc s\<close>
      using safeI.prems safeI.hyps(2)
      by fastforce
    moreover then have quasireflp_atoms_s: \<open>quasireflp_head_atoms cc s\<close>
      apply (clarsimp simp add: quasireflp_atoms_def quasireflp_head_atoms_def imp_ex_conjL)
      apply (meson head_atoms_subseteq_all_atoms mset_subset_eqD)
      done
    moreover have \<open>quasirefl_blocking_doloops_head_atoms cc s\<close>
      using safeI.prems safeI.hyps(2)
      by fastforce
    moreover then have \<open>quasirefl_blocking_head_doloops_head_atoms cc s\<close>
      by (force simp add: quasirefl_blocking_doloops_head_atoms_def
          quasirefl_blocking_head_doloops_head_atoms_def imp_ex_conjL heads_subcomm_original)
    moreover have \<open>all_sec_determ (unliftC cc) ((lsx, ssx), (lsy, ssy))\<close>
      using exch4_two_apply s_eq' safeI.hyps(2) safeI.prems(3)
      by auto
    moreover then have \<open>head_sec_determ (unliftC cc) ((lsx, ssx), (lsy, ssy))\<close>
      by (simp add: all_sec_determ_implies_head_sec_determ)
    moreover obtain \<pi>\<alpha> where equiv_aopstep:
      \<open>strip_aact (snd \<pi>\<alpha>) = \<alpha>\<close>
      \<open>(s, cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((ls', ss'), cc')\<close>
      using assms2 opstep_then_aopstep
      by blast
    ultimately show
      \<open>(\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
        (\<alpha> = Tau \<longrightarrow> ls' =  ls) \<and>
        secure R F G I q n' cc' (ls', ss')\<close>
      using s_eq assms2 safeI.prems
      apply -
        (** forward reasoning *)
      apply (frule doublest_step_then_singlest_unliftC_step)
          apply force
         apply (simp add: exch4_def; fail)
        apply blast
       apply blast
      apply (frule safeI.hyps(5), force)
      (** solve the goal *)
      apply (clarsimp simp add: leq_exch4_shunt simp del: sup_apply comp_apply sup.bounded_iff)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (blast dest: aopstep_preserves_quasireflp_atoms)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (blast dest: aopstep_preserves_quasirefl_blocking_doloops_head_atoms)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (blast dest: aopstep_preserves_all_sec_determ)
      apply blast
      done
  next
    fix n' f \<alpha> lsf' ss' cc'
    assume assms2:
      \<open>n = Suc n'\<close>
      \<open>F (f, ss)\<close>
      \<open>ls ## f\<close>
      \<open>((ls + f, ss), cc) \<midarrow>\<alpha>\<rightarrow> ((lsf', ss'), cc')\<close>

    have \<open>quasireflp_atoms cc (ls + f, ss)\<close>
      using safeI.prems safeI.hyps(2) assms2(2,3) s_eq(1)
      by (metis sepconj_conjI sup.order_iff sup1I2)
    moreover then have \<open>quasireflp_head_atoms cc (ls + f, ss)\<close>
      apply (clarsimp simp add: quasireflp_atoms_def quasireflp_head_atoms_def imp_ex_conjL)
      apply (meson head_atoms_subseteq_all_atoms mset_subset_eqD)
      done
    moreover have \<open>quasirefl_blocking_doloops_head_atoms cc (ls + f, ss)\<close>
      using safeI.prems safeI.hyps(2) assms2(2,3) s_eq(1)
      by (meson predicate1D sepconj_conjI sup.boundedE) 
    moreover then have \<open>quasirefl_blocking_head_doloops_head_atoms cc (ls + f, ss)\<close>
      by (force simp add: quasirefl_blocking_doloops_head_atoms_def
          quasirefl_blocking_head_doloops_head_atoms_def imp_ex_conjL heads_subcomm_original)
    moreover have \<open>all_sec_determ (unliftC cc) ((lsx + fst f, ssx), (lsy + snd f, ssy))\<close>
      using exch4_two_apply s_eq safeI.hyps(2) safeI.prems(3) assms2(2,3)
      by (clarsimp simp add: le_fun_def all_conj_distrib sepconj_conjI)
    moreover then have \<open>head_sec_determ (unliftC cc) ((lsx + fst f, ssx), (lsy + snd f, ssy))\<close>
      by (simp add: all_sec_determ_implies_head_sec_determ)
    moreover obtain \<pi>\<alpha> where equiv_aopstep:
      \<open>strip_aact (snd \<pi>\<alpha>) = \<alpha>\<close>
      \<open>((ls + f, ss), cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a ((lsf', ss'), cc')\<close>
      using assms2 opstep_then_aopstep
      by fastforce
    ultimately show
      \<open>(\<alpha> \<noteq> Tau \<longrightarrow> G ss ss') \<and>
       (\<exists>ls'.
          ls' ## f \<and> lsf' = ls' + f \<and> 
          (\<alpha> = Tau \<longrightarrow> ls' = ls) \<and>
          secure R F G I q n' cc' (ls', ss'))\<close>
      using safeI.prems s_eq assms2
      (** forward reasoning *)
      apply (clarsimp simp del: sup_apply comp_apply sup.bounded_iff)
      apply (frule doublest_step_then_singlest_unliftC_step)
          apply force
         apply (simp add: exch4_def; fail)
        apply blast
       apply blast
      apply (frule safeI.hyps(6)[where fs=f])
         apply (clarsimp simp del: sup_apply comp_apply sup.bounded_iff)
         apply (simp; fail)
        apply force
       apply force
      apply (clarsimp simp add: leq_exch4_shunt simp del: sup_apply comp_apply sup.bounded_iff)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (meson aopstep_preserves_quasireflp_atoms order.trans; fail)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (meson aopstep_preserves_quasirefl_blocking_doloops_head_atoms order.trans; fail)
      apply (drule mp[of \<open>_ \<le> _\<close>])
       apply (meson aopstep_preserves_all_sec_determ order.trans)
      apply blast
      done
  next
    fix n' \<pi>\<alpha> sa sax say sa' cc'
    assume assms2:
      \<open>n = Suc n'\<close>
      \<open>sa = s \<or> (\<exists>f. F (f, ss) \<and> ls ## f \<and> sa = (ls + f, ss))\<close>
      \<open>exch4 sa = (sax, say)\<close>

    have \<open>quasireflp_atoms cc sa\<close>
      using safeI.prems safeI.hyps(2) assms2(2,3) s_eq(1)
      by (metis le_sup_iff sepconj_conjI sup.order_iff sup1I2)
    moreover then have \<open>quasireflp_head_atoms cc sa\<close>
      apply (clarsimp simp add: quasireflp_atoms_def quasireflp_head_atoms_def imp_ex_conjL)
      apply (meson head_atoms_subseteq_all_atoms mset_subset_eqD)
      done
    moreover have \<open>quasirefl_blocking_doloops_head_atoms cc sa\<close>
      using safeI.prems safeI.hyps(2) assms2(2,3) s_eq(1)
      by (meson predicate1D sepconj_conjI sup.boundedE) 
    moreover then have \<open>quasirefl_blocking_head_doloops_head_atoms cc sa\<close>
      by (force simp add: quasirefl_blocking_doloops_head_atoms_def
          quasirefl_blocking_head_doloops_head_atoms_def imp_ex_conjL heads_subcomm_original)
    ultimately show
      \<open>\<forall>sa' cc' sax' say'.
        (sa, cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sa', cc') \<longrightarrow>
        exch4 sa' = (sax', say') \<longrightarrow>
        (sax, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sax', unliftC cc') \<and>
        (say, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (say', unliftC cc')\<close>
      using assms2(3)
      by (force dest: doublest_step_then_singlest_unliftC_step)

    have \<open>all_sec_determ (unliftC cc) (sax, say)\<close>
      using s_eq safeI.hyps(2) safeI.prems(3) assms2(2,3)
      by (metis (no_types, lifting) comp_def predicate1D sepconj_conjI sup.boundedE)
    then have \<open>head_sec_determ (unliftC cc) (sax, say)\<close>
      by (simp add: all_sec_determ_implies_head_sec_determ)
    then show
      \<open>\<forall>sax' say' cx' cy'.
        (sax, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (sax', cx') \<longrightarrow>
        (say, unliftC cc) \<midarrow>\<pi>\<alpha>\<rightarrow>\<^sub>a (say', cy') \<longrightarrow>
        cx' = cy'\<close>
      by (blast dest: same_initcomm_and_aact_then_same_fincomm)
  qed
qed

end
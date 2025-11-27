theory SecRGSep
  imports "../RGLogic"
begin

definition rel_compl :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)\<close> (\<open>_\<^sup>c\<close> [86] 85) where
  \<open>a\<^sup>c \<equiv> (\<lambda>x y. a y x)\<close>

lemma rel_compl_rel_comp_distrib:
  \<open>(a OO b)\<^sup>c = (b\<^sup>c OO a\<^sup>c)\<close>
  by (force simp add: rel_compl_def relcompp_apply fun_eq_iff)

definition
  \<open>LL r \<equiv> \<lambda>(x,_). (\<exists>z. r (x,z))\<close>

lemma LL_apply:
  \<open>LL a (x,y) = (\<exists>z. a (x,z))\<close>
  by (simp add: LL_def)

definition
  \<open>RR r \<equiv> \<lambda>(_,y). (\<exists>z. r (z,y))\<close>

lemma RR_apply:
  \<open>RR a (x,y) = (\<exists>z. a (z,y))\<close>
  by (simp add: RR_def)



definition box (\<open>\<^bold>\<box>\<close>) where
  \<open>box p \<equiv> \<lambda>(x,y). p (x,y) \<and> p (x,x) \<and> p (y,y)\<close>


syntax
  "_twoPredLiftBasic"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"  ("\<lblot> _ \<rblot>" [0] 999)
  "_twoPredLiftDouble"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar> _ \<rblot>" [0,0] 998)
  "_twoPredLiftL"  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<lblot> _ \<bar>" [0] 997)
  "_twoPredLiftR"  :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)"  ("\<bar> _ \<rblot>" [0] 997)

translations
  "_twoPredLiftBasic p" \<rightharpoonup> "(CONST pred_Times) p p"
  "_twoPredLiftDouble p q" \<rightleftharpoons> "(CONST pred_Times) p q"
  "_twoPredLiftL p" \<rightharpoonup> "(CONST pred_Times) p \<top>"
  "_twoPredLiftR q" \<rightharpoonup> "(CONST pred_Times) \<top> q"


definition
  \<open>major \<equiv> \<lambda>((x,x'), (y,y')). (x, y)\<close>

definition
  \<open>minor \<equiv> \<lambda>((x,x'), (y,y')). (x', y')\<close>

definition
  \<open>exch4 \<equiv> \<lambda>((a,b),(c,d)). ((a,c),(b,d))\<close>

definition
  \<open>rel_exch4 r \<equiv> \<lambda>a b. r (exch4 a) (exch4 b)\<close>


type_synonym ('a,'b) secstate = \<open>(('a \<times> 'a) \<times> ('b \<times> 'b))\<close>


definition sec_agree
  :: \<open>('a \<Rightarrow> 'v) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bbbA>\<close>)
  where
    \<open>\<bbbA> vf \<equiv> (\<lambda>(ab,ab'). vf ab = vf ab')\<close>

lemma conj_agree_iff:
  \<open>\<bbbA> v1 \<sqinter> \<bbbA> v2 = \<bbbA> (\<lambda>x. (v1 x, v2 x))\<close>
  by (simp add: sec_agree_def exch4_def comp_def fun_eq_iff split: prod.splits)

lemma eqrel_times_eqrel_eq[simp]:
  \<open>((=) \<times>\<^sub>R (=)) = (=)\<close>
  by (force simp add: rel_Times_def)


section \<open> relational logic  \<close>

subsection \<open> refl \<close>

lemma sepconj_reflp[intro]:
  \<open>reflp (curry p) \<Longrightarrow> reflp (curry q) \<Longrightarrow> reflp (curry (p \<^emph> q))\<close>
  nitpick[card 'a=1]
  oops

lemma conj_reflp[intro]:
  \<open>reflp (curry p) \<Longrightarrow> reflp (curry q) \<Longrightarrow> reflp (curry (p \<sqinter> q))\<close>
  by (simp add: reflp_on_def)

lemma disj_reflpL[intro]:
  \<open>reflp (curry p) \<Longrightarrow> reflp (curry (p \<squnion> q))\<close>
  by (simp add: reflp_on_def)

lemma disj_reflpR[intro]:
  \<open>reflp (curry q) \<Longrightarrow> reflp (curry (p \<squnion> q))\<close>
  by (simp add: reflp_on_def)

lemma implies_reflp[intro]:
  \<open>reflp (curry q) \<Longrightarrow> reflp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: reflp_on_def)

lemma neg_reflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry (- p))\<close>
  apply (clarsimp simp add: reflp_on_def prepost_state_def' curry_def split: prod.splits)
  nitpick[card 'a=2]
  oops

lemma both_quasireflp[intro]:
  \<open>quasireflp (curry (\<lblot> p \<rblot>))\<close>
  unfolding pred_Times_def reflp_on_def prepost_state_def' curry_def
  by blast

lemma agree_quasireflp[intro]:
  \<open>quasireflp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def reflp_on_def prepost_state_def' curry_def
  by blast

lemma reflp_top[intro]:
  \<open>reflp (curry \<top>)\<close>
  by (simp add: curry_def prepost_state_def' reflp_on_def)


subsection \<open> quasirefl \<close>

lemma sepconj_quasireflp[intro]:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<^emph> q))\<close>
  apply (clarsimp simp add: reflp_on_def symp_def prepost_state_def' sepconj_def)
  apply (intro conjI)
   apply (clarsimp, blast)+
  done

lemma conj_quasireflp[intro]:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<sqinter> q))\<close>
  by (simp add: reflp_on_def prepost_state_def', blast)

lemma disj_quasireflp[intro]:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<squnion> q))\<close>
  by (simp add: reflp_on_def prepost_state_def', blast)

lemma implies_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<leadsto> q))\<close>
  apply (clarsimp simp add: prepost_state_def' reflp_on_def curry_def split: prod.splits)
  nitpick[card 'a=2]
  oops

lemma neg_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry (- p))\<close>
  apply (clarsimp simp add: reflp_on_def prepost_state_def' curry_def split: prod.splits)
  nitpick[card 'a=2]
  oops

lemma both_quasireflp[intro]:
  \<open>quasireflp (curry (\<lblot> p \<rblot>))\<close>
  unfolding pred_Times_def reflp_on_def prepost_state_def' curry_def
  by blast

lemma agree_quasireflp[intro]:
  \<open>quasireflp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def reflp_on_def prepost_state_def' curry_def
  by blast

lemma quasireflp_top[intro]:
  \<open>quasireflp (curry \<top>)\<close>
  by (simp add: curry_def prepost_state_def' reflp_on_def)

lemma quasireflp_bot[intro]:
  \<open>quasireflp (curry \<bottom>)\<close>
  by (simp add: curry_def prepost_state_def' reflp_on_def)


subsection \<open> symmetric \<close>

lemma sepconj_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<^emph> q))\<close>
  by (simp add: symp_def sepconj_def prepost_state_def' curry_def, blast)

lemma conj_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<sqinter> q))\<close>
  by (simp add: symp_def)

lemma disj_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<squnion> q))\<close>
  by (simp add: symp_def)

lemma implies_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma not_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry (- p))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma both_symp[intro!]:
  \<open>symp (curry (\<lblot> p \<rblot>))\<close>
  unfolding pred_Times_def symp_def prepost_state_def' curry_def
  by blast

lemma agree_symp[intro!]:
  \<open>symp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def symp_def curry_def
  by force


subsection \<open> trans \<close>

lemma sepconj_symp:
  \<open>transp (curry p) \<Longrightarrow> transp (curry q) \<Longrightarrow> transp (curry (p \<^emph> q))\<close>
  nitpick[card 'a=2]
  oops

lemma conj_transp:
  \<open>transp (curry p) \<Longrightarrow> transp (curry q) \<Longrightarrow> transp (curry (p \<sqinter> q))\<close>
  by (simp add: transp_def, blast)

lemma disj_transp:
  \<open>transp (curry p) \<Longrightarrow> transp (curry q) \<Longrightarrow> transp (curry (p \<squnion> q))\<close>
  nitpick[card 'a=2]
  oops

lemma implies_transp:
  \<open>transp (curry p) \<Longrightarrow> transp (curry q) \<Longrightarrow> transp (curry (p \<leadsto> q))\<close>
  nitpick[card 'a=2]
  oops

lemma not_transp:
  \<open>transp (curry p) \<Longrightarrow> transp (curry (- p))\<close>
  nitpick[card 'a=2]
  oops

lemma both_transp:
  \<open>transp (curry (\<lblot> p \<rblot>))\<close>
  unfolding pred_Times_def transp_def prepost_state_def' curry_def
  by blast

lemma agree_transp:
  \<open>transp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def transp_def curry_def
  by force


subsection \<open> quasiequiv \<close>

definition \<open>quasiequivp \<equiv> quasireflp \<sqinter> symp \<sqinter> transp\<close>

lemma conj_quasiequivp:
  \<open>quasiequivp (curry p) \<Longrightarrow> quasiequivp (curry q) \<Longrightarrow> quasiequivp (curry (p \<sqinter> q))\<close>
  unfolding quasiequivp_def
  by (clarsimp simp add: conj_quasireflp conj_symp conj_transp)

lemma not_transp:
  \<open>quasiequivp (curry p) \<Longrightarrow> quasiequivp (curry (\<^bold>\<box>(-p)))\<close>
  unfolding quasiequivp_def
  apply clarsimp
  apply (intro conjI)
    apply (clarsimp simp add: reflp_on_def box_def prepost_state_def', blast)
   apply (force simp add: symp_on_def box_def)
  apply (simp add: transp_on_def box_def, blast)
  done

lemma both_quasiequivp:
  \<open>quasiequivp (curry (\<lblot> p \<rblot>))\<close>
  unfolding quasiequivp_def
  by (simp add: both_quasireflp both_symp both_transp)

lemma agree_quasiequivp:
  \<open>quasiequivp (curry (\<bbbA> p))\<close>
  unfolding quasiequivp_def
  by (simp add: agree_quasireflp agree_symp agree_transp)


subsection \<open> completions \<close>

lemma quasirefl_LL_apply[simp]:
  \<open>quasireflp (curry p) \<Longrightarrow> LL p (x,y) = p (x,x)\<close>
  by (simp add: LL_def reflp_on_def prepost_state_def' curry_def, blast)

lemma quasirefl_RR_apply[simp]:
  \<open>quasireflp (curry p) \<Longrightarrow> RR p (x,y) = p (y,y)\<close>
  by (simp add: RR_def reflp_on_def prepost_state_def' curry_def, blast)


lemma quasirefl_LL_def:
  \<open>quasireflp (curry p) \<Longrightarrow> LL p = (\<lambda>(x,y). p (x,x))\<close>
  by (simp add: LL_def reflp_on_def prepost_state_def' curry_def, blast)

lemma quasirefl_RR_def:
  \<open>quasireflp (curry p) \<Longrightarrow> RR p = (\<lambda>(x,y). p (y,y))\<close>
  by (simp add: RR_def reflp_on_def prepost_state_def' curry_def, blast)

definition qr_cl (\<open>\<diamond>\<^sub>=\<close>) where
  \<open>\<diamond>\<^sub>= p \<equiv> \<lambda>(x,y). p (x,y) \<or> (\<exists>z. p (x,z)) \<and> x = y \<or> (\<exists>z. p (z,y)) \<and> x = y\<close>

lemma qr_cl_quasireflexive[intro!]:
  \<open>quasireflp (curry (\<diamond>\<^sub>= p))\<close>
  by (force simp add: qr_cl_def curry_def prepost_state_def' reflp_on_def)

lemma qr_cl_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry (\<diamond>\<^sub>= p))\<close>
  by (force simp add: qr_cl_def symp_def curry_def)


definition qr_neg :: \<open>('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool)\<close> (\<open>-\<^sub>= _\<close> [81] 80) where
  \<open>-\<^sub>= p \<equiv> \<diamond>\<^sub>= (- p)\<close>

lemma qr_neg_quasireflp[intro!]:
  \<open>quasireflp (curry (-\<^sub>= p))\<close>
  by (force simp add: qr_neg_def)

lemma qr_neg_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry (-\<^sub>= p))\<close>
  by (force simp add: qr_neg_def)

lemma qr_logic_exmiddle:
  \<open>p \<squnion> -\<^sub>= p = \<top>\<close>
  by (simp add: qr_neg_def qr_cl_def fun_eq_iff)

lemma qr_neg_excluded_middle_counterex:
  fixes p :: \<open>'a \<times> 'a \<Rightarrow> bool\<close>
  shows \<open>np = -\<^sub>= p \<Longrightarrow> p \<sqinter> np = \<bottom>\<close>
  nitpick[card 'a=2]
  oops

lemma qr_neg_weak_excluded_middle_counterex:
  \<open>quasireflp (curry p) \<Longrightarrow> -\<^sub>= p \<sqinter> -\<^sub>= (-\<^sub>= p) = \<bottom>\<close>
  nitpick[card 'a=2]
  oops

lemma qr_neg_antimonotone:
  \<open>p \<le> q \<Longrightarrow> -\<^sub>= q \<le> -\<^sub>= p\<close>
  by (force simp add: qr_neg_def qr_cl_def)

lemma qr_neg_top_eq[simp]:
  \<open>-\<^sub>= \<top> = \<bottom>\<close>
  by (simp add: qr_neg_def qr_cl_def fun_eq_iff)

lemma qr_neg_bot_eq[simp]:
  \<open>-\<^sub>= \<bottom> = \<top>\<close>
  by (simp add: qr_neg_def qr_cl_def fun_eq_iff)

lemma semi_qrneg_sup:
  \<open>-\<^sub>= (p \<squnion> q) \<le> -\<^sub>= p \<sqinter> -\<^sub>= q\<close>
  by (force simp add: qr_neg_def qr_cl_def fun_eq_iff)

lemma qrneg_inf:
  \<open>-\<^sub>= (p \<sqinter> q) = -\<^sub>= p \<squnion> -\<^sub>= q\<close>
  by (force simp add: qr_neg_def qr_cl_def fun_eq_iff)

lemma qrneg_nnnn2nn[simp]:
  \<open>-\<^sub>= (-\<^sub>= (-\<^sub>= (-\<^sub>= p))) = -\<^sub>= (-\<^sub>= p)\<close>
  apply (clarsimp simp add: qr_neg_def qr_cl_def fun_eq_iff)
  apply (intro iffI)
   apply (elim disjE; blast)
  apply (elim disjE)
    apply blast
   apply (clarsimp, metis (full_types))
  apply blast
  done

lemma double_qrneg_sup:
  \<open>-\<^sub>= (-\<^sub>= (p \<squnion> q)) = -\<^sub>= (-\<^sub>= p) \<squnion> -\<^sub>= (-\<^sub>= q)\<close>
  apply (clarsimp simp add: qr_neg_def qr_cl_def fun_eq_iff)
  apply (intro iffI)
   apply (elim disjE; metis (full_types))
  apply (elim disjE; metis (full_types))
  done

lemma semi_double_qrneg_inf:
  \<open>-\<^sub>= (-\<^sub>= (p \<sqinter> q)) \<le> -\<^sub>= (-\<^sub>= p) \<sqinter> -\<^sub>= (-\<^sub>= q)\<close>
  by (clarsimp simp add: qr_neg_def qr_cl_def le_fun_def, blast)

lemma opposite_double_qrneg_inf_counterex:
  \<open>-\<^sub>= (-\<^sub>= (p \<sqinter> q)) \<ge> -\<^sub>= (-\<^sub>= p) \<sqinter> -\<^sub>= (-\<^sub>= q)\<close>
  nitpick[card 'a=2]
  oops

lemma semi_triple_qrneg_inf:
  \<open>-\<^sub>= (-\<^sub>= (-\<^sub>= (p \<sqinter> q))) = -\<^sub>= (-\<^sub>= (-\<^sub>= p)) \<squnion> -\<^sub>= (-\<^sub>= (-\<^sub>= q))\<close>
  by (simp add: qrneg_inf double_qrneg_sup)


lemma qr_neg_disj_syll:
  \<open>(-\<^sub>= p) \<sqinter> (p \<squnion> q) \<le> q\<close>
  nitpick[card 'a=2]
  oops

lemma qr_neg_strong_mp:
  \<open>p \<sqinter> (-\<^sub>= p \<squnion> q) \<le> q\<close>
  nitpick[card 'a=2]
  oops

definition qr_impl :: \<open>('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'a \<Rightarrow> bool)\<close>
  (infixr \<open>\<leadsto>\<^sub>=\<close> 60) where
    \<open>p \<leadsto>\<^sub>= q \<equiv> \<diamond>\<^sub>= (p \<leadsto> q)\<close>


subsubsection \<open> Lemmas \<close>

lemma qr_neg_eq_lr_impl_bot:
  \<open>-\<^sub>= p = p \<leadsto>\<^sub>= \<bottom>\<close>
  by (simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)

lemma lr_impl_refl:
  \<open>(p \<leadsto>\<^sub>= p) = \<top>\<close>
  by (simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)

lemma lr_impl_weaken:
  \<open>q \<sqinter> (p \<leadsto>\<^sub>= q) = q\<close>
  by (force simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)
  
lemma lr_impl_mp_eqn:
  \<open>p \<sqinter> (p \<leadsto>\<^sub>= q) = p \<sqinter> q\<close>
  nitpick[card 'a=2]
  oops

lemma quasireflp_then_lr_impl_right_conj_distrib:
  \<open>p \<leadsto>\<^sub>= q1 \<sqinter> q2 = (p \<leadsto>\<^sub>= q1) \<sqinter> (p \<leadsto>\<^sub>= q2)\<close>
  nitpick[card 'a=2]
  oops

lemma qrefl_then_lr_impl_impl_subst:
  \<open>p \<leadsto>\<^sub>= q \<leadsto>\<^sub>= r \<le> (p \<leadsto>\<^sub>= q) \<leadsto>\<^sub>= p \<leadsto>\<^sub>= r\<close>
  nitpick[card 'a=2]
  oops

lemma qrefl_then_lr_impl_id_embellish:
  \<open>p \<le> q \<leadsto>\<^sub>= p \<sqinter> q\<close>
  by (force simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)

lemma qrefl_then_lr_impl_galois:
  \<open>p \<le> q \<leadsto>\<^sub>= r \<longleftrightarrow> p \<sqinter> q \<le> r\<close>
  nitpick[card 'a=2]
  oops

lemma lr_impl_disj_left:
  \<open>(p \<leadsto>\<^sub>= r) \<sqinter> (q \<leadsto>\<^sub>= r) \<le> p \<squnion> q \<leadsto>\<^sub>= r\<close>
  nitpick[card 'a=2]
  oops

lemma quasimpl_disj_implies_qrimpl:
  \<open>-\<^sub>= p \<squnion> q \<le> p \<leadsto>\<^sub>= q\<close>
  by (force simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)

lemma quasimpl_conj_implies_qrimpl:
  \<open>-\<^sub>= (p \<sqinter> -\<^sub>= q) \<le> p \<leadsto>\<^sub>= q\<close>
  by (force simp add: fun_eq_iff qr_impl_def qr_neg_def qr_cl_def)

lemma qr_quasimpl_conj_implies_qr_quasimpl_disj_counterex:
  \<open>-\<^sub>= (p \<sqinter> -\<^sub>= q) \<ge> -\<^sub>= p \<squnion> q\<close>
  nitpick[card 'a=2]
  oops

lemma qr_quasimpl_disj_implies_qr_quasimpl_conj_counterex:
  \<open>-\<^sub>= (p \<sqinter> -\<^sub>= q) \<le> -\<^sub>= p \<squnion> q\<close>
  nitpick[card 'a=2]
  oops

lemma qrimpl_modus_ponens:
  \<open>(p \<leadsto>\<^sub>= q) \<sqinter> p \<le> q\<close>
  nitpick[card 'a=2]
  oops

lemma qrefl_then_quasireflp[intro]:
  \<open>quasireflp (curry (p \<leadsto>\<^sub>= q))\<close>
  by (force simp add: qr_impl_def)

lemma lr_impl_symp[intro]:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto>\<^sub>= q))\<close>
  by (simp add: qr_impl_def symp_def qr_cl_def, blast)

lemma lift_impl_eq:
  \<open>\<lblot> p \<leadsto> q \<rblot> = ((p \<leadsto> q) \<circ> fst) \<sqinter> ((p \<leadsto> q) \<circ> snd)\<close>
  by (force simp add: pred_Times_def fun_eq_iff imp_conjR)

lemma agree_reflp:
  \<open>reflp (curry (\<bbbA> f))\<close>
  by (simp add: reflpI sec_agree_def)

lemma reflp_conseq_impl:
  \<open>reflp (curry q) \<Longrightarrow> reflp (curry (p \<leadsto> q))\<close>
  using reflp_on_mono by fastforce

lemma boolean_split_as_both:
  \<open>\<bbbA> p = \<lblot> p \<rblot> \<squnion> \<lblot> -p \<rblot>\<close>
  by (force simp add: pred_Times_def sec_agree_def fun_eq_iff)

lemma split_as_both:
  \<open>\<bbbA> \<oo> = (\<Squnion>v. \<lblot> ((=) v) \<circ> \<oo> \<rblot>)\<close>
  by (force simp add: pred_Times_def sec_agree_def fun_eq_iff)

(* TODO: move to await *)
lemma
  \<open>sp (rel_lift pa \<top> \<sqinter> (=)) pb = (pa \<sqinter> pb)\<close>
  by (simp add: sp_def fun_eq_iff)

lemma \<open>wssa R p = \<top> \<Longrightarrow> p = \<top>\<close>
  by (metis top.extremum_uniqueI wssa_weaker)
  









lemma twoLift_implies_box_closed:
  \<open>(\<exists>px. p = \<lblot> px \<rblot>) \<Longrightarrow> \<^bold>\<box>p = p\<close>
  unfolding box_def pred_Times_def
  by force

lemma agree_equivp:
  \<open>equivp (curry (\<bbbA> \<oo>))\<close>
  by (force simp add: equivp_def sec_agree_def fun_eq_iff)


(* S4 Rules *)
lemma modal_distribution:
  \<open>\<top> \<le> \<^bold>\<box>(p \<leadsto> q) \<leadsto> (\<^bold>\<box>p \<leadsto> \<^bold>\<box>q)\<close>
  unfolding box_def impl_def le_fun_def
  by simp

lemma modal_T:
  \<open>\<^bold>\<box>p \<le> p\<close>
  unfolding box_def impl_def le_fun_def
  by simp

lemma modal_4:
  \<open>\<^bold>\<box>p \<le> \<^bold>\<box>(\<^bold>\<box>p)\<close>
  unfolding box_def impl_def le_fun_def
  by simp

lemma intermediate_kp:
  fixes p q r :: \<open>('a \<times> 'a) \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry p)\<close>
  assumes \<open>quasireflp (curry q)\<close>
  assumes \<open>quasireflp (curry r)\<close>
  shows \<open>\<top> \<le> (-\<^sub>L\<^sub>R p \<leadsto>\<^sub>L\<^sub>R q \<squnion> r) \<leadsto>\<^sub>L\<^sub>R ((-\<^sub>L\<^sub>R p \<leadsto>\<^sub>L\<^sub>R q) \<squnion> (-\<^sub>L\<^sub>R p \<leadsto>\<^sub>L\<^sub>R r))\<close>
  using assms
  apply (subst (2) qr_implies_def, fast, fast)
  apply (subst qr_implies_def, fast, fast)+
  apply (simp add: qr_neg_def)
  apply (clarsimp simp add: le_fun_def)
  apply blast
  done

lemma intermediate_bd2:
  fixes p q r :: \<open>('a \<times> 'a) \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry p)\<close>
  assumes \<open>quasireflp (curry q)\<close>
  shows \<open>\<top> \<le> p \<squnion> (p \<leadsto>\<^sub>L\<^sub>R q \<squnion> -\<^sub>L\<^sub>R q)\<close>
  using assms
  apply (subst qr_implies_def, fast, fast)+
  apply (simp add: qr_implies_def qr_neg_def)
  apply blast
  done

lemma intermediate_bb3:
  fixes p q r :: \<open>('a \<times> 'a) \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry p)\<close>
  assumes \<open>quasireflp (curry q)\<close>
  assumes \<open>quasireflp (curry r)\<close>
  shows \<open>\<top> \<le> ((p \<leadsto>\<^sub>L\<^sub>R q \<squnion> r) \<leadsto>\<^sub>L\<^sub>R q \<squnion> r) \<sqinter> ((q \<leadsto>\<^sub>L\<^sub>R p \<squnion> r) \<leadsto>\<^sub>L\<^sub>R p \<squnion> r) \<sqinter> ((r \<leadsto>\<^sub>L\<^sub>R p \<squnion> q) \<leadsto>\<^sub>L\<^sub>R p \<squnion> q)
                \<leadsto>\<^sub>L\<^sub>R (p \<squnion> q \<squnion> r)\<close>
  using assms
  apply (subst (7) qr_implies_def, fast, fast)
  apply (subst (18) qr_implies_def, fast, fast)
  apply (subst (16) qr_implies_def, fast, fast)
  apply (subst (14) qr_implies_def, fast, fast)
  apply (subst (12) qr_implies_def, fast, fast)
  apply (subst (10) qr_implies_def, fast, fast)
  apply (subst (8) qr_implies_def, fast, fast)
  apply (subst (6) qr_implies_def, fast, fast)
  apply (subst (4) qr_implies_def, fast, fast)
  apply (subst (2) qr_implies_def, fast, fast)
  apply (subst qr_implies_def, fast, fast)+
  apply (simp add: qr_neg_def)
  apply blast
  done

lemma
  fixes p q :: \<open>('a \<times> 'a) \<Rightarrow> bool\<close>
  assumes \<open>quasireflp (curry p)\<close>
  assumes \<open>quasireflp (curry q)\<close>
  shows \<comment> \<open> neither is true \<close>
    \<open>(p \<leadsto>\<^sub>L\<^sub>R q) \<le> (-\<^sub>L\<^sub>R p \<squnion> q)\<close>
    \<open>-\<^sub>L\<^sub>R (p \<sqinter> -\<^sub>L\<^sub>R q) \<le> (p \<leadsto>\<^sub>L\<^sub>R q)\<close>
  nitpick
  oops

lemma disj_weakening:
  \<open>\<lblot> p \<rblot> \<squnion> \<lblot> q \<rblot> \<le> \<lblot> p \<squnion> q \<rblot>\<close>
  unfolding le_fun_def
  by (simp add: pred_Times_def)

lemma lift_sepconjConj_eq:
  \<open>\<lblot> p \<^emph>\<and> q \<rblot> = (\<lblot> p \<rblot> \<circ> exch4) \<^emph>\<and> (\<lblot> q \<rblot> \<circ> exch4) \<circ> exch4\<close>
  unfolding pred_Times_def sepconj_conj_def
  apply (clarsimp simp add: fun_eq_iff exch4_def split: prod.splits)
  apply (rename_tac al as bl bs)
  apply (rule iffI)
   apply blast
   apply clarsimp
  apply blast
  done

lemma
  \<open>-\<^sub>L\<^sub>R \<bbbA> f = \<bottom>\<close>
  apply (subst qr_neg_def, blast)
  apply (simp add: sec_agree_def fun_eq_iff)
  done

lemma
  \<open>-\<^sub>L\<^sub>R (\<bbbA> (\<lambda>(a,b,c). (a,b))) \<le> \<bbbA> (\<lambda>(a,b,c). a = b)\<close>
  apply (subst qr_neg_def, blast)
  apply (simp add: sec_agree_def split: prod.splits)
  apply (clarsimp simp add: sec_agree_def)
  done

section \<open> Program \<close>

abbreviation
  \<open>Output v \<equiv> Assert (\<bbbA> v \<circ> exch4)\<close>

abbreviation
  \<open>Leak v \<equiv> Await (\<bbbA> v \<circ> exch4)\<close>


section \<open> relational lifting \<close>

abbreviation(input) \<open>liftP p \<equiv> \<lblot> p \<rblot>\<close>
definition \<open>liftR r \<equiv> \<lambda>(x,x') (y,y'). r x y \<and> r x' y'\<close>

fun liftC :: \<open>('s \<Rightarrow> 'v) \<Rightarrow> 's comm \<Rightarrow> ('s \<times> 's) comm\<close> where
  \<open>liftC f Skip = Skip\<close>
| \<open>liftC f (c1 ;; c2) = liftC f c1 ;; liftC f c2\<close>
| \<open>liftC f (c1 \<parallel> c2) = liftC f c1 \<parallel> liftC f c2\<close>
| \<open>liftC f (c1 \<^bold>+ c2) = liftC f c1 \<^bold>+ liftC f c2\<close>
| \<open>liftC f (c1 \<box> c2) = liftC f c1 \<box> liftC f c2\<close>
| \<open>liftC f \<langle>p, q\<rangle> = \<langle>liftP p \<sqinter> \<bbbA> f, liftR q\<rangle>\<close>
| \<open>liftC f (DO c OD) = DO liftC f c OD\<close>


lemma tmpname:
  \<open>quasireflp (curry (liftP p))\<close>
  \<open>symp (curry (liftP p))\<close>
  \<open>transp (curry (liftP p))\<close>
  \<open>quasireflp (curry (sp (liftR r) (liftP p)))\<close>
  \<open>symp (curry (sp (liftR r) (liftP p)))\<close>
  \<open>transp (curry (sp (liftR r) (liftP p)))\<close>
  unfolding pred_Times_def liftR_def curry_def reflp_on_def prepost_state_def'
    symp_def transp_def sp_def
  by blast+

(* all of these aren't true *)
lemma tmpname2:
  \<open>quasireflp (curry (wlp (liftR r) (liftP q)))\<close>
  \<open>symp (curry (wlp (liftR r) (liftP q)))\<close>
  \<open>transp (curry (wlp (liftR r) (liftP q)))\<close>
  unfolding pred_Times_def liftR_def curry_def reflp_on_def prepost_state_def'
    symp_def transp_def wlp_def
  nitpick
  oops




(*
definition
  \<open>SAwait p \<equiv>
    \<langle>
     (\<bbbA> p \<circ> exch4),
      \<lambda>x a x'. (\<lblot> p \<rblot> \<circ> exch4) x \<and> x' = x
    \<rangle>\<close>

definition sec_atom_lift
  :: \<open>('x \<Rightarrow> bool) \<times> ('x \<Rightarrow> 'a \<Rightarrow> 'y \<Rightarrow> bool) \<Rightarrow>
        ('x \<times> 'x \<Rightarrow> bool) \<times> ('x \<times> 'x \<Rightarrow> 'a \<Rightarrow> 'y \<times> 'y \<Rightarrow> bool)\<close>
  where
  \<open>sec_atom_lift \<equiv> \<lambda>(p, q). (\<lblot> p \<rblot> \<sqinter> \<bbbA> (\<lambda>x. \<exists>a y. q x a y), \<lambda>(x1,x2) a (y1,y2). q x1 a y1 \<and> q x2 a y2)\<close>

(*
lemma
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { \<bbbA> v }
      \<langle> output v \<rangle>
      { \<top> }\<close>
*)

(*
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { p \<mapsto> \<midarrow> }
      [p] := e
      { p \<mapsto> e }\<close>

    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub>
      { \<not> (p \<mapsto> \<midarrow>) }
      [p] := e
      { X }\<close>
    ???
*)

lemma rgsat_single_leak:
  fixes p :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
    and S F :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
  assumes
    \<open>\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> (\<bbbA> v \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v \<circ> exch4)) \<^emph>\<and> f\<close>
    \<open>p \<le> S\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub> { p } Leak v { p \<sqinter> (\<bbbA> v \<circ> exch4) }\<close>
  apply (rule_tac p=p and q=\<open>p \<sqinter> (\<bbbA> v \<circ> exch4)\<close> and p'=p in rgsat_assume)
       apply (simp add: assms(1); fail)
      apply force
     apply force
    apply force
   apply force
  apply (simp add: assms(2); fail)
  done

definition emp_conj :: \<open>'a::perm_alg \<times> 'b \<Rightarrow> bool\<close> (\<open>emp\<^sub>1\<close>) where
  \<open>emp\<^sub>1 \<equiv> sepadd_unit \<circ> fst\<close>

lemma emp1_unit_sepconj_conj_left[simp]:
  fixes p :: \<open>('a::multiunit_sep_alg \<times> 'b) \<Rightarrow> bool\<close>
  shows \<open>emp\<^sub>1 \<^emph>\<and> p = p\<close>
  apply (clarsimp simp add: sepadd_unit_def sepconj_conj_def emp_conj_def fun_eq_iff)
  apply (metis disjoint_sym partial_add_commute unitof_disjoint unitof_is_unitR2)
  done

lemma frame_safe_pred_conj_helper_counterexample:
  fixes p :: \<open>('a::multiunit_sep_alg,'b) secstate \<Rightarrow> bool\<close>
    and v1 :: \<open>'a \<times> 'b \<Rightarrow> 'v1\<close>
    and v2 :: \<open>'a \<times> 'b \<Rightarrow> 'v2\<close>
  shows
    \<open>F = \<top> \<Longrightarrow>
      p = emp\<^sub>1 \<Longrightarrow>
      \<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> (\<bbbA> v2 \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v2 \<circ> exch4)) \<^emph>\<and> f \<Longrightarrow>
      \<forall>f\<le>F. ((p \<sqinter> (\<bbbA> v1 \<circ> exch4)) \<^emph>\<and> f) \<sqinter> (\<bbbA> v2 \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v1 \<circ> exch4) \<sqinter> (\<bbbA> v2 \<circ> exch4)) \<^emph>\<and> f\<close>
  apply clarsimp
  nitpick[card 'v1=2, card 'v2=2, card 'a=3, card 'b=1]
  sorry

lemma
  fixes p :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
    and v :: \<open>'a \<times> 'b \<Rightarrow> 'v\<close>
    and S F :: \<open>('a::perm_alg,'b) secstate \<Rightarrow> bool\<close>
  assumes
    \<open>\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> (\<bbbA> v1 \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v1 \<circ> exch4)) \<^emph>\<and> f\<close>
    \<open>\<forall>f\<le>F. ((p \<sqinter> (\<bbbA> v1 \<circ> exch4)) \<^emph>\<and> f) \<sqinter> (\<bbbA> v2 \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v1 \<circ> exch4) \<sqinter> (\<bbbA> v2 \<circ> exch4)) \<^emph>\<and> f\<close>
    \<open>p \<le> S\<close>
  shows
    \<open>(=), (=) \<turnstile>\<^bsub>S, F\<^esub> { p } Leak v1 ;; Leak v2 { p \<sqinter> (\<bbbA> v1 \<circ> exch4) \<sqinter> (\<bbbA> v2 \<circ> exch4) }\<close>
  apply (rule_tac ?p2.0=\<open>p \<sqinter> (\<bbbA> v1 \<circ> exch4)\<close> in rgsat_seq)
    apply (rule rgsat_single_leak)
     apply (simp add: assms(1); fail)
    apply (rule order.refl)
   apply (rule rgsat_single_leak)
    apply (simp add: assms(2); fail)
   apply (rule order.refl)
  apply (simp add: assms(3))
  done


lemma rgsat_sec_leak:
  fixes p :: \<open>('a::pre_perm_alg \<times> 'a) \<times> ('b \<times> 'b) \<Rightarrow> bool\<close>
  assumes framing:
    \<open>\<forall>f\<le>F. (p \<^emph>\<and> f) \<sqinter> (\<bbbA> v \<circ> exch4) \<le> (p \<sqinter> (\<bbbA> v \<circ> exch4)) \<^emph>\<and> f\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>p, F\<^esub> { p } Leak v { p \<sqinter> (\<bbbA> v \<circ> exch4) }\<close>
  using assms
  apply (rule_tac p=p and q=\<open>p \<sqinter> (\<bbbA> v \<circ> exch4)\<close> in rgsat_assume)
       apply (simp; fail)
      apply force
     apply force
    apply force
   apply force
  apply force
  done

lemma helper:
  fixes p :: \<open>('a::pre_perm_alg \<times> 'b) \<Rightarrow> bool\<close>
  shows
    \<open>- (\<bool> p \<circ> exch4) = (\<bool> (-p) \<circ> exch4)\<close>
  nitpick
  oops

definition
  \<open>SecIfThenElse p ct cf \<equiv> Output p ;; IfThenElse (\<bool> p \<circ> exch4) ct cf\<close>

lemma sec_if_then_else:
  fixes p :: \<open>'a::perm_alg \<times> 'b \<Rightarrow> bool\<close>
  assumes framing:
    \<open>\<forall>f\<le>F. (\<bbbA> p \<circ> exch4) \<^emph>\<and> f \<le> \<bbbA> p \<circ> exch4\<close>
  assumes p_atoms:
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub> { (\<bool> p \<circ> exch4) } ctt { q1 }\<close>
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub> { (\<bool> (-p) \<circ> exch4) } cff { q2 }\<close>
  shows
    \<open>(=), \<top> \<turnstile>\<^bsub>S, F\<^esub>
      { (\<bbbA> p \<circ> exch4) } SecIfThenElse p ctt cff { q1 \<squnion> q2 }\<close>
  unfolding SecIfThenElse_def
  apply -
  apply (rule rgsat_seq[of _ _ _ _ _ _ _ _ _ S])
    apply (rule rgsat_weaken[OF
        rgsat_assert[of _ _ \<top>]
        _ order.refl order.refl order.refl order.refl order.refl])
       apply (simp, metis framing)
      apply force
     apply force
    apply force
   apply simp
   apply (rule_tac rgsat_weaken[OF
        rgsat_if_then_else
        _ order.refl order.refl order.refl _ order.refl])


  apply (rule_tac ?g1.0=\<top> and ?g2.0=\<top> and ?q1.0=q1 and ?q2.0=q2 in rgsat_endet)
       apply (rule_tac rgsat_seq)
        apply (rule_tac p=\<open>(\<bbbA> v \<circ> exch4) p\<close> and q=\<open>(\<bool> p \<circ> exch4)\<close> and q'=\<open>(\<bool> p \<circ> exch4)\<close> in rgsat_atom)
            apply force
           apply force
          apply (clarsimp simp add: sec_both_def sec_agree_def post_state_def le_fun_def
      seclift_pred_def exch4_def pguard_def sp_def; fail)
         apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def split: prod.splits)
         apply (metis assms(1))
        apply force
       apply (metis assms(3))
      apply (rule_tac rgsat_seq)
       apply (rule_tac p=\<open>(\<bbbA> v \<circ> exch4) p\<close> and q=\<open>(\<bool> v \<circ> exch4) (-p)\<close> and q'=\<open>(\<bool> v \<circ> exch4) (-p)\<close> in rgsat_atom)
           apply force
          apply force
         apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def sec_agree_def split: prod.splits;
      fail)
        apply (clarsimp simp add: sp_def leakL_def rel_exch4_def exch4_def
      le_fun_def sepconj_conj_def sec_both_def sec_agree_def split: prod.splits)
        apply (metis p_framing(2))
       apply force
      apply (metis assms(4))
     apply force
    apply force
   apply force
  apply force
  done
*)

end
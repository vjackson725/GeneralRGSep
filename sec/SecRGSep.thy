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

lemma LL_apply[simp]:
  \<open>LL a (x,y) = (\<exists>z. a (x,z))\<close>
  by (simp add: LL_def)

definition
  \<open>RR r \<equiv> \<lambda>(_,y). (\<exists>z. r (z,y))\<close>

lemma RR_apply[simp]:
  \<open>RR a (x,y) = (\<exists>z. a (z,y))\<close>
  by (simp add: RR_def)



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


definition sec_both
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool\<close> (\<open>\<bool>\<close>)
  where
    \<open>\<bool> p \<equiv> (\<lambda>(ab,ab'). p ab \<and> p ab')\<close>

lemma sec_both_conj_distrib:
  \<open>\<bool> p \<sqinter> \<bool> q = \<bool> (p \<sqinter> q)\<close>
  by (force simp add: sec_both_def exch4_def fun_eq_iff)

lemma sec_both_disj_semidistrib:
  \<open>\<bool> p \<squnion> \<bool> q \<le> \<bool> (p \<squnion> q)\<close>
  by (force simp add: sec_both_def exch4_def fun_eq_iff)


section \<open> relational logic  \<close>


subsection \<open> quasirefl \<close>

lemma sepconj_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<^emph> q))\<close>
  apply (clarsimp simp add: reflp_on_def symp_def prepost_state_def' sepconj_def)
  apply (intro conjI)
   apply (clarsimp, blast)+
  done

lemma conj_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow> quasireflp (curry (p \<sqinter> q))\<close>
  by (simp add: reflp_on_def prepost_state_def', blast)

lemma disj_quasireflp:
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

lemma both_quasireflp:
  \<open>quasireflp (curry (\<bool> p))\<close>
  unfolding sec_both_def reflp_on_def prepost_state_def' curry_def
  by blast

lemma agree_quasireflp:
  \<open>quasireflp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def reflp_on_def prepost_state_def' curry_def
  by blast

subsection \<open> symmetric \<close>

lemma sepconj_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<^emph> q))\<close>
  by (simp add: symp_def sepconj_def prepost_state_def' curry_def, blast)

lemma conj_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<sqinter> q))\<close>
  by (simp add: symp_def sepconj_def)

lemma disj_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<squnion> q))\<close>
  by (simp add: symp_def sepconj_def)

lemma implies_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto> q))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma not_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry (- p))\<close>
  by (clarsimp simp add: symp_def sepconj_def)

lemma both_symp:
  \<open>symp (curry (\<bool> p))\<close>
  unfolding sec_both_def symp_def prepost_state_def' curry_def
  by blast

lemma agree_symp:
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

lemma disj_symp:
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
  \<open>transp (curry (\<bool> p))\<close>
  unfolding sec_both_def transp_def prepost_state_def' curry_def
  by blast

lemma agree_transp:
  \<open>transp (curry (\<bbbA> p))\<close>
  unfolding sec_agree_def transp_def curry_def
  by force


subsection \<open> completions \<close>

lemma quasirefl_LL_apply[simp]:
  \<open>quasireflp (curry p) \<Longrightarrow> LL p (x,y) = p (x,x)\<close>
  by (simp add: LL_def reflp_on_def prepost_state_def' curry_def, blast)

lemma quasirefl_RR_apply[simp]:
  \<open>quasireflp (curry p) \<Longrightarrow> RR p (x,y) = p (y,y)\<close>
  by (simp add: RR_def reflp_on_def prepost_state_def' curry_def, blast)


definition lr_neg :: \<open>('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>-\<^sub>L\<^sub>R _\<close> [81] 80) where
  \<open>-\<^sub>L\<^sub>R p \<equiv> - p \<sqinter> - LL p \<sqinter> - RR p\<close>



lemma lr_neg_apply[simp]:
  \<open>(-\<^sub>L\<^sub>R p) (x,y) = (- p \<sqinter> - LL p \<sqinter> - RR p) (x,y)\<close>
  by (simp add: lr_neg_def)

lemma lr_neg_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry (-\<^sub>L\<^sub>R p))\<close>
  unfolding lr_neg_def reflp_on_def curry_def prepost_state_def'
  by (simp, blast)

lemma lr_neg_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry (-\<^sub>L\<^sub>R p))\<close>
  unfolding lr_neg_def symp_def curry_def
  by (simp, blast)


lemma noncontra_lr_neg:
  \<open>p \<sqinter> -\<^sub>L\<^sub>R p = \<bottom>\<close>
  by (simp add: lr_neg_def fun_eq_iff)

lemma lr_neg_excluded_middle_counterex:
  \<open>quasireflp (curry p) \<Longrightarrow> p \<squnion> -\<^sub>L\<^sub>R p = \<top>\<close>
  nitpick[card 'a=2]
  oops

lemma lr_neg_weak_excluded_middle_counterex:
  \<open>quasireflp (curry p) \<Longrightarrow> -\<^sub>L\<^sub>R p \<squnion> -\<^sub>L\<^sub>R(-\<^sub>L\<^sub>Rp) = \<top>\<close>
  nitpick[card 'a=2]
  oops

lemma lr_neg_order_reversing:
  \<open>p \<le> q \<Longrightarrow> -\<^sub>L\<^sub>R q \<le> -\<^sub>L\<^sub>R p\<close>
  by (force simp add: lr_neg_def)

lemma lr_neg_top_eq[simp]:
  \<open>-\<^sub>L\<^sub>R \<top> = \<bottom>\<close>
  by force

lemma lr_neg_bot_eq[simp]:
  \<open>-\<^sub>L\<^sub>R \<bottom> = \<top>\<close>
  by force

lemma lr_neg_de_Morgan_disj:
  \<open>-\<^sub>L\<^sub>R p \<sqinter> -\<^sub>L\<^sub>R q = -\<^sub>L\<^sub>R (p \<squnion> q)\<close>
  by force

lemma lr_neg_semi_de_Morgan_conj:
  \<open>-\<^sub>L\<^sub>R p \<squnion> -\<^sub>L\<^sub>R q \<le> -\<^sub>L\<^sub>R (p \<sqinter> q)\<close>
  by force


lemma lr_neg_pseudo_dual[simp]:
  \<open>-\<^sub>L\<^sub>R (-\<^sub>L\<^sub>R (-\<^sub>L\<^sub>R p)) = -\<^sub>L\<^sub>R p\<close>
  by (force simp add: lr_neg_def)

lemma lr_neg_dual_counterex:
  \<open>-\<^sub>L\<^sub>R (-\<^sub>L\<^sub>R p) = p\<close>
  nitpick[card 'a=2, card 'b=1]
  oops

lemma double_lr_neg_conj_distrib:
  \<open>quasireflp (curry p) \<Longrightarrow>
    quasireflp (curry q) \<Longrightarrow>
    -\<^sub>L\<^sub>R(-\<^sub>L\<^sub>R(p \<sqinter> q)) = -\<^sub>L\<^sub>R(-\<^sub>L\<^sub>Rp) \<sqinter> -\<^sub>L\<^sub>R(-\<^sub>L\<^sub>Rq)\<close>
  apply (clarsimp simp add: lr_neg_def reflp_on_def curry_def prepost_state_def' fun_eq_iff)
  apply (rule iffI, blast, metis)
  done

text \<open> Thus \<open>-\<^sub>L\<^sub>R\<close> is a pseudocomplement on quasi-reflexive relations. \<close>


lemma lr_neg_disj_syll:
  \<open>(-\<^sub>L\<^sub>R p) (x,y) \<Longrightarrow> (p \<squnion> q) (x,y) \<Longrightarrow> q (x,y)\<close>
  by (simp)

lemma lr_neg_strong_mp:
  \<open>p (x,y) \<Longrightarrow> (-\<^sub>L\<^sub>R p \<squnion> q) (x,y) \<Longrightarrow> q (x,y)\<close>
  by simp


definition lr_implies
  :: \<open>('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<leadsto>\<^sub>L\<^sub>R\<close> 60)
  where
  \<open>p \<leadsto>\<^sub>L\<^sub>R q \<equiv> (p \<leadsto> q) \<sqinter> (LL p \<leadsto> LL q) \<sqinter> (RR p \<leadsto> RR q)\<close>

lemma lr_implies_apply[simp]:
  \<open>(p \<leadsto>\<^sub>L\<^sub>R q) (x,y) = ((p \<leadsto> q) \<sqinter> (LL p \<leadsto> LL q) \<sqinter> (RR p \<leadsto> RR q)) (x,y)\<close>
  by (force simp add: lr_implies_def)

subsubsection \<open> Lemmas \<close>

lemma lr_neg_eq_lr_impl_bot:
  \<open>-\<^sub>L\<^sub>R p = p \<leadsto>\<^sub>L\<^sub>R \<bottom>\<close>
  by fastforce

lemma lr_impl_refl:
  \<open>(p \<leadsto>\<^sub>L\<^sub>R p) = \<top>\<close>
  by (simp add: fun_eq_iff)

lemma lr_impl_weaken:
  \<open>q \<sqinter> (p \<leadsto>\<^sub>L\<^sub>R q) = q\<close>
  by (force simp add: fun_eq_iff)

lemma lr_impl_mp_eqn:
  \<open>p \<sqinter> (p \<leadsto>\<^sub>L\<^sub>R q) = p \<sqinter> q\<close>
  by (force simp add: fun_eq_iff)

lemma quasireflp_then_lr_impl_right_conj_distrib:
  \<open>quasireflp (curry q1) \<Longrightarrow>
    quasireflp (curry q2) \<Longrightarrow>
    p \<leadsto>\<^sub>L\<^sub>R q1 \<sqinter> q2 = (p \<leadsto>\<^sub>L\<^sub>R q1) \<sqinter> (p \<leadsto>\<^sub>L\<^sub>R q2)\<close>
  by (clarsimp simp add: fun_eq_iff reflp_on_def prepost_state_def' curry_def
      all_conj_distrib, metis)

lemma qrefl_then_lr_impl_impl_subst:
  \<open>quasireflp (curry p) \<Longrightarrow>
    p \<leadsto>\<^sub>L\<^sub>R q \<leadsto>\<^sub>L\<^sub>R r \<le> (p \<leadsto>\<^sub>L\<^sub>R q) \<leadsto>\<^sub>L\<^sub>R p \<leadsto>\<^sub>L\<^sub>R r\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def' curry_def, metis)

lemma qrefl_then_lr_impl_id_embellish:
  \<open>quasireflp (curry p) \<Longrightarrow>
    quasireflp (curry q) \<Longrightarrow>
    p \<le> q \<leadsto>\<^sub>L\<^sub>R p \<sqinter> q\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def' curry_def, metis)

lemma qrefl_then_lr_impl_galois:
  \<open>quasireflp (curry p) \<Longrightarrow>
    quasireflp (curry q) \<Longrightarrow>
    p \<le> q \<leadsto>\<^sub>L\<^sub>R r \<longleftrightarrow> p \<sqinter> q \<le> r\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def' curry_def le_fun_def, blast)

lemma lr_impl_disj_left:
  \<open>(p \<leadsto>\<^sub>L\<^sub>R r) \<sqinter> (q \<leadsto>\<^sub>L\<^sub>R r) \<le> p \<squnion> q \<leadsto>\<^sub>L\<^sub>R r\<close>
  by (clarsimp simp add: reflp_on_def prepost_state_def' curry_def, metis)


lemma lr_impl_then_disj_qimpl:
  \<open>-\<^sub>L\<^sub>R p \<squnion> q \<le> p \<leadsto>\<^sub>L\<^sub>R q\<close>
  by (force simp add: le_fun_def)

lemma lr_impl_then_conj_qimpl:
  \<open>p \<leadsto>\<^sub>L\<^sub>R q \<le> -\<^sub>L\<^sub>R (p \<sqinter> -\<^sub>L\<^sub>R q)\<close>
  by (force simp add: le_fun_def)


lemma lr_impl_then_lr_impl_counterex:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow>
    \<forall>x. p (x,x) \<longrightarrow> (\<exists>y. x \<noteq> y \<and> (p (x,y) \<or> p (y,x))) \<Longrightarrow>
    \<forall>x. q (x,x) \<longrightarrow> (\<exists>y. x \<noteq> y \<and> (q (x,y) \<or> q (y,x))) \<Longrightarrow>
    A = p \<leadsto>\<^sub>L\<^sub>R q \<Longrightarrow>
    B = (-\<^sub>L\<^sub>R p \<squnion> q) \<Longrightarrow>
    A \<le> B\<close>
  nitpick[card 'a=2]
  oops

lemma lr_impl_then_lr_impl_counterex:
  \<open>quasireflp (curry p) \<Longrightarrow> quasireflp (curry q) \<Longrightarrow>
    \<forall>x. p (x,x) \<longrightarrow> (\<exists>y. x \<noteq> y \<and> (p (x,y) \<or> p (y,x))) \<Longrightarrow>
    \<forall>x. q (x,x) \<longrightarrow> (\<exists>y. x \<noteq> y \<and> (q (x,y) \<or> q (y,x))) \<Longrightarrow>
    A = -\<^sub>L\<^sub>R (p \<sqinter> -\<^sub>L\<^sub>R q) \<Longrightarrow>
    B = p \<leadsto>\<^sub>L\<^sub>R q \<Longrightarrow>
    A \<le> B\<close>
  nitpick[card 'a=2]
  oops
lemma lr_then_mp:
  \<open>(p \<leadsto>\<^sub>L\<^sub>R q) (x,y) \<Longrightarrow> p (x,y) \<Longrightarrow> q (x,y)\<close>
  by simp

lemma qrefl_then_quasireflp:
  \<open>quasireflp (curry p) \<Longrightarrow>
    quasireflp (curry q) \<Longrightarrow>
    quasireflp (curry (p \<leadsto>\<^sub>L\<^sub>R q))\<close>
  by (simp add: lr_implies_def reflp_on_def curry_def prepost_state_def', blast)

lemma qrefl_then_symp:
  \<open>symp (curry p) \<Longrightarrow> symp (curry q) \<Longrightarrow> symp (curry (p \<leadsto>\<^sub>L\<^sub>R q))\<close>
  by (simp add: lr_implies_def symp_def, blast)


section \<open> relational lifting \<close>

definition \<open>liftP p \<equiv> \<lambda>(x,x'). p x \<and> p x'\<close>
definition \<open>liftR r \<equiv> \<lambda>(x,x') (y,y'). r x y \<and> r x' y'\<close>

lemma tmpname:
  \<open>quasireflp (curry (liftP p))\<close>
  \<open>symp (curry (liftP p))\<close>
  \<open>transp (curry (liftP p))\<close>
  \<open>quasireflp (curry (sp (liftR r) (liftP p)))\<close>
  \<open>symp (curry (sp (liftR r) (liftP p)))\<close>
  \<open>transp (curry (sp (liftR r) (liftP p)))\<close>
  unfolding liftP_def liftR_def curry_def reflp_on_def prepost_state_def'
    symp_def transp_def sp_def
  by blast+

(* all of these aren't true *)
lemma tmpname2:
  \<open>quasireflp (curry (wlp (liftR r) (liftP q)))\<close>
  \<open>symp (curry (wlp (liftR r) (liftP q)))\<close>
  \<open>transp (curry (wlp (liftR r) (liftP q)))\<close>
  unfolding liftP_def liftR_def curry_def reflp_on_def prepost_state_def'
    symp_def transp_def wlp_def
  nitpick
  oops


section \<open> Program \<close>

abbreviation
  \<open>Output v \<equiv> Assert (\<bbbA> v \<circ> exch4)\<close>

abbreviation
  \<open>Leak v \<equiv> Assume (\<bbbA> v \<circ> exch4)\<close>

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


end
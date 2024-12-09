theory Lang
  imports SepAlgInstances
begin


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype ('s, 'a) comm =
  Skip
  | Seq \<open>('s, 'a) comm\<close> \<open>('s, 'a) comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>('s, 'a) comm\<close> \<open>('s, 'a) comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>('s, 'a) comm\<close> \<open>('s, 'a) comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Endet \<open>('s, 'a) comm\<close> \<open>('s, 'a) comm\<close> (infixr \<open>\<box>\<close> 65)
  \<comment> \<open> An atomic action is represented by a precondition and a (relational) post-condition.
       Trying to evaluate the action outside the precondition results in a crash.
       Trying to evaluate the action outside the domain of the postcondition results in deadlock,
       until a state in the domain is reached. \<close>
  | Atomic \<open>'s \<Rightarrow> bool\<close> \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>\<langle>_, _\<rangle>\<close> [0,0] 999)
  | Iter \<open>('s, 'a) comm\<close> (\<open>DO (_) OD\<close> [0] 999)


subsection \<open> substitution \<close>

subsection \<open> Map atomic commands \<close>

fun map_comm :: \<open>('u \<Rightarrow> 's) \<Rightarrow> ('s, 'a) comm \<Rightarrow> ('u, 'b) comm\<close> where
  \<open>map_comm f Skip = Skip\<close>
| \<open>map_comm f (a ;; b) = map_comm f a ;; map_comm f b\<close>
| \<open>map_comm f (a \<parallel> b) = map_comm f a \<parallel> map_comm f b\<close>
| \<open>map_comm f (a \<^bold>+ b) = map_comm f a \<^bold>+ map_comm f b\<close>
| \<open>map_comm f (a \<box> b) = map_comm f a \<box> map_comm f b\<close>
| \<open>map_comm f (Atomic p q) = Atomic (p \<circ> f) (q \<circ>\<^sub>2 f)\<close>
| \<open>map_comm f (DO a OD) = DO map_comm f a OD\<close>

lemma map_comm_rev_iff:
  \<open>map_comm f c = Skip \<longleftrightarrow> c = Skip\<close>
  \<open>map_comm f c = c1' ;; c2' \<longleftrightarrow>
    (\<exists>c1 c2. c = c1 ;; c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<parallel> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<parallel> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<^bold>+ c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<^bold>+ c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = c1' \<box> c2' \<longleftrightarrow>
      (\<exists>c1 c2. c = c1 \<box> c2 \<and> c1' = map_comm f c1 \<and> c2' = map_comm f c2)\<close>
  \<open>map_comm f c = DO c' OD \<longleftrightarrow>
      (\<exists>ca. c = DO ca OD \<and> c' = map_comm f ca)\<close>
  \<open>map_comm f c = Atomic p q \<longleftrightarrow>
      (\<exists>p' q'. c = Atomic p' q' \<and> p = (p' \<circ> f) \<and> q = (q' \<circ>\<^sub>2 f))\<close>
        apply (induct c; (simp add: fun_eq_iff; argo)+)+
  apply (induct c; force)
  done

lemmas map_comm_rev_iff2 = map_comm_rev_iff[THEN trans[OF eq_commute]]

subsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('s, 'a) comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm P Skip\<close>
| seq[intro!]: \<open>all_atom_comm P c1 \<Longrightarrow> all_atom_comm P c2 \<Longrightarrow> all_atom_comm P (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm P c1 \<Longrightarrow> all_atom_comm P c2 \<Longrightarrow> all_atom_comm P (c1 \<parallel> c2)\<close>
| indet[intro!]: \<open>all_atom_comm P c1 \<Longrightarrow> all_atom_comm P c2 \<Longrightarrow> all_atom_comm P (c1 \<^bold>+ c2)\<close>
| endet[intro!]: \<open>all_atom_comm P c1 \<Longrightarrow> all_atom_comm P c2 \<Longrightarrow> all_atom_comm P (c1 \<box> c2)\<close>
| iter[intro!]: \<open>all_atom_comm P c \<Longrightarrow> all_atom_comm P (DO c OD)\<close>
| atom[intro!]: \<open>P p q \<Longrightarrow> all_atom_comm P (Atomic p q)\<close>

inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm P (c1 ;; c2)\<close>
inductive_cases all_atom_comm_indetE[elim!]: \<open>all_atom_comm P (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_endetE[elim!]: \<open>all_atom_comm P (c1 \<box> c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm P (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm P (DO c OD)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm P (Atomic ap aq)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm P (c1 ;; c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<box> c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm P c1 \<and> all_atom_comm P c2\<close>
  \<open>all_atom_comm P (DO c OD) \<longleftrightarrow> all_atom_comm P c\<close>
  \<open>all_atom_comm P (Atomic ap aq) \<longleftrightarrow> P ap aq\<close>
  by fastforce+

lemma all_atom_comm_pred_mono:
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P c \<Longrightarrow> all_atom_comm Q c\<close>
  by (induct c) force+

lemma all_atom_comm_pred_mono':
  \<open>P \<le> Q \<Longrightarrow> all_atom_comm P \<le> all_atom_comm Q\<close>
  using all_atom_comm_pred_mono by auto

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq[simp]:
  \<open>all_atom_comm (P \<sqinter> Q) c \<longleftrightarrow> all_atom_comm P c \<and> all_atom_comm Q c\<close>
  by (induct c) force+

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  by (induct c) force+


section \<open> Specific Languages \<close>

subsection \<open> Sugared atomic programs \<close>

subsubsection \<open> Assert \<close>

definition \<open>Assert p \<equiv> Atomic p (=)\<close>

subsubsection \<open> Await \<close>

definition \<open>Await p \<equiv> Atomic \<top> (rel_liftL p \<sqinter> (=))\<close>

lemma Await_inject[simp]:
  \<open>Await p1 = Await p2 \<longleftrightarrow> p1 = p2\<close>
  by (force simp add: Await_def fun_eq_iff rel_liftL_def)

subsection \<open> If-then-else \<close>

definition \<open>IfThenElse p ct cf \<equiv> Await p ;; ct \<box> Await (-p) ;; cf\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (force simp add: IfThenElse_def fun_eq_iff)

lemma IfThenElse_distinct[simp]:
  \<open>IfThenElse p ct cf \<noteq> Skip\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>IfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>IfThenElse p ct cf \<noteq> Atomic ap aq\<close>
  \<open>Skip \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> IfThenElse p ct cf\<close>
  \<open>Atomic ap aq \<noteq> IfThenElse p ct cf\<close>
  by (simp add: IfThenElse_def)+


subsection \<open> WhileLoop \<close>

definition \<open>WhileLoop p c \<equiv> DO (Await p ;; c) OD\<close>

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def Await_def fun_eq_iff, blast)

lemma WhileLoop_distinct[simp]:
  \<open>WhileLoop p c \<noteq> Skip\<close>
  \<open>WhileLoop p c \<noteq> c1 \<box> c2\<close>
  \<open>WhileLoop p c \<noteq> c1 \<parallel> c2\<close>
  \<open>WhileLoop p c \<noteq> Atomic ap aq\<close>
  \<open>Skip \<noteq> WhileLoop p c\<close>
  \<open>c1 \<box> c2 \<noteq> WhileLoop p c\<close>
  \<open>c1 \<parallel> c2 \<noteq> WhileLoop p c\<close>
  \<open>Atomic ap aq \<noteq> WhileLoop p c\<close>
  by (simp add: WhileLoop_def; fail)+


section \<open> Logic Utils \<close>


section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

subsection \<open> rel relf + trans \<close>

lemma relyrel_trans: \<open>transp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
  by (metis rel_Times_left_eq_rtranclp_distrib transp_rtranclp)

lemma relyrel_mono: \<open>r1 \<le> r2 \<Longrightarrow> ((=) \<times>\<^sub>R r1\<^sup>*\<^sup>*) \<le> ((=) \<times>\<^sub>R r2\<^sup>*\<^sup>*)\<close>
  by (simp add: le_fun_def, metis mono_rtranclp)

subsection \<open> step properties \<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sswa_step:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemmas sswa_stepD = sswa_step[rotated]

lemma wssa_step:
  \<open>r y y' \<Longrightarrow>
    wssa r p (x, y) \<Longrightarrow>
    wssa r p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)

lemmas wssa_stepD = wssa_step[rotated]

subsection \<open> closure operator properties \<close>

lemmas sswa_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_trivial[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

lemmas sswa_rel_mono = sp_rel_mono[OF relyrel_mono]

lemmas wssa_weaker = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (meson le_boolE le_funE wssa_weaker)

lemmas wssa_rel_antimono = wlp_rel_antimono[OF relyrel_mono]


lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]


subsection \<open> absorption/pseduo-idempotence properties \<close>

(*
lemmas sswa_idem[simp] =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_idem[simp] =
  wlp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]
*)

lemma sswa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1) sp_comp_rel)

lemma wssa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (wssa r2 p) = wssa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2) wlp_comp_rel)

lemma sswa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (wssa r2 p) = wssa r2 p\<close>
  by (force simp add: relyrel_trans relyrel_mono sp_wlp_absorb)

lemma wssa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: relyrel_mono relyrel_trans wlp_sp_absorb)


subsection \<open> semi-distributivity with sepconj-conj \<close>

lemma wlp_rely_sepconj_conj_semidistrib_mono:
  \<open>p' \<le> wlp ((=) \<times>\<^sub>R r) p \<Longrightarrow>
    q' \<le> wlp ((=) \<times>\<^sub>R r) q \<Longrightarrow>
    p' \<^emph>\<and> q' \<le> wlp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q)\<close>
  by (fastforce simp add: wlp_def sepconj_conj_def le_fun_def)

lemmas wlp_rely_sepconj_conj_semidistrib =
  wlp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma sp_rely_sepconj_conj_semidistrib_mono:
  \<open>sp ((=) \<times>\<^sub>R r) p \<le> p' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) q \<le> q' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q) \<le> p' \<^emph>\<and> q'\<close>
  by (fastforce simp add: sp_def sepconj_conj_def le_fun_def)

lemmas sp_rely_sepconj_conj_semidistrib =
  sp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

subsection \<open> Interaction with pred-Times \<close>

lemma wssa_of_pred_Times_eq[simp]:
  \<open>wssa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def sp_def split: prod.splits)


subsection \<open> Local and shared predicate lifting \<close>

abbreviation(input) local_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S>(p) \<equiv> p \<circ> snd\<close>

lemma wssa_ignore_local[simp]:
  \<open>wssa r (\<L> pl) = \<L> pl\<close>
  by (fastforce simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_ignore_local[simp]:
  \<open>sswa r (\<L> pl) = \<L> pl\<close>
  \<open>sswa r (\<L> pl \<^emph>\<and> q) = \<L> pl \<^emph>\<and> sswa r q\<close>
  \<open>sswa r (p \<^emph>\<and> \<L> ql) = sswa r p \<^emph>\<and> \<L> ql\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)+

lemma wssa_over_shared:
  \<open>wssa r (\<S> ps) = \<S> (wlp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_over_shared:
  \<open>sswa r (\<S> ps) = \<S> (sp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)

lemma wssa_semiignore_local[simp]:
  \<open>\<L> pl \<^emph>\<and> wssa r q \<le> wssa r (\<L> pl \<^emph>\<and> q)\<close>
  \<open>wssa r p \<^emph>\<and> \<L> ql \<le> wssa r (p \<^emph>\<and> \<L> ql)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)+

text \<open>
  The full law local ignore law is _not_ true for \<open>wssa\<close>, unlike the one for \<open>sswa\<close>.
  Imagine the following situation:
    State model: \<open>bool \<times> bool\<close>
    Sep-algebra: \<open>R000, R011, R101, R111\<close>
    Inputs:
      \<open>q = {11, 00}\<close>
      \<open>r = (0 \<leadsto> 1, 0 \<leadsto> 1)\<close>
    Results:
      \<open>wssa r q = {}\<close>
      \<open>\<L> \<top> \<^emph>\<and> q = {11, 10, 00}\<close>
      \<open>(\<L> pl \<^emph>\<and> wssa r q) = {}\<close>
      \<open>wssa r (\<L> pl \<^emph>\<and> q) = {11, 10}\<close>
    Here we observe that the outputs are not the same, because \<open>wssa\<close> only preserves
    a \<^emph>\<open>subset\<close> of the initial predicate, and this subset might not be compatible
    with the frame.
\<close>

lemma sepconj_local_eq:
  \<open>\<L> p \<^emph>\<and> \<L> q = \<L> (p \<^emph> q)\<close>
  by (simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma sepconj_shared_eq:
  \<open>(\<S> p :: 'a::multiunit_sep_alg \<times> 'b \<Rightarrow> bool) \<^emph>\<and> \<S> q = \<S> (p \<sqinter> q)\<close>
  by (force simp add: sepconj_conj_def sepconj_def fun_eq_iff)


end
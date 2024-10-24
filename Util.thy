theory Util
  imports Main
begin

text \<open> We extensively use lattice syntax for separation logic \<close>
unbundle lattice_syntax

text \<open> Helper Lemmas \<close>

section \<open> Functional Programming \<close>

definition flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)\<close> where
  \<open>flip f a b \<equiv> f b a\<close>
declare flip_def[simp]

lemma le_fun_eta[simp]: \<open>(\<lambda>x. a) \<le> (\<lambda>x. b) \<longleftrightarrow> a \<le> b\<close>
  by (simp add: le_fun_def)

section \<open> Logic \<close>

lemmas conj_left_mp[simp] =
  SMT.verit_bool_simplify(7)
  arg_cong[where f=\<open>\<lambda>x. x \<and> R\<close> for R, OF SMT.verit_bool_simplify(7), simplified conj_assoc]
lemmas conj_right_mp[simp] =
  SMT.verit_bool_simplify(8)
  arg_cong[where f=\<open>\<lambda>x. x \<and> R\<close> for R, OF SMT.verit_bool_simplify(8), simplified conj_assoc]

lemma strong_imp_conj_iff: "(P \<Longrightarrow> R) \<Longrightarrow> ((Q \<longrightarrow> R) \<and> P) = P"
  by blast

lemma conj_imp_distribR:
  \<open>(p \<longrightarrow> q) \<and> r \<longleftrightarrow> (\<not> p \<and> r) \<or> (q \<and> r)\<close>
  by force

lemma conj_imp_distribL:
  \<open>p \<and> (q \<longrightarrow> r) \<longleftrightarrow> (p \<and> \<not> q) \<or> (p \<and> r)\<close>
  by force

lemma if_eq_disj_cases: \<open>(A \<longrightarrow> B) \<and> (\<not> A \<longrightarrow> C) \<longleftrightarrow> (A \<and> B) \<or> (\<not> A \<and> C)\<close>
  by blast

lemma imp_impL[simp]: \<open>(A \<longrightarrow> B) \<longrightarrow> C \<longleftrightarrow> (\<not> A \<longrightarrow> C) \<and> (B \<longrightarrow> C)\<close>
  by blast

lemma all2_push[simp]:
  \<open>(\<forall>x y. P y \<longrightarrow> Q x y) = (\<forall>y. P y \<longrightarrow> (\<forall>x. Q x y))\<close>
  by force

lemma imp_ex_conjL:
  \<open>\<And>P Q. ((\<exists>x. P x \<and> Q x) \<longrightarrow> R) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x \<longrightarrow> R)\<close>
  \<open>\<And>P Q. ((\<exists>x y. P x y \<and> Q x y) \<longrightarrow> R) \<longleftrightarrow> (\<forall>x y. P x y \<longrightarrow> Q x y \<longrightarrow> R)\<close>
  \<open>\<And>P Q. ((\<exists>x y z. P x y z \<and> Q x y z) \<longrightarrow> R) \<longleftrightarrow> (\<forall>x y z. P x y z \<longrightarrow> Q x y z \<longrightarrow> R)\<close>
  by blast+

lemma imp_conj_common:
  \<open>(A1 \<longrightarrow> B \<longrightarrow> C1) \<and> (A2 \<longrightarrow> B \<longrightarrow> C2) \<longleftrightarrow> (B \<longrightarrow> (A1 \<longrightarrow> C1) \<and> (A2 \<longrightarrow> C2))\<close>
  \<open>(A1 \<longrightarrow> B \<longrightarrow> C1) \<and> (A2 \<longrightarrow> B \<longrightarrow> C2) \<and> D \<longleftrightarrow> (B \<longrightarrow> (A1 \<longrightarrow> C1) \<and> (A2 \<longrightarrow> C2)) \<and> D\<close>
  by blast+

lemma imp_all_conj_common:
  \<open>(A1 \<longrightarrow> (\<forall>x. B x \<longrightarrow> C1 x)) \<and> (A2 \<longrightarrow> (\<forall>x. B x \<longrightarrow> C2 x)) \<longleftrightarrow> (\<forall>x. B x \<longrightarrow> (A1 \<longrightarrow> C1 x) \<and> (A2 \<longrightarrow> C2 x))\<close>
  \<open>(A1 \<longrightarrow> (\<forall>x. B x \<longrightarrow> C1 x)) \<and> (A2 \<longrightarrow> (\<forall>x. B x \<longrightarrow> C2 x)) \<and> D \<longleftrightarrow>
    (\<forall>x. B x \<longrightarrow> (A1 \<longrightarrow> C1 x) \<and> (A2 \<longrightarrow> C2 x)) \<and> D\<close>
  by blast+

lemma all_conj_ex1:
  \<open>(\<forall>x. P x \<longrightarrow> Q x) \<and> Ex P \<longleftrightarrow> (\<exists>x. P x \<and> Q x) \<and> (\<forall>x. P x \<longrightarrow> Q x)\<close>
  by blast

lemma exsome_conj_some_imp:
  \<open>(\<exists>x. y = Some x) \<and> (\<forall>x. y = Some x \<longrightarrow> P x) \<longleftrightarrow> (\<exists>x. y = Some x \<and> P x)\<close>
  by blast

lemma ex_eq_pair_iff[simp]:
  \<open>(\<exists>x y. a = (x, y) \<and> P x y) \<longleftrightarrow> P (fst a) (snd a)\<close>
  by force

lemmas disjCI2 = disjCI[THEN Meson.disj_comm]

lemma pred_conjD: \<open>(A1 \<sqinter> A2) s \<Longrightarrow> A1 \<le> B1 \<Longrightarrow> A2 \<le> B2 \<Longrightarrow> (B1 \<sqinter> B2) s\<close>
  by blast


section \<open> Tuples \<close>

lemma prod_eq_decompose:
  \<open>a = (b,c) \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  \<open>(b,c) = a \<longleftrightarrow> fst a = b \<and> snd a = c\<close>
  by force+

lemma common_if_prod[simp]:
  \<open>(if P then a1 else a2, if P then b1 else b2) = (if P then (a1,b1) else (a2,b2))\<close>
  by simp

abbreviation plus_right_fst :: \<open>'a::plus \<times> 'b \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'b\<close> (infixl \<open>+\<^sub>L\<close> 65) where
  \<open>plus_right_fst xy a \<equiv> apfst (\<lambda>z. z + a) xy\<close>

abbreviation plus_right_snd :: \<open>'a \<times> 'b::plus \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b\<close> (infixl \<open>+\<^sub>R\<close> 65) where
  \<open>plus_right_snd xy a \<equiv> apsnd (\<lambda>z. z + a) xy\<close>

lemma plus_right_fst_accum[simp]:
  fixes x :: \<open>'a :: semigroup_add\<close>
  shows \<open>(xy +\<^sub>L x) +\<^sub>L x' = xy +\<^sub>L (x + x')\<close>
  by (cases xy, simp add: add.assoc)

lemma plus_right_snd_accum[simp]:
  fixes y :: \<open>'a :: semigroup_add\<close>
  shows \<open>(xy +\<^sub>R y) +\<^sub>R y' = xy +\<^sub>R (y + y')\<close>
  by (cases xy, simp add: add.assoc)

section \<open> Lists \<close>

lemma upt_add_eq_append:
  assumes \<open>i \<le> j\<close> \<open>j \<le> k\<close>
  shows \<open>[i..<k] = [i..<j] @ [j..<k]\<close>
  using assms
proof (induct k arbitrary: i j)
  case 0 then show ?case by simp
next
  case (Suc k)
  show ?case
  proof (cases \<open>j \<le> k\<close>)
    case True
    have \<open>[i..<Suc k] = [i..<k] @ [k]\<close>
      using Suc.prems True
      by simp
    also have \<open>... = [i..<j] @ [j..<k] @ [k]\<close>
      using Suc.prems True
      by (subst Suc.hyps[where j=j]; simp)
    also have \<open>... = [i..<j] @ [j..<Suc k]\<close>
      using True
      by simp
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using Suc.prems
      by (clarsimp simp add: le_Suc_eq)
  qed
qed

section \<open> Relations \<close>

definition \<open>rel_liftL p \<equiv> \<lambda>a b. p a\<close>
definition \<open>rel_liftR p \<equiv> \<lambda>a b. p b\<close>
definition \<open>rel_lift p \<equiv> \<lambda>a b. p a \<and> p b\<close>
definition \<open>rel_imp_lift p \<equiv> \<lambda>a b. p a \<longrightarrow> p b\<close>

definition \<open>pre_state_of B r \<equiv> \<lambda>a. \<exists>b\<in>B. r a b\<close>
definition \<open>post_state_of A r \<equiv> \<lambda>b. \<exists>a\<in>A. r a b\<close>

abbreviation \<open>pre_state \<equiv> pre_state_of UNIV\<close>
abbreviation \<open>post_state \<equiv> post_state_of UNIV\<close>

lemmas pre_state_def = pre_state_of_def[of UNIV, simplified]
lemmas post_state_def = post_state_of_def[of UNIV, simplified]

definition \<open>prepost_state \<equiv> pre_state \<squnion> post_state\<close>

lemmas prepost_state_def' = prepost_state_def pre_state_def post_state_def

abbreviation \<open>quasireflp r \<equiv> reflp_on (Collect (prepost_state r)) r\<close>

definition \<open>pre_change_state r \<equiv> \<lambda>a. \<exists>b. r a b \<and> a \<noteq> b\<close>
definition \<open>post_change_state r \<equiv> \<lambda>b. \<exists>a. r a b \<and> a \<noteq> b\<close>
definition \<open>change_state \<equiv> pre_change_state \<squnion> post_change_state\<close>

lemma quasireflpD1[dest]:
  \<open>quasireflp r \<Longrightarrow> r x y \<Longrightarrow> r x x\<close>
  by (metis mem_Collect_eq pre_state_def prepost_state_def reflp_onD sup2CI)

lemma quasireflpD2[dest]:
  \<open>quasireflp r \<Longrightarrow> r x y \<Longrightarrow> r y y\<close>
  by (metis mem_Collect_eq post_state_def prepost_state_def reflp_onD sup2CI)

lemma quasireflpD1'[dest]:
  \<open>quasireflp r \<Longrightarrow> pre_state r x \<Longrightarrow> r x x\<close>
  by (metis mem_Collect_eq prepost_state_def reflp_onD sup2CI)

lemma quasireflpD2'[dest]:
  \<open>quasireflp r \<Longrightarrow> post_state r y \<Longrightarrow> r y y\<close>
  by (metis mem_Collect_eq prepost_state_def reflp_onD sup2CI)

lemma pre_state_trancl_eq[simp]:
  \<open>pre_state (r\<^sup>+\<^sup>+) = pre_state r\<close>
  unfolding pre_state_def
  apply (intro ext iffI)
   apply (clarify, rule tranclp_induct[of r]; blast)
  apply blast
  done

lemma post_state_trancl_eq[simp]:
  \<open>post_state (r\<^sup>+\<^sup>+) = post_state r\<close>
  unfolding post_state_def
  apply (intro ext iffI)
   apply (clarify, rule tranclp_induct[of r]; blast)
  apply blast
  done

lemma pre_state_relconj_le:
  \<open>pre_state (r1 \<sqinter> r2) \<le> pre_state r1 \<sqinter> pre_state r2\<close>
  by (force simp add: pre_state_def)

lemma pre_state_reldisj[simp]:
  \<open>pre_state (r1 \<squnion> r2) = pre_state r1 \<squnion> pre_state r2\<close>
  by (force simp add: pre_state_def)

lemma post_state_relconj_le:
  \<open>post_state (r1 \<sqinter> r2) \<le> post_state r1 \<sqinter> post_state r2\<close>
  by (force simp add: post_state_def)

lemma post_state_reldisj[simp]:
  \<open>post_state (r1 \<squnion> r2) = post_state r1 \<squnion> post_state r2\<close>
  by (force simp add: post_state_def)

lemma rel_liftL_unfold[simp]:
  \<open>rel_liftL p a b = p a\<close>
  by (simp add: rel_liftL_def)

lemma rel_liftR_unfold[simp]:
  \<open>rel_liftR p a b = p b\<close>
  by (simp add: rel_liftR_def)

lemma rel_subid_unfold[simp]:
  \<open>rel_lift p a b = (p a \<and> p b)\<close>
  by (simp add: rel_lift_def)

lemma liftL_le_liftL[simp]:
  \<open>rel_liftL p \<le> rel_liftL q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: rel_liftL_def le_fun_def)

lemma liftR_le_liftR[simp]:
  \<open>rel_liftR p \<le> rel_liftR q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: rel_liftR_def)

lemma rel_lift_top[simp]:
  \<open>rel_lift \<top> = \<top>\<close>
  by (force simp add: rel_lift_def)

lemma rel_lift_bot[simp]:
  \<open>rel_lift \<bottom> = \<bottom>\<close>
  by (force simp add: rel_lift_def)
lemma rel_lift_pred_True[simp]:
  \<open>rel_lift (\<lambda>x. True) = \<top>\<close>
  by (force simp add: rel_lift_def)

lemma rel_lift_pred_False[simp]:
  \<open>rel_lift (\<lambda>x. False) = \<bottom>\<close>
  by (force simp add: rel_lift_def)

lemma pre_change_state_mono[dest]:
  \<open>r1 \<le> r2 \<Longrightarrow> pre_change_state r1 x \<Longrightarrow> pre_change_state r2 x\<close>
  by (force simp add: pre_change_state_def)

lemma post_change_state_mono[dest]:
  \<open>r1 \<le> r2 \<Longrightarrow> post_change_state r1 x \<Longrightarrow> post_change_state r2 x\<close>
  by (force simp add: post_change_state_def)

lemma change_state_mono[dest]:
  \<open>r1 \<le> r2 \<Longrightarrow> change_state r1 x \<Longrightarrow> change_state r2 x\<close>
  by (force simp add: change_state_def)

lemma implies_rel_then_rtranscl_implies_rel:
  assumes assms_induct:
    \<open>r\<^sup>*\<^sup>* x y\<close>
    \<open>\<forall>x y. r x y \<longrightarrow> s x y\<close>
  and assms_misc:
    \<open>(\<And>a. s a a)\<close>
    \<open>(\<And>a b c. s a b \<Longrightarrow> s b c \<Longrightarrow> s a c)\<close>
  shows \<open>s x y\<close>
  using assms_induct
  by (induct rule: rtranclp_induct)
    (blast intro: assms_misc)+

lemma transp_subrel_compp_smaller:
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> S OO R \<le> S\<close>
  \<open>transp S \<Longrightarrow> R \<le> S \<Longrightarrow> R OO S \<le> S\<close>
  by (meson order.refl order.trans relcompp_mono transp_relcompp_less_eq)+

lemma rel_le_rtranscp_relcompp_absorb:
  \<open>R \<le> S \<Longrightarrow> S\<^sup>*\<^sup>* OO R\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
  \<open>R \<le> S \<Longrightarrow> R\<^sup>*\<^sup>* OO S\<^sup>*\<^sup>* = S\<^sup>*\<^sup>*\<close>
   apply -
   apply (rule antisym)
    apply (metis rtranclp_mono transp_rtranclp transp_subrel_compp_smaller(1))
   apply force
  apply (rule antisym)
   apply (simp add: rtranclp_mono transp_subrel_compp_smaller(2))
  apply force
  done

lemma rtransp_rel_is_rtransclp:
  \<open>reflp R \<Longrightarrow> transp R \<Longrightarrow> R\<^sup>*\<^sup>* = R\<close>
  apply (intro ext iffI)
   apply ((rule rtranclp_induct, assumption); force dest: reflpD transpD)
  apply force
  done

lemma rtranclp_absorb_id_right[simp]:
  \<open>(\<lambda>x y. r x y \<or> x = y)\<^sup>*\<^sup>* = r\<^sup>*\<^sup>*\<close>
  apply (rule HOL.trans[where s=\<open>r\<^sup>=\<^sup>=\<^sup>*\<^sup>*\<close>])
   apply (simp del: rtranclp_reflclp add: sup_fun_def)
  apply simp
  done

lemma rtranclp_absorb_id_left[simp]:
  \<open>(\<lambda>x y. x = y \<or> r x y)\<^sup>*\<^sup>* = r\<^sup>*\<^sup>*\<close>
  by (subst disj_commute, simp)


lemma refl_le_trans_eq[simp]:
  \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> r1 OO r2 = r2\<close>
  by (metis (no_types, lifting) OO_eq eq_comp_r reflclp_ident_if_reflp relcompp_distrib2
      sup.absorb_iff2 transp_subrel_compp_smaller(2))

lemma refl_le_trans_eq2[simp]:
  \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> r2 OO r1 = r2\<close>
  by (metis (no_types, lifting) OO_eq dual_order.eq_iff reflp_eq relcompp_mono
      transp_subrel_compp_smaller(1))

lemma rtransp_relcompp_absorb_lr[simp]: \<open>(r1 \<squnion> r2)\<^sup>*\<^sup>* OO r1\<^sup>*\<^sup>* = (r1 \<squnion> r2)\<^sup>*\<^sup>*\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1))

lemma rtransp_relcompp_absorb_rr[simp]: \<open>(r1 \<squnion> r2)\<^sup>*\<^sup>* OO r2\<^sup>*\<^sup>* = (r1 \<squnion> r2)\<^sup>*\<^sup>*\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1))

lemma rtransp_relcompp_absorb_rl[simp]: \<open>r2\<^sup>*\<^sup>* OO (r1 \<squnion> r2)\<^sup>*\<^sup>* = (r1 \<squnion> r2)\<^sup>*\<^sup>*\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2))

lemma rtransp_relcompp_absorb_ll[simp]: \<open>r1\<^sup>*\<^sup>*  OO (r1 \<squnion> r2)\<^sup>*\<^sup>* = (r1 \<squnion> r2)\<^sup>*\<^sup>*\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2))

declare eq_OO[simp] OO_eq[simp]

lemma rtranclp_tuple_rel_semidistrib:
  \<open>(\<lambda>(a, c) (b, d). r1 a b \<and> r2 c d)\<^sup>*\<^sup>* ac bd
    \<Longrightarrow> r1\<^sup>*\<^sup>* (fst ac) (fst bd) \<and> r2\<^sup>*\<^sup>* (snd ac) (snd bd)\<close>
  by (induct rule: rtranclp_induct; force)

lemma rtranclp_tuple_lift_eq_left:
  \<open>r2\<^sup>*\<^sup>* c d \<Longrightarrow> (\<lambda>(a, c) (b, d). a = b \<and> r2 c d)\<^sup>*\<^sup>* (a,c) (a,d)\<close>
  by (induct rule: rtranclp_induct, fast, simp add: rtranclp.rtrancl_into_rtrancl)

lemma rtranclp_eq_eq[simp]:
  \<open>(=)\<^sup>*\<^sup>* = (=)\<close>
  by (simp add: rtransp_rel_is_rtransclp)


section \<open> Function Properties \<close>

lemmas bij_betw_disjoint_insert =
  bij_betw_disjoint_Un[where A=\<open>{b}\<close> and C=\<open>{d}\<close> for b d, simplified]

lemma bij_betw_insert_ignore:
  \<open>bij_betw f B D \<Longrightarrow> b \<in> B \<Longrightarrow> d \<in> D \<Longrightarrow> bij_betw f (insert b B) (insert d D)\<close>
  by (simp add: insert_absorb)

lemma bij_betw_singleton:
  \<open>f a = b \<Longrightarrow> bij_betw f {a} {b}\<close>
  by (simp add: bij_betw_def)

lemmas bij_betw_combine_insert =
  bij_betw_combine[where A=\<open>{b}\<close> and B=\<open>{d}\<close> for b d, simplified]

section \<open> Options \<close>

lemma not_eq_None[simp]: \<open>None \<noteq> x \<longleftrightarrow> (\<exists>z. x = Some z)\<close>
  using option.exhaust_sel by auto

text \<open> We need to do this with cases to avoid infinite simp loops \<close>
lemma option_eq_iff:
  \<open>x = y \<longleftrightarrow> (case x of
                None \<Rightarrow> (case y of None \<Rightarrow> True | Some _ \<Rightarrow> False)
              | Some x' \<Rightarrow> (case y of None \<Rightarrow> False | Some y' \<Rightarrow> x' = y'))\<close>
  by (force split: option.splits)

section \<open> Partial Maps \<close>

lemma map_le_restrict_eq: \<open>ma \<subseteq>\<^sub>m mb \<Longrightarrow> mb |` dom ma = ma\<close>
  by (rule ext, metis domIff map_le_def restrict_map_def)

lemma map_restrict_un_eq:
  \<open>m |` (A \<union> B) = m |` A ++ m |` B\<close>
  by (force simp add: restrict_map_def map_add_def split: option.splits)

lemma map_le_split:
  assumes \<open>ma \<subseteq>\<^sub>m mb\<close>
  shows \<open>mb = ma ++ mb |` (- dom ma)\<close>
  using assms
  by (subst map_le_restrict_eq[OF assms, symmetric], force simp add: map_restrict_un_eq[symmetric])

lemma map_disjoint_dom_cancel_right:
  assumes disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
    and disjoint_ac: \<open>dom b \<inter> dom c = {}\<close>
  shows \<open>(a ++ c = b ++ c) \<longleftrightarrow> a = b\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)

lemma map_disjoint_dom_cancel_left:
  assumes disjoint_ac: \<open>dom a \<inter> dom b = {}\<close>
    and disjoint_ac: \<open>dom a \<inter> dom c = {}\<close>
  shows \<open>(a ++ b = a ++ c) \<longleftrightarrow> b = c\<close>
  using assms
  by (metis (no_types, lifting) Int_Un_distrib Int_commute Un_Int_eq(3)
      disjoint_ac dom_map_add map_add_comm map_le_iff_map_add_commute map_le_restrict_eq)

lemma le_map_le_iff_sepadd:
  \<open>(a \<subseteq>\<^sub>m b) = (\<exists>c. dom a \<inter> dom c = {} \<and> b = a ++ c)\<close>
  by (metis dom_restrict inf_compl_bot_right map_add_comm map_le_map_add map_le_split)

lemma disjoint_dom_map_add_restrict_distrib:
  \<open>dom a \<inter> dom b = {} \<Longrightarrow> (a ++ b) |` A = a |` A ++ b |` A\<close>
  by (simp add: fun_eq_iff restrict_map_def map_add_def)

lemma antidom_restrict_eq[simp]:
  \<open>a |` (- dom a) = Map.empty\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemma dom_subset_restrict_eq:
  \<open>dom a \<subseteq> A \<Longrightarrow>  a |` A = a\<close>
  by (force simp add: restrict_map_def subset_iff domIff)

lemmas dom_disjoint_restrict_eq =
  dom_subset_restrict_eq[OF iffD1[OF disjoint_eq_subset_Compl]]

section \<open> Sets \<close>

lemma disjoint_equiv_iff_eq:
  \<open>(\<forall>C. A \<inter> C = {} \<longleftrightarrow> B \<inter> C = {}) \<longleftrightarrow> A = B\<close>
  by blast

lemma surj_disjoint_equiv_iff_eq:
  \<open>surj f \<Longrightarrow> (\<forall>x. A \<inter> f x = {} \<longleftrightarrow> B \<inter> f x = {}) \<longleftrightarrow> A = B\<close>
  by (metis disjoint_equiv_iff_eq surjD)

section \<open> Options \<close>

lemma not_Some_prod_eq[iff]: \<open>(\<forall>a b. x \<noteq> Some (a,b)) \<longleftrightarrow> x = None\<close>
  by (metis not_eq_None prod.collapse)

lemma not_Some_prodprod_eq[iff]: \<open>(\<forall>a b c. x \<noteq> Some ((a,b),c)) \<longleftrightarrow> x = None\<close>
  by (metis not_eq_None prod.collapse)

lemmas rev_finite_subset_Collect =
  rev_finite_subset[of \<open>Collect P\<close> \<open>Collect Q\<close> for P Q, OF _ iffD2[OF Collect_mono_iff]]

(* We can prove the existence of a map satisfying a relation by showing
    the relation is nice and that there exists a value for every input.
*)
lemma finite_map_choice_iff:
  shows \<open>(\<exists>f. finite (dom f) \<and> (\<forall>x. P x (f x))) \<longleftrightarrow>
          (finite {x. (\<exists>y. P x (Some y)) \<and> \<not> P x None} \<and> (\<forall>x. \<exists>y. P x y))\<close>
  apply -
  apply (rule iffI)
  subgoal (* 1 \<Longrightarrow> 2 *)
    apply (clarsimp simp add: dom_def)
    apply (subgoal_tac \<open>(\<forall>x. f x = None \<longrightarrow> P x None) \<and> (\<forall>x y. f x = Some y \<longrightarrow> P x (Some y))\<close>)
     prefer 2
     apply metis
    apply (rule conjI)
     apply (rule rev_finite_subset, assumption)
     apply blast
    apply force
    done
  subgoal (* 2 \<Longrightarrow> 1 *)
    apply (clarsimp simp add: dom_def)
    apply (clarsimp simp add: choice_iff)
    apply (rule_tac x=\<open>\<lambda>x. if \<exists>y. P x (Some y) \<and> \<not> P x None then f x else None\<close> in exI)
    apply (rule conjI)
     apply clarsimp
     apply (simp add: rev_finite_subset_Collect)
    apply (simp, metis option.exhaust_sel)
    done
  done

section \<open> Orders \<close>

lemma order_neq_less_conv:
  \<open>x \<le> y \<Longrightarrow> (x :: ('a :: order)) \<noteq> y \<longleftrightarrow> x < y\<close>
  \<open>y \<le> x \<Longrightarrow> (x :: ('a :: order)) \<noteq> y \<longleftrightarrow> y < x\<close>
  by fastforce+

lemma order_sandwich:
  fixes k x :: \<open>'a :: order\<close>
  shows
    \<open>k \<le> x \<and> x \<le> k \<and> P \<longleftrightarrow> x = k \<and> P\<close>
    \<open>k \<le> x \<and> P \<and> x \<le> k \<and> Q \<longleftrightarrow> x = k \<and> P \<and> Q\<close>
  by force+

lemma (in preorder) le_disj_eq_absorb[simp]: \<open>a \<le> b \<or> a = b \<longleftrightarrow> a \<le> b\<close>
  by force

lemmas preordering_refl =
  preordering.axioms(1)[THEN partial_preordering.refl]

lemmas preordering_trans =
  preordering.axioms(1)[THEN partial_preordering.trans]

definition (in order) \<open>downset x \<equiv> {y. y\<le>x}\<close>
definition (in order) \<open>Downset X \<equiv> {y. \<exists>x\<in>X. y \<le> x}\<close>

definition (in conditionally_complete_lattice) \<open>supcl (A::'a set) \<equiv> {\<Squnion>A'|A'. A' \<noteq> {} \<and> A'\<subseteq>A}\<close>
definition (in conditionally_complete_lattice) \<open>infcl (A::'a set) \<equiv> {\<Sqinter>A'|A'. A' \<noteq> {} \<and> A'\<subseteq>A}\<close>


section \<open> Groups \<close>

lemmas eq_diff_eq_comm =
  HOL.trans[OF eq_diff_eq, OF arg_cong[where f=\<open>\<lambda>x. x = y\<close> for y], OF add.commute]
thm eq_diff_eq

section \<open> Arithmetic \<close>

(* It feels like Isabelle/HOL is missing a theory of non-abelian ordered monoids.
   An example of an instance of such a thing is traces.
*)
lemma prefixcl_weak_canonical_plusD:
  fixes a1 a2 :: \<open>'a :: {order,monoid_add}\<close>
  assumes zero_le: \<open>\<And>a::'a. 0 \<le> a\<close>
  assumes add_left_cancel_le: \<open>\<And>a b c::'a. b \<le> c \<Longrightarrow> a + b \<le> a + c\<close>
  shows \<open>a1 \<le> a1 + a2\<close>
  using assms
  by (metis add.right_neutral)

lemma ex_times_k_iff:
  fixes a :: \<open>'a :: division_ring\<close>
  assumes \<open>k \<noteq> 0\<close>
  shows \<open>(\<exists>x. a = x * k \<and> P x) \<longleftrightarrow> P (a / k)\<close>
  using assms
  by (metis eq_divide_eq)

lemma max_eq_k_iff:
  fixes a b :: \<open>'a :: linorder\<close>
  shows \<open>(max a b = k) = (a = k \<and> b \<le> k \<or> a \<le> k \<and> b = k)\<close>
  by (simp add: eq_iff le_max_iff_disj)

lemma min_eq_k_iff:
  fixes a b :: \<open>'a :: linorder\<close>
  shows \<open>(min a b = k) = (a = k \<and> k \<le> b \<or> k \<le> a \<and> b = k)\<close>
  by (simp add: eq_iff min_le_iff_disj)

lemma field_All_mult_inverse_iff:
  fixes x k :: \<open>'a :: field\<close>
  shows \<open>k \<noteq> 0 \<Longrightarrow> (\<forall>y. x = y * k \<longrightarrow> P y) \<longleftrightarrow> P (x / k)\<close>
  by fastforce

lemma zero_less_plus_positive:
  fixes a b :: \<open>'a :: {order,monoid_add}\<close>
  shows \<open>0 < a + b \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < a \<or> 0 < b\<close>
  by force

lemma linordered_field_min_bounded_divide_by:
  fixes x k :: \<open>'a :: linordered_field\<close>
  shows \<open>1 \<le> i \<Longrightarrow> i < k \<Longrightarrow> 0 \<le> x \<Longrightarrow> x \<le> i \<Longrightarrow> min i (x / k) = x / k\<close>
  by (metis leD le_divide_eq_1 min.absorb2 nle_le order_trans)

lemmas min_absorb_plus_divide_left =
  min.absorb2[OF
    order.trans[OF
      add_mono[OF
        frac_le[of _ _ 1, simplified, OF _ order.refl] order.refl]], rotated 2]
lemmas min_absorb_plus_divide_right =
  min.absorb2[OF
    order.trans[OF
      add_mono[OF
        order.refl frac_le[of _ _ 1, simplified, OF _ order.refl]]], rotated 2]

lemma ordered_ab_group_add_ge0_le_iff_add:
  fixes a b :: \<open>'a :: ordered_ab_group_add\<close>
  shows \<open>(a \<le> b) = (\<exists>c\<ge>0. b = a + c)\<close>
  by (metis add.commute diff_add_cancel le_add_same_cancel1)

lemma linordered_semidom_ge0_le_iff_add:
  fixes a b :: \<open>'a :: linordered_semidom\<close>
  shows \<open>(a \<le> b) = (\<exists>c\<ge>0. b = a + c)\<close>
  by (metis le_add_diff_inverse le_add_same_cancel1)

lemma pos_eq_neg_iff_zero:
  fixes x y z :: \<open>'a :: linordered_field\<close>
  shows
    \<open>0 \<le> x \<Longrightarrow> 0 \<le> z \<Longrightarrow> x = - z \<longleftrightarrow> x = 0 \<and> z = 0\<close>
    \<open>0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> z \<Longrightarrow> x + y = - z \<longleftrightarrow> x = 0 \<and> y = 0 \<and> z = 0\<close>
  by fastforce+

lemma min_mult_extract_right_mult_right:
  fixes p x y :: \<open>_ :: linordered_field\<close>
  shows
    \<open>0 < p \<Longrightarrow> min x (y * p) = min (x/p) y * p\<close>
    \<open>0 > p \<Longrightarrow> min x (y * p) = max (x/p) y * p\<close>
  by (simp add: min_def pos_divide_le_eq max_mult_distrib_right)+

lemma max_mult_extract_right_mult_right:
  fixes p x y :: \<open>_ :: linordered_field\<close>
  shows
    \<open>0 < p \<Longrightarrow> max x (y * p) = max (x/p) y * p\<close>
    \<open>0 > p \<Longrightarrow> max x (y * p) = min (x/p) y * p\<close>
  by (simp add: max_def pos_divide_le_eq min_mult_distrib_right)+

lemma min_mult_extract_left_mult_right:
  fixes p x y :: \<open>_ :: linordered_field\<close>
  shows
    \<open>0 < p \<Longrightarrow> min x (p * y) = p * min (x/p) y\<close>
    \<open>0 > p \<Longrightarrow> min x (p * y) = p * max (x/p) y\<close>
  by (metis min_mult_extract_right_mult_right mult.commute)+

lemma max_mult_extract_right_mult_left:
  fixes p x y :: \<open>_ :: linordered_field\<close>
  shows
    \<open>0 < p \<Longrightarrow> max x (p * y) = p * max (x/p) y\<close>
    \<open>0 > p \<Longrightarrow> max x (p * y) = p * min (x/p) y\<close>
  by (metis max_mult_extract_right_mult_right mult.commute)+

lemma ordered_comm_monoid_add_add_min_assoc:
  fixes x y z k :: \<open>'a :: ordered_comm_monoid_add\<close>
  assumes \<open>x \<ge> 0\<close> \<open>z \<ge> 0\<close>
  shows \<open>min k (min k (x + y) + z) = min k (x + min k (y + z))\<close>
  using assms
  by (clarsimp simp add: min_def add.commute add.left_commute add_increasing add_increasing2 eq_iff,
      metis add.assoc add_increasing2)

lemma le_Suc_iff0: \<open>m \<le> Suc n \<longleftrightarrow> m = 0 \<or> (\<exists>m'. m = Suc m' \<and> m' \<le> n)\<close>
  by presburger

lemma ge0_plus_le_then_left_le:
  fixes a :: \<open>'a :: ordered_ab_semigroup_monoid_add_imp_le\<close>
  shows \<open>0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b \<le> c \<Longrightarrow> a \<le> c\<close>
  by (meson le_add_same_cancel1 order_trans)

lemma ge0_plus_le_then_right_le:
  fixes a :: \<open>'a :: ordered_ab_semigroup_monoid_add_imp_le\<close>
  shows \<open>0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a + b \<le> c \<Longrightarrow> b \<le> c\<close>
  by (meson le_add_same_cancel2 order_trans)


section \<open> Sequencing Algebra \<close>

text \<open> Note this is a subalgebra of a relation algebra. \<close>

class seq =
  fixes seq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infixr \<open>\<triangleright>\<close> 110)

class skip =
  fixes skip :: 'a (\<open>SKIP\<close>)

class monoid_seq = seq + skip +
  assumes seq_assoc[algebra_simps, algebra_split_simps]: \<open>(a \<triangleright> b) \<triangleright> c = a \<triangleright> (b \<triangleright> c)\<close>
    and add_skip_left[simp]: \<open>SKIP \<triangleright> a = a\<close>
    and add_skip_right[simp]: \<open>a \<triangleright> SKIP = a\<close>
begin

sublocale monoid seq skip
  by standard (simp add: seq_assoc)+

end

(*
section \<open>Top Extension\<close>

datatype 'a top_ext =
    Top | TEVal 'a

lemma not_TEVal_eq[simp]: \<open>(\<forall>x. a \<noteq> TEVal x) \<longleftrightarrow> a = Top\<close>
  by (meson top_ext.distinct top_ext.exhaust)

lemma not_Top_all_TEVal_iff: \<open>a \<noteq> Top \<Longrightarrow> (\<forall>x. a = TEVal x \<longrightarrow> Q x) \<longleftrightarrow> (\<exists>x. a = TEVal x \<and> Q x)\<close>
  using not_TEVal_eq by blast

instantiation top_ext :: (order) order_top
begin

definition \<open>top_top_ext \<equiv> Top\<close>
definition \<open>less_eq_top_ext a b \<equiv> b = Top \<or> (\<exists>b'. b = TEVal b' \<and> (\<exists>a'. a = TEVal a' \<and> a' \<le> b'))\<close>
definition \<open>less_top_ext a b \<equiv> b = Top \<and> a \<noteq> Top \<or> (\<exists>b'. b = TEVal b' \<and> (\<exists>a'. a = TEVal a' \<and> a' < b'))\<close>

instance
  by standard
    (force simp add: less_eq_top_ext_def less_top_ext_def top_top_ext_def)+

lemmas Top_greatest[simp] =
  HOL.subst[OF meta_eq_to_obj_eq[OF top_top_ext_def], where P=\<open>(\<le>) a\<close> for a, OF top_greatest]

end

instantiation top_ext :: (plus) plus
begin
definition \<open>plus_top_ext a b \<equiv>
              case a of
                TEVal a' \<Rightarrow> 
                  (case b of
                    TEVal b' \<Rightarrow> TEVal (a' + b')
                  | Top \<Rightarrow> Top)
                | Top \<Rightarrow> Top\<close>
instance by standard
end

instance top_ext :: (semigroup_add) semigroup_add
  by standard
    (simp add: plus_top_ext_def add.assoc split: top_ext.splits)+

instantiation top_ext :: (zero) zero
begin
definition \<open>zero_top_ext \<equiv> TEVal 0\<close>
instance by standard
end

instance top_ext :: (monoid_add) monoid_add
  by standard
    (simp add: plus_top_ext_def zero_top_ext_def split: top_ext.splits)+

instance top_ext :: (ab_semigroup_add) ab_semigroup_add
  by standard
    (force simp add: plus_top_ext_def add_ac split: top_ext.splits)+

instance top_ext :: (comm_monoid_add) comm_monoid_add
  by standard
    (force simp add: plus_top_ext_def zero_top_ext_def split: top_ext.splits)+

instance top_ext :: (ordered_ab_semigroup_add) ordered_ab_semigroup_add
  by standard
    (force simp add: plus_top_ext_def zero_top_ext_def less_eq_top_ext_def add_ac
      intro: add_left_mono split: top_ext.splits)+

instance top_ext :: (linorder) linorder
  by (standard, simp add: less_eq_top_ext_def, metis nle_le not_TEVal_eq)

instance top_ext :: (ordered_comm_monoid_add) ordered_comm_monoid_add
  by standard

section \<open>Zero-Bot Extension\<close>

datatype 'a bot_ext = Bot | BEVal 'a

lemma not_BEVal_eq[simp]: \<open>(\<forall>x. a \<noteq> BEVal x) \<longleftrightarrow> a = Bot\<close>
  by (meson bot_ext.distinct bot_ext.exhaust)

instantiation bot_ext :: (ord) ord
begin
definition \<open>less_eq_bot_ext a b \<equiv> (a = Bot \<or> (\<exists>a'. a = BEVal a' \<and> (\<exists>b'. b = BEVal b' \<and> a' \<le> b')))\<close>
definition \<open>less_bot_ext a b \<equiv> (a = Bot \<and> b \<noteq> Bot \<or> (\<exists>a'. a = BEVal a' \<and> (\<exists>b'. b = BEVal b' \<and> a' < b')))\<close>
instance by standard
end

instance bot_ext :: (preorder) preorder
  by standard
    (force simp add: less_eq_bot_ext_def less_bot_ext_def less_le_not_le dest: order.trans)+

instantiation bot_ext :: (order) order_bot
begin
definition \<open>bot_bot_ext \<equiv> Bot\<close>
instance
  by standard
    (force simp add: less_eq_bot_ext_def bot_bot_ext_def)+
end

instance bot_ext :: (linorder) linorder
  by standard
    (simp add: less_eq_bot_ext_def, meson nle_le not_BEVal_eq)

instantiation bot_ext :: (plus) plus
begin
definition
  \<open>plus_bot_ext a b \<equiv>
    (case a of Bot \<Rightarrow> b | BEVal a' \<Rightarrow> (case b of Bot \<Rightarrow> a | BEVal b' \<Rightarrow> BEVal (a' + b')))\<close>
instance by standard
end

instantiation bot_ext :: (type) zero
begin
definition \<open>zero_bot_ext \<equiv> Bot\<close>
instance by standard
end

instance bot_ext :: (semigroup_add) semigroup_add
  by standard
    (force simp add: plus_bot_ext_def add.assoc split: bot_ext.splits)

instance bot_ext :: (ab_semigroup_add) ab_semigroup_add
  by standard
    (force simp add: plus_bot_ext_def add.commute split: bot_ext.splits)

instance bot_ext :: (monoid_add) monoid_add
  by standard
    (force simp add: plus_bot_ext_def zero_bot_ext_def split: bot_ext.splits)+

instance bot_ext :: (comm_monoid_add) comm_monoid_add
  by standard
    (force simp add: plus_bot_ext_def zero_bot_ext_def split: bot_ext.splits)

instantiation bot_ext :: (canonically_ordered_monoid_add) canonically_ordered_monoid_add
begin
instance
  apply standard
  apply (simp add: plus_bot_ext_def zero_bot_ext_def less_eq_bot_ext_def le_iff_add split: bot_ext.splits)+
  apply (case_tac a, force, case_tac b, force)
  apply (simp, metis bot_ext.inject group_cancel.rule0 not_BEVal_eq)
  done
end
*)

section \<open> Lattices \<close>

context lattice
begin

lemma inf_twist_sup_idem: \<open>a \<sqinter> b \<squnion> b \<sqinter> a = a \<sqinter> b\<close>
  by (simp add: inf.commute)

lemma inf_twist_sup_idem_assoc: \<open>a \<sqinter> b \<squnion> b \<sqinter> a \<squnion> c = a \<sqinter> b \<squnion> c\<close>
  by (simp add: inf_twist_sup_idem)

lemma inf_abac_eq_abc:
  shows \<open>(a \<sqinter> b) \<sqinter> a \<sqinter> c = a \<sqinter> b \<sqinter> c\<close>
  by (simp add: inf.absorb1)

end

context boolean_algebra
begin

definition implies :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<leadsto>" 60) where
  "a \<leadsto> b \<equiv> -a \<squnion> b"

lemma implies_shunt:
  \<open>c \<sqinter> a \<le> b \<longleftrightarrow> c \<le> a \<leadsto> b\<close>
  by (simp add: implies_def shunt1)

lemma implies_shunt2:
  \<open>-(a \<leadsto> b) \<le> c \<longleftrightarrow> a \<le> b \<squnion> c\<close>
  by (simp add: implies_def shunt2)

lemma implies_simps[simp]:
  \<open>(a \<leadsto> b) x = (a x \<longrightarrow> b x)\<close>
  \<open>All (a \<leadsto> b) = (\<forall>x. a x \<longrightarrow> b x)\<close>
  \<open>Ex (a \<leadsto> b) = (\<exists>x. a x \<longrightarrow> b x)\<close>
  \<open>\<top> \<leadsto> b = b\<close>
  \<open>\<bottom> \<leadsto> b = \<top>\<close>
  \<open>a \<leadsto> \<bottom> = - a\<close>
  \<open>a \<leadsto> \<top> = \<top>\<close>
  \<open>a \<leadsto> a = \<top>\<close>
  by (force simp add: boolean_algebra_class.implies_def)+

definition bequiv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<sim>" 60) where
  "a \<sim> b \<equiv> (a \<leadsto> b) \<sqinter> (b \<leadsto> a)"

lemma bequiv_simps[simp]:
  \<open>(a \<sim> b) x = (a x = b x)\<close>
  \<open>All (a \<sim> b) = (\<forall>x. a x = b x)\<close>
  \<open>Ex (a \<sim> b) = (\<exists>x. a x = b x)\<close>
  \<open>a \<sim> a = \<top>\<close>
  \<open>a \<sim> -a = \<bottom>\<close>
  \<open>-a \<sim> a = \<bottom>\<close>
  \<open>a \<sim> \<top> = a\<close>
  \<open>\<top> \<sim> a = a\<close>
  \<open>a \<sim> \<bottom> = -a\<close>
  \<open>\<bottom> \<sim> a = -a\<close>
  by (force simp add: boolean_algebra_class.bequiv_def)+

lemma bequiv_iff: \<open>a \<sim> b = (-a \<squnion> b) \<sqinter> (-b \<squnion> a)\<close>
  by (simp add: bequiv_def implies_def)

lemma bequiv_iff2: \<open>a \<sim> b = (a \<sqinter> b) \<squnion> (-a \<sqinter> -b)\<close>
  using bequiv_iff sup.commute sup_inf_distrib2 by force

end

lemma mem_implies_iff[simp]:
  \<open>x \<in> A \<leadsto> B \<longleftrightarrow> (x \<in> A \<longrightarrow> x \<in> B)\<close>
  by (simp add: implies_def)

subsection \<open> Bounded distributive lattices \<close>

class distrib_lattice_bot = distrib_lattice + bounded_lattice_bot
class distrib_lattice_top = distrib_lattice + bounded_lattice_top
class bounded_distrib_lattice = distrib_lattice_bot + distrib_lattice_top

context boolean_algebra
begin
subclass distrib_lattice_bot by standard
subclass distrib_lattice_top by standard
subclass bounded_distrib_lattice by standard
end

section \<open> Times \<close>

definition pred_Times :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close>
  (infixr \<open>\<times>\<^sub>P\<close> 80) where
  \<open>p \<times>\<^sub>P q \<equiv> \<lambda>(a,b). p a \<and> q b\<close>

lemma pred_Times_iff[simp]: \<open>(p1 \<times>\<^sub>P p2) (a, b) \<longleftrightarrow> p1 a \<and> p2 b\<close>
  by (force simp add: pred_Times_def)

lemma pred_Times_almost_assoc:
  \<open>((p1 \<times>\<^sub>P p2) \<times>\<^sub>P p3) ((a,b),c) = (p1 \<times>\<^sub>P p2 \<times>\<^sub>P p3) (a,b,c)\<close>
  by simp

lemma top_pred_Times_top_eq[simp]: \<open>\<top> \<times>\<^sub>P \<top> = \<top>\<close>
  by (simp add: pred_Times_def fun_eq_iff)

lemma bot_pred_Times_eq[simp]: \<open>\<bottom> \<times>\<^sub>P b = \<bottom>\<close>
  by (simp add: pred_Times_def fun_eq_iff)

lemma pred_Times_bot_eq[simp]: \<open>a \<times>\<^sub>P \<bottom> = \<bottom>\<close>
  by (simp add: pred_Times_def fun_eq_iff)

definition rel_Times :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool)\<close>
  (infixr \<open>\<times>\<^sub>R\<close> 80) where
  \<open>r1 \<times>\<^sub>R r2 \<equiv> \<lambda>(a,c) (b, d). r1 a b \<and> r2 c d\<close>

lemma rel_Times_iff[simp]: \<open>(r1 \<times>\<^sub>R r2) (x1, x2) (y1, y2) \<longleftrightarrow> r1 x1 y1 \<and> r2 x2 y2\<close>
  by (force simp add: rel_Times_def)

lemma rel_Times_almost_assoc:
  \<open>((r1 \<times>\<^sub>R r2) \<times>\<^sub>R r3) ((a,b),c) ((a',b'),c') = (r1 \<times>\<^sub>R r2 \<times>\<^sub>R r3) (a,b,c) (a',b',c')\<close>
  by simp

lemma rel_Times_reflp_iff[simp]:
  \<open>reflp (r1 \<times>\<^sub>R r2) \<longleftrightarrow> reflp r1 \<and> reflp r2\<close>
  by (simp add: rel_Times_def reflp_def)

lemma rel_Times_rtranclp_semidistrib:
  \<open>(r1 \<times>\<^sub>R r2)\<^sup>*\<^sup>* \<le> r1\<^sup>*\<^sup>* \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (clarsimp simp add: le_fun_def rel_Times_def)
  apply (metis rtranclp_tuple_rel_semidistrib fst_conv snd_conv)
  done

lemma rel_Times_left_eq_rtranclp_distrib[simp]:
  \<open>((=) \<times>\<^sub>R r2)\<^sup>*\<^sup>* = (=) \<times>\<^sub>R r2\<^sup>*\<^sup>*\<close>
  apply (rule order.antisym)
   apply (force dest: rtranclp_tuple_rel_semidistrib simp add: le_fun_def rel_Times_def)
  apply (force dest: rtranclp_tuple_lift_eq_left simp add: le_fun_def rel_Times_def)
  done

lemma rel_Times_comp[simp]:
  \<open>(a \<times>\<^sub>R b) OO (c \<times>\<^sub>R d) = (a OO c) \<times>\<^sub>R (b OO d)\<close>
  by (force simp add: fun_eq_iff OO_def)


lemma Times_singleton[simp]:
  \<open>{x} \<times> B = Pair x ` B\<close>
  \<open>A \<times> {y} = flip Pair y ` A\<close>
  by force+


section \<open> Relations + Relations as Programs \<close>

definition \<open>deterministic r \<equiv> (\<forall>x y1 y2. r x y1 \<longrightarrow> r x y2 \<longrightarrow> y1 = y2)\<close>

definition \<open>changes r \<equiv> \<lambda>x y. r x y \<and> y \<noteq> x\<close>
abbreviation \<open>changedom r \<equiv> \<lambda>x. \<exists>y. changes r x y\<close>
lemmas changedom_def = changes_def

lemma pre_state_eq_changedom_and_refl:
  \<open>pre_state r = (changedom r) \<squnion> (\<lambda>x. r x x)\<close>
  by (force simp add: changedom_def pre_state_def)
  

lemma changedom_rtranclp[simp]:
  \<open>changedom (r\<^sup>*\<^sup>*) = changedom r\<close>
proof -
  { fix x y
    assume \<open>r\<^sup>*\<^sup>* x y\<close> \<open>y \<noteq> x\<close>
    then have \<open>\<exists>y. r x y \<and> y \<noteq> x\<close>
      by (induct rule: rtranclp_induct) blast+
  } then show ?thesis
    by (fastforce simp add: changedom_def dest: r_into_rtranclp[of r])
qed


text \<open> strongest postcondition, by way of relations \<close>
definition sp :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)\<close> where
  \<open>sp r p \<equiv> \<lambda>y. (\<exists>x. r x y \<and> p x)\<close>

text \<open> weakest liberal precondition, by way of relations \<close>
definition wlp :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>wlp r q \<equiv> \<lambda>x. (\<forall>y. r x y \<longrightarrow> q y)\<close>

paragraph \<open> wlp predicate properties \<close>

lemma wlp_mono:
  \<open>p \<le> q \<Longrightarrow> wlp r p \<le> wlp r q\<close>
  by (force simp add: wlp_def)

lemma wlp_top[simp]:
  \<open>wlp r \<top> = \<top>\<close>
  by (force simp add: wlp_def)

lemma wlp_Ktrue[simp]:
  \<open>wlp r (\<lambda>_. True) = \<top>\<close>
  by (force simp add: wlp_def)

lemma wlp_inf[simp]: \<open>wlp r (p \<sqinter> q) = wlp r p \<sqinter> wlp r q\<close>
  by (force simp add: wlp_def)

lemma wlp_Inf[simp]: \<open>wlp r (\<Sqinter>P) = \<Sqinter>(wlp r ` P)\<close>
  by (fastforce simp add: wlp_def)

lemma wlp_bot[simp]:
  \<open>wlp r \<bottom> = - pre_state r\<close>
  by (simp add: wlp_def fun_eq_iff pre_state_def)

lemma wlp_Kfalse[simp]:
  \<open>wlp r (\<lambda>_. False) = - pre_state r\<close>
  by (simp add: wlp_def fun_eq_iff pre_state_def)

lemma wlp_sup_semidistrib:
  \<open>wlp r p \<squnion> wlp r q \<le> wlp r (p \<squnion> q)\<close>
  by (force simp add: wlp_def)

lemma wlp_disj_determ[simp]:
  \<open>deterministic r \<Longrightarrow> wlp r (p \<squnion> q) = wlp r p \<squnion> wlp r q\<close>
  by (force simp add: deterministic_def wlp_def)

lemma wlp_Sup_semidistrib: \<open>\<Squnion>(wlp r ` P) \<le> wlp r (\<Squnion>P)\<close>
  by (force simp add: wlp_def)

lemma wlp_Sup_determ[simp]:
  assumes \<open>deterministic r\<close>
    and \<open>P \<noteq> {}\<close>
  shows \<open>wlp r (\<Squnion>P) = \<Squnion>(wlp r ` P)\<close>
proof (rule order.antisym; auto simp add: wlp_def)
  fix x
  assume \<open>\<forall>y. r x y \<longrightarrow> (\<exists>px\<in>P. px y)\<close>
  then obtain px where \<open>r x \<le> px\<close> \<open>px \<in> P\<close>
    using assms unfolding deterministic_def
    by (metis ex_in_conv predicate1I)
  then show \<open>\<exists>f\<in>P. \<forall>y. r x y \<longrightarrow> f y\<close>
    by blast
qed

paragraph \<open> wlp relation properties \<close>

lemma wlp_rel_antimono:
  \<open>r1 \<le> r2 \<Longrightarrow> wlp r2 p \<le> wlp r1 p\<close>
  by (force simp add: wlp_def)

lemma wlp_eq_rel[simp]:
  \<open>wlp (=) p = p\<close>
  by (force simp add: wlp_def)

lemma wlp_bot_rel[simp]:
  \<open>wlp \<bottom> p = \<top>\<close>
  by (force simp add: wlp_def)

lemma wlp_top_rel[simp]:
  \<open>p < \<top> \<Longrightarrow> wlp \<top> p = \<bottom>\<close>
  by (force simp add: wlp_def less_fun_def)

lemma wlp_sup_rel[simp]:
  \<open>wlp (r1 \<squnion> r2) p = wlp r1 p \<sqinter> wlp r2 p\<close>
  by (force simp add: wlp_def fun_eq_iff)

lemma wlp_inf_rel_semidistrib:
  \<open>wlp r1 p \<squnion> wlp r2 p \<le> wlp (r1 \<sqinter> r2) p\<close>
  by (force simp add: wlp_def fun_eq_iff)

lemma wlp_comp_rel:
  \<open>wlp r1 (wlp r2 p) = wlp (r1 OO r2) p\<close>
  by (force simp add: wlp_def)

paragraph \<open> sp predicate properties \<close>

lemma sp_mono:
  \<open>p \<le> q \<Longrightarrow> sp r p \<le> sp r q\<close>
  by (force simp add: sp_def)

lemma sp_mono2:
  \<open>p \<le> q \<Longrightarrow> sp r p x \<Longrightarrow> sp r q x\<close>
  by (force simp add: sp_def)

lemma sp_bot[simp]:
  \<open>sp r \<bottom> = \<bottom>\<close>
  by (force simp add: sp_def)

lemma sp_Kfalse[simp]:
  \<open>sp r (\<lambda>_. False) = \<bottom>\<close>
  by (force simp add: sp_def)

lemma sp_sup[simp]:
  \<open>sp r (p \<squnion> q) = sp r p \<squnion> sp r q\<close>
  by (force simp add: sp_def)

lemma sp_Sup[simp]:
  \<open>sp r (\<Squnion>P) = \<Squnion>(sp r ` P)\<close>
  by (fastforce simp add: sp_def)

lemma sp_top[simp]:
  \<open>sp r \<top> = post_state r\<close>
  by (clarsimp simp add: sp_def post_state_def fun_eq_iff)

lemma sp_Ktrue[simp]:
  \<open>sp r (\<lambda>_. True) = post_state r\<close>
  by (force simp add: sp_def post_state_def fun_eq_iff)

lemma sp_inf_semidistrib:
  \<open>sp r (p \<sqinter> q) \<le> sp r p \<sqinter> sp r q\<close>
  by (force simp add: sp_def)

lemma sp_inf_determ[simp]:
  \<open>deterministic (r\<inverse>\<inverse>) \<Longrightarrow> sp r (p \<sqinter> q) = sp r p \<sqinter> sp r q\<close>
  by (simp add: sp_def deterministic_def, blast)

lemma sp_Inf_semidistrib: \<open>sp r (\<Sqinter>P) \<le> \<Sqinter>{sp r p| p. p \<in> P}\<close>
  by (fastforce simp add: sp_def)

lemma sp_Inf_determ[simp]:
  assumes \<open>deterministic (r\<inverse>\<inverse>)\<close>
    and \<open>P \<noteq> {}\<close>
  shows \<open>sp r (\<Sqinter>P) = \<Sqinter>{sp r p| p. p \<in> P}\<close>
  using assms
  apply (intro order.antisym sp_Inf_semidistrib)
  apply (clarsimp simp add: sp_def imp_ex deterministic_def)
  apply (metis ex_in_conv)
  done

paragraph \<open> sp relation properties \<close>

lemma sp_rel_mono:
  \<open>r1 \<le> r2 \<Longrightarrow> sp r1 p \<le> sp r2 p\<close>
  by (force simp add: sp_def)

lemma sp_eq_rel[simp]:
  \<open>sp (=) p = p\<close>
  by (force simp add: sp_def)

lemma sp_bot_rel[simp]:
  \<open>sp \<bottom> p = \<bottom>\<close>
  by (force simp add: sp_def)

lemma sp_top_rel[simp]:
  \<open>\<bottom> < p \<Longrightarrow> sp \<top> p = \<top>\<close>
  by (force simp add: sp_def less_fun_def fun_eq_iff)

lemma sp_sup_rel[simp]:
  \<open>sp (r1 \<squnion> r2) p = sp r1 p \<squnion> sp r2 p\<close>
  by (force simp add: sp_def)

lemma sp_inf_rel_semidistrib:
  \<open>sp (r1 \<sqinter> r2) p \<le> sp r1 p \<sqinter> sp r2 p\<close>
  by (force simp add: sp_def)

lemma sp_comp_rel:
  \<open>sp r2 (sp r1 p) = sp (r1 OO r2) p\<close>
  by (force simp add: sp_def relcompp_apply)

paragraph \<open> wlp/sp misc properties \<close>

lemma wlp_weaker_iff_sp_stronger:
  \<open>p \<le> wlp r q \<longleftrightarrow> sp r p \<le> q\<close>
  by (force simp add: wlp_def sp_def le_fun_def)

lemma wlp_refl_rel_le: \<open>reflp r \<Longrightarrow> wlp r p \<le> p\<close>
  by (metis predicate1I[of \<open>wlp r p\<close> p for r p] reflpD wlp_def)

lemma wlp_refl_relD: \<open>reflp r \<Longrightarrow> wlp r p s \<Longrightarrow> p s\<close>
  by (simp add: reflpD wlp_def)

lemma sp_refl_rel_le: \<open>reflp r \<Longrightarrow> p \<le> sp r p\<close>
  by (metis predicate1I[of p \<open>sp r p\<close> for r p] reflpD sp_def)

lemma sp_refl_relI: \<open>reflp r \<Longrightarrow> p s \<Longrightarrow> sp r p s\<close>
  by (force simp add: reflpD sp_def)

lemma wlp_impliesD[dest]:
  \<open>p \<le> wlp r q  \<Longrightarrow> r s s' \<Longrightarrow> p s \<Longrightarrow> q s'\<close>
  by (metis predicate1D wlp_def)

lemma sp_impliesD[dest]:
  \<open>sp r p \<le> q \<Longrightarrow> r s s' \<Longrightarrow> p s \<Longrightarrow> q s'\<close>
  by (metis predicate1D sp_def)

lemmas refl_rel_wlp_le_sp = order.trans[OF wlp_refl_rel_le sp_refl_rel_le]
lemmas refl_rel_wlp_impl_sp = predicate1D[OF refl_rel_wlp_le_sp]

lemma rel_lift_impl_iff_sp_impl:
  \<open>rel_liftL p \<sqinter> b \<le> rel_liftR q \<longleftrightarrow> sp b p \<le> q\<close>
  by (force simp add: le_fun_def sp_def wlp_def pre_state_def)

lemma sp_wlp_weak_absorb:
  \<open>r2 OO r1 \<le> r \<Longrightarrow> sp r2 (wlp r p) \<le> wlp r1 p\<close>
  by (force simp add: sp_comp_rel le_fun_def sp_def wlp_def OO_def)

lemma sp_wlp_absorb:
  \<open>transp r1 \<Longrightarrow> reflp r2 \<Longrightarrow> r2 \<le> r1 \<Longrightarrow> sp r2 (wlp r1 p) = wlp r1 p\<close>
  by (rule order.antisym; simp add: sp_wlp_weak_absorb sp_refl_rel_le)

lemma wlp_sp_weak_absorb:
  \<open>r2 OO r1 \<le> r \<Longrightarrow> sp r2 p \<le> wlp r1 (sp r p)\<close>
  by (force simp add: sp_comp_rel le_fun_def sp_def wlp_def)

lemma wlp_sp_absorb:
  \<open>reflp r1 \<Longrightarrow> transp r2 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> wlp r1 (sp r2 p) = sp r2 p\<close>
  by (rule order.antisym; simp add: wlp_sp_weak_absorb wlp_refl_rel_le)




\<comment> \<open> TODO: move \<close>

abbreviation map_suml :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a + 'c \<Rightarrow> 'b + 'c\<close> where
  \<open>map_suml f \<equiv> map_sum f (\<lambda>x. x)\<close>

abbreviation map_sumr :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'c\<close> where
  \<open>map_sumr f \<equiv> map_sum (\<lambda>x. x) f\<close>

end
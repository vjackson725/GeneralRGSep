theory SepLogic
  imports Util
begin

thm less_induct

section \<open>Predicate Logic\<close>

lemma pred_conj_simp:
  \<open>(p \<sqinter> q) x \<longleftrightarrow> p x \<and> q x\<close>
  by (simp add:)

lemma pred_disj_simp:
  \<open>(p \<squnion> q) x \<longleftrightarrow> p x \<or> q x\<close>
  by (simp add:)


lemma pred_conjD: \<open>(A1 \<sqinter> A2) s \<Longrightarrow> A1 \<le> B1 \<Longrightarrow> A2 \<le> B2 \<Longrightarrow> (B1 \<sqinter> B2) s\<close>
  by blast

lemma pred_abac_eq_abc:
  fixes A B C :: \<open>'a :: lattice\<close>
  shows \<open>(A \<sqinter> B) \<sqinter> A \<sqinter> C = A \<sqinter> B \<sqinter> C\<close>
  by (simp add: inf.absorb1)

section \<open> mfault \<close>

datatype 'a mfault =
  Success (the_success: 'a)
  | Fault

instantiation mfault :: (ord) ord
begin

fun less_eq_mfault :: \<open>'a mfault \<Rightarrow> 'a mfault \<Rightarrow> bool\<close> where
  \<open>less_eq_mfault _ Fault = True\<close>
| \<open>less_eq_mfault Fault (Success b) = False\<close>
| \<open>less_eq_mfault (Success a) (Success b) = (a \<le> b)\<close>

lemma less_eq_mfault_def:
  \<open>a \<le> b =
    (case b of
      Fault \<Rightarrow> True
    | Success b \<Rightarrow>
      (case a of
        Fault \<Rightarrow> False
      | Success a \<Rightarrow> a \<le> b))\<close>
  by (cases a; cases b; force)

fun less_mfault :: \<open>'a mfault \<Rightarrow> 'a mfault \<Rightarrow> bool\<close> where
  \<open>less_mfault Fault _ = False\<close>
| \<open>less_mfault (Success a) Fault = True\<close>
| \<open>less_mfault (Success a) (Success b) = (a < b)\<close>

lemma less_mfault_def:
  \<open>a < b =
    (case a of
      Fault \<Rightarrow> False
    | Success a \<Rightarrow>
      (case b of
        Fault \<Rightarrow> True
      | Success b \<Rightarrow> a < b))\<close>
  by (cases a; cases b; force)

instance proof qed

end

instantiation mfault :: (preorder) preorder
begin

instance proof
  fix x y z :: \<open>'a :: preorder mfault\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close>
    by (simp add: less_eq_mfault_def less_mfault_def mfault.case_eq_if less_le_not_le)
  show \<open>x \<le> x\<close>
    by (simp add: less_eq_mfault_def mfault.case_eq_if)
  show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
    by (force dest: order_trans simp add: less_eq_mfault_def split: mfault.splits)
qed

end


instantiation mfault :: (order) order_top
begin

definition \<open>top_mfault \<equiv> Fault\<close>

instance proof
  fix x y z :: \<open>'a :: order mfault\<close>
  show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
    by (simp add: less_eq_mfault_def split: mfault.splits)
  show \<open>x \<le> top\<close>
    by (simp add: top_mfault_def)
qed

end

instantiation mfault :: (linorder) linorder
begin

instance proof
  fix x y z :: \<open>'a :: linorder mfault\<close>
  show \<open>x \<le> y \<or> y \<le> x\<close>
    by (cases x; cases y; force)
qed

end

instantiation mfault :: (order_bot) order_bot
begin

definition \<open>bot_mfault = Success bot\<close>

instance proof
  fix a :: \<open>'a :: order_bot mfault\<close>
  show \<open>\<bottom> \<le> a\<close>
    by (simp add: bot_mfault_def less_eq_mfault_def mfault.case_eq_if)
qed

end

section \<open> Separation Logic \<close>

subsection \<open> Common Notions \<close>


class disjoint =
  fixes disjoint :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>##\<close> 60)

class disjoint_zero = disjoint + zero +
  assumes zero_disjointL[simp]: \<open>0 ## a\<close>
  assumes zero_disjointR[simp]: \<open>a ## 0\<close>

subsection \<open> Permission Algebras \<close>

class perm_alg = disjoint + plus + order +
  (* ordered partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  (* separation laws *)
  assumes disjoint_symm: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  assumes disjoint_add_right_commute: \<open>a ## c \<Longrightarrow> b ## a + c \<Longrightarrow> a ## (b + c)\<close>
  assumes positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> a + a = a\<close>
  assumes less_iff_sepadd: \<open>a < b \<longleftrightarrow> a \<noteq> b \<and> (\<exists>c. a ## c \<and> b = a + c)\<close>
  (* exclusion laws *)
  (* assumes no_almost_units: \<open>(\<And>x. x ## u \<Longrightarrow> x + u = x) \<Longrightarrow> u ## u\<close> *)
begin

lemma le_iff_sepadd_weak: \<open>a \<le> b \<longleftrightarrow> a = b \<or> (\<exists>c. a ## c \<and> b = a + c)\<close>
  using le_less less_iff_sepadd by auto

lemma disjoint_symm_iff: \<open>a ## b \<longleftrightarrow> b ## a\<close>
  using disjoint_symm by blast

lemma partial_le_plus[simp]: \<open>a ## b \<Longrightarrow> a \<le> a + b\<close>
  by (metis less_iff_sepadd nless_le order.refl)

lemma partial_le_plus2[simp]: \<open>a ## b \<Longrightarrow> b \<le> a + b\<close>
  by (metis partial_le_plus disjoint_symm partial_add_commute)

(* TODO: think about decreasing and increasing elements from
    'Bringing order to the separation logic Jungle'.
  All our elements are increasing, I think, because of the above two rules.
*)

lemma common_subresource_selfsep:
  \<open>a ## b \<Longrightarrow> ab \<le> a \<Longrightarrow> ab \<le> b \<Longrightarrow> ab ## ab\<close>
  by (metis disjoint_add_rightL disjoint_symm order.order_iff_strict less_iff_sepadd)

lemma disjoint_add_rightR: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## c\<close>
  by (metis disjoint_add_rightL disjoint_symm partial_add_commute)

lemma disjoint_add_leftL: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## c\<close>
  using disjoint_add_rightL disjoint_symm by blast

lemma disjoint_add_leftR: \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c\<close>
  by (metis disjoint_add_leftL disjoint_symm partial_add_commute)

lemma disjoint_add_commuteL: \<open>c ## b \<Longrightarrow> c + b ## a \<Longrightarrow> a + b ## c\<close>
  by (simp add: disjoint_add_right_commute disjoint_symm)

lemma disjoint_add_swap:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + b ## c\<close>
  using disjoint_add_commuteL disjoint_symm_iff partial_add_commute by auto

lemma disjoint_add_swap2:
  \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> a ## b + c\<close>
  by (metis disjoint_add_commuteL disjoint_add_leftR disjoint_symm partial_add_commute)

lemma weak_positivity: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> a ## a\<close>
  by (meson disjoint_add_rightL disjoint_symm)

lemma weak_positivityR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> b ## b\<close>
  using disjoint_symm partial_add_commute weak_positivity by blast

lemma positivityR: \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> c ## c \<Longrightarrow> c + c = c \<Longrightarrow> b + b = b\<close>
  using disjoint_symm partial_add_commute positivity by blast

lemma partial_add_left_commute:
  \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> b + (a + c) = a + (b + c)\<close>
  by (metis disjoint_symm partial_add_assoc partial_add_commute)

lemma disjoint_preservation:
  \<open>a' \<le> a \<Longrightarrow> a ## b \<Longrightarrow> a' ## b\<close>
  by (metis disjoint_add_leftL order.order_iff_strict less_iff_sepadd)

lemma partial_add_double_assoc:
  \<open>a ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> b ## c + d \<Longrightarrow> a ## b + (c + d) \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute partial_add_assoc
      partial_add_left_commute)

lemma sepadd_left_mono:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b \<le> c \<Longrightarrow> a + b \<le> a + c\<close>
  by (simp add: le_iff_sepadd_weak,
      metis disjoint_add_rightR disjoint_add_swap partial_add_assoc)

lemma sepadd_right_mono: \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> a \<le> b \<Longrightarrow> a + c \<le> b + c\<close>
  by (metis disjoint_symm_iff partial_add_commute sepadd_left_mono)

subsection \<open> unit_sepadd \<close>

definition \<open>unit_sepadd a \<equiv> \<forall>b. a ## b \<longrightarrow> a + b = b\<close>

subsection \<open>sepdomeq\<close>

definition \<open>sepdomeq a b \<equiv> \<forall>c. a ## c = b ## c\<close>

lemma sepdomeq_reflp:
  \<open>reflp sepdomeq\<close>
  by (simp add: reflpI sepdomeq_def)

lemma sepdomeq_symp:
  \<open>symp sepdomeq\<close>
  by (metis sepdomeq_def sympI)

lemma sepdomeq_transp:
  \<open>transp sepdomeq\<close>
  by (simp add: sepdomeq_def transp_def)

lemma same_sepdom_disjoint_leftD:
  \<open>sepdomeq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomeq_def)

lemma sepdomeq_disjoint_rightD:
  \<open>sepdomeq a b \<Longrightarrow> b ## c \<Longrightarrow> a ## c\<close>
  by (simp add: sepdomeq_def)

definition \<open>sepdomsubseteq a b \<equiv> \<forall>c. a ## c \<longrightarrow> b ## c\<close>

lemma sepdomsubseteq_reflp:
  \<open>reflp sepdomsubseteq\<close>
  by (simp add: reflpI sepdomsubseteq_def)

lemma sepdomsubseteq_transp:
  \<open>transp sepdomsubseteq\<close>
  by (simp add: sepdomsubseteq_def transp_def)

lemma sepdomsubseteq_disjointD:
  \<open>sepdomsubseteq a b \<Longrightarrow> a ## c \<Longrightarrow> b ## c\<close>
  by (simp add: sepdomsubseteq_def)

subsection \<open> Greatest lower bound \<close>

definition
  \<open>glb_exists a b \<equiv> \<exists>ab. ab \<le> a \<and> ab \<le> b \<and> (\<forall>ab'. ab' \<le> a \<longrightarrow> ab' \<le> b \<longrightarrow> ab' \<le> ab)\<close>

definition \<open>glb a b \<equiv> (GREATEST ab. ab \<le> a \<and> ab \<le> b)\<close>

lemma weak_distrib_law:
  assumes
    \<open>a ## b\<close>
    \<open>a ## c\<close>
    \<open>glb_exists b c\<close>
    \<open>glb_exists (a + b) (a + c)\<close>
  shows
    \<open>a + glb b c \<le> glb (a + b) (a + c)\<close>
proof -
  obtain bc where
    \<open>bc \<le> b\<close>
    \<open>bc \<le> c\<close>
    \<open>\<forall>bc'. bc' \<le> b \<longrightarrow> bc' \<le> c \<longrightarrow> bc' \<le> bc\<close>
    using assms(3) glb_exists_def by blast
  moreover obtain abac where
    \<open>abac \<le> a + b\<close>
    \<open>abac \<le> a + c\<close>
    \<open>\<forall>abac'. abac' \<le> a + b \<longrightarrow> abac' \<le> a + c \<longrightarrow> abac' \<le> abac\<close>
    using assms(4) glb_exists_def by blast
  ultimately show ?thesis
    unfolding glb_def
    using assms(1,2)
    apply -
    apply (subst Greatest_equality[where x=bc], blast, blast)
    apply (subst Greatest_equality[where x=abac], blast, blast)
    apply (meson disjoint_preservation disjoint_symm_iff sepadd_left_mono)
    done
qed

lemma weak_distrib_law2:
  \<open>b ## c \<Longrightarrow>
    glb_exists a b \<Longrightarrow>
    glb_exists a c \<Longrightarrow>
    glb_exists a (b + c) \<Longrightarrow>
    glb a b + glb a c \<le> glb a (b + c)\<close>
  text \<open> not true! \<close>
  oops

subsection \<open> Seplogic connectives \<close>

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<close> 88) where
  \<open>P \<^emph> Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

definition sepimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<^emph>\<close> 65) where
  \<open>P \<midarrow>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1. h ## h1 \<longrightarrow> P h1 \<longrightarrow> Q (h + h1)\<close>

definition sepcoimp :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<sim>\<^emph>\<close> 65) where
  \<open>P \<sim>\<^emph> Q \<equiv> \<lambda>h. \<forall>h1 h2. h1 ## h2 \<longrightarrow> h = h1 + h2 \<longrightarrow> P h1 \<longrightarrow> Q h2\<close>

definition septract :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<midarrow>\<odot>\<close> 67) where
  \<open>P \<midarrow>\<odot> Q \<equiv> \<lambda>h. \<exists>h1. h ## h1 \<and> P h1 \<and> Q (h + h1)\<close>

definition septract_rev :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixr \<open>\<odot>\<midarrow>\<close> 67) where
  \<open>P \<odot>\<midarrow> Q \<equiv> \<lambda>h. \<exists>h'. h ## h' \<and> P (h + h') \<and> Q h'\<close>

definition subheapexist :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>subheapexist P \<equiv> \<lambda>h. \<exists>h1. h1 \<le> h \<and> P h1\<close>

subsection \<open> Seplogic connective properties \<close>

lemma septract_reverse: \<open>P \<midarrow>\<odot> Q = Q \<odot>\<midarrow> P\<close>
  by (force simp add: septract_def septract_rev_def)

lemma sepconj_assoc: \<open>(P \<^emph> Q) \<^emph> R = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (intro ext iffI)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_symm partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_comm: \<open>P \<^emph> Q = Q \<^emph> P\<close>
  unfolding sepconj_def
  by (metis disjoint_symm partial_add_commute)

lemma sepconj_left_comm: \<open>Q \<^emph> (P \<^emph> R) = P \<^emph> (Q \<^emph> R)\<close>
  apply (clarsimp simp add: sepconj_def ex_simps[symmetric] partial_add_assoc simp del: ex_simps)
  apply (rule ext)
  apply (metis disjoint_add_rightR disjoint_add_rightL disjoint_add_right_commute
      partial_add_left_commute)
  done

lemmas sepconj_ac = sepconj_assoc sepconj_comm sepconj_left_comm

(*

\<^emph>   < ~ >  \<midarrow>\<^emph>
|           X
\<sim>\<^emph>  < ~ > \<midarrow>\<odot>

*)


lemma septract_sepimp_dual: \<open>P \<midarrow>\<odot> Q = -(P \<midarrow>\<^emph> (-Q))\<close>
  unfolding septract_def sepimp_def
  by force

lemma sepimp_sepcoimp_dual: \<open>P \<sim>\<^emph> Q = -(P \<^emph> (-Q))\<close>
  unfolding sepconj_def sepcoimp_def
  by force

lemma sepconj_sepimp_galois: \<open>P \<^emph> Q \<le> R \<longleftrightarrow> P \<le> Q \<midarrow>\<^emph> R\<close>
  using sepconj_def sepimp_def by fastforce

lemma sepcoimp_septract_galois: \<open>P \<odot>\<midarrow> Q \<le> R \<longleftrightarrow> P \<le> Q \<sim>\<^emph> R\<close>
  unfolding sepcoimp_def septract_rev_def le_fun_def
  using disjoint_symm partial_add_commute by fastforce

lemma sepcoimp_curry: \<open>P \<sim>\<^emph> Q \<sim>\<^emph> R = P \<^emph> Q \<sim>\<^emph> R\<close>
  apply (clarsimp simp add: sepcoimp_def sepconj_def)
  apply (intro ext iffI; clarsimp)
   apply (metis disjoint_add_leftR disjoint_add_right_commute disjoint_symm partial_add_assoc
      partial_add_commute)+
  done

lemma sepconj_mono[intro]:
  \<open>P \<le> P' \<Longrightarrow> Q \<le> Q' \<Longrightarrow> P \<^emph> Q \<le> P' \<^emph> Q'\<close>
  using sepconj_def by auto

lemma sepconj_monoL[intro]:
  \<open>P \<le> Q \<Longrightarrow> P \<^emph> R \<le> Q \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_monoR[intro]:
  \<open>Q \<le> R \<Longrightarrow> P \<^emph> Q \<le> P \<^emph> R\<close>
  using sepconj_def by auto

lemma sepconj_comm_imp:
  \<open>P \<^emph> Q \<le> Q \<^emph> P\<close>
  by (simp add: sepconj_comm)

lemma sepimp_sepconjL:
  \<open>P \<^emph> Q \<midarrow>\<^emph> R = P \<midarrow>\<^emph> Q \<midarrow>\<^emph> R\<close>
  apply (clarsimp simp add: sepconj_def sepimp_def fun_eq_iff)
  apply (rule iffI)
   apply (metis disjoint_add_rightR disjoint_add_right_commute disjoint_symm partial_add_assoc
      partial_add_commute)+
  done

lemma sepimp_conjR:
  \<open>P \<midarrow>\<^emph> Q \<sqinter> R = (P \<midarrow>\<^emph> Q) \<sqinter> (P \<midarrow>\<^emph> R)\<close>
  by (force simp add: sepimp_def fun_eq_iff)

section \<open> Precision \<close>

definition precise :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>precise P \<equiv> \<forall>h1 h1' h2 h2'.
                  P h1 \<longrightarrow> P h2 \<longrightarrow> h1 ## h1' \<longrightarrow> h2 ## h2' \<longrightarrow> h1 + h1' = h2 + h2' \<longrightarrow>
                  h1 = h2\<close>

definition intuitionistic :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<le> h' \<longrightarrow> P h'\<close>


lemma strong_sepcoimp_imp_sepconj:
  \<open>(P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> Q\<close>
  by (force simp add: sepconj_def sepcoimp_def precise_def le_fun_def)

lemma sepconj_pdisj_distrib_left: \<open>P \<^emph> (Q1 \<squnion> Q2) = P \<^emph> Q1 \<squnion> P \<^emph> Q2\<close>
  by (force simp add: sepconj_def)

lemma sepcoimp_pconj_distrib_left:
  \<open>P \<sim>\<^emph> (Q \<sqinter> Q') = (P \<sim>\<^emph> Q) \<sqinter> (P \<sim>\<^emph> Q')\<close>
  by (force simp add: sepcoimp_def)

lemma sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp:
  shows \<open>(\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')) \<longleftrightarrow> (\<forall>Q. P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q))\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
  apply (intro iffI)
  subgoal
    apply (rule allI)
    apply (rule ext)
    apply (rule iffI)
     apply simp
     apply (rule conjI)
      apply blast
     apply clarsimp
     apply (drule_tac x=\<open>Q\<close> in spec)
     apply (drule_tac x=\<open>(=) h2a\<close> in spec)
     apply (drule_tac x=\<open>h1a + h2a\<close> in cong[OF _ refl])
     apply fastforce
    apply fastforce
    done
  apply (simp add: fun_eq_iff, blast)
  done


lemma sepconj_distrib_conj_imp_sepconj_eq_strong_sepcoimp:
  assumes \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  shows \<open>P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  using assms sepconj_distrib_conj_iff_sepconj_eq_strong_sepcoimp
  by blast

lemma sepconj_middle_monotone_left: \<open>A1 \<^emph> A2 \<le> B \<Longrightarrow> A1 \<^emph> C \<^emph> A2 \<le> C \<^emph> B\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_monoL)

lemma sepconj_middle_monotone_right: \<open>A \<le> B1 \<^emph> B2 \<Longrightarrow> C \<^emph> A \<le> B1 \<^emph> C \<^emph> B2\<close>
  by (metis sepconj_assoc sepconj_comm sepconj_monoL)


definition supported :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>supported P \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>hp. P hp \<and> hp \<le> s \<and> (\<forall>s'. hp \<le> s' \<longrightarrow> s' \<le> s \<longrightarrow> P s'))\<close>

lemma precise_to_supported:
  \<open>precise P \<Longrightarrow> supported (P \<^emph> \<top>)\<close>
  by (metis order.eq_iff supported_def)

end

subsection \<open> Separation Algebras \<close>

class sep_alg = perm_alg + disjoint_zero + order_bot +
  assumes partial_add_0[simp]: \<open>0 + a = a\<close>
begin

lemma le_iff_sepadd: \<open>a \<le> b \<longleftrightarrow> (\<exists>c. a ## c \<and> b = a + c)\<close>
  by (metis order.order_iff_strict less_iff_sepadd partial_add_0 partial_add_commute zero_disjointR)

subsection \<open>partial canonically_ordered_monoid_add lemmas\<close>

lemma zero_le[simp]: \<open>0 \<le> x\<close>
  by (metis partial_le_plus partial_add_0 zero_disjointL)

lemma le_zero_eq[simp]: "n \<le> 0 \<longleftrightarrow> n = 0"
  by (auto intro: order.antisym)

lemma not_less_zero[simp]: "\<not> n < 0"
  by (auto simp: less_le)

lemma zero_less_iff_neq_zero: "0 < n \<longleftrightarrow> n \<noteq> 0"
  by (auto simp: less_le)

lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 < n"
  by (rule zero_less_iff_neq_zero[THEN iffD2]) iprover

lemma not_gr_zero[simp]: "\<not> 0 < n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

lemma gr_implies_not_zero: "m < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma zero_only_unit:
  \<open>unit_sepadd x \<Longrightarrow> x = 0\<close>
  by (metis partial_add_0 partial_add_commute unit_sepadd_def zero_disjointR)

lemma sepadd_eq_0_iff_both_eq_0[simp]: "x ## y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (metis partial_le_plus le_zero_eq partial_add_0)

lemma zero_eq_sepadd_iff_both_eq_0[simp]: "x ## y \<Longrightarrow> 0 = x + y \<longleftrightarrow> x = 0 \<and> y = 0"
  using sepadd_eq_0_iff_both_eq_0[of x y] unfolding eq_commute[of 0] .

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero

subsection \<open>Misc\<close>

lemma unit_sepadd_0: \<open>unit_sepadd 0\<close>
  by (simp add: unit_sepadd_def)

lemma sep_add_0_right[simp]: "a + 0 = a"
  by (metis zero_disjointR partial_add_0 partial_add_commute)

definition sepconj_mfault ::
  \<open>('a \<Rightarrow> bool) mfault \<Rightarrow> ('a \<Rightarrow> bool) mfault \<Rightarrow> ('a \<Rightarrow> bool) mfault\<close> (infixl \<open>\<^emph>\<^sub>f\<close> 88)
  where
    \<open>P \<^emph>\<^sub>f Q \<equiv>
      case P of
        Fault \<Rightarrow> Fault
      | Success P \<Rightarrow>
        (case Q of
          Fault \<Rightarrow> Fault
        | Success Q \<Rightarrow> Success (\<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2))\<close>


definition emp :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>emp \<equiv> (\<lambda>h. h = 0)\<close>

definition emp_mfault :: \<open>('a \<Rightarrow> bool) mfault\<close> ("emp\<^sub>f") where
  \<open>emp\<^sub>f \<equiv> Success emp\<close>

fun iterated_sepconj :: \<open>('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>iterated_sepconj (P # Ps) = P \<^emph> iterated_sepconj Ps\<close>
| \<open>iterated_sepconj [] = emp\<close>

lemma emp_sepconj_unit[simp]: \<open>emp \<^emph> P = P\<close>
  by (simp add: emp_def sepconj_def)

lemma emp_sepconj_unit_right[simp]: \<open>P \<^emph> emp = P\<close>
  by (simp add: emp_def sepconj_def)

lemma secoimp_imp_sepconj:
  \<open>P \<sqinter> (P \<sim>\<^emph> Q) \<le> P \<^emph> (Q \<sqinter> emp)\<close>
  unfolding sepcoimp_def sepconj_def le_fun_def le_bool_def emp_def
  by force

lemma not_coimp_emp:
  \<open>h \<noteq> 0 \<Longrightarrow> (- (\<top> \<sim>\<^emph> emp)) h\<close>
  apply (clarsimp simp add: sepcoimp_def emp_def)
  apply (rule_tac x=0 in exI, force)
  done

lemma le_iff_sepadd:
  \<open>a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)\<close>
  nitpick[card=2]
  oops

lemma precise_to_intuitionistic:
  fixes P :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>precise P \<Longrightarrow> intuitionistic (P \<^emph> \<top>)\<close>
  apply (simp add: sepconj_def precise_def intuitionistic_def)
  apply clarsimp
  oops

lemma supported_intuitionistic_to_precise:
  \<open>supported P \<Longrightarrow> intuitionistic P \<Longrightarrow> precise (P \<sqinter> - (P \<^emph> (-emp)))\<close>
  nitpick[card=4]
  oops

end

section \<open> Permission/Separation Algebra Subclasses \<close>

subsection \<open>Strongly Separated Separation Algebra\<close>

class strong_separated_sep_alg = sep_alg +
  assumes only_zero_self_sep: \<open>a ## a \<Longrightarrow> a = 0\<close>
begin

lemma selfsep_iff: \<open>a ## a \<longleftrightarrow> a = 0\<close>
  using only_zero_self_sep zero_disjointL by blast

end

subsection \<open>Trivial Self-disjointness Separation Algebra\<close>

class trivial_selfdisjoint_perm_alg = perm_alg +
  assumes disjointness: \<open>a ## a \<Longrightarrow> a + a = b \<Longrightarrow> a = b\<close>

class trivial_selfdisjoint_sep_alg = sep_alg + trivial_selfdisjoint_perm_alg

subsection \<open>Cross-Split Separation Algebra\<close>

class crosssplit_perm_alg = perm_alg +
  assumes cross_split:
  \<open>a ## b \<Longrightarrow> c ## d \<Longrightarrow> a + b = z \<Longrightarrow> c + d = z \<Longrightarrow>
    \<exists>ac ad bc bd.
      ac ## ad \<and> bc ## bd \<and> ac ## bc \<and> ad ## bd \<and>
      ac + ad = a \<and> bc + bd = b \<and> ac + bc = c \<and> ad + bd = d\<close>

class crosssplit_sep_alg = sep_alg + crosssplit_perm_alg

subsection \<open>Cancellative Separation Logic\<close>

class cancel_perm_alg = perm_alg +
  assumes partial_right_cancel[simp]: \<open>\<And>a b c. a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
begin

lemma partial_right_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (a + c = b + c) = (a = b)\<close>
  using partial_right_cancel disjoint_symm
  by force

lemma partial_left_cancel[simp]:
  \<open>a ## c \<Longrightarrow> b ## c \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  by (metis partial_add_commute partial_right_cancel)

lemma partial_left_cancel2[simp]:
  \<open>c ## a \<Longrightarrow> c ## b \<Longrightarrow> (c + a = c + b) = (a = b)\<close>
  using partial_left_cancel disjoint_symm
  by force

lemmas partial_right_cancelD = iffD1[OF partial_right_cancel, rotated 2]
lemmas partial_right_cancel2D = iffD1[OF partial_right_cancel2, rotated 2]
lemmas partial_left_cancelD = iffD1[OF partial_left_cancel, rotated 2]
lemmas partial_left_cancel2D = iffD1[OF partial_left_cancel2, rotated 2]


lemma precise_iff_conj_distrib:
  fixes P :: \<open>'a \<Rightarrow> bool\<close>
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q'))\<close>
proof (rule iffI)
  assume distrib_assm: \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
  show \<open>precise P\<close>
  proof (clarsimp simp add: precise_def)
    fix h1 h1' h2 h2'
    assume precise_assms:
      \<open>h1 + h1' = h2 + h2'\<close>
      \<open>h1 ## h1'\<close>
      \<open>h2 ## h2'\<close>
      \<open>P h1\<close>
      \<open>P h2\<close>

    have \<open>(P \<^emph> ((=) h1')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by (metis (mono_tags, lifting) perm_alg_class.sepconj_def)
    moreover have \<open>(P \<^emph> ((=) h2')) (h2+h2')\<close>
      using precise_assms partial_add_commute disjoint_symm sepconj_def
      by (metis (mono_tags, lifting) perm_alg_class.sepconj_def)
    ultimately have \<open>(P \<^emph> ((=) h1' \<sqinter> (=) h2')) (h2+h2')\<close>
      using distrib_assm precise_assms
      by simp
    then show \<open>h1 = h2\<close>
      using precise_assms disjoint_symm
      by (force dest: partial_right_cancelD simp add: sepconj_def)
  qed
next
  assume precise_assm: \<open>precise P\<close>
  then show \<open>\<forall>Q Q'. P \<^emph> (Q \<sqinter> Q') = (P \<^emph> Q) \<sqinter> (P \<^emph> Q')\<close>
    by (simp add: sepconj_def precise_def fun_eq_iff, blast dest: partial_left_cancel2)
qed

lemma precise_iff_all_sepconj_imp_sepcoimp:
  shows \<open>precise P \<longleftrightarrow> (\<forall>Q. P \<^emph> Q \<le> P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
  apply (rule iffI)
   apply (metis partial_left_cancel2)
  apply (metis le_less order.irrefl partial_right_cancel)
  done

lemma precise_sepconj_eq_strong_sepcoimp:
  shows \<open>precise P \<Longrightarrow> P \<^emph> Q = (P \<^emph> \<top>) \<sqinter> (P \<sim>\<^emph> Q)\<close>
  apply (clarsimp simp add: sepconj_def sepcoimp_def precise_def le_fun_def)
  apply (rule ext)
  apply (rule iffI)
  apply (blast dest: partial_left_cancel2)
  apply blast
  done

end

class cancel_sep_alg = cancel_perm_alg + sep_alg
begin

lemma weak_emp:
  \<open>a ## a \<and> a + a = a \<longleftrightarrow> a = 0\<close>
  by (metis sep_add_0_right zero_disjointR partial_left_cancel2)

lemma strong_positivity:
  \<open>a ## b \<Longrightarrow> c ## c \<Longrightarrow> a + b = c \<Longrightarrow> c + c = c \<Longrightarrow> a = b \<and> b = c\<close>
  using weak_emp by force

lemma \<open>(a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>) \<le> ((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top>\<close>
  nitpick[card=4]
  oops

lemma \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
proof -
  have F1: \<open>((a \<^emph> b) \<squnion> (a \<sqinter> b)) \<^emph> \<top> = (a \<^emph> b) \<^emph> \<top> \<squnion> (a \<sqinter> b) \<^emph> \<top>\<close>
    by (simp add: sepconj_comm sepconj_pdisj_distrib_left)
  moreover have \<open>a \<^emph> b \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (metis le_infI sepconj_comm sepconj_middle_monotone_left top_greatest)
  moreover have \<open>(a \<sqinter> b) \<^emph> \<top> \<le> (a \<^emph> \<top>) \<sqinter> (b \<^emph> \<top>)\<close>
    by (simp add: sepconj_monoL)
  ultimately show ?thesis
    by simp
qed

end

subsection \<open> Halving \<close>

class halving_perm_alg = perm_alg +
  fixes half :: \<open>'a \<Rightarrow> 'a\<close>
  assumes half_additive_split: \<open>\<And>a. half a + half a = a\<close>
  assumes half_self_disjoint: \<open>\<And>a. half a ## half a\<close>
  assumes half_sepadd_distrib: \<open>\<And>a b. a ## b \<Longrightarrow> half (a + b) = half a + half b\<close>
begin

lemma half_disjoint_preservation_left: \<open>a ## b \<Longrightarrow> half a ## b\<close>
  by (metis disjoint_add_leftR half_additive_split half_self_disjoint)

lemma half_disjoint_preservation_right: \<open>a ## b \<Longrightarrow> a ## half b\<close>
  using half_disjoint_preservation_left disjoint_symm by blast

lemma half_disjoint_preservation: \<open>a ## b \<Longrightarrow> half a ## half b\<close>
  by (simp add: half_disjoint_preservation_left half_disjoint_preservation_right)


lemma half_disjoint_distribL:
  \<open>a ## c \<Longrightarrow> a + c ## b \<Longrightarrow> a + half c ## b + half c\<close>
  by (metis disjoint_add_leftL disjoint_add_right_commute disjoint_symm half_additive_split
      half_self_disjoint partial_add_assoc)

lemma half_disjoint_distribR:
  \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a + half c ## b + half c\<close>
  using half_disjoint_distribL disjoint_symm by blast

lemma half_eq_full_imp_self_additive:
  \<open>half a = a \<Longrightarrow> a + a = a\<close>
  by (metis half_additive_split)

end

class halving_sep_alg = sep_alg + halving_perm_alg

subsection \<open> Disjoint Parts Algebra \<close>

class disjoint_parts_perm_alg = perm_alg +
  assumes disjointness_left_plusI: \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a + b ## c\<close>
begin

lemmas disjointness_left_plusI' =
  disjointness_left_plusI
  disjointness_left_plusI[OF disjoint_symm]
  disjointness_left_plusI[OF _ disjoint_symm]
  disjointness_left_plusI[OF _ _ disjoint_symm]
  disjointness_left_plusI[OF _ disjoint_symm disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm _ disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm disjoint_symm]
  disjointness_left_plusI[OF disjoint_symm disjoint_symm disjoint_symm]

lemma disjointness_right_plusI:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> b ## c \<Longrightarrow> a ## b + c\<close>
  using disjointness_left_plusI disjoint_symm by auto

lemmas disjointness_right_plusI' =
  disjointness_right_plusI
  disjointness_right_plusI[OF disjoint_symm]
  disjointness_right_plusI[OF _ disjoint_symm]
  disjointness_right_plusI[OF _ _ disjoint_symm]
  disjointness_right_plusI[OF _ disjoint_symm disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm _ disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm disjoint_symm]
  disjointness_right_plusI[OF disjoint_symm disjoint_symm disjoint_symm]

lemma disjointness_left_plus_eq:
  \<open>a ## b \<Longrightarrow> a + b ## c \<longleftrightarrow> a ## c \<and> b ## c\<close>
  by (metis disjointness_left_plusI disjoint_add_leftL disjoint_add_leftR)

lemma disjointness_right_plus_eq:
  \<open>b ## c \<Longrightarrow> a ## b + c \<longleftrightarrow> a ## b \<and> a ## c\<close>
  by (metis disjointness_right_plusI disjoint_add_rightL disjoint_add_rightR)

lemma partial_add_double_assoc2:
  \<open>a ## b \<Longrightarrow> a ## c \<Longrightarrow> a ## d \<Longrightarrow> b ## c \<Longrightarrow> b ## d \<Longrightarrow> c ## d \<Longrightarrow> a + b + (c + d) = (a + c) + (b + d)\<close>
  by (meson disjointness_right_plusI partial_add_double_assoc)

end

class disjoint_parts_sep_alg = sep_alg + disjoint_parts_perm_alg

subsection \<open> Indivisible units \<close>

class indivisible_units_perm_alg = perm_alg +
  assumes \<open>x ## y \<Longrightarrow> unit_sepadd (x + y) \<Longrightarrow> unit_sepadd x\<close>

(* nondivisible_units_sep_alg = sep_alg,
    as there's exactly one unit element less than everything else. *)
context sep_alg
begin

lemma \<open>x ## y \<Longrightarrow> unit_sepadd (x + y) \<Longrightarrow> unit_sepadd x\<close>
  using zero_only_unit by fastforce

end

section \<open> Trivial self-disjoint + halving (very boring) \<close>

class trivial_halving_perm_alg = trivial_selfdisjoint_perm_alg + halving_perm_alg
begin

lemma trivial_half[simp]: \<open>half a = a\<close>
  by (simp add: disjointness half_additive_split half_self_disjoint)

end



section \<open> Labelled Permission algebra \<close>

text \<open>
  This subclass is supposed to be the algebraic version of a heap.
  It introduces an order which must be compatible with, but can be more coarse than,
  the subresource relation. The equivalence classes induced by this order represent
  resources with the same set of labels.

  We want labels to form a distributive lattice, to take advantage of
  Birkhoff's representation theorem.
  TODO,sorry: The law \<open>labels_strong_distrib_law\<close> probably does this, but I need to check.
\<close>

class labelled_perm_alg = perm_alg + indivisible_units_perm_alg +
  fixes labels_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50)
    and labels_less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>l\<close> 50)
  assumes labels_leq_less_preorder:
    \<open>preordering labels_leq labels_less\<close>
  assumes labels_less_embeds: \<open>\<And>a b. a < b \<Longrightarrow> a <\<^sub>l b\<close>
  assumes labels_leq_upper_bound:
    \<open>\<And>a b c. a ## b \<Longrightarrow> a \<le>\<^sub>l c \<Longrightarrow> b \<le>\<^sub>l c \<Longrightarrow> a + b \<le>\<^sub>l c\<close>
  assumes labels_strong_distrib_law:
    \<open>\<And>a b c.
      a ## b \<Longrightarrow> a ## c \<Longrightarrow> glb_exists b c \<Longrightarrow> glb_exists (a + b) (a + c) \<Longrightarrow>
        glb (a + b) (a + c) \<le>\<^sub>l a + glb b c\<close>
begin

lemma labels_leq_embeds:
  \<open>a \<le> b \<Longrightarrow> a \<le>\<^sub>l b\<close>
  using labels_leq_less_preorder labels_less_embeds
  by (metis order.order_iff_strict preordering.axioms(1) partial_preordering.refl
      preordering.strict_implies_order)

lemma labels_leq_add:
  \<open>a ## b \<Longrightarrow> a \<le>\<^sub>l (a + b)\<close>
  by (simp add: labels_leq_embeds)

definition labels_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>=\<^sub>l\<close> 50) where
  \<open>labels_eq a b \<equiv> a \<le>\<^sub>l b \<and> b \<le>\<^sub>l a\<close>

lemma labels_eq_equivp: \<open>equivp (=\<^sub>l)\<close>
  unfolding labels_eq_def
  using labels_leq_less_preorder
  by (force intro: equivpI reflpI sympI transpI dest: preordering_refl preordering_trans)

lemma disjoint_units_have_same_labels:
  assumes
    \<open>a ## b\<close>
    \<open>unit_sepadd a\<close>
    \<open>unit_sepadd b\<close>
  shows
    \<open>a =\<^sub>l b\<close>
  using assms
  by (metis labels_eq_def labels_leq_add disjoint_symm unit_sepadd_def)

lemma same_labels_as_unit_is_unit:
  assumes
    \<open>a ## b\<close>
    \<open>unit_sepadd a\<close>
    \<open>a =\<^sub>l b\<close>
  shows
    \<open>unit_sepadd b\<close>
  using assms
  by (metis labels_eq_def order.order_iff_strict labels_leq_less_preorder labels_less_embeds
      partial_le_plus unit_sepadd_def preordering.strict_iff_not)

subsection  \<open> Label overlap \<close>

definition \<open>label_overlap a b \<equiv> \<exists>c. c \<le>\<^sub>l a \<and> c \<le>\<^sub>l b \<and> \<not> unit_sepadd c\<close>

lemma label_overlap_refl:
  \<open>\<not> unit_sepadd a \<Longrightarrow> label_overlap a a\<close>
  using label_overlap_def labels_leq_embeds by blast

lemma label_overlap_sym:
  \<open>label_overlap a b \<Longrightarrow> label_overlap b a\<close>
  using label_overlap_def by blast

lemma same_labels_implies_label_overlap:
  \<open>a =\<^sub>l b \<Longrightarrow> \<not> unit_sepadd a \<Longrightarrow> \<not> unit_sepadd b \<Longrightarrow> label_overlap a b\<close>
  using label_overlap_def labels_eq_def labels_leq_embeds by blast

end

class halving_labelled_perm_alg = halving_perm_alg + labelled_perm_alg
begin

lemma half_subseteq_labels: \<open>half a \<le>\<^sub>l a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_embeds partial_le_plus2)

lemma half_superseteq_labels: \<open>a \<le>\<^sub>l half a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_upper_bound labels_leq_embeds
      order.refl)

lemma half_has_same_labels: \<open>half a =\<^sub>l a\<close>
  by (simp add: half_subseteq_labels half_superseteq_labels labels_eq_def)

end

section \<open> Instances \<close>

instantiation prod  :: (sep_alg,sep_alg) sep_alg
begin

definition plus_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> where
  \<open>plus_prod a b \<equiv> (fst a + fst b, snd a + snd b)\<close>
declare plus_prod_def[simp]

definition less_eq_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_eq_prod a b \<equiv> (fst a \<le> fst b \<and> snd a \<le> snd b)\<close>
declare less_eq_prod_def[simp]

definition less_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>less_prod x y \<equiv> fst x \<le> fst y \<and> snd x \<le> snd y \<and> (\<not> fst y \<le> fst x \<or> \<not> snd y \<le> snd x)\<close>
declare less_prod_def[simp]

definition disjoint_prod  :: \<open>'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool\<close> where
  \<open>disjoint_prod a b \<equiv> (fst a ## fst b \<and> snd a ## snd b)\<close>
declare disjoint_prod_def[simp]

definition zero_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>zero_prod \<equiv> (0, 0)\<close>
declare zero_prod_def[simp]

definition bot_prod  :: \<open>'a \<times> 'b\<close> where
  \<open>bot_prod \<equiv> (\<bottom>, \<bottom>)\<close>
declare bot_prod_def[simp]

instance
  apply standard
                 apply force+
          apply (force simp add: partial_add_assoc)
         apply (force dest: partial_add_commute)
        apply (force simp add: disjoint_symm)
       apply (force dest: disjoint_add_rightL)
      apply (force dest: disjoint_add_right_commute)
     apply (force dest: positivity)
   apply (clarsimp simp add: less_iff_sepadd)
    (* subgoal *)
   apply (rename_tac a1 b1 a2 b2)
   apply (case_tac \<open>a1 = a2\<close>)
    apply (case_tac \<open>b1 = b2\<close>)
     apply force
    apply (metis le_iff_sepadd order_class.order_eq_iff)
   apply (metis le_iff_sepadd order_class.order_eq_iff)
    (* done *)
  apply force
  done

end

instantiation unit :: perm_alg
begin

definition plus_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> unit\<close> where
  \<open>plus_unit a b \<equiv> ()\<close>
declare plus_unit_def[simp]

definition disjoint_unit :: \<open>unit \<Rightarrow> unit \<Rightarrow> bool\<close> where
  \<open>disjoint_unit a b \<equiv> True\<close>
declare disjoint_unit_def[simp]

instance
  by standard simp+

end


end
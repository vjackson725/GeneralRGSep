theory Lang
  imports SepAlgInstances
begin


section \<open> Language Definition \<close>

subsection \<open> Commands \<close>

datatype 'a comm =
  Skip
  | Seq \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>;;\<close> 75)
  | Par \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<parallel>\<close> 65)
  | Indet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<^bold>+\<close> 65)
  | Endet \<open>'a comm\<close> \<open>'a comm\<close> (infixr \<open>\<box>\<close> 65)
  \<comment> \<open> An atomic action is represnted by a precondition and a (relational) post-condition.
       Trying to evaluate the action outside the precondition results in a crash.
       Trying to evaluate the action outside the domain of the postcondition results in deadlock,
       until a state in the domain is reached. \<close>
  | Atomic \<open>'a \<Rightarrow> bool\<close> \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (\<open>\<langle>_, _\<rangle>\<close> [0] 999)
  | Iter \<open>'a comm\<close> (\<open>DO (_) OD\<close> [0] 999)

subsection \<open> substitution \<close>

subsection \<open> Map atoms \<close>

fun map_comm :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a comm \<Rightarrow> 'b comm\<close> where
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
  \<open>map_comm f c = Atomic p q \<longleftrightarrow> (\<exists>p' q'. c = Atomic p' q' \<and> p = (p' \<circ> f) \<and> q = (q' \<circ>\<^sub>2 f))\<close>
  by (induct c; simp add: fun_eq_iff; (argo?; blast))+

lemmas map_comm_rev_iff2 = map_comm_rev_iff[THEN trans[OF eq_commute]]

subsection \<open> All atom commands predicate \<close>

text \<open> Predicate to ensure atomic actions have a given property \<close>

inductive all_atom_comm :: \<open>(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'a comm \<Rightarrow> bool\<close> where
  skip[iff]: \<open>all_atom_comm p Skip\<close>
| seq[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 ;; c2)\<close>
| par[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<parallel> c2)\<close>
| indet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<^bold>+ c2)\<close>
| endet[intro!]: \<open>all_atom_comm p c1 \<Longrightarrow> all_atom_comm p c2 \<Longrightarrow> all_atom_comm p (c1 \<box> c2)\<close>
| iter[intro!]: \<open>all_atom_comm p c \<Longrightarrow> all_atom_comm p (DO c OD)\<close>
| atom[intro!]: \<open>p ap aq \<Longrightarrow> all_atom_comm p (Atomic ap aq)\<close>

inductive_cases all_atom_comm_seqE[elim!]: \<open>all_atom_comm p (c1 ;; c2)\<close>
inductive_cases all_atom_comm_indetE[elim!]: \<open>all_atom_comm p (c1 \<^bold>+ c2)\<close>
inductive_cases all_atom_comm_endetE[elim!]: \<open>all_atom_comm p (c1 \<box> c2)\<close>
inductive_cases all_atom_comm_parE[elim!]: \<open>all_atom_comm p (c1 \<parallel> c2)\<close>
inductive_cases all_atom_comm_iterE[elim!]: \<open>all_atom_comm p (DO c OD)\<close>
inductive_cases all_atom_comm_atomE[elim!]: \<open>all_atom_comm p (Atomic ap aq)\<close>

lemma all_atom_comm_simps[simp]:
  \<open>all_atom_comm p (c1 ;; c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<^bold>+ c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<box> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (c1 \<parallel> c2) \<longleftrightarrow> all_atom_comm p c1 \<and> all_atom_comm p c2\<close>
  \<open>all_atom_comm p (DO c OD) \<longleftrightarrow> all_atom_comm p c\<close>
  \<open>all_atom_comm p (Atomic ap aq) \<longleftrightarrow> p ap aq\<close>
  by fastforce+

lemma all_atom_comm_pred_mono:
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p c \<Longrightarrow> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_pred_mono':
  \<open>p \<le> q \<Longrightarrow> all_atom_comm p \<le> all_atom_comm q\<close>
  using all_atom_comm_pred_mono by auto

lemmas all_atom_comm_pred_monoD = all_atom_comm_pred_mono[rotated]

lemma all_atom_comm_conj_eq:
  \<open>all_atom_comm (p \<sqinter> q) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_pconj_eq[simp]:
  \<open>all_atom_comm (p \<sqinter> q) c \<longleftrightarrow> all_atom_comm p c \<and> all_atom_comm q c\<close>
  by (induct c) force+

lemma all_atom_comm_top_eq[simp]:
  \<open>all_atom_comm \<top> c\<close>
  by (induct c) force+

definition
  \<open>atoms_subrel_of r \<equiv> all_atom_comm (\<lambda>ap aq. ap \<le> pre_state r \<and> aq \<sqinter> rel_liftL ap \<le> r)\<close>


section \<open> Specific Languages \<close>

subsection \<open> Sugared atomic programs \<close>

subsubsection \<open> Assert \<close>

definition \<open>Assert p \<equiv> Atomic p ((=) \<sqinter> rel_liftL p)\<close>

subsubsection \<open> Assume \<close>

definition \<open>Assume p \<equiv> Atomic \<top> ((=) \<sqinter> rel_liftL p)\<close>

subsection \<open> If-then-else \<close>

definition \<open>IfThenElse p ct cf \<equiv> Assume p ;; ct \<box> Assume (-p) ;; cf\<close>

lemma IfThenElse_inject[simp]:
  \<open>IfThenElse p1 ct1 cf1 = IfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (simp add: IfThenElse_def Assume_def fun_eq_iff, blast)

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

definition \<open>WhileLoop p c \<equiv> DO (Assume p ;; c) OD\<close>

lemma WhileLoop_inject[simp]:
  \<open>WhileLoop p1 c1 = WhileLoop p2 c2 \<longleftrightarrow> p1 = p2 \<and> c1 = c2\<close>
  by (simp add: WhileLoop_def Assume_def fun_eq_iff, blast)

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

end